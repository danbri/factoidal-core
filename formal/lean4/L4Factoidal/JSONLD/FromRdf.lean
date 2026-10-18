/-
L4Factoidal.JSONLD.FromRdf — JSON-LD 1.1 "Serialize RDF as JSON-LD".

Port of `formal/fstar/JSONLD.FromRdf.fst`.

Specification implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §8.5 Serialize RDF as JSON-LD Algorithm — node-map construction per
    graph, `rdf:type` folding into `@type`, graph-name nodes carrying
    `@graph`, and node ordering by `@id`;
  * §8.6 RDF to Object Conversion — `useNativeTypes`, `rdf:JSON`
    literals, `xsd:string` unwrapping, language-tagged strings;
  * §8.7 List Conversion — an `rdf:first`/`rdf:rest` chain of
    referenced-once blank nodes terminating at `rdf:nil` collapses to
    `{"@list": [...]}`;
  * the `rdfDirection` API option in both its modes — `i18n-datatype`
    (decode `https://www.w3.org/ns/i18n#<lang>_<dir>` back into
    `@direction`/`@language`) and `compound-literal` (collapse a blank
    node bearing `rdf:value`/`rdf:direction` into a value object).

The output is an EXPANDED-FORM `Json` tree; the consumer compares it
against the suite's `-out.jsonld` fixture through
`JSONLD.ToRdf.expandedEqual` (RFC 8785 canonical equality), which is the
same comparison `bin/jsonld-fromrdf-runner` makes.

## Scoped out

  * RDF 1.2 triple terms have no settled JSON-LD serialisation; a
    dataset containing one is reported as an error (`.ok none` never
    hides it) rather than serialised wrongly. Same choice as the F*
    source.
  * Framing, and the `@embed`-family options, are a separate
    specification.

## Termination

The list/compound-literal resolution walks a `rdf:rest` chain that the
dataset may make cyclic, so — exactly as the F* source does — every such
walk carries an explicit fuel `Nat` derived from the graph's node count
and decreases it on each step. No `partial`, no well-founded recursion.
-/
import L4Factoidal.JSONLD.ToRdf
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.JSONLD.FromRdf

open L4Factoidal.JSON
open L4Factoidal.RDF

/-! ## Options

The subset of the fromRdf option surface the W3C manifest exercises
(JSON-LD 1.1 API §8.5, the `useNativeTypes` / `useRdfType` /
`rdfDirection` parameters). -/

/-- `rdfDirection` is `none`, `some "i18n-datatype"`, or
`some "compound-literal"`; the two transforms are mutually exclusive —
the suite's cross-paired fixtures (di07/di08 feed a compound literal to
an `i18n-datatype` run; di09/di10 the reverse) pin that each is gated
strictly on its own mode. -/
structure Options where
  useNativeTypes : Bool := false
  useRdfType     : Bool := false
  rdfDirection   : Option String := none
  deriving Repr

def defaultOptions : Options := {}

/-! ## Fixed vocabulary IRIs (compared as plain strings) -/

def rdfTypeIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfFirstIri     : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
def rdfRestIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
def rdfNilIri       : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
def rdfJsonIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"
def rdfListIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"
def rdfValueIri     : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#value"
def rdfDirectionIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#direction"
def rdfLanguageIri  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#language"
def i18nPrefix      : String := "https://www.w3.org/ns/i18n#"

def sXsdString  : String := "http://www.w3.org/2001/XMLSchema#string"
def sXsdInteger : String := "http://www.w3.org/2001/XMLSchema#integer"
def sXsdDouble  : String := "http://www.w3.org/2001/XMLSchema#double"
def sXsdBoolean : String := "http://www.w3.org/2001/XMLSchema#boolean"

/-! ## The intermediate object-value tree

`Ov` is the F* source's `ov`: a node reference, a fully-built value
object, or an RDF collection converted to `@list`. Structural equality
is needed for the spec's "if the value is not already in the array"
duplicate check (fixture 0017); `Json` is a NESTED inductive whose
`DecidableEq` is hand-written, so `Ov` likewise gets a hand-written
mutual `eqb` rather than a derived instance (pitfall #1: never
`deriving BEq`). -/
inductive Ov where
  | ref  : String → Ov
  | val  : Json → Ov
  | lst  : List Ov → Ov
  deriving Repr

mutual

/-- Structural equality on `Ov` (port of F*'s eqtype `=` on `ov`). -/
def Ov.eqb : Ov → Ov → Bool
  | .ref a, .ref b => a == b
  | .val a, .val b => a == b
  | .lst a, .lst b => Ov.eqbList a b
  | _, _ => false

def Ov.eqbList : List Ov → List Ov → Bool
  | [], []           => true
  | x :: xs, y :: ys => Ov.eqb x y && Ov.eqbList xs ys
  | _, _             => false

end

instance : BEq Ov := ⟨Ov.eqb⟩

/-- A node object under construction (F*: `fr_node`). `types` and each
property's value list keep insertion order and are deduplicated. -/
structure FrNode where
  id    : String
  blank : Bool
  types : List String
  props : List (String × List Ov)
  deriving Repr

/-- One named graph's node map plus its display name (F*: `named_nm`). -/
structure NamedNm where
  name  : String
  blank : Bool
  map   : List FrNode
  deriving Repr

/-! ## Display identifiers

The F* `named_graph.ng_name` is a bare IRI string that packs a
blank-node label as `"_:label"`; this port's `RDF.NamedGraph.name` is a
`Subject`, so the packing happens here instead. -/

def subjId : Subject → String
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

def subjIsBlank : Subject → Bool
  | .bnode _ => true
  | _        => false

/-- `some (display-id, isBlank)` when the object is a node; `none` for a
literal or a triple term (which is not a node identifier). -/
def termNodeId : Term → Option (String × Bool)
  | .iri i   => some (i.val, false)
  | .bnode b => some ("_:" ++ b, true)
  | _        => none

def startsWithUnderscoreColon (s : String) : Bool :=
  s.startsWith "_:"

/-! ## Node-map primitives -/

def findNode (nm : List FrNode) (id : String) : Option FrNode :=
  nm.find? (fun n => n.id == id)

def nodeExists (nm : List FrNode) (id : String) : Bool := (findNode nm id).isSome

def ensureNode (nm : List FrNode) (id : String) (blank : Bool) : List FrNode :=
  if nodeExists nm id then nm
  else nm ++ [{ id := id, blank := blank, types := [], props := [] }]

/-- Append preserving order, dropping structural duplicates (F*:
`snoc_unique`). -/
def snocUniqueStr : List String → String → List String
  | [],      x => [x]
  | h :: tl, x => if h == x then h :: tl else h :: snocUniqueStr tl x

def snocUniqueOv : List Ov → Ov → List Ov
  | [],      x => [x]
  | h :: tl, x => if Ov.eqb h x then h :: tl else h :: snocUniqueOv tl x

/-! ### Run-time forms of the list primitives

`snocUniqueStr`, `snocUniqueOv` and `propAdd` rebuild the list in front of the
place they change after their recursive call returns, so each takes one native
frame for each element it passes: one node with 20,000 references overflowed a
stack of 512 KB in `snocUniqueOv` (https://github.com/danbri/factoidal/issues/853).
Each `...Go` form below walks the list with the elements passed so far in a
reversed accumulator and puts them back in front with one `reverseAux` (a loop).
Each `..._eq_fast` theorem proves the two forms equal and makes the compiler
emit the loop for every call (`csimp`). The time is unchanged: each call still
reads the list (https://github.com/danbri/factoidal/issues/712). -/

def snocUniqueStrGo (x : String) : List String → List String → List String
  | acc, []      => acc.reverseAux [x]
  | acc, h :: tl => if h == x then acc.reverseAux (h :: tl) else snocUniqueStrGo x (h :: acc) tl

theorem snocUniqueStrGo_eq (x : String) : ∀ (acc l : List String),
    snocUniqueStrGo x acc l = acc.reverse ++ snocUniqueStr l x
  | acc, [] => by simp [snocUniqueStrGo, snocUniqueStr, List.reverseAux_eq]
  | acc, h :: tl => by
    unfold snocUniqueStrGo snocUniqueStr
    by_cases hh : (h == x) = true
    · simp [hh, List.reverseAux_eq]
    · simp [hh, snocUniqueStrGo_eq x (h :: acc) tl]

def snocUniqueStrFast (l : List String) (x : String) : List String := snocUniqueStrGo x [] l

@[csimp] theorem snocUniqueStr_eq_fast : @snocUniqueStr = @snocUniqueStrFast := by
  funext l x; simp [snocUniqueStrFast, snocUniqueStrGo_eq]

def snocUniqueOvGo (x : Ov) : List Ov → List Ov → List Ov
  | acc, []      => acc.reverseAux [x]
  | acc, h :: tl => if Ov.eqb h x then acc.reverseAux (h :: tl) else snocUniqueOvGo x (h :: acc) tl

theorem snocUniqueOvGo_eq (x : Ov) : ∀ (acc l : List Ov),
    snocUniqueOvGo x acc l = acc.reverse ++ snocUniqueOv l x
  | acc, [] => by simp [snocUniqueOvGo, snocUniqueOv, List.reverseAux_eq]
  | acc, h :: tl => by
    unfold snocUniqueOvGo snocUniqueOv
    by_cases hh : Ov.eqb h x = true
    · simp [hh, List.reverseAux_eq]
    · simp [hh, snocUniqueOvGo_eq x (h :: acc) tl]

def snocUniqueOvFast (l : List Ov) (x : Ov) : List Ov := snocUniqueOvGo x [] l

@[csimp] theorem snocUniqueOv_eq_fast : @snocUniqueOv = @snocUniqueOvFast := by
  funext l x; simp [snocUniqueOvFast, snocUniqueOvGo_eq]

def findProp (props : List (String × List Ov)) (p : String) : Option (List Ov) :=
  (props.find? (fun kv => kv.1 == p)).map Prod.snd

/-- The single value of a property, when it has exactly one. -/
def nodePropSingle (n : FrNode) (p : String) : Option Ov :=
  match findProp n.props p with
  | some [v] => some v
  | _        => none

def propAdd : List (String × List Ov) → String → Ov → List (String × List Ov)
  | [],             p, v => [(p, [v])]
  | (k, vals) :: tl, p, v =>
    if k == p then (k, snocUniqueOv vals v) :: tl
    else (k, vals) :: propAdd tl p v

def propAddGo (p : String) (v : Ov) :
    List (String × List Ov) → List (String × List Ov) → List (String × List Ov)
  | acc, []              => acc.reverseAux [(p, [v])]
  | acc, (k, vals) :: tl =>
    if k == p then acc.reverseAux ((k, snocUniqueOv vals v) :: tl)
    else propAddGo p v ((k, vals) :: acc) tl

theorem propAddGo_eq (p : String) (v : Ov) : ∀ (acc l : List (String × List Ov)),
    propAddGo p v acc l = acc.reverse ++ propAdd l p v
  | acc, [] => by simp [propAddGo, propAdd, List.reverseAux_eq]
  | acc, (k, vals) :: tl => by
    unfold propAddGo propAdd
    by_cases hh : (k == p) = true
    · simp [hh, List.reverseAux_eq]
    · simp [hh, propAddGo_eq p v ((k, vals) :: acc) tl]

def propAddFast (l : List (String × List Ov)) (p : String) (v : Ov) : List (String × List Ov) :=
  propAddGo p v [] l

@[csimp] theorem propAdd_eq_fast : @propAdd = @propAddFast := by
  funext l p v; simp [propAddFast, propAddGo_eq]

#guard (snocUniqueStrFast ["a", "b"] "b") == ["a", "b"]
#guard (snocUniqueStrFast ["a", "b"] "c") == ["a", "b", "c"]
#guard (snocUniqueOvFast [.ref "a"] (.ref "a")).length == 1
#guard (snocUniqueOvFast [.ref "a"] (.ref "b")).length == 2
#guard ((propAddFast [("p", [.ref "a"]), ("q", [])] "q" (.ref "b")).map (·.2.length)) == [1, 1]
#guard ((propAddFast [("p", [.ref "a"])] "r" (.ref "b")).map (·.1)) == ["p", "r"]

def nodeUpdateProp (nm : List FrNode) (id p : String) (v : Ov) : List FrNode :=
  nm.map (fun n => if n.id == id then { n with props := propAdd n.props p v } else n)

def nodeUpdateType (nm : List FrNode) (id t : String) : List FrNode :=
  nm.map (fun n => if n.id == id then { n with types := snocUniqueStr n.types t } else n)

/-! ## RDF to Object Conversion — JSON-LD 1.1 API §8.6 -/

def isDecDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `xsd:integer` lexical space (approximated as the spec's canonical
form requires): optional sign then one or more digits. -/
def isIntLexeme (s : String) : Bool :=
  let cs := s.toList
  let cs := match cs with
            | c :: rest => if c == '+' || c == '-' then rest else cs
            | []        => cs
  !cs.isEmpty && cs.all isDecDigit

/-- A double lexeme is "natively serializable" iff it is a syntactically
valid JSON number AND finite. Non-JSON forms (`+INF`, `NaN`) and
astronomically large exponents (which overflow to infinity, e.g.
`"0.1e999999999999999"` in fixture 0027) are NOT native; the
exponent-digit bound (at most 3 digits) is the F* source's heuristic and
is reproduced exactly. -/
def isFiniteDouble (s : String) : Bool :=
  match parseJson s with
  | .ok (.number _) =>
    match s.toList.findIdx? (fun c => c == 'e' || c == 'E') with
    | none    => true
    | some ei => ((s.toList.drop (ei + 1)).filter isDecDigit).length ≤ 3
  | _ => false

/-- §8.6 step 8: `useNativeTypes` conversion of a typed literal. -/
def nativeValue (lex dt : String) : Ov :=
  if dt == sXsdBoolean then
    -- xsd:boolean lexical space is {true, false, 1, 0}; "True"/"notnative"
    -- stay typed strings (fixture 0027).
    if lex == "true" || lex == "1" then .val (.object [("@value", .bool true)])
    else if lex == "false" || lex == "0" then .val (.object [("@value", .bool false)])
    else .val (.object [("@value", .string lex), ("@type", .string dt)])
  else if dt == sXsdInteger then
    if isIntLexeme lex then .val (.object [("@value", .number lex)])
    else .val (.object [("@value", .string lex), ("@type", .string dt)])
  else if dt == sXsdDouble then
    if isFiniteDouble lex then .val (.object [("@value", .number lex)])
    else .val (.object [("@value", .string lex), ("@type", .string dt)])
  else
    .val (.object [("@value", .string lex), ("@type", .string dt)])

/-- `rdfDirection="i18n-datatype"` reverse mapping: a literal typed
`https://www.w3.org/ns/i18n#<lang>_<dir>` becomes a value object with
`@direction`, plus `@language` only when `<lang>` is non-empty (di05:
`#_rtl` gives no `@language`; di06: `#en-us_rtl` gives `"en-us"`). The
fragment splits on its LAST `_` so a hyphenated subtag stays intact. -/
def i18nValueObject (lex dt : String) : Ov :=
  let frag := (dt.toList.drop i18nPrefix.toList.length)
  -- index of the last '_' in frag, or frag.length when absent
  let up := frag.foldl (fun (acc : Nat × Nat) c =>
              (acc.1 + 1, if c == '_' then acc.1 else acc.2)) (0, frag.length)
  let upPos := up.2
  let lang := if upPos ≥ frag.length then "" else String.ofList (frag.take upPos)
  let dir  := if upPos ≥ frag.length then String.ofList frag
              else String.ofList (frag.drop (upPos + 1))
  let base := [("@value", Json.string lex)]
  let withLang := if lang.isEmpty then base else base ++ [("@language", Json.string lang)]
  .val (.object (withLang ++ [("@direction", Json.string dir)]))

/-- §8.6. `none` signals the fatal "invalid JSON literal" error the
negative fixtures js08/js09 expect. -/
def rdfToObject (opts : Options) : Term → Option Ov
  | .iri i     => some (.ref i.val)
  | .bnode b   => some (.ref ("_:" ++ b))
  -- RDF 1.2 triple terms have no from-RDF JSON-LD representation; report
  -- unsupported rather than emit a wrong value object.
  | .tripleTerm _ _ _ => none
  | .literal l =>
    let lex := l.val.lexicalForm
    let dt  := l.val.datatype.val
    match l.val.langTag with
    | some tag => some (.val (.object [("@value", .string lex), ("@language", .string tag)]))
    | none =>
      if opts.rdfDirection == some "i18n-datatype" && dt.startsWith i18nPrefix then
        some (i18nValueObject lex dt)
      else if dt == rdfJsonIri then
        match parseJson lex with
        | .ok j    => some (.val (.object [("@value", j), ("@type", .string "@json")]))
        | .error _ => none
      else if dt == sXsdString then
        some (.val (.object [("@value", .string lex)]))
      else if opts.useNativeTypes then
        some (nativeValue lex dt)
      else
        some (.val (.object [("@value", .string lex), ("@type", .string dt)]))

/-! ## Node-map construction (per graph) — §8.5 steps 3-5 -/

def processTriple (opts : Options) (nm : List FrNode) (t : Triple)
    : Option (List FrNode) :=
  let sId := subjId t.s
  let nm1 := ensureNode nm sId (subjIsBlank t.s)
  let nm2 := match termNodeId t.o with
             | some (oid, ob) => ensureNode nm1 oid ob
             | none           => nm1
  let p := t.p.val
  let objIsNode := match t.o with | .iri _ => true | .bnode _ => true | _ => false
  if p == rdfTypeIri && !opts.useRdfType && objIsNode then
    match termNodeId t.o with
    | some (oid, _) => some (nodeUpdateType nm2 sId oid)
    | none          => some nm2
  else
    match rdfToObject opts t.o with
    | none   => none
    | some v => some (nodeUpdateProp nm2 sId p v)

def buildNodemap (opts : Options) : List FrNode → List Triple → Option (List FrNode)
  | nm, []      => some nm
  | nm, t :: tl =>
    match processTriple opts nm t with
    | none     => none
    | some nm' => buildNodemap opts nm' tl

def buildNamed (opts : Options) : List NamedGraph → Option (List NamedNm)
  | []        => some []
  | ng :: tl  =>
    match buildNodemap opts [] ng.graph with
    | none   => none
    | some m =>
      match buildNamed opts tl with
      | none        => none
      | some others =>
        let nm := subjId ng.name
        some ({ name := nm, blank := startsWithUnderscoreColon nm, map := m } :: others)

/-- `buildNamed` with the graphs built so far in a reversed accumulator: a loop
over the named graphs (`buildNamed` waits for the rest of the list before it
conses, one native frame for each graph, issue 853). -/
def buildNamedGo (opts : Options) : List NamedNm → List NamedGraph → Option (List NamedNm)
  | acc, []       => some acc.reverse
  | acc, ng :: tl =>
    match buildNodemap opts [] ng.graph with
    | none   => none
    | some m =>
      let nm := subjId ng.name
      buildNamedGo opts ({ name := nm, blank := startsWithUnderscoreColon nm, map := m } :: acc) tl

theorem buildNamedGo_eq (opts : Options) : ∀ (acc : List NamedNm) (l : List NamedGraph),
    buildNamedGo opts acc l = (buildNamed opts l).map (acc.reverse ++ ·)
  | acc, [] => by simp [buildNamedGo, buildNamed]
  | acc, ng :: tl => by
    simp only [buildNamedGo, buildNamed]
    split
    · rfl
    · rw [buildNamedGo_eq opts _ tl]
      cases buildNamed opts tl <;> simp

def buildNamedFast (opts : Options) (l : List NamedGraph) : Option (List NamedNm) :=
  buildNamedGo opts [] l

@[csimp] theorem buildNamed_eq_fast : @buildNamed = @buildNamedFast := by
  funext opts l; simp [buildNamedFast, buildNamedGo_eq]

def addGraphNames : List FrNode → List NamedNm → List FrNode
  | nm, []      => nm
  | nm, g :: tl => addGraphNames (ensureNode nm g.name g.blank) tl

def isGraphName (named : List NamedNm) (id : String) : Bool :=
  named.any (fun g => g.name == id)

def lookupGraphMap (named : List NamedNm) (id : String) : Option (List FrNode) :=
  (named.find? (fun g => g.name == id)).map NamedNm.map

/-! ## Global "referenced exactly once" count

Counted across ALL graphs: fixtures 0020/0021 pin that a blank list node
referenced from a second graph is NOT collapsed. -/

def ovsRefids : List Ov → List String
  | []             => []
  | .ref x :: tl   => x :: ovsRefids tl
  | _ :: tl        => ovsRefids tl

def propsRefids : List (String × List Ov) → List String
  | []              => []
  | (_, vals) :: tl => ovsRefids vals ++ propsRefids tl

def nodesRefids : List FrNode → List String
  | []      => []
  | n :: tl => propsRefids n.props ++ nodesRefids tl

def mapsRefids : List (List FrNode) → List String
  | []      => []
  | m :: tl => nodesRefids m ++ mapsRefids tl

/-! ### Run-time forms of the reference lists

The four functions above append the rest of their list after the recursive call
returns: one native frame for each value, property, node or graph (issue 853).
The `...Fast` forms are the same lists as `filterMap` and `flatMap`, which run as
loops (their `csimp` theorems in Lean core). -/

def ovRefid? : Ov → Option String
  | .ref x => some x
  | _      => none

def ovsRefidsFast (l : List Ov) : List String := l.filterMap ovRefid?

theorem ovsRefids_eq_filterMap : ∀ l : List Ov, ovsRefids l = l.filterMap ovRefid?
  | [] => rfl
  | .ref x :: tl => by simp [ovsRefids, ovRefid?, ovsRefids_eq_filterMap tl]
  | .val _ :: tl => by
    simp only [ovsRefids]; rw [List.filterMap_cons]; exact ovsRefids_eq_filterMap tl
  | .lst _ :: tl => by
    simp only [ovsRefids]; rw [List.filterMap_cons]; exact ovsRefids_eq_filterMap tl

@[csimp] theorem ovsRefids_eq_fast : @ovsRefids = @ovsRefidsFast := by
  funext l; exact ovsRefids_eq_filterMap l

def propsRefidsFast (l : List (String × List Ov)) : List String :=
  l.flatMap (fun kv => ovsRefids kv.2)

theorem propsRefids_eq_flatMap : ∀ l : List (String × List Ov),
    propsRefids l = l.flatMap (fun kv => ovsRefids kv.2)
  | [] => rfl
  | (_, vals) :: tl => by simp [propsRefids, propsRefids_eq_flatMap tl]

@[csimp] theorem propsRefids_eq_fast : @propsRefids = @propsRefidsFast := by
  funext l; exact propsRefids_eq_flatMap l

def nodesRefidsFast (l : List FrNode) : List String := l.flatMap (fun n => propsRefids n.props)

theorem nodesRefids_eq_flatMap : ∀ l : List FrNode,
    nodesRefids l = l.flatMap (fun n => propsRefids n.props)
  | [] => rfl
  | n :: tl => by simp [nodesRefids, nodesRefids_eq_flatMap tl]

@[csimp] theorem nodesRefids_eq_fast : @nodesRefids = @nodesRefidsFast := by
  funext l; exact nodesRefids_eq_flatMap l

def mapsRefidsFast (l : List (List FrNode)) : List String := l.flatMap nodesRefids

theorem mapsRefids_eq_flatMap : ∀ l : List (List FrNode), mapsRefids l = l.flatMap nodesRefids
  | [] => rfl
  | m :: tl => by simp [mapsRefids, mapsRefids_eq_flatMap tl]

@[csimp] theorem mapsRefids_eq_fast : @mapsRefids = @mapsRefidsFast := by
  funext l; exact mapsRefids_eq_flatMap l

#guard ovsRefidsFast [.ref "a", .val .null, .ref "b", .lst [.ref "c"]] == ["a", "b"]
#guard ovsRefidsFast [.val .null] == []
#guard propsRefidsFast [("p", [.ref "a"]), ("q", [.ref "b", .ref "a"])] == ["a", "b", "a"]

def referencedOnce (refids : List String) (id : String) : Bool :=
  (refids.filter (fun y => y == id)).length == 1

/-! ## Compound-literal collapse (`rdfDirection = "compound-literal"`)

A blank node bearing `rdf:value` / `rdf:direction` (/ `rdf:language`) is
folded into a value object and every referenced-once reference to it is
replaced by that object — the exact reverse of the toRdf side's
compound-literal term (di11, di12). Gated on the mode so an
`i18n-datatype` run leaves the same blank node untouched (di07/di08). -/

def objLookup (fields : List (String × Json)) (k : String) : Option Json :=
  (fields.find? (fun kv => kv.1 == k)).map Prod.snd

/-- The `@value` payload of a sub-literal reached through property `p`. -/
def clField (n : FrNode) (p : String) : Option Json :=
  match nodePropSingle n p with
  | some (.val (.object fields)) => objLookup fields "@value"
  | _                            => none

def isClShape (n : FrNode) : Bool :=
  n.blank
  && (nodePropSingle n rdfValueIri).isSome
  && (nodePropSingle n rdfDirectionIri).isSome

def clValueObject (n : FrNode) : Option Json :=
  match clField n rdfValueIri, clField n rdfDirectionIri with
  | some v, some d =>
    let lang := clField n rdfLanguageIri
    some (.object ([("@value", v)]
                   ++ (match lang with | some l => [("@language", l)] | none => [])
                   ++ [("@direction", d)]))
  | _, _ => none

def isClCollapsible (g : List FrNode) (refids : List String) (id : String) : Bool :=
  match findNode g id with
  | none   => false
  | some n => isClShape n && referencedOnce refids id

/-! ## List Conversion — JSON-LD 1.1 API §8.7 -/

/-- The shape a list cell must have: a blank node whose ONLY properties
are exactly one `rdf:first` and one `rdf:rest` (optionally typed
`rdf:List`). -/
def isListShape (n : FrNode) : Bool :=
  n.blank
  && (n.types.isEmpty || n.types == [rdfListIri])
  && n.props.length == 2
  && (nodePropSingle n rdfFirstIri).isSome
  && (nodePropSingle n rdfRestIri).isSome

/-- A node id is collapsible iff it is a referenced-once blank list cell
whose `rest` chain terminates at `rdf:nil`. A cycle never reaches nil,
so it is not collapsible (fixture 0012) — which is also why the walk
carries fuel. -/
def isCollapsible (g : List FrNode) (refids : List String) : String → Nat → Bool
  | _,  0        => false
  | id, fuel + 1 =>
    match findNode g id with
    | none   => false
    | some n =>
      if !isListShape n then false
      else if !referencedOnce refids id then false
      else
        match nodePropSingle n rdfRestIri with
        | some (.ref rt) =>
          if rt == rdfNilIri then true else isCollapsible g refids rt fuel
        | _ => false

mutual

/-- The ordered element list of a collapsible chain starting at `id`. -/
def listFrom (g : List FrNode) (refids : List String) (clMode : Bool)
    : String → Nat → List Ov
  | _,  0        => []
  | id, fuel + 1 =>
    match findNode g id with
    | none   => []
    | some n =>
      match nodePropSingle n rdfFirstIri, nodePropSingle n rdfRestIri with
      | some fv, some (.ref rt) =>
        let elem := resolveOv g refids clMode fv fuel
        if rt == rdfNilIri then [elem]
        else elem :: listFrom g refids clMode rt fuel
      | _, _ => []

/-- Rewrite one value: a reference to a collapsible list head (or to
`rdf:nil`) becomes a nested `@list`; under compound-literal mode a
reference to a collapsible compound literal becomes its value object. -/
def resolveOv (g : List FrNode) (refids : List String) (clMode : Bool)
    : Ov → Nat → Ov
  | v, 0        => v
  | v, fuel + 1 =>
    match v with
    | .ref x =>
      if x == rdfNilIri then .lst []
      else if isCollapsible g refids x (fuel + 1) then
        .lst (listFrom g refids clMode x fuel)
      else if clMode && isClCollapsible g refids x then
        match findNode g x with
        | some n => match clValueObject n with
                    | some j => .val j
                    | none   => .ref x
        | none   => .ref x
      else .ref x
    | .val j  => .val j
    | .lst l  => .lst l

end

/-! ### Run-time form of the list conversion

`listFrom` conses each element onto the result of its recursive call: one native
frame for each cell of an `rdf:first`/`rdf:rest` chain (issue 853). `listFromW`
collects the elements in a reversed accumulator and `resolveOvW` calls it;
otherwise the two functions are `listFrom` and `resolveOv` line for line.
`listFromW_eq` proves them equal at every fuel (induction on the fuel, both
functions at once), and `resolveOv_eq_fast` makes the compiler emit `resolveOvW`
for the calls outside the block. -/

mutual

def listFromW (g : List FrNode) (refids : List String) (clMode : Bool)
    (acc : List Ov) : String → Nat → List Ov
  | _,  0        => acc.reverse
  | id, fuel + 1 =>
    match findNode g id with
    | none   => acc.reverse
    | some n =>
      match nodePropSingle n rdfFirstIri, nodePropSingle n rdfRestIri with
      | some fv, some (.ref rt) =>
        let elem := resolveOvW g refids clMode fv fuel
        if rt == rdfNilIri then (elem :: acc).reverse
        else listFromW g refids clMode (elem :: acc) rt fuel
      | _, _ => acc.reverse

def resolveOvW (g : List FrNode) (refids : List String) (clMode : Bool)
    : Ov → Nat → Ov
  | v, 0        => v
  | v, fuel + 1 =>
    match v with
    | .ref x =>
      if x == rdfNilIri then .lst []
      else if isCollapsible g refids x (fuel + 1) then
        .lst (listFromW g refids clMode [] x fuel)
      else if clMode && isClCollapsible g refids x then
        match findNode g x with
        | some n => match clValueObject n with
                    | some j => .val j
                    | none   => .ref x
        | none   => .ref x
      else .ref x
    | .val j  => .val j
    | .lst l  => .lst l

end

theorem listFromW_eq (g : List FrNode) (refids : List String) (clMode : Bool) :
    ∀ fuel : Nat,
      (∀ acc id, listFromW g refids clMode acc id fuel =
                   acc.reverse ++ listFrom g refids clMode id fuel) ∧
      (∀ v, resolveOvW g refids clMode v fuel = resolveOv g refids clMode v fuel)
  | 0 => ⟨fun acc id => by simp [listFromW, listFrom], fun v => by simp [resolveOvW, resolveOv]⟩
  | fuel + 1 => by
    obtain ⟨ihL, ihR⟩ := listFromW_eq g refids clMode fuel
    refine ⟨fun acc id => ?_, fun v => ?_⟩
    · simp only [listFromW, listFrom]
      split
      · simp
      · split
        · rename_i fv rt _ _
          simp only [ihR]
          split
          · simp
          · rw [ihL]; simp
        · simp
    · simp only [resolveOvW, resolveOv]
      split
      · rename_i x
        simp only [ihL, List.reverse_nil, List.nil_append]
      · rfl
      · rfl

def resolveOvFast (g : List FrNode) (refids : List String) (clMode : Bool) (v : Ov) (fuel : Nat) : Ov :=
  resolveOvW g refids clMode v fuel

@[csimp] theorem resolveOv_eq_fast : @resolveOv = @resolveOvFast := by
  funext g refids clMode v fuel; exact ((listFromW_eq g refids clMode fuel).2 v).symm

def listFromFast (g : List FrNode) (refids : List String) (clMode : Bool) (id : String)
    (fuel : Nat) : List Ov :=
  listFromW g refids clMode [] id fuel

@[csimp] theorem listFrom_eq_fast : @listFrom = @listFromFast := by
  funext g refids clMode id fuel
  simp [listFromFast, (listFromW_eq g refids clMode fuel).1]

def rewriteNode (g : List FrNode) (refids : List String) (clMode : Bool) (fuel : Nat)
    (n : FrNode) : FrNode :=
  { n with props := n.props.map (fun pv =>
      (pv.1, pv.2.map (fun v => resolveOv g refids clMode v fuel))) }

/-! ## JSON emission -/

mutual

def ovToJson : Ov → Json
  | .ref id => .object [("@id", .string id)]
  | .val j  => j
  | .lst l  => .object [("@list", .array (ovListToJson l))]

def ovListToJson : List Ov → List Json
  | []      => []
  | v :: tl => ovToJson v :: ovListToJson tl

end

/-! ### Run-time form of the JSON emission of a value

`ovListToJson` conses the head onto the result of its recursive call: one native
frame for each element of a `@list` (issue 853). `ovListToJsonW` collects the
elements in a reversed accumulator; the depth of the recursion is the nesting of
the lists. `ovToJsonW_eq` proves both forms equal and `ovToJson_eq_fast` makes the
compiler emit `ovToJsonW` for the calls outside the block. -/

mutual

def ovToJsonW : Ov → Json
  | .ref id => .object [("@id", .string id)]
  | .val j  => j
  | .lst l  => .object [("@list", .array (ovListToJsonW [] l))]

def ovListToJsonW : List Json → List Ov → List Json
  | acc, []      => acc.reverse
  | acc, v :: tl => ovListToJsonW (ovToJsonW v :: acc) tl

end

mutual

theorem ovToJsonW_eq : ∀ v : Ov, ovToJsonW v = ovToJson v
  | .ref _ => by simp [ovToJsonW, ovToJson]
  | .val _ => by simp [ovToJsonW, ovToJson]
  | .lst l => by simp [ovToJsonW, ovToJson, ovListToJsonW_eq [] l]

theorem ovListToJsonW_eq : ∀ (acc : List Json) (l : List Ov),
    ovListToJsonW acc l = acc.reverse ++ ovListToJson l
  | acc, [] => by simp [ovListToJsonW, ovListToJson]
  | acc, v :: tl => by
    rw [ovListToJsonW, ovListToJsonW_eq (ovToJsonW v :: acc) tl, ovToJsonW_eq v]
    simp [ovListToJson]

end

@[csimp] theorem ovToJson_eq_fast : @ovToJson = @ovToJsonW := by
  funext v; exact (ovToJsonW_eq v).symm

def ovListToJsonFast (l : List Ov) : List Json := ovListToJsonW [] l

@[csimp] theorem ovListToJson_eq_fast : @ovListToJson = @ovListToJsonFast := by
  funext l; simp [ovListToJsonFast, ovListToJsonW_eq]

#guard ovToJsonW (.lst [.ref "a", .val (.string "x")]) ==
  .object [("@list", .array [.object [("@id", .string "a")], .string "x"])]
#guard ovToJsonW (.lst [.ref "a", .ref "b"]) != .object [("@list", .array [.object [("@id", .string "b")], .object [("@id", .string "a")]])]

def typesField (types : List String) : List (String × Json) :=
  if types.isEmpty then [] else [("@type", .array (types.map Json.string))]

def graphField : Option (List Json) → List (String × Json)
  | some gs => [("@graph", .array gs)]
  | none    => []

def propsFields (props : List (String × List Ov)) : List (String × Json) :=
  props.map (fun pv => (pv.1, .array (pv.2.map ovToJson)))

def nodeToJson (n : FrNode) (gj : Option (List Json)) : Json :=
  .object ([("@id", .string n.id)] ++ typesField n.types ++ graphField gj
           ++ propsFields n.props)

/-! ## Node ordering — byte order on `@id`, as the fixtures are written -/

def insertSortedNode (n : FrNode) : List FrNode → List FrNode
  | []      => [n]
  | h :: tl => if strLt n.id h.id then n :: h :: tl else h :: insertSortedNode n tl

def sortNodes : List FrNode → List FrNode
  | []      => []
  | h :: tl => insertSortedNode h (sortNodes tl)

/-! ### Run-time form of the node sort

`insertSortedNode` rebuilds the nodes in front of the place of the new node after
its recursive call returns, and `sortNodes` inserts the head after its recursive
call returns: two native frames for each node (one node map of 20,000 subjects
overflowed a stack of 512 KB in `insertSortedNode`, issue 853). `insertSortedNodeGo`
walks with a reversed accumulator, and `sortNodesFast` inserts from the end of the
list with a left fold, which is what `sortNodes` does from the inside out. The
order of the result is the same (`sortNodes_eq_fast`); the time is still quadratic
in the number of nodes (https://github.com/danbri/factoidal/issues/712). -/

def insertSortedNodeGo (n : FrNode) : List FrNode → List FrNode → List FrNode
  | acc, []      => acc.reverseAux [n]
  | acc, h :: tl =>
    if strLt n.id h.id then acc.reverseAux (n :: h :: tl) else insertSortedNodeGo n (h :: acc) tl

theorem insertSortedNodeGo_eq (n : FrNode) : ∀ (acc l : List FrNode),
    insertSortedNodeGo n acc l = acc.reverse ++ insertSortedNode n l
  | acc, [] => by simp [insertSortedNodeGo, insertSortedNode, List.reverseAux_eq]
  | acc, h :: tl => by
    unfold insertSortedNodeGo insertSortedNode
    by_cases hh : strLt n.id h.id = true
    · simp [hh, List.reverseAux_eq]
    · simp [hh, insertSortedNodeGo_eq n (h :: acc) tl]

def insertSortedNodeFast (n : FrNode) (l : List FrNode) : List FrNode := insertSortedNodeGo n [] l

@[csimp] theorem insertSortedNode_eq_fast : @insertSortedNode = @insertSortedNodeFast := by
  funext n l; simp [insertSortedNodeFast, insertSortedNodeGo_eq]

def sortNodesFast (l : List FrNode) : List FrNode :=
  l.reverse.foldl (fun acc h => insertSortedNode h acc) []

theorem sortNodes_eq_foldr : ∀ l : List FrNode, sortNodes l = l.foldr insertSortedNode []
  | [] => rfl
  | h :: tl => by simp [sortNodes, sortNodes_eq_foldr tl]

@[csimp] theorem sortNodes_eq_fast : @sortNodes = @sortNodesFast := by
  funext l; simp [sortNodesFast, sortNodes_eq_foldr, List.foldl_reverse]

private def nodeN (id : String) : FrNode := { id := id, blank := false, types := [], props := [] }
#guard (sortNodesFast [nodeN "c", nodeN "a", nodeN "b"]).map (·.id) == ["a", "b", "c"]
#guard (sortNodesFast [nodeN "c", nodeN "a", nodeN "b"]).map (·.id) ==
  (sortNodes [nodeN "c", nodeN "a", nodeN "b"]).map (·.id)
#guard (sortNodesFast [nodeN "b", nodeN "a"]).map (·.id) != ["b", "a"]

/-! ## Per-graph node emission -/

def graphFuel (g : List FrNode) : Nat := 4 * g.length + 16

/-- A named graph's contents. Under compound-literal mode the collapsed
blank nodes drop out of the survivors (their references were rewritten
into inline value objects). -/
def emitNamedNodes (g : List FrNode) (refids : List String) (clMode : Bool) : List Json :=
  let fuel := graphFuel g
  let survivors := g.filter (fun n =>
    !isCollapsible g refids n.id fuel
    && !(clMode && isClCollapsible g refids n.id)
    && (!n.types.isEmpty || !n.props.isEmpty))
  let rewritten := survivors.map (rewriteNode g refids clMode fuel)
  (sortNodes rewritten).map (fun n => nodeToJson n none)

/-- The default graph: same survivorship, plus graph-name nodes carry
their graph's contents under `@graph`. -/
def emitDefaultNodes (dm : List FrNode) (named : List NamedNm) (refids : List String)
    (clMode : Bool) : List Json :=
  let fuel := graphFuel dm
  let survivors := dm.filter (fun n =>
    !isCollapsible dm refids n.id fuel
    && !(clMode && isClCollapsible dm refids n.id)
    && (!n.types.isEmpty || !n.props.isEmpty || isGraphName named n.id))
  let rewritten := survivors.map (rewriteNode dm refids clMode fuel)
  (sortNodes rewritten).map (fun n =>
    let gj := if isGraphName named n.id then
                match lookupGraphMap named n.id with
                | some gm => some (emitNamedNodes gm refids clMode)
                | none    => some []
              else none
    nodeToJson n gj)

/-! ## Entry point — §8.5 -/

/-- Serialize an RDF dataset as an expanded-form JSON-LD document.
`none` is the fatal "invalid JSON literal" / unsupported-term error. -/
def fromRdf (ds : Dataset) (opts : Options) : Option Json :=
  match buildNodemap opts [] ds.default with
  | none     => none
  | some dm0 =>
    match buildNamed opts ds.named with
    | none       => none
    | some named =>
      let dm := addGraphNames dm0 named
      let allMaps := dm :: named.map NamedNm.map
      let refids := mapsRefids allMaps
      let clMode := opts.rdfDirection == some "compound-literal"
      some (.array (emitDefaultNodes dm named refids clMode))

/-! ## Linear-time forms (https://github.com/danbri/factoidal/issues/712)

The definitions above are the readable statement of §8.5-§8.7. Run as written,
they read the node list for every triple (`ensureNode`, `nodeUpdateProp`), the
value list of a property for every value (`snocUniqueOv`), the whole reference
list for every `referencedOnce` test, and the rest of an `rdf:rest` chain for
every cell of the chain (`isCollapsible`), and they sort by insertion. A
collection of 5,000 cells did not finish in 120 s.

The forms below keep the same results and use hash maps:

  * `NmF` is the node map: the node ids in order of first appearance, and a
    hash map from id to `NodeF`. A `NodeF` keeps its types and its property
    values as arrays, each with a hash set of the members, and its properties
    as an array of names with a hash map from name to values. `NmF.abs` is the
    `List FrNode` that `buildNodemap` builds (`buildNodemap_eq_fast`).
  * `countMap` counts the references once (`referencedOnce_eq_countMap`).
  * `firstMap` finds a node or a named graph by id in one probe
    (`findNode_eq_firstMap`).
  * `memoC` computes, for every node of a graph, the length of the
    `rdf:first`/`rdf:rest` chain that starts there, in one walk of each chain
    with the results kept (`collF_eq`). `isCollapsible` is a test on that
    length (`isCollapsible_eq_collS`, `collS_eq_lenS`).
  * `sortM` sorts with `List.mergeSort` when the node ids are distinct, which
    they are in every node map (`sortNodes_eq_sortM`).

Each `@[csimp]` theorem makes the compiler use the fast form; the readable
definition stays the one every other theorem is about. -/

section Fast

open Std

/-! ### `Ov` equality is `=` -/

mutual

theorem Ov.eqb_iff : ∀ a b : Ov, Ov.eqb a b = true ↔ a = b
  | .ref a, .ref b => by simp [Ov.eqb]
  | .val a, .val b => by simp [Ov.eqb]
  | .lst a, .lst b => by rw [Ov.eqb, Ov.eqbList_iff a b]; simp
  | .ref _, .val _ => by simp [Ov.eqb]
  | .ref _, .lst _ => by simp [Ov.eqb]
  | .val _, .ref _ => by simp [Ov.eqb]
  | .val _, .lst _ => by simp [Ov.eqb]
  | .lst _, .ref _ => by simp [Ov.eqb]
  | .lst _, .val _ => by simp [Ov.eqb]

theorem Ov.eqbList_iff : ∀ a b : List Ov, Ov.eqbList a b = true ↔ a = b
  | [], [] => by simp [Ov.eqbList]
  | x :: xs, y :: ys => by
    rw [Ov.eqbList, Bool.and_eq_true, Ov.eqb_iff x y, Ov.eqbList_iff xs ys]; simp
  | [], _ :: _ => by simp [Ov.eqbList]
  | _ :: _, [] => by simp [Ov.eqbList]

end

instance : LawfulBEq Ov where
  eq_of_beq h := (Ov.eqb_iff _ _).1 h
  rfl := (Ov.eqb_iff _ _).2 rfl

/-- A hash of a value that reads one level of a value object (its keys and
its string and number members). Any function is a lawful hash here, because
`==` on `Ov` is `=`. -/
def jsonLeafHash : Json → UInt64
  | .null      => 1
  | .bool b    => if b then 2 else 3
  | .string s  => mixHash 4 (hash s)
  | .number s  => mixHash 5 (hash s)
  | .array l   => mixHash 6 (hash l.length)
  | .object l  => mixHash 7 (hash l.length)

def jsonShallowHash : Json → UInt64
  | .object kvs => kvs.foldl (fun h kv => mixHash h (mixHash (hash kv.1) (jsonLeafHash kv.2))) 8
  | j           => jsonLeafHash j

def Ov.hash : Ov → UInt64
  | .ref x => mixHash 11 (Hashable.hash x)
  | .val j => mixHash 13 (jsonShallowHash j)
  | .lst l => mixHash 17 (Hashable.hash l.length)

instance : Hashable Ov := ⟨Ov.hash⟩

/-! ### The append-unique functions as membership tests -/

theorem snocUniqueStr_eq_if : ∀ (l : List String) (x : String),
    snocUniqueStr l x = if x ∈ l then l else l ++ [x]
  | [], x => by simp [snocUniqueStr]
  | h :: tl, x => by
    by_cases hh : h = x
    · subst hh; simp [snocUniqueStr]
    · have hb : (h == x) = false := by simpa using hh
      rw [snocUniqueStr, hb, snocUniqueStr_eq_if tl x]
      by_cases hm : x ∈ tl
      · simp [hm]
      · have : x ∉ h :: tl := by simp [hm, Ne.symm hh]
        simp [hm, this]

theorem snocUniqueOv_eq_if : ∀ (l : List Ov) (x : Ov),
    snocUniqueOv l x = if x ∈ l then l else l ++ [x]
  | [], x => by simp [snocUniqueOv]
  | h :: tl, x => by
    by_cases hh : h = x
    · subst hh
      have : Ov.eqb h h = true := (Ov.eqb_iff h h).2 rfl
      simp [snocUniqueOv, this]
    · have hb : Ov.eqb h x = false := by
        cases e : Ov.eqb h x
        · rfl
        · exact absurd ((Ov.eqb_iff h x).1 e) hh
      rw [snocUniqueOv, hb, snocUniqueOv_eq_if tl x]
      by_cases hm : x ∈ tl
      · simp [hm]
      · have : x ∉ h :: tl := by simp [hm, Ne.symm hh]
        simp [hm, this]

/-! ### `propAdd` over a list of distinct keys -/

theorem propAdd_map_notMem (g : String → List Ov) (p : String) (v : Ov) :
    ∀ keys : List String, p ∉ keys →
      propAdd (keys.map (fun k => (k, g k))) p v = keys.map (fun k => (k, g k)) ++ [(p, [v])]
  | [], _ => by simp [propAdd]
  | k :: ks, h => by
    have hk : k ≠ p := fun e => h (e ▸ List.mem_cons_self)
    have hks : p ∉ ks := fun m => h (List.mem_cons_of_mem _ m)
    simp [propAdd, hk, propAdd_map_notMem g p v ks hks]

theorem propAdd_map_mem (g : String → List Ov) (p : String) (v : Ov) :
    ∀ keys : List String, keys.Nodup → p ∈ keys →
      propAdd (keys.map (fun k => (k, g k))) p v =
        keys.map (fun k => (k, if k = p then snocUniqueOv (g k) v else g k))
  | [], _, h => absurd h List.not_mem_nil
  | k :: ks, nd, h => by
    rw [List.nodup_cons] at nd
    by_cases hk : k = p
    · subst hk
      simp only [List.map_cons, propAdd, beq_self_eq_true, if_true, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro k' hk'
      have : k' ≠ k := fun e => nd.1 (e ▸ hk')
      simp [this]
    · have hp : p ∈ ks := by
        cases List.mem_cons.1 h with
        | inl e => exact absurd e.symm hk
        | inr m => exact m
      have hb : (k == p) = false := by simpa using hk
      simp only [List.map_cons, propAdd, hb, Bool.false_eq_true, if_false, hk,
        propAdd_map_mem g p v ks nd.2 hp]

/-! ### Node objects under construction -/

structure NodeF where
  blank   : Bool
  types   : Array String
  typeSet : HashSet String
  pkeys   : Array String
  pvals   : HashMap String (Array Ov × HashSet Ov)

def NodeF.empty (b : Bool) : NodeF := ⟨b, #[], ∅, #[], ∅⟩

instance : Inhabited NodeF := ⟨NodeF.empty false⟩

def NodeF.propsL (nf : NodeF) : List (String × List Ov) :=
  nf.pkeys.toList.map (fun k => (k, (nf.pvals.getD k (#[], ∅)).1.toList))

def NodeF.toFr (k : String) (nf : NodeF) : FrNode :=
  { id := k, blank := nf.blank, types := nf.types.toList, props := nf.propsL }

@[simp] theorem NodeF.toFr_id (k : String) (nf : NodeF) : (nf.toFr k).id = k := rfl

structure NodeF.Good (nf : NodeF) : Prop where
  types : ∀ t, nf.typeSet.contains t = true ↔ t ∈ nf.types.toList
  nodup : nf.pkeys.toList.Nodup
  keys  : ∀ k, nf.pvals.contains k = true ↔ k ∈ nf.pkeys.toList
  vals  : ∀ (k : String) (a : Array Ov) (s : HashSet Ov), nf.pvals[k]? = some (a, s) →
    ∀ v, s.contains v = true ↔ v ∈ a.toList

theorem NodeF.good_empty (b : Bool) : (NodeF.empty b).Good :=
  ⟨by simp [NodeF.empty], by simp [NodeF.empty], by simp [NodeF.empty],
   by simp [NodeF.empty]⟩

def NodeF.addType (nf : NodeF) (t : String) : NodeF :=
  if nf.typeSet.contains t then nf
  else { nf with types := nf.types.push t, typeSet := nf.typeSet.insert t }

theorem NodeF.addType_spec (nf : NodeF) (t : String) (h : nf.Good) :
    (nf.addType t).blank = nf.blank ∧
    (nf.addType t).types.toList = snocUniqueStr nf.types.toList t ∧
    (nf.addType t).propsL = nf.propsL ∧ (nf.addType t).Good := by
  unfold NodeF.addType
  by_cases hc : nf.typeSet.contains t = true
  · have hm : t ∈ nf.types.toList := (h.types t).1 hc
    simp only [hc, if_true, snocUniqueStr_eq_if, hm]
    exact ⟨by first | rfl | simp, by first | rfl | simp, by first | rfl | simp, h⟩
  · have hm : t ∉ nf.types.toList := fun m => hc ((h.types t).2 m)
    simp only [hc, Bool.false_eq_true, if_false, snocUniqueStr_eq_if, hm]
    refine ⟨by first | rfl | simp, by first | rfl | simp, by first | rfl | simp, ⟨?_, h.nodup, h.keys, h.vals⟩⟩
    intro t'
    simp only [HashSet.contains_insert, Array.toList_push, List.mem_append, List.mem_singleton,
      Bool.or_eq_true, beq_iff_eq, h.types t']
    constructor
    · rintro (e | m)
      · exact Or.inr e.symm
      · exact Or.inl m
    · rintro (m | e)
      · exact Or.inr m
      · exact Or.inl e.symm

def NodeF.addProp (nf : NodeF) (p : String) (v : Ov) : NodeF :=
  match nf.pvals[p]? with
  | some (a, s) =>
    if s.contains v then nf
    else { nf with pvals := nf.pvals.insert p (a.push v, s.insert v) }
  | none =>
    { nf with pkeys := nf.pkeys.push p, pvals := nf.pvals.insert p (#[v], (∅ : HashSet Ov).insert v) }

theorem NodeF.addProp_spec (nf : NodeF) (p : String) (v : Ov) (h : nf.Good) :
    (nf.addProp p v).blank = nf.blank ∧ (nf.addProp p v).types = nf.types ∧
    (nf.addProp p v).propsL = propAdd nf.propsL p v ∧ (nf.addProp p v).Good := by
  unfold NodeF.addProp
  split
  · rename_i a s hp
    have hpk : p ∈ nf.pkeys.toList := by
      rw [← h.keys p, HashMap.contains_eq_isSome_getElem?, hp]; rfl
    have hg : (nf.pvals.getD p (#[], ∅)).1.toList = a.toList := by
      rw [HashMap.getD_eq_getD_getElem?, hp]; rfl
    have hv := h.vals p a s hp
    unfold NodeF.propsL
    rw [propAdd_map_mem _ p v _ h.nodup hpk]
    by_cases hc : s.contains v = true
    · have hm : v ∈ a.toList := (hv v).1 hc
      simp only [hc, if_true]
      refine ⟨by first | rfl | simp, by first | rfl | simp, ?_, h⟩
      apply List.map_congr_left
      intro k _
      by_cases e : k = p
      · subst e; simp [hg, snocUniqueOv_eq_if, hm]
      · simp [e]
    · have hm : v ∉ a.toList := fun m => hc ((hv v).2 m)
      simp only [hc, Bool.false_eq_true, if_false]
      refine ⟨by first | rfl | simp, by first | rfl | simp, ?_, ⟨h.types, h.nodup, ?_, ?_⟩⟩
      · apply List.map_congr_left
        intro k _
        by_cases e : k = p
        · subst e; simp [hg, snocUniqueOv_eq_if, hm]
        · have : (p == k) = false := by simpa using Ne.symm e
          simp [e, HashMap.getD_insert, this]
      · intro k
        simp only [HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, h.keys k]
        constructor
        · rintro (e | m)
          · exact e ▸ hpk
          · exact m
        · intro m; exact Or.inr m
      · intro k a' s' hk w
        rw [HashMap.getElem?_insert] at hk
        by_cases e : p = k
        · have : (p == k) = true := by simpa using e
          simp only [this, if_true, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          simp only [HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Array.toList_push,
            List.mem_append, List.mem_singleton, hv w]
          constructor
          · rintro (e | m)
            · exact Or.inr e.symm
            · exact Or.inl m
          · rintro (m | e)
            · exact Or.inr m
            · exact Or.inl e.symm
        · have : (p == k) = false := by simpa using e
          simp only [this, Bool.false_eq_true, if_false] at hk
          exact h.vals k a' s' hk w
  · rename_i hp
    have hpk : p ∉ nf.pkeys.toList := by
      rw [← h.keys p, HashMap.contains_eq_isSome_getElem?, hp]; simp
    unfold NodeF.propsL
    rw [propAdd_map_notMem _ p v _ hpk]
    refine ⟨by first | rfl | simp, by first | rfl | simp, ?_, ⟨h.types, ?_, ?_, ?_⟩⟩
    · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      congr 1
      · apply List.map_congr_left
        intro k hk
        have : (p == k) = false := by
          simp only [beq_eq_false_iff_ne]; intro e; exact hpk (e ▸ hk)
        simp [HashMap.getD_insert, this]
      · simp [HashMap.getD_insert]
    · simp only [Array.toList_push]
      rw [List.nodup_append]
      refine ⟨h.nodup, by simp, ?_⟩
      intro a ha b hb e
      simp at hb; subst hb; subst e; exact hpk ha
    · intro k
      simp only [HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, h.keys k,
        Array.toList_push, List.mem_append, List.mem_singleton]
      constructor
      · rintro (e | m)
        · exact Or.inr e.symm
        · exact Or.inl m
      · rintro (m | e)
        · exact Or.inr m
        · exact Or.inl e.symm
    · intro k a' s' hk w
      rw [HashMap.getElem?_insert] at hk
      by_cases e : p = k
      · have : (p == k) = true := by simpa using e
        simp only [this, if_true, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        simp [HashSet.contains_insert]
        exact eq_comm
      · have : (p == k) = false := by simpa using e
        simp only [this, Bool.false_eq_true, if_false] at hk
        exact h.vals k a' s' hk w

/-! ### The node map -/

structure NmF where
  keys  : Array String
  nodes : HashMap String NodeF

def NmF.empty : NmF := ⟨#[], ∅⟩

def NmF.abs (s : NmF) : List FrNode :=
  s.keys.toList.map (fun k => (s.nodes.getD k default).toFr k)

structure NmF.Good (s : NmF) : Prop where
  keys  : ∀ k, s.nodes.contains k = true ↔ k ∈ s.keys.toList
  nodes : ∀ (k : String) (nf : NodeF), s.nodes[k]? = some nf → nf.Good

theorem NmF.good_empty : NmF.empty.Good := ⟨by simp [NmF.empty], by simp [NmF.empty]⟩

theorem NmF.abs_empty : NmF.empty.abs = [] := rfl

theorem nodeExists_map (F : String → FrNode) (hF : ∀ k, (F k).id = k) (keys : List String)
    (id : String) : nodeExists (keys.map F) id = decide (id ∈ keys) := by
  unfold nodeExists findNode
  rw [List.find?_map]
  cases e : List.find? ((fun n => n.id == id) ∘ F) keys with
  | none =>
    rw [List.find?_eq_none] at e
    simp only [Option.map_none, Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not]
    intro m; have := e id m; simp [hF] at this
  | some k =>
    have hk := List.find?_some e
    have hm := List.mem_of_find?_eq_some e
    simp [hF] at hk; subst hk
    simp [hm]

def NmF.ensure (s : NmF) (id : String) (b : Bool) : NmF :=
  if s.nodes.contains id then s else ⟨s.keys.push id, s.nodes.insert id (NodeF.empty b)⟩

theorem NmF.ensure_spec (s : NmF) (id : String) (b : Bool) (h : s.Good) :
    (s.ensure id b).abs = ensureNode s.abs id b ∧ (s.ensure id b).Good := by
  unfold NmF.ensure ensureNode
  have hx : nodeExists s.abs id = decide (id ∈ s.keys.toList) :=
    nodeExists_map _ (fun _ => rfl) _ id
  by_cases hc : s.nodes.contains id = true
  · have hm : id ∈ s.keys.toList := (h.keys id).1 hc
    simp [hc, hx, hm, h]
  · have hm : id ∉ s.keys.toList := fun m => hc ((h.keys id).2 m)
    simp only [hc, Bool.false_eq_true, if_false, hx, hm, decide_false]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · unfold NmF.abs
      simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
      congr 1
      · apply List.map_congr_left
        intro k hk
        have : (id == k) = false := by
          simp only [beq_eq_false_iff_ne]; intro e; exact hm (e ▸ hk)
        simp [HashMap.getD_insert, this]
      · simp [HashMap.getD_insert, NodeF.toFr, NodeF.empty, NodeF.propsL]
    · intro k
      simp only [HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, h.keys k,
        Array.toList_push, List.mem_append, List.mem_singleton]
      constructor
      · rintro (e | m)
        · exact Or.inr e.symm
        · exact Or.inl m
      · rintro (m | e)
        · exact Or.inr m
        · exact Or.inl e.symm
    · intro k nf hk
      rw [HashMap.getElem?_insert] at hk
      by_cases e : id = k
      · have : (id == k) = true := by simpa using e
        simp only [this, if_true, Option.some.injEq] at hk
        subst hk; exact NodeF.good_empty b
      · have : (id == k) = false := by simpa using e
        simp only [this, Bool.false_eq_true, if_false] at hk
        exact h.nodes k nf hk

/-- Shared step of `updProp` and `updType`: replace the node `id` by `f` of it. -/
def NmF.upd (s : NmF) (id : String) (f : NodeF → NodeF) : NmF :=
  match s.nodes[id]? with
  | some nf => { s with nodes := s.nodes.insert id (f nf) }
  | none    => s

theorem NmF.upd_spec (s : NmF) (id : String) (f : NodeF → NodeF) (g : FrNode → FrNode)
    (h : s.Good) (hf : ∀ nf, nf.Good → (f nf).Good ∧ (f nf).toFr id = g (nf.toFr id)) :
    (s.upd id f).abs = s.abs.map (fun n => if n.id == id then g n else n) ∧ (s.upd id f).Good := by
  unfold NmF.upd NmF.abs
  rw [List.map_map]
  split
  · rename_i nf hn
    have hg := h.nodes id nf hn
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · apply List.map_congr_left
      intro k hk
      by_cases e : k = id
      · subst e
        have hd : s.nodes.getD k default = nf := by
          rw [HashMap.getD_eq_getD_getElem?, hn]; rfl
        simp only [HashMap.getD_insert, beq_self_eq_true, if_true, hd, Function.comp_apply,
          NodeF.toFr_id]
        exact (hf nf hg).2
      · have : (id == k) = false := by simpa using Ne.symm e
        simp [HashMap.getD_insert, this, NodeF.toFr, e]
    · intro k
      simp only [HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, h.keys k]
      constructor
      · rintro (e | m)
        · rw [← e, ← h.keys id, HashMap.contains_eq_isSome_getElem?, hn]; rfl
        · exact m
      · intro m; exact Or.inr m
    · intro k nf' hk
      rw [HashMap.getElem?_insert] at hk
      by_cases e : id = k
      · have : (id == k) = true := by simpa using e
        simp only [this, if_true, Option.some.injEq] at hk
        subst hk; exact (hf nf hg).1
      · have : (id == k) = false := by simpa using e
        simp only [this, Bool.false_eq_true, if_false] at hk
        exact h.nodes k nf' hk
  · rename_i hn
    have hm : id ∉ s.keys.toList := by
      rw [← h.keys id, HashMap.contains_eq_isSome_getElem?, hn]; simp
    refine ⟨?_, h⟩
    apply List.map_congr_left
    intro k hk
    have : k ≠ id := fun e => hm (e ▸ hk)
    simp [NodeF.toFr, this]

def NmF.updProp (s : NmF) (id p : String) (v : Ov) : NmF := s.upd id (fun nf => nf.addProp p v)

def NmF.updType (s : NmF) (id t : String) : NmF := s.upd id (fun nf => nf.addType t)

theorem NmF.updProp_spec (s : NmF) (id p : String) (v : Ov) (h : s.Good) :
    (s.updProp id p v).abs = nodeUpdateProp s.abs id p v ∧ (s.updProp id p v).Good := by
  apply NmF.upd_spec s id _ (fun n => { n with props := propAdd n.props p v }) h
  intro nf hg
  obtain ⟨hb, ht, hp, hgood⟩ := NodeF.addProp_spec nf p v hg
  exact ⟨hgood, by simp [NodeF.toFr, hb, ht, hp]⟩

theorem NmF.updType_spec (s : NmF) (id t : String) (h : s.Good) :
    (s.updType id t).abs = nodeUpdateType s.abs id t ∧ (s.updType id t).Good := by
  apply NmF.upd_spec s id _ (fun n => { n with types := snocUniqueStr n.types t }) h
  intro nf hg
  obtain ⟨hb, ht, hp, hgood⟩ := NodeF.addType_spec nf t hg
  exact ⟨hgood, by simp [NodeF.toFr, hb, ht, hp]⟩

/-! ### Node-map construction on `NmF` -/

def processTripleF (opts : Options) (s : NmF) (t : Triple) : Option NmF :=
  let sId := subjId t.s
  let s1 := s.ensure sId (subjIsBlank t.s)
  let s2 := match termNodeId t.o with
            | some (oid, ob) => s1.ensure oid ob
            | none           => s1
  let p := t.p.val
  let objIsNode := match t.o with | .iri _ => true | .bnode _ => true | _ => false
  if p == rdfTypeIri && !opts.useRdfType && objIsNode then
    match termNodeId t.o with
    | some (oid, _) => some (s2.updType sId oid)
    | none          => some s2
  else
    match rdfToObject opts t.o with
    | none   => none
    | some v => some (s2.updProp sId p v)

theorem processTripleF_spec (opts : Options) (s : NmF) (t : Triple) (h : s.Good) :
    processTriple opts s.abs t = (processTripleF opts s t).map NmF.abs ∧
    ∀ s', processTripleF opts s t = some s' → s'.Good := by
  rcases t with ⟨ts, tp, to⟩
  obtain ⟨e1, g1⟩ := NmF.ensure_spec s (subjId ts) (subjIsBlank ts) h
  cases to with
  | iri i =>
    obtain ⟨e2, g2⟩ := NmF.ensure_spec (s.ensure (subjId ts) (subjIsBlank ts)) i.val false g1
    simp only [processTriple, processTripleF, termNodeId, ← e1, ← e2]
    split
    · obtain ⟨e, g⟩ := NmF.updType_spec _ (subjId ts) i.val g2
      exact ⟨by simp [e], fun s' hs' => by cases hs'; exact g⟩
    · cases rdfToObject opts (Term.iri i) with
      | none => exact ⟨rfl, fun s' hs' => by cases hs'⟩
      | some v =>
        obtain ⟨e, g⟩ := NmF.updProp_spec _ (subjId ts) tp.val v g2
        exact ⟨by simp [e], fun s' hs' => by cases hs'; exact g⟩
  | bnode b =>
    obtain ⟨e2, g2⟩ := NmF.ensure_spec (s.ensure (subjId ts) (subjIsBlank ts)) ("_:" ++ b) true g1
    simp only [processTriple, processTripleF, termNodeId, ← e1, ← e2]
    split
    · obtain ⟨e, g⟩ := NmF.updType_spec _ (subjId ts) ("_:" ++ b) g2
      exact ⟨by simp [e], fun s' hs' => by cases hs'; exact g⟩
    · cases rdfToObject opts (Term.bnode b) with
      | none => exact ⟨rfl, fun s' hs' => by cases hs'⟩
      | some v =>
        obtain ⟨e, g⟩ := NmF.updProp_spec _ (subjId ts) tp.val v g2
        exact ⟨by simp [e], fun s' hs' => by cases hs'; exact g⟩
  | literal l =>
    simp only [processTriple, processTripleF, termNodeId, ← e1, Bool.and_false,
      Bool.false_eq_true, if_false]
    cases rdfToObject opts (Term.literal l) with
    | none => exact ⟨rfl, fun s' hs' => by cases hs'⟩
    | some v =>
      obtain ⟨e, g⟩ := NmF.updProp_spec _ (subjId ts) tp.val v g1
      exact ⟨by simp [e], fun s' hs' => by cases hs'; exact g⟩
  | tripleTerm a b c =>
    simp only [processTriple, processTripleF, termNodeId, ← e1, Bool.and_false,
      Bool.false_eq_true, if_false]
    cases rdfToObject opts (Term.tripleTerm a b c) with
    | none => exact ⟨rfl, fun s' hs' => by cases hs'⟩
    | some v =>
      obtain ⟨e, g⟩ := NmF.updProp_spec _ (subjId ts) tp.val v g1
      exact ⟨by simp [e], fun s' hs' => by cases hs'; exact g⟩

def buildF (opts : Options) : NmF → List Triple → Option NmF
  | s, []      => some s
  | s, t :: tl =>
    match processTripleF opts s t with
    | none    => none
    | some s' => buildF opts s' tl

theorem buildF_spec (opts : Options) : ∀ (ts : List Triple) (s : NmF), s.Good →
    buildNodemap opts s.abs ts = (buildF opts s ts).map NmF.abs
  | [], s, _ => rfl
  | t :: tl, s, h => by
    obtain ⟨e, g⟩ := processTripleF_spec opts s t h
    simp only [buildNodemap, buildF, e]
    cases hp : processTripleF opts s t with
    | none => rfl
    | some s' => exact buildF_spec opts tl s' (g s' hp)

/-- `buildNodemap` line for line, for the inputs `buildNodemapFast` does not
start from an empty map. -/
def buildNodemapRef (opts : Options) : List FrNode → List Triple → Option (List FrNode)
  | nm, []      => some nm
  | nm, t :: tl =>
    match processTriple opts nm t with
    | none     => none
    | some nm' => buildNodemapRef opts nm' tl

theorem buildNodemapRef_eq (opts : Options) : ∀ nm ts, buildNodemapRef opts nm ts = buildNodemap opts nm ts
  | _, [] => rfl
  | nm, t :: tl => by
    simp only [buildNodemapRef, buildNodemap]
    cases processTriple opts nm t with
    | none => rfl
    | some nm' => exact buildNodemapRef_eq opts nm' tl

def buildNodemapFast (opts : Options) (nm : List FrNode) (ts : List Triple) : Option (List FrNode) :=
  match nm with
  | [] => (buildF opts NmF.empty ts).map NmF.abs
  | _  => buildNodemapRef opts nm ts

@[csimp] theorem buildNodemap_eq_fast : @buildNodemap = @buildNodemapFast := by
  funext opts nm ts
  unfold buildNodemapFast
  split
  · rw [← buildF_spec opts ts NmF.empty NmF.good_empty]; rfl
  · exact (buildNodemapRef_eq opts nm ts).symm

end Fast

end L4Factoidal.JSONLD.FromRdf
