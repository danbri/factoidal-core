/-
L4Factoidal.JSONLD.Frame — the JSON-LD 1.1 Framing algorithm.

Spec: <https://www.w3.org/TR/json-ld11-framing/>.

Framing shapes a JSON-LD document into a tree a caller describes with a
FRAME document: which node types appear at the top level, which
properties are embedded inline, which are left as references, and which
defaults fill the gaps.

The pipeline follows the `frame()` method of Framing §5.1:

  1. expand the input and expand the frame (the frame under the Framing
     grammar, `JSONLD.Expand`'s `frameExpansion` flag);
  2. generate the node map of the input (API §7.2, `JSONLD.Flatten.nmg`),
     one node map per graph, plus the merged node map (API §7.3);
  3. run the Framing Algorithm (§4.1), with the Frame Matching Algorithm
     (§4.2) and the Value Pattern Matching Algorithm (§4.3);
  4. remove the identifiers of blank nodes that occur once (§5.1, when
     `pruneBlankNodeIdentifiers` holds) and replace each `@preserve`
     wrapper by the value it holds;
  5. compact against the frame's `@context`, replace `@null` by `null`,
     and arrange the top-level `@graph` according to `omitGraph`.

## What this covers

  * `@type` / `@id` / property matching, with `@requireAll` (§4.2): the
    wildcard `{}`, "match none" `[]`, `@type` default objects, node
    patterns matched recursively, value patterns (§4.3) including the
    array and wildcard forms of `@value`, `@type` and `@language`, and
    list patterns;
  * the object embed flag `@embed` (`@always`, `@once`, `@never`, and the
    boolean forms), and in `json-ld-1.0` processing mode the legacy
    `@first` and `@last`, where `@last` replaces an earlier embed by a
    node reference, together with the dependent embeds that replacement
    drops;
  * `@explicit`, `@requireAll` and `@omitDefault`, as options and as
    entries of a frame;
  * `@default` (any expanded value, `@null`, and `@type` defaults),
    `@reverse`, `@included`;
  * named graphs: framing the merged graph or, when the frame has a
    top-level `@graph`, the default graph; `@graph` entries of a frame
    that descend into the named graph of a matched node;
  * blank-node identifier pruning, `@preserve` removal, `@null`
    replacement, `omitGraph`, and the frame errors `invalid frame` and
    `invalid @embed value`.

## Where the specification leaves room

  * `@embed` takes `@always`, `@once` or `@never` (§5.3.2) and the boolean
    forms. `@first` and `@last`, which the earlier drafts defined, are
    accepted only under `json-ld-1.0` processing, because fixture `#t0059`
    needs `@last`. `@link` of the earlier drafts is not a value of
    `JsonLdEmbed` and is an `invalid @embed value`.
  * The traversal order is fixed: subjects and properties are visited in
    code-point order. §4.1 makes that order mandatory when `ordered` is
    true and leaves it open when `ordered` is false, so the fixed order
    satisfies both settings and the `ordered` option has no effect.

## State, and why it is an arena

§4.1 mutates its output after the fact: `@embed: @last` turns an
embedded node that is already part of the output into a node reference.
The mutated node belongs to a parent whose construction is still in
progress higher up the recursion. A purely functional walk cannot reach
that parent, so the output is built in an arena — a growable array of
containers (arrays and objects) that refer to each other by index — and
the "unique embeds" registry records the arena index of each embed's
parent. The arena is then turned into a `Json` tree.

## Recursion

The algorithm recurses over the node graph, which may be cyclic. Every
recursive function takes an explicit `fuel` that decreases at each call,
as the other JSON-LD modules do; exhaustion is `contextOverflow`, never
a wrong answer. A cycle is also cut by the algorithm itself (the subject
stack of §4.1 forbids an embed that would create a circular reference).

## Language tags

Language tags are lower-cased in the expanded input before framing. API
§5.1.2 allows this ("Processors MAY normalize language tags to lower
case") and §4.2 compares `@language` "without regard to case". The
normalisation is applied here, not in `JSONLD.Expand`, so that the
expansion manifest keeps measuring the case-preserving behaviour.
-/
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.Flatten

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Small helpers over `Json` -/

/-- A JSON-LD keyword key starts with a commercial at. -/
def isKeyword (k : String) : Bool := k.startsWith "@"

def objFields : Json → List (String × Json)
  | .object fs => fs
  | _ => []

def objGet (v : Json) (k : String) : Option Json :=
  (objFields v).find? (fun kv => kv.1 == k) |>.map Prod.snd

def objHas (v : Json) (k : String) : Bool := (objGet v k).isSome

/-- The values a node (or a frame) holds for a key, as a list. -/
def getValues (v : Json) (k : String) : List Json :=
  match objGet v k with
  | some x => asArray x
  | none => []

/-- Equality of two values as the suites compare them (RFC 8785 form). -/
def jsonEqv (a b : Json) : Bool := jcsDocument a == jcsDocument b

def isEmptyObj : Json → Bool
  | .object [] => true
  | _ => false

def isValueObj : Json → Bool
  | .object fs => hasField "@value" fs
  | _ => false

def isListObj : Json → Bool
  | .object fs => hasField "@list" fs
  | _ => false

/-- A node reference: an object whose only entry is `@id`. -/
def isSubjectRef : Json → Bool
  | .object [("@id", _)] => true
  | _ => false

/-- A node pattern or node object: not a value, set or list object, and
either more than an `@id` or no `@id` at all. -/
def isSubjectObj : Json → Bool
  | .object fs =>
    !(hasField "@value" fs || hasField "@set" fs || hasField "@list" fs)
      && (fs.length > 1 || !hasField "@id" fs)
  | _ => false

/-- The keys of an association list, in code-point order. -/
def sortedKeys {α : Type} (xs : List (String × α)) : List String :=
  (flSortByKey xs).map Prod.fst

def lowerJson : Json → Json
  | .string s => .string (cmpLower s)
  | other => other

/-- The framing keywords of §4.1.1. They do not count when deciding
whether a frame object is the wildcard. -/
def isFramingKeyword' (k : String) : Bool :=
  k == "@embed" || k == "@explicit" || k == "@requireAll" || k == "@omitDefault"
    || k == "@default"

/-! ## Options -/

/-- The options of `JsonLdProcessor.frame()` (Framing §5.3.2) together
with the API options it reads. -/
structure FrameOptions where
  /-- The object embed flag a frame without `@embed` falls back to. -/
  embed : String := "@once"
  explicit : Bool := false
  omitDefault : Bool := false
  requireAll : Bool := false
  /-- `none`: false under `json-ld-1.0`, true otherwise (§5.3.2). -/
  omitGraph : Option Bool := none
  /-- `none`: false under `json-ld-1.0`, true otherwise (§5.1). -/
  pruneBlankNodeIdentifiers : Option Bool := none
  /-- Accepted; the traversal order is fixed (see the module header). -/
  ordered : Bool := false
  compactArrays : Bool := true
  processingMode : Option String := none
  base : Option String := none

/-- The three flags §4.1 initialises from the frame: the object embed
flag, the explicit inclusion flag, and the require all flag. -/
structure Flags where
  embed : String
  explicit : Bool
  requireAll : Bool

/-- The first value of a frame entry, looking through the array form. -/
def frameEntry (fr : Json) (k : String) : Option Json :=
  match objGet fr k with
  | some (.array (x :: _)) => some x
  | some (.array []) => none
  | some x => some x
  | none => none

/-- A boolean frame entry. The strings `"true"` and `"false"` are read as
booleans, because a fixture writes `"@omitDefault": "true"`. -/
def frameBool (fr : Json) (k : String) (dflt : Bool) : Bool :=
  match frameEntry fr k with
  | some (.bool b) => b
  | some (.string "true") => true
  | some (.string "false") => false
  | _ => dflt

/-- The object embed flag of a frame (§4.1, §5.3.2). `true` is `@once`
and `false` is `@never`. `@first` and `@last` are legacy values that only
`json-ld-1.0` processing accepts. -/
def frameEmbed (fr : Json) (dflt : String) (mode10 : Bool) : Res String :=
  match frameEntry fr "@embed" with
  | none => .ok dflt
  | some (.bool true) => .ok "@once"
  | some (.bool false) => .ok "@never"
  | some (.string s) =>
    if s == "@always" || s == "@never" || s == "@once" then .ok s
    else if mode10 && (s == "@first" || s == "@last") then .ok s
    else .error .invalidEmbedValue
  | some _ => .error .invalidEmbedValue

def frameFlags (opts : FrameOptions) (mode10 : Bool) (fr : Json) : Res Flags :=
  match frameEmbed fr opts.embed mode10 with
  | .error e => .error e
  | .ok em =>
    .ok { embed := em, explicit := frameBool fr "@explicit" opts.explicit,
          requireAll := frameBool fr "@requireAll" opts.requireAll }

/-- The frame §4.1 builds for a property the frame does not mention: a
new map with `@embed`, `@explicit` and `@requireAll` taken from the
current flags. -/
def implicitFrame (fl : Flags) : Json :=
  .array [.object [("@embed", .array [.string fl.embed]),
                   ("@explicit", .array [.bool fl.explicit]),
                   ("@requireAll", .array [.bool fl.requireAll])]]

/-! ## Frame validation (§4.1 step 1) -/

/-- An absolute IRI reference: `scheme ":" rest` with no white space. -/
def isAbsoluteIriRef (s : String) : Bool :=
  match s.splitOn ":" with
  | scheme :: _ :: _ =>
    let rest := String.ofList (s.toList.drop (scheme.toList.length + 1))
    let schemeOk :=
      scheme == "_" ||
      (match scheme.toList with
       | c :: cs => c.isAlpha && cs.all (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.')
       | [] => false)
    schemeOk && !(rest.toList.any Char.isWhitespace)
  | _ => false

/-- An `@id` or `@type` entry of a frame: a wildcard or default object,
or an absolute IRI that is not a blank node identifier. -/
def frameIriEntryOk : Json → Bool
  | .object _ => true
  | .string s => isAbsoluteIriRef s && !isBnodeId s
  | _ => false

/-- §4.1 step 1: a frame is a single object; its `@id` and `@type`
entries are IRIs, the wildcard, or (for `@type`) default objects.

A value pattern (a frame object with `@value`, §4.3) is a frame too, but
its `@type` is a datatype IRI or the keyword `@json`, so the IRI test of
`@id` and `@type` entries is for node patterns only. -/
def validateFrame (frame : Json) : Res Json :=
  match frame with
  | .array [fr@(.object fs)] =>
    if hasField "@value" fs then .ok fr
    else if (getValues fr "@id").all frameIriEntryOk && (getValues fr "@type").all frameIriEntryOk
    then .ok fr
    else .error .invalidFrame
  | _ => .error .invalidFrame

/-! ## Node-map access -/

/-- The node maps of every graph: `"@default"`, each named graph, and
`"@merged"` when the merged graph is framed. -/
structure Env where
  graphs : Std.TreeMap String NmGraph
  rootGraph : String
  opts : FrameOptions
  mode10 : Bool

def Env.nodes (env : Env) (g : String) : NmGraph := (env.graphs.get? g).getD Std.TreeMap.empty

def Env.node (env : Env) (g id : String) : Option NmNode := (env.nodes g).get? id

/-- The values of a key in a node, as a list. -/
def nodeValues (n : NmNode) (k : String) : List Json :=
  match n.find? k with
  | some x => x.items
  | none => []

/-! ## Matching (§4.2, §4.3) -/

/-- Entries of a value pattern component, as a list: absent and `null`
are empty. -/
def patternList (pattern : Json) (k : String) : List Json :=
  match objGet pattern k with
  | none | some .null => []
  | some x => asArray x

/-- §4.3 Value Pattern Matching. A pattern component that is empty
accepts only a value that lacks the component; `[{}]` accepts any value
that has it; otherwise the value must be one of the listed ones.
Language tags compare without regard to case. -/
def valueMatch (pattern value : Json) : Bool :=
  let v1 := objGet value "@value"
  let t1 := objGet value "@type"
  let l1 := (objGet value "@language").map lowerJson
  let v2 := patternList pattern "@value"
  let t2 := patternList pattern "@type"
  let l2 := (patternList pattern "@language").map lowerJson
  let wild (xs : List Json) : Bool := match xs.head? with | some h => isEmptyObj h | none => false
  if v2.isEmpty && t2.isEmpty && l2.isEmpty then true
  else
    let okV := (match v1 with | some x => v2.any (jsonEqv x) | none => false) || wild v2
    let okT := (t1.isNone && t2.isEmpty)
               || (match t1 with | some x => t2.any (jsonEqv x) | none => false)
               || (t1.isSome && wild t2)
    let okL := (l1.isNone && l2.isEmpty)
               || (match l1 with | some x => l2.any (jsonEqv x) | none => false)
               || (l1.isSome && wild l2)
    okV && okT && okL

/-- Is this frame object the wildcard: empty once the framing keywords
are set aside? -/
def patternIsWildcard (p : Json) : Bool :=
  (objFields p).all (fun kv => isFramingKeyword' kv.1)

/-- Does some element satisfy a test that can fail? -/
def anyRes {α : Type} (xs : List α) (f : α → Res Bool) : Res Bool :=
  match xs with
  | [] => .ok false
  | x :: rest =>
    match f x with
    | .error e => .error e
    | .ok true => .ok true
    | .ok false => anyRes rest f

mutual

/-- §4.2: does a node (of the root graph) match a node pattern? The
match is recursive; `fuel` bounds the descent through the pattern. -/
def nodeMatch (env : Env) (requireAll : Bool) (pattern value : Json) (fuel : Nat) : Res Bool :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match objGet value "@id" with
    | some (.string vid) =>
      match env.node env.rootGraph vid with
      | some n => filterSubject env requireAll n pattern fuel
      | none => .ok false
    | _ => .ok false

/-- §4.2 Frame Matching for one node and one frame object. -/
def filterSubject (env : Env) (requireAll : Bool) (node : NmNode) (fr : Json) (fuel : Nat)
    : Res Bool :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 => filterKeys env requireAll node fr (flSortByKey (objFields fr)) true false fuel

/-- The loop over a frame object's entries. `wildcard` is true while the
frame has had no `@type` or property entry; `matchesSome` records that
some entry matched. -/
def filterKeys (env : Env) (requireAll : Bool) (node : NmNode) (fr : Json)
    (entries : List (String × Json)) (wildcard matchesSome : Bool) (fuel : Nat) : Res Bool :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => .ok (wildcard || matchesSome)
    | (key, fv) :: rest =>
      let nvals := nodeValues node key
      let fvals := asArray fv
      let isEmpty := fvals.isEmpty
      -- the common ending of one entry
      let finish (matchThis : Bool) (wild : Bool) : Res Bool :=
        if !matchThis && requireAll then .ok false
        else filterKeys env requireAll node fr rest wild (matchesSome || matchThis) fuel
      if key == "@id" then
        let matchThis :=
          match fvals.head? with
          | none => true
          | some h =>
            isEmptyObj h ||
            fvals.any (fun f => match f, nvals.head? with
                                | .string a, some (.string b) => a == b
                                | _, _ => false)
        if !requireAll then .ok matchThis else finish matchThis wildcard
      else if key == "@type" then
        if isEmpty then
          -- "match none": a node with a type does not match
          if !nvals.isEmpty then .ok false
          else if !requireAll then .ok true else finish true false
        else
          let matchThis :=
            if fvals.length == 1 && fvals.all isEmptyObj then !nvals.isEmpty
            else
              fvals.foldl (fun acc t =>
                match t with
                | .object tf =>
                  if hasField "@default" tf then true else acc
                | .string ts => acc || nvals.any (fun nv => match nv with
                                                          | .string x => x == ts
                                                          | _ => false)
                | _ => acc) false
          if !requireAll then .ok matchThis else finish matchThis false
      else if isKeyword key then
        filterKeys env requireAll node fr rest wildcard matchesSome fuel
      else
        let thisFrame := fvals.head?
        let hasDefault := match thisFrame with | some t => objHas t "@default" | none => false
        if nvals.isEmpty && hasDefault then
          filterKeys env requireAll node fr rest false matchesSome fuel
        else if !nvals.isEmpty && isEmpty then .ok false
        else
          match thisFrame with
          | none => finish true false
          | some tf =>
            match validateFrame (.array [tf]) with
            | .error e => .error e
            | .ok _ =>
              let matched : Res Bool :=
                if isListObj tf then
                  match nvals.head? with
                  | some nv0 =>
                    if isListObj nv0 then
                      let items := getValues nv0 "@list"
                      match (getValues tf "@list").head? with
                      | some lv =>
                        if isValueObj lv then .ok (items.any (valueMatch lv))
                        else if isSubjectObj lv || isSubjectRef lv then
                          anyRes items (fun it => nodeMatch env requireAll lv it fuel)
                        else .ok false
                      | none => .ok false
                    else .ok false
                  | none => .ok false
                else if isValueObj tf then .ok (nvals.any (valueMatch tf))
                else if patternIsWildcard tf then .ok (!nvals.isEmpty)
                else if isSubjectObj tf || isSubjectRef tf then
                  anyRes nvals (fun nv => nodeMatch env requireAll tf nv fuel)
                else .ok false
              match matched with
              | .error e => .error e
              | .ok m => finish m false

end

/-- The subjects (ids) of `subjects` that match the frame, in code-point
order of their identifiers. -/
def matchingSubjects (env : Env) (graph : String) (subjects : List String) (fr : Json)
    (fl : Flags) : Res (List String) :=
  (matchingSubjectsGo env graph fr fl (Json.size fr + 16) subjects).map
    (fun ids => ids.mergeSort (fun a b => !strLt b a))
where
  /-- The ids of `subjects` whose node matches, in the order given; the
  first error stops the walk. -/
  matchingSubjectsGo (env : Env) (graph : String) (fr : Json) (fl : Flags) (fuel : Nat) :
      List String → Res (List String)
    | [] => .ok []
    | id :: rest =>
      match env.node graph id with
      | none => matchingSubjectsGo env graph fr fl fuel rest
      | some n =>
        match filterSubject env fl.requireAll n fr fuel with
        | .error e => .error e
        | .ok true => (matchingSubjectsGo env graph fr fl fuel rest).map (fun r => id :: r)
        | .ok false => matchingSubjectsGo env graph fr fl fuel rest

/-- `matchingSubjects.matchingSubjectsGo` with a reverse accumulator: a
tail call per subject. The walk visits every subject of a graph, so its
length is the size of the data; the readable form conses after its
recursive call, one frame per matching subject
(https://github.com/danbri/factoidal/issues/746). The `csimp` theorem makes
the compiler emit this form. -/
def matchingSubjectsGoTR (env : Env) (graph : String) (fr : Json) (fl : Flags) (fuel : Nat)
    (subjects : List String) : Res (List String) :=
  go subjects []
where
  go : List String → List String → Res (List String)
    | [], acc => .ok acc.reverse
    | id :: rest, acc =>
      match env.node graph id with
      | none => go rest acc
      | some n =>
        match filterSubject env fl.requireAll n fr fuel with
        | .error e => .error e
        | .ok true => go rest (id :: acc)
        | .ok false => go rest acc

theorem matchingSubjectsGoTR_go_eq (env : Env) (graph : String) (fr : Json) (fl : Flags)
    (fuel : Nat) : ∀ (subjects acc : List String),
      matchingSubjectsGoTR.go env graph fr fl fuel subjects acc =
        (matchingSubjects.matchingSubjectsGo env graph fr fl fuel subjects).map
          (acc.reverse ++ ·)
  | [], acc => by
      simp [matchingSubjectsGoTR.go, matchingSubjects.matchingSubjectsGo, Except.map]
  | id :: rest, acc => by
      simp only [matchingSubjectsGoTR.go, matchingSubjects.matchingSubjectsGo]
      cases env.node graph id with
      | none => exact matchingSubjectsGoTR_go_eq env graph fr fl fuel rest acc
      | some n =>
          simp only
          cases filterSubject env fl.requireAll n fr fuel with
          | error e => rfl
          | ok b =>
              cases b with
              | true =>
                  simp only
                  rw [matchingSubjectsGoTR_go_eq env graph fr fl fuel rest (id :: acc)]
                  cases matchingSubjects.matchingSubjectsGo env graph fr fl fuel rest <;>
                    simp [Except.map]
              | false => exact matchingSubjectsGoTR_go_eq env graph fr fl fuel rest acc

@[csimp] theorem matchingSubjectsGo_eq_TR :
    @matchingSubjects.matchingSubjectsGo = @matchingSubjectsGoTR := by
  funext env graph fr fl fuel subjects
  rw [matchingSubjectsGoTR, matchingSubjectsGoTR_go_eq]
  cases matchingSubjects.matchingSubjectsGo env graph fr fl fuel subjects <;> simp [Except.map]

/-! ## The output arena -/

/-- A value in the output under construction: a finished JSON value, or
a container in the arena. -/
inductive OVal where
  | lit : Json → OVal
  | ref : Nat → OVal

/-- An output container: a JSON array, or a JSON object whose members are
values or other containers. The items of an `arr` are stored NEWEST FIRST,
so adding an item is a `cons`; `matCont` reverses once when it builds the
JSON value. The members of an `obj` are an insertion-ordered map, so
setting a member does not scan the members already present. -/
inductive OCont where
  | arr : List OVal → OCont
  | obj : OMap OVal → OCont

structure FState where
  arena : Array OCont
  /-- The subject stack of §4.1: the (graph, id) of each node being
  embedded, innermost first. -/
  stack : List (String × String)
  /-- The unique embeds map of §4.1: per graph, per node id, the parent
  container and the property under which the node was last embedded. -/
  embeds : Std.TreeMap String (OMap (Nat × Option String))
  /-- How many output nodes carry each blank node identifier. -/
  bnodes : Std.TreeMap String Nat

abbrev FM := StateT FState Res

def liftRes {α : Type} (r : Res α) : FM α :=
  match r with
  | .ok a => pure a
  | .error e => throw e

def FState.get (st : FState) (i : Nat) : OCont := st.arena[i]?.getD (.arr [])

def FState.put (st : FState) (i : Nat) (c : OCont) : FState :=
  { st with arena := st.arena.set! i c }

def FState.embedsOf (st : FState) (g : String) : OMap (Nat × Option String) :=
  (st.embeds.get? g).getD OMap.empty

def FState.hasEmbed (st : FState) (g id : String) : Bool := (st.embedsOf g).contains id

def FState.onStack (st : FState) (g id : String) : Bool :=
  st.stack.any (fun e => e.1 == g && e.2 == id)

def FState.setEmbed (st : FState) (g id : String) (parent : Nat) (prop : Option String)
    : FState :=
  { st with embeds := st.embeds.insert g ((st.embedsOf g).upsert id (parent, prop)) }

def FState.bumpBnode (st : FState) (id : String) : FState :=
  { st with bnodes := st.bnodes.insert id (((st.bnodes.get? id).getD 0) + 1) }

/-- Add a container to the arena and return its index. One `modifyGet`, so
the state is used once and the arena is extended in place: a `get` followed
by a `set` keeps the old state alive and copies the whole arena. -/
def allocM (c : OCont) : FM Nat :=
  modifyGet (fun st => (st.arena.size, { st with arena := st.arena.push c }))

/-- The object member of a container, if it is an object. -/
def FState.member (st : FState) (i : Nat) (k : String) : Option OVal :=
  match st.get i with
  | .obj es => es.find? k
  | .arr _ => none

def FState.setMember (st : FState) (i : Nat) (k : String) (v : OVal) : FState :=
  match st.get i with
  | .obj es => st.put i (.obj (es.upsert k v))
  | .arr _ => st

/-- The `@id` of an output value, if it is a node or a node reference. -/
def FState.idOf (st : FState) : OVal → Option String
  | .lit (.object fs) =>
    (match fs.find? (fun kv => kv.1 == "@id") with
     | some (_, .string s) => some s
     | _ => none)
  | .lit _ => none
  | .ref i =>
    (match st.member i "@id" with
     | some (.lit (.string s)) => some s
     | _ => none)

/-- Add `item` to `parent`: appended to it if it is an array, else
appended to the array held under `property` (created on first use). -/
def FState.addOutput (st : FState) (parent : Nat) (property : Option String) (item : OVal)
    : FState :=
  match st.get parent with
  | .arr xs => st.put parent (.arr (item :: xs))
  | .obj es =>
    match property with
    | none => st
    | some p =>
      match es.find? p with
      | some (.ref k) =>
        (match st.get k with
         | .arr xs => st.put k (.arr (item :: xs))
         | .obj _ => st)
      | _ =>
        let k := st.arena.size
        let st1 := { st with arena := st.arena.push (.arr [item]) }
        st1.put parent (.obj (es.upsert p (.ref k)))

/-- Replace the first value for which `hit` holds by `reference`; the list
is unchanged when no value matches. -/
def FState.replaceFirstMatch (hit : OVal → Bool) (reference : OVal) : List OVal → List OVal
  | [] => []
  | x :: rest => if hit x then reference :: rest else x :: FState.replaceFirstMatch hit reference rest

/-- `replaceFirstMatch` as a loop: the values before the match go on a
newest-first list, one tail call per value, put back in front once at the
end (the values of one property are data; https://github.com/danbri/factoidal/issues/752). -/
def FState.replaceFirstMatchLoop (hit : OVal → Bool) (reference : OVal) :
    List OVal → List OVal → List OVal
  | [], acc => acc.reverse
  | x :: rest, acc =>
      if hit x then acc.reverseAux (reference :: rest)
      else FState.replaceFirstMatchLoop hit reference rest (x :: acc)

theorem FState.replaceFirstMatchLoop_eq (hit : OVal → Bool) (reference : OVal) :
    ∀ (l acc : List OVal), FState.replaceFirstMatchLoop hit reference l acc =
      acc.reverse ++ FState.replaceFirstMatch hit reference l
  | [], acc => by simp [FState.replaceFirstMatchLoop, FState.replaceFirstMatch]
  | x :: rest, acc => by
      by_cases h : hit x = true
      · simp [FState.replaceFirstMatchLoop, FState.replaceFirstMatch, h]
      · simp [FState.replaceFirstMatchLoop, FState.replaceFirstMatch, h,
          FState.replaceFirstMatchLoop_eq hit reference rest]

def FState.replaceFirstMatchFast (hit : OVal → Bool) (reference : OVal) (l : List OVal) :
    List OVal :=
  FState.replaceFirstMatchLoop hit reference l []

/-- The compiler runs `replaceFirstMatchFast` wherever the source says
`replaceFirstMatch`. -/
@[csimp] theorem FState.replaceFirstMatch_eq_fast :
    @FState.replaceFirstMatch = @FState.replaceFirstMatchFast := by
  funext hit reference l
  simp [FState.replaceFirstMatchFast, FState.replaceFirstMatchLoop_eq]

/-- §4.1: replace the embedded node `id` by a node reference, drop the
embeds that depended on it. Mirrors the legacy `@last` handling: the
reference to a replaced property value moves to the end of its array. -/
def FState.removeEmbed (st : FState) (g id : String) : FState :=
  match (st.embedsOf g).find? id with
  | none => st
  | some (parent, prop) =>
    let reference : OVal := .lit (.object [("@id", .string id)])
    let st1 :=
      match st.get parent with
      | .arr xsRev =>
        -- the items are stored newest first; "first" is the oldest match
        st.put parent (.arr (FState.replaceFirstMatch (fun x => st.idOf x == some id)
          reference xsRev.reverse).reverse)
      | .obj es =>
        match prop with
        | none => st
        | some p =>
          match es.find? p with
          | some (.ref k) =>
            (match st.get k with
             | .arr xsRev =>
               st.put k (.arr (reference :: xsRev.filter (fun x => st.idOf x != some id)))
             | .obj _ => st)
          | _ => st
    -- drop the embeds whose parent is a node with this identifier,
    -- and those whose parent's identifier is a dropped embed's identifier
    let rec dropDependents (cur : FState) (target : String) (fuel : Nat) : FState :=
      match fuel with
      | 0 => cur
      | fuel + 1 =>
        let ids := (cur.embedsOf g).toList.filter (fun e =>
          match cur.member e.2.1 "@id" with
          | some (.lit (.string pid)) => pid == target
          | _ => false)
        ids.foldl (fun acc e =>
          let acc1 := { acc with embeds := acc.embeds.insert g ((acc.embedsOf g).erase e.1) }
          dropDependents acc1 e.1 fuel) cur
    dropDependents st1 id (st1.arena.size + 4)

def addOutputM (parent : Nat) (property : Option String) (item : OVal) : FM Unit :=
  modify (fun st => st.addOutput parent property item)

/-! ## The Framing Algorithm (§4.1) -/

/-- The node ids of a graph, in code-point order. -/
def Env.subjectsOf (env : Env) (g : String) : List String := (env.nodes g).keys

/-- The `@id` of the node a `{"@id": ...}` reference names. -/
def refTarget (o : Json) : Option String :=
  match objGet o "@id" with
  | some (.string s) => some s
  | _ => none

/-- The first frame object of a frame value, or the empty frame. -/
def headFrame (f : Json) : Json :=
  match (asArray f).head? with
  | some h => h
  | none => .object []

/-- The object held by an output object under a member name. -/
def ensureObjMember (parent : Nat) (k : String) : FM Nat := do
  let st ← StateT.get
  match st.member parent k with
  | some (.ref a) => pure a
  | _ =>
    let a ← allocM (.obj OMap.empty)
    modify (fun s => s.setMember parent k (.ref a))
    pure a

/-- The array held by an output object under a member name. -/
def ensureArrayMember (parent : Nat) (k : String) : FM Nat := do
  let st ← StateT.get
  match st.member parent k with
  | some (.ref a) => pure a
  | _ =>
    let a ← allocM (.arr [])
    modify (fun s => s.setMember parent k (.ref a))
    pure a

mutual

/-- Run the Framing Algorithm: frame `subjects` of `graph` against `frameJ`
(an expanded frame), adding the results to `parent` (under `property` when
`parent` is an object). -/
def frameRec (env : Env) (graph : String) (embedded : Bool) (subjects : List String)
    (frameJ : Json) (parent : Nat) (property : Option String) (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 => do
    let fr ← liftRes (validateFrame frameJ)
    let fl ← liftRes (frameFlags env.opts env.mode10 fr)
    let ids ← liftRes (matchingSubjects env graph subjects fr fl)
    frameSubjects env graph embedded subjects fr fl ids parent property fuel
termination_by fuel

def frameSubjects (env : Env) (graph : String) (embedded : Bool) (subjects : List String)
    (fr : Json) (fl : Flags) (ids : List String) (parent : Nat) (property : Option String)
    (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match ids with
    | [] => pure ()
    | id :: rest => do
      frameOne env graph embedded subjects fr fl id parent property fuel
      frameSubjects env graph embedded subjects fr fl rest parent property fuel
termination_by fuel

/-- One matched subject (the body of the `for each` of §4.1). -/
def frameOne (env : Env) (graph : String) (embedded : Bool) (subjects : List String)
    (fr : Json) (fl : Flags) (id : String) (parent : Nat) (property : Option String)
    (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 => do
    -- Each top-level match starts with an empty unique embeds map.
    modify (fun st =>
      if property.isNone then { st with embeds := Std.TreeMap.empty.insert graph OMap.empty }
      else if st.embeds.contains graph then st
      else { st with embeds := st.embeds.insert graph OMap.empty })
    let out ← allocM (.obj (OMap.empty.upsert "@id" (.lit (.string id))))
    if isBnodeId id then modify (fun st => st.bumpBnode id)
    let st ← StateT.get
    if !embedded && st.hasEmbed graph id then
      -- already embedded in another node of the current top-level match
      pure ()
    else if embedded && (fl.embed == "@never" || st.onStack graph id) then
      -- a reference stands in for the embed
      addOutputM parent property (.ref out)
    else if embedded && (fl.embed == "@once" || fl.embed == "@first") && st.hasEmbed graph id then
      addOutputM parent property (.ref out)
    else do
      if fl.embed == "@last" && st.hasEmbed graph id then
        modify (fun s => s.removeEmbed graph id)
      modify (fun s => (s.setEmbed graph id parent property))
      modify (fun s => { s with stack := (graph, id) :: s.stack })
      match env.node graph id with
      | none => pure ()
      | some node => do
        -- the node is also the name of a graph
        if env.graphs.contains id then
          let (recurse, subframe) : Bool × Json :=
            if !objHas fr "@graph" then (graph != "@merged", Json.object [])
            else
              let sf := match (getValues fr "@graph").head? with
                        | some (.object o) => Json.object o
                        | _ => Json.object []
              (!(id == "@merged" || id == "@default"), sf)
          if recurse then
            frameRec env id false (env.subjectsOf id) (.array [subframe]) out (some "@graph") fuel
        -- @included
        match objGet fr "@included" with
        | some inc => frameRec env graph false subjects inc out (some "@included") fuel
        | none => pure ()
        -- the node's own properties
        frameProps env graph fr fl out node.toSortedFields fuel
        -- defaults for the frame's properties the output lacks
        frameDefaults env fr out (flSortByKey (objFields fr)) fuel
        -- @reverse
        match objGet fr "@reverse" with
        | some (.object rentries) =>
          frameReverseProps env graph out id property (flSortByKey rentries) fuel
        | _ => pure ()
        -- the output joins its parent
        addOutputM parent property (.ref out)
      modify (fun s => { s with stack := s.stack.drop 1 })
termination_by fuel

/-- The members of a node: keywords are copied, properties are framed. -/
def frameProps (env : Env) (graph : String) (fr : Json) (fl : Flags) (out : Nat)
    (props : List (String × Json)) (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match props with
    | [] => pure ()
    | (prop, vals) :: rest => do
      if isKeyword prop then
        modify (fun s => s.setMember out prop (.lit vals))
        if prop == "@type" then
          for t in asArray vals do
            match t with
            | .string ts => if isBnodeId ts then modify (fun s => s.bumpBnode ts)
            | _ => pure ()
      else if fl.explicit && !objHas fr prop then pure ()
      else frameValues env graph fr fl out prop (asArray vals) fuel
      frameProps env graph fr fl out rest fuel
termination_by fuel

/-- The values of one property of a node. -/
def frameValues (env : Env) (graph : String) (fr : Json) (fl : Flags) (out : Nat)
    (prop : String) (vals : List Json) (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match vals with
    | [] => pure ()
    | o :: rest => do
      let propFrame := objGet fr prop
      let subframe : Json := propFrame.getD (implicitFrame fl)
      if isListObj o then
        let lsub : Json :=
          match propFrame with
          | some pf =>
            (match objGet (headFrame pf) "@list" with
             | some l => l
             | none => implicitFrame fl)
          | none => implicitFrame fl
        let arrIdx ← allocM (.arr [])
        let lst ← allocM (.obj (OMap.empty.upsert "@list" (.ref arrIdx)))
        addOutputM out (some prop) (.ref lst)
        frameListItems env graph lsub lst (getValues o "@list") fuel
      else if isSubjectRef o then
        match refTarget o with
        | some rid => frameRec env graph true [rid] subframe out (some prop) fuel
        | none => pure ()
      else if valueMatch (headFrame subframe) o then
        addOutputM out (some prop) (.lit o)
      else pure ()
      frameValues env graph fr fl out prop rest fuel
termination_by fuel

/-- The items of a list value: node references are framed, everything
else is copied. -/
def frameListItems (env : Env) (graph : String) (lsub : Json) (lst : Nat)
    (items : List Json) (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => pure ()
    | oo :: rest => do
      if isSubjectRef oo then
        match refTarget oo with
        | some rid => frameRec env graph true [rid] lsub lst (some "@list") fuel
        | none => pure ()
      else addOutputM lst (some "@list") (.lit oo)
      frameListItems env graph lsub lst rest fuel
termination_by fuel

/-- Properties of the frame the output does not have yet get their
`@default`, wrapped in `@preserve`; `@omitDefault` switches this off. -/
def frameDefaults (env : Env) (fr : Json) (out : Nat) (entries : List (String × Json))
    (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => pure ()
    | (prop, fv) :: rest => do
      let skip : Bool :=
        if prop == "@type" then
          !(match (asArray fv).head? with
            | some (.object o) => hasField "@default" o
            | _ => false)
        else isKeyword prop
      if !skip then
        let next := headFrame fv
        let omitOn := frameBool next "@omitDefault" env.opts.omitDefault
        let st ← StateT.get
        if !omitOn && (st.member out prop).isNone then
          let preserve : Json :=
            match objGet next "@default" with
            | some (.array xs) => .array xs
            | some d => .array [d]
            | none => .array [.string "@null"]
          let a ← allocM (.arr [.lit (.object [("@preserve", preserve)])])
          modify (fun s => s.setMember out prop (.ref a))
      frameDefaults env fr out rest fuel
termination_by fuel

/-- `@reverse`: for each reverse property of the frame, embed the nodes
that point at this one. -/
def frameReverseProps (env : Env) (graph : String) (out : Nat) (id : String)
    (property : Option String) (entries : List (String × Json)) (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => pure ()
    | (rprop, subframe) :: rest => do
      frameReverseSubjects env graph out id property rprop subframe
        (env.subjectsOf env.rootGraph) fuel
      frameReverseProps env graph out id property rest fuel
termination_by fuel

def frameReverseSubjects (env : Env) (graph : String) (out : Nat) (id : String)
    (property : Option String) (rprop : String) (subframe : Json) (subs : List String)
    (fuel : Nat) : FM Unit :=
  match fuel with
  | 0 => throw .contextOverflow
  | fuel + 1 =>
    match subs with
    | [] => pure ()
    | s :: rest => do
      match env.node env.rootGraph s with
      | none => pure ()
      | some n =>
        if (nodeValues n rprop).any (fun v => refTarget v == some id) then
          let d ← ensureObjMember out "@reverse"
          let arrIdx ← ensureArrayMember d rprop
          let saved := (← StateT.get).embeds
          frameRec env graph true [s] subframe arrIdx property fuel
          -- a reverse frame reached from the top level runs with a fresh
          -- unique embeds map that is discarded afterwards
          if property.isNone then modify (fun st => { st with embeds := saved })
      frameReverseSubjects env graph out id property rprop subframe rest fuel
termination_by fuel

end

/-! ## From the arena to JSON -/

mutual

/-- Build the JSON tree of container `i`. The output is a tree, so the
depth is bounded by the size of the arena; `fuel` makes that explicit. -/
def matCont (arena : Array OCont) (i : Nat) (fuel : Nat) : Json :=
  match fuel with
  | 0 => .null
  | fuel + 1 =>
    match arena[i]? with
    | some (.arr vsRev) => .array (matValsAcc arena vsRev.reverse fuel [])
    | some (.obj es) => .object (matEntriesAcc arena es.toList fuel [])
    | none => .null

def matVals (arena : Array OCont) (vs : List OVal) (fuel : Nat) : List Json :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match vs with
    | [] => []
    | .lit j :: rest => j :: matVals arena rest fuel
    | .ref k :: rest => matCont arena k fuel :: matVals arena rest fuel

def matEntries (arena : Array OCont) (es : List (String × OVal)) (fuel : Nat)
    : List (String × Json) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match es with
    | [] => []
    | (k, .lit j) :: rest => (k, j) :: matEntries arena rest fuel
    | (k, .ref c) :: rest => (k, matCont arena c fuel) :: matEntries arena rest fuel

/-- `matVals` onto a reverse accumulator: a tail call per value, so the
number of values of one property costs no stack; only the nesting of
containers (`matCont`) takes a frame per level. `matCont` calls this form;
`matValsAcc_eq` proves it equal to `matVals`
(https://github.com/danbri/factoidal/issues/746). -/
def matValsAcc (arena : Array OCont) (vs : List OVal) (fuel : Nat) (acc : List Json) :
    List Json :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
    match vs with
    | [] => acc.reverse
    | .lit j :: rest => matValsAcc arena rest fuel (j :: acc)
    | .ref k :: rest => matValsAcc arena rest fuel (matCont arena k fuel :: acc)

/-- `matEntries` onto a reverse accumulator (see `matValsAcc`). -/
def matEntriesAcc (arena : Array OCont) (es : List (String × OVal)) (fuel : Nat)
    (acc : List (String × Json)) : List (String × Json) :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
    match es with
    | [] => acc.reverse
    | (k, .lit j) :: rest => matEntriesAcc arena rest fuel ((k, j) :: acc)
    | (k, .ref c) :: rest => matEntriesAcc arena rest fuel ((k, matCont arena c fuel) :: acc)

end

theorem matValsAcc_eq (arena : Array OCont) : ∀ (fuel : Nat) (vs : List OVal) (acc : List Json),
    matValsAcc arena vs fuel acc = acc.reverse ++ matVals arena vs fuel
  | 0, vs, acc => by simp [matValsAcc, matVals]
  | _ + 1, [], acc => by simp [matValsAcc, matVals]
  | fuel + 1, .lit j :: rest, acc => by
      simp [matValsAcc, matVals, matValsAcc_eq arena fuel rest]
  | fuel + 1, .ref k :: rest, acc => by
      simp [matValsAcc, matVals, matValsAcc_eq arena fuel rest]

theorem matEntriesAcc_eq (arena : Array OCont) :
    ∀ (fuel : Nat) (es : List (String × OVal)) (acc : List (String × Json)),
      matEntriesAcc arena es fuel acc = acc.reverse ++ matEntries arena es fuel
  | 0, es, acc => by simp [matEntriesAcc, matEntries]
  | _ + 1, [], acc => by simp [matEntriesAcc, matEntries]
  | fuel + 1, (k, .lit j) :: rest, acc => by
      simp [matEntriesAcc, matEntries, matEntriesAcc_eq arena fuel rest]
  | fuel + 1, (k, .ref c) :: rest, acc => by
      simp [matEntriesAcc, matEntries, matEntriesAcc_eq arena fuel rest]

/-- `matCont` builds arrays and objects exactly as `matVals` and
`matEntries` describe them. -/
theorem matCont_arr (arena : Array OCont) (i fuel : Nat) (vsRev : List OVal)
    (h : arena[i]? = some (.arr vsRev)) :
    matCont arena i (fuel + 1) = .array (matVals arena vsRev.reverse fuel) := by
  simp [matCont, h, matValsAcc_eq]

theorem matCont_obj (arena : Array OCont) (i fuel : Nat) (es : OMap OVal)
    (h : arena[i]? = some (.obj es)) :
    matCont arena i (fuel + 1) = .object (matEntries arena es.toList fuel) := by
  simp [matCont, h, matEntriesAcc_eq]

/-- `matVals` with the empty accumulator: what the compiler emits for
`matVals` (`csimp`), so no caller pays a frame per value. -/
def matValsImpl (arena : Array OCont) (vs : List OVal) (fuel : Nat) : List Json :=
  matValsAcc arena vs fuel []

@[csimp] theorem matVals_eq_matValsImpl : @matVals = @matValsImpl := by
  funext arena vs fuel; simp [matValsImpl, matValsAcc_eq]

def matEntriesImpl (arena : Array OCont) (es : List (String × OVal)) (fuel : Nat) :
    List (String × Json) :=
  matEntriesAcc arena es fuel []

@[csimp] theorem matEntries_eq_matEntriesImpl : @matEntries = @matEntriesImpl := by
  funext arena es fuel; simp [matEntriesImpl, matEntriesAcc_eq]

def OCont.weight : OCont → Nat
  | .arr vs => 1 + vs.length
  | .obj es => 1 + es.size

/-- The JSON tree of the whole arena, rooted at container `root`. -/
def FState.materialize (st : FState) (root : Nat) : Json :=
  matCont st.arena root (2 * st.arena.foldl (fun n c => n + c.weight) 0 + 16)

/-! ## Clean-up of the framed result (Framing §5.1) -/

/-- Replace every `@preserve` wrapper by the first value it holds, and
drop the `@id` of each blank node that `clear` lists. A value object is
left alone; a list object has its items cleaned. -/
def cleanupPreserve (clear : Std.TreeSet String) (j : Json) (fuel : Nat) : Json :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
    match j with
    | .array xs => .array (xs.map (fun x => cleanupPreserve clear x fuel))
    | .object fs =>
      match objGet j "@preserve" with
      | some p => (match p with | .array (h :: _) => h | other => other)
      | none =>
        if hasField "@value" fs then j
        else if hasField "@list" fs then
          .object (fs.map (fun kv =>
            if kv.1 == "@list" then (kv.1, cleanupPreserve clear kv.2 fuel) else kv))
        else
          .object (fs.filterMap (fun kv =>
            match kv with
            | ("@id", .string s) =>
              if clear.contains s then none else some (kv.1, .string s)
            | _ => some (kv.1, cleanupPreserve clear kv.2 fuel)))
    | other => other

/-- Replace each `"@null"` by `null`; an array that holds nothing but
nulls becomes empty (Framing §5.1). -/
def cleanupNull (j : Json) (fuel : Nat) : Json :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
    match j with
    | .string "@null" => .null
    | .array xs =>
      let ys := xs.map (fun x => cleanupNull x fuel)
      if !ys.isEmpty && ys.all (fun y => match y with | .null => true | _ => false)
      then .array [] else .array ys
    | .object fs => .object (fs.map (fun kv => (kv.1, cleanupNull kv.2 fuel)))
    | other => other

/-- Lower-case every `@language` of a value object in an expanded
document (see the module header). -/
def lowerLanguages (j : Json) (fuel : Nat) : Json :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
    match j with
    | .array xs => .array (xs.map (fun x => lowerLanguages x fuel))
    | .object fs =>
      .object (fs.map (fun kv =>
        if kv.1 == "@language" then (kv.1, lowerJson kv.2)
        else (kv.1, lowerLanguages kv.2 fuel)))
    | other => other

/-- The blank node identifiers that occur exactly once. -/
def singletonBnodes (st : FState) : Std.TreeSet String :=
  st.bnodes.foldl (fun acc id n => if n == 1 then acc.insert id else acc) Std.TreeSet.empty

/-! ## The entry point -/

/-- Merge Node Maps (API §7.3, used by Framing §5.1): every node of every
graph, merged by identifier. Keywords other than `@type` are copied; the
values of all other entries are added unless already present. Graphs are
visited in code-point order of their names, and the nodes of each in
code-point order of their identifiers. -/
def mergeNodeMaps (graphs : Std.TreeMap String NmGraph) : NmGraph :=
  graphs.foldl (fun merged _ gr =>
    gr.foldl (fun acc id node =>
      let base : NmNode := (acc.get? id).getD (NmNode.fresh id)
      let merged' := node.toSortedFields.foldl (fun n kv =>
        if isKeyword kv.1 && kv.1 != "@type" then n.upsert kv.1 (.one kv.2)
        else (asArray kv.2).foldl (fun n' item => nodeAppendProp n' kv.1 item true) n) base
      acc.insert id merged') merged) Std.TreeMap.empty

/-- Does the frame document have a top-level entry that expands to
`@graph`? Then the default graph is framed, not the merged graph. -/
def frameNamesGraph (ac : ActiveContext) (frameRoot : Json) : Bool :=
  (objFields frameRoot).any (fun kv => kv.1 != "@context" && expandIri ac kv.1 true == some "@graph")

/-- The framing algorithm proper (Framing §5.1 steps 4 to 8): node map
generation on the expanded input, the Framing Algorithm of §4.1 over it,
and the removal of `@preserve` wrappers and singleton blank node
identifiers. The result is the framed array BEFORE compaction.
`merged` selects the merged graph as the graph to frame (the frame has no
top-level `@graph`). -/
def frameResults (opts : FrameOptions) (mode10 merged : Bool) (expandedRaw expandedFrame : Json)
    : Res Json :=
  let expanded := lowerLanguages expandedRaw (Json.size expandedRaw + 8)
  match generateNodeMap expanded with
  | .error e => .error e
  | .ok nst =>
    let graphs := if merged then nst.graphs.insert "@merged" (mergeNodeMaps nst.graphs)
                  else nst.graphs
    let root := if merged then "@merged" else "@default"
    let env : Env := { graphs := graphs, rootGraph := root, opts := opts, mode10 := mode10 }
    let fuel := 64 * (Json.size expanded + Json.size expandedFrame) + 4096
    let init : FState :=
      { arena := #[.arr []], stack := [], embeds := Std.TreeMap.empty,
        bnodes := Std.TreeMap.empty }
    match (frameRec env root false (env.subjectsOf root) expandedFrame 0 none fuel).run init with
    | .error e => .error e
    | .ok ((), st) =>
      let prune := opts.pruneBlankNodeIdentifiers.getD (!mode10)
      let clear := if prune then singletonBnodes st else Std.TreeSet.empty
      let tree := st.materialize 0
      .ok (cleanupPreserve clear tree (Json.size tree + 8))

/-- Frame `input` according to `frame` (Framing §5.1, `frame()`). -/
def frameDocumentWith (loader : Loader) (input frame : String) (opts : FrameOptions) : Res Json :=
  let mode10 := opts.processingMode == some "json-ld-1.0"
  match expandDocument loader input opts.base none opts.processingMode false with
  | .error e => .error e
  | .ok expandedRaw =>
    match expandDocument loader frame opts.base none opts.processingMode true with
    | .error e => .error e
    | .ok expandedFrame =>
      match parseJson frame with
      | .error _ => .error .notJsonLd
      | .ok frameRoot =>
        let ctxVal : Option Json :=
          match frameRoot with
          | .object cf => cmpField cf "@context"
          | _ => none
        let acSeed : ActiveContext :=
          { cur := { emptyContextCore with
                     base := opts.base, mode10 := mode10,
                     docUrl := opts.base, originalBase := opts.base },
            prev := [] }
        match (match ctxVal with
               | some cv => contextProcess loader acSeed cv false contextFuel remoteContextFuel []
               | none => .ok acSeed) with
        | .error e => .error e
        | .ok ac =>
          let merged := !frameNamesGraph ac frameRoot
          match frameResults opts mode10 merged expandedRaw expandedFrame with
          | .error e => .error e
          | .ok results =>
              let co : CmpOpts := { arrays := opts.compactArrays, rel := true }
              match compactElem loader ac none results co (16 * Json.size results + 128) with
              | .error e => .error e
              | .ok compacted0 =>
                let omitGraph := opts.omitGraph.getD (!mode10)
                -- `omitGraph` keeps a bare node when there is exactly one
                -- result; otherwise the results live under `@graph`.
                let shaped : Json :=
                  if omitGraph then
                    (match compacted0 with
                     | .array [x] => if opts.compactArrays then x else compacted0
                     | .array [] => if opts.compactArrays then .object [] else compacted0
                     | other => other)
                  else
                    (match compacted0 with
                     | .object _ => .array [compacted0]
                     | other => other)
                let gkey := aliasKw ac co "@graph"
                let body : List (String × Json) :=
                  match shaped with
                  | .array xs => [(gkey, .array xs)]
                  | .object fs => fs
                  | _ => []
                let cleaned := cleanupNull (.object body) (Json.size (.object body) + 8)
                let fields := objFields cleaned
                match ctxVal with
                | some cv =>
                  if cmpCtxIsEmpty cv then .ok (.object fields)
                  else .ok (.object (("@context", cv) :: fields))
                | none => .ok (.object fields)

/-- Frame `input` according to `frame`: the form the earlier port had.
`base` seeds expansion and relative-IRI compaction; `processingMode`
selects 1.0 when it is `"json-ld-1.0"`; `omitGraph` overrides the
default (false under `json-ld-1.0`, true otherwise). -/
def frameDocument (loader : Loader) (input frame : String) (base : Option String)
    (processingMode : Option String) (omitGraph : Option Bool := none) : Res Json :=
  frameDocumentWith loader input frame
    { base := base, processingMode := processingMode, omitGraph := omitGraph }

end L4Factoidal.JSONLD
