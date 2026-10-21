/-
L4Factoidal.RDF.TermJson — RDF terms and quads as JSON values, for a host
that builds its own term objects (RDF/JS) from the engine's answer.
https://github.com/danbri/factoidal/issues/894 items 1 and 4.

A host must make no lexical decision about an RDF term: it must not escape,
unescape, or read an IRI, a blank-node label or a literal out of a text
syntax. So the engine gives each term as a JSON object whose members are the
term's components (RDF 1.2 Concepts §3), in the shape of SPARQL 1.1 Query
Results JSON §3.3 with the RDF 1.2 additions (`"triple"`, `"its:dir"`):

  IRI            {"type":"uri","value":IRI}
  blank node     {"type":"bnode","value":LABEL}
  literal        {"type":"literal","value":LEX,"datatype":IRI
                  [,"xml:lang":TAG [,"its:dir":"ltr"|"rtl"]]}
  triple term    {"type":"triple","value":{"subject":S,"predicate":P,"object":O}}

The `datatype` member is always present, also for a language-tagged string
(`rdf:langString` / `rdf:dirLangString`), so the decoder reads the four
components of `Literal` back without a rule of its own. A quad is a JSON
array `[s, p, o]` (default graph) or `[s, p, o, g]` (named graph `g`).

Theorems:
  * `decodeTerm_encodeTerm`  : `decodeTerm (encodeTerm t) = some t`
  * `decodeQuad_encodeQuad`  : the same for quads
  * `mem_quadList_default`, `mem_quadList_named` : `Dataset.quadList` lists
    exactly the dataset's quads
  * `toCanonicalNQuads_eq_quadList` : the order of `quadList` is the line
    order of `Dataset.toCanonicalNQuads`
  * `quadPage_append` : consecutive pages concatenate to the list
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Graph
import L4Factoidal.JSON.Value
import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.RDF.TermJson

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.Syntax

/-! ## Encoding -/

def iriJson (i : WfIri) : Json := .object [("type", .string "uri"), ("value", .string i.val)]

def bnodeJson (b : BNodeId) : Json := .object [("type", .string "bnode"), ("value", .string b)]

def subjectJson : Subject → Json
  | .iri i => iriJson i
  | .bnode b => bnodeJson b

def dirString : TextDirection → String
  | .ltr => "ltr"
  | .rtl => "rtl"

def dirOf? (s : String) : Option TextDirection :=
  if s == "ltr" then some .ltr else if s == "rtl" then some .rtl else none

theorem dirOf?_dirString (d : TextDirection) : dirOf? (dirString d) = some d := by
  cases d <;> rfl

def literalJson (l : Literal) : Json :=
  .object ([("type", .string "literal"), ("value", .string l.lexicalForm),
            ("datatype", .string l.datatype.val)] ++
    (match l.langTag with
     | some tag => [("xml:lang", .string tag)]
     | none => []) ++
    (match l.direction with
     | some d => [("its:dir", .string (dirString d))]
     | none => []))

def encodeTerm : Term → Json
  | .iri i => iriJson i
  | .bnode b => bnodeJson b
  | .literal l => literalJson l.val
  | .tripleTerm s p o =>
      .object [("type", .string "triple"),
               ("value", .object [("subject", subjectJson s), ("predicate", iriJson p),
                                  ("object", encodeTerm o)])]

/-- A quad: the graph `none` is the default graph. -/
abbrev Quad := Option Subject × Triple

def encodeQuad : Quad → Json
  | (none, t) => .array [subjectJson t.s, iriJson t.p, encodeTerm t.o]
  | (some g, t) => .array [subjectJson t.s, iriJson t.p, encodeTerm t.o, subjectJson g]

/-! ## Decoding -/

def iriOf? (s : String) : Option WfIri := if h : isIri s then some ⟨s, h⟩ else none

theorem iriOf?_val (i : WfIri) : iriOf? i.val = some i := by
  simp [iriOf?, i.property]

def decodeIri (j : Json) : Option WfIri := do
  if j.getString? "type" == some "uri" then (j.getString? "value").bind iriOf? else none

def decodeSubject (j : Json) : Option Subject :=
  match j.getString? "type" with
  | some "uri" => ((j.getString? "value").bind iriOf?).map .iri
  | some "bnode" => (j.getString? "value").map .bnode
  | _ => none

/-- The literal of the members; `none` when the four do not form a
well-formed literal (`literalWf`). -/
def decodeLiteral (j : Json) : Option WfLiteral := do
  let lex ← j.getString? "value"
  let dt ← (j.getString? "datatype").bind iriOf?
  let lang := j.getString? "xml:lang"
  let dir ← match j.getString? "its:dir" with
    | none => some none
    | some s => (dirOf? s).map some
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := lang, direction := dir }
  if h : literalWf l then some ⟨l, h⟩ else none

def decodeTermFuel : Nat → Json → Option Term
  | 0, _ => none
  | n + 1, j =>
    match j.getString? "type" with
    | some "uri" => ((j.getString? "value").bind iriOf?).map .iri
    | some "bnode" => (j.getString? "value").map .bnode
    | some "literal" => (decodeLiteral j).map .literal
    | some "triple" => do
        let v ← j.field? "value"
        let s ← (v.field? "subject").bind decodeSubject
        let p ← (v.field? "predicate").bind decodeIri
        let o ← (v.field? "object").bind (decodeTermFuel n)
        pure (.tripleTerm s p o)
    | _ => none

-- Nesting depth of a JSON value: the fuel the decoder is given.
mutual
def jsonDepth : Json → Nat
  | .object kvs => fieldsDepth kvs + 1
  | .array xs => itemsDepth xs + 1
  | _ => 1
def fieldsDepth : List (String × Json) → Nat
  | [] => 0
  | (_, v) :: r => max (jsonDepth v) (fieldsDepth r)
def itemsDepth : List Json → Nat
  | [] => 0
  | v :: r => max (jsonDepth v) (itemsDepth r)
end

def decodeTerm (j : Json) : Option Term := decodeTermFuel (jsonDepth j) j

def decodeQuad (j : Json) : Option Quad :=
  match j with
  | .array [s, p, o] => do
      pure (none, { s := ← decodeSubject s, p := ← decodeIri p, o := ← decodeTerm o })
  | .array [s, p, o, g] => do
      pure (some (← decodeSubject g),
            { s := ← decodeSubject s, p := ← decodeIri p, o := ← decodeTerm o })
  | _ => none

/-! ## Round trip -/

/-- Triple-term nesting depth. -/
def Term.nest : Term → Nat
  | .tripleTerm _ _ o => Term.nest o + 1
  | _ => 0

theorem decodeIri_iriJson (i : WfIri) : decodeIri (iriJson i) = some i := by
  simp [decodeIri, iriJson, Json.getString?, Json.field?, Json.asString?, iriOf?_val]

theorem decodeSubject_subjectJson (s : Subject) : decodeSubject (subjectJson s) = some s := by
  cases s <;>
    simp [decodeSubject, subjectJson, iriJson, bnodeJson, Json.getString?, Json.field?,
      Json.asString?, iriOf?_val]

theorem decodeLiteral_literalJson (l : WfLiteral) : decodeLiteral (literalJson l.val) = some l := by
  obtain ⟨⟨lex, dt, lang, dir⟩, h⟩ := l
  cases lang <;> cases dir <;>
    simp [decodeLiteral, literalJson, Json.getString?, Json.field?, Json.asString?,
      iriOf?_val, dirOf?_dirString, h]

theorem jsonDepth_encodeTerm (t : Term) : Term.nest t < jsonDepth (encodeTerm t) := by
  induction t with
  | iri i => simp [Term.nest, encodeTerm, iriJson, jsonDepth]
  | bnode b => simp [Term.nest, encodeTerm, bnodeJson, jsonDepth]
  | literal l => simp [Term.nest, encodeTerm, literalJson, jsonDepth]
  | tripleTerm s p o ih =>
      simp only [Term.nest, encodeTerm, jsonDepth, fieldsDepth]
      omega

theorem decodeTermFuel_encodeTerm (t : Term) :
    ∀ n, Term.nest t < n → decodeTermFuel n (encodeTerm t) = some t := by
  induction t with
  | iri i =>
      intro n hn
      cases n with
      | zero => omega
      | succ n => simp [decodeTermFuel, encodeTerm, iriJson, Json.getString?, Json.field?,
                    Json.asString?, iriOf?_val]
  | bnode b =>
      intro n hn
      cases n with
      | zero => omega
      | succ n => simp [decodeTermFuel, encodeTerm, bnodeJson, Json.getString?, Json.field?,
                    Json.asString?]
  | literal l =>
      intro n hn
      cases n with
      | zero => omega
      | succ n =>
          have hl := decodeLiteral_literalJson l
          have ht : (literalJson l.val).getString? "type" = some "literal" := by
            simp [literalJson, Json.getString?, Json.field?, Json.asString?]
          simp only [decodeTermFuel, encodeTerm, ht, hl, Option.map_some]
  | tripleTerm s p o ih =>
      intro n hn
      cases n with
      | zero => omega
      | succ n =>
          have ho := ih n (by simp [Term.nest] at hn; omega)
          simp [decodeTermFuel, encodeTerm, Json.getString?, Json.field?, Json.asString?,
            decodeSubject_subjectJson, decodeIri_iriJson, ho]

/-- The encoding round-trips: `decode (encode t) = t`. -/
theorem decodeTerm_encodeTerm (t : Term) : decodeTerm (encodeTerm t) = some t :=
  decodeTermFuel_encodeTerm t _ (jsonDepth_encodeTerm t)

theorem decodeQuad_encodeQuad (q : Quad) : decodeQuad (encodeQuad q) = some q := by
  obtain ⟨g, ⟨s, p, o⟩⟩ := q
  cases g <;>
    simp [decodeQuad, encodeQuad, decodeSubject_subjectJson, decodeIri_iriJson,
      decodeTerm_encodeTerm]

/-! ## The quads of a dataset, in the N-Quads line order -/

def Dataset.quadList (ds : Dataset) : List Quad :=
  ds.default.map (fun t => (none, t)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => (some ng.name, t)))

theorem mem_quadList_default (ds : Dataset) (t : Triple) :
    (none, t) ∈ Dataset.quadList ds ↔ t ∈ ds.default := by
  simp [Dataset.quadList]

theorem mem_quadList_named (ds : Dataset) (g : Subject) (t : Triple) :
    (some g, t) ∈ Dataset.quadList ds ↔ ∃ ng ∈ ds.named, ng.name = g ∧ t ∈ ng.graph := by
  simp only [Dataset.quadList, List.mem_append, List.mem_map, List.mem_flatMap]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨ng, hng, t', ht', h⟩)
    · cases h
    · cases h; exact ⟨ng, hng, rfl, ht'⟩
  · rintro ⟨ng, hng, rfl, ht⟩
    exact Or.inr ⟨ng, hng, t, ht, rfl⟩

/-- The canonical N-Quads line of one quad. -/
def quadLine : Quad → String
  | (none, t) => Triple.toCanonicalNTriples t
  | (some g, t) => L4Factoidal.Syntax.canonNamedLine g t

/-- `Dataset.toCanonicalNQuads` writes the quads of `quadList`, one line
each, in the order of `quadList`. -/
theorem toCanonicalNQuads_eq_quadList (ds : Dataset) :
    Dataset.toCanonicalNQuads ds = String.join ((Dataset.quadList ds).map quadLine) := by
  simp only [Dataset.toCanonicalNQuads, Graph.toCanonicalNTriples, Dataset.quadList,
    List.map_append, String.join_append]
  congr 1
  · simp [List.map_map, quadLine, Function.comp_def]
  · induction ds.named with
    | nil => rfl
    | cons ng r ih =>
        simp [List.flatMap_cons, List.map_append, String.join_append, ih, quadLine,
          Function.comp_def]

/-- One page of `quadList`: `limit` quads from `offset`. -/
def quadPage (ds : Dataset) (offset limit : Nat) : List Quad :=
  ((Dataset.quadList ds).drop offset).take limit

/-- A page followed by the rest is the list from the page's offset; so the
pages 0, k, 2k, … concatenate to `quadList`. -/
theorem quadPage_append (ds : Dataset) (offset limit : Nat) :
    quadPage ds offset limit ++ (Dataset.quadList ds).drop (offset + limit) =
      (Dataset.quadList ds).drop offset := by
  have h := List.take_append_drop limit ((Dataset.quadList ds).drop offset)
  simpa [quadPage, List.drop_drop, Nat.add_comm] using h

/-! ## Build-time checks -/

private def exIri : WfIri := ⟨"http://e/a", rfl⟩

#guard (decodeTerm (encodeTerm (.iri exIri))) == some (.iri exIri)
#guard (decodeTerm (.object [("type", .string "uri"), ("value", .string "no-colon")])).isNone
#guard (decodeTerm (.object [("type", .string "literal"), ("value", .string "x"),
          ("datatype", .string "http://www.w3.org/2001/XMLSchema#string"),
          ("xml:lang", .string "en")])).isNone
#guard (decodeTerm (.object [("type", .string "literal"), ("value", .string "x"),
          ("datatype", .string "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"),
          ("xml:lang", .string "en")])).isSome
#guard (decodeTerm (.object [("type", .string "triple"), ("value", .object [
          ("subject", .object [("type", .string "literal"), ("value", .string "x"),
             ("datatype", .string "http://e/d")]),
          ("predicate", iriJson exIri), ("object", iriJson exIri)])])).isNone
#guard (decodeQuad (.array [iriJson exIri, bnodeJson "b", iriJson exIri])).isNone
#guard (decodeQuad (.array [bnodeJson "b", iriJson exIri, bnodeJson "c", bnodeJson "g"])).isSome

end L4Factoidal.RDF.TermJson
