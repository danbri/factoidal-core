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

A language-tagged string with no direction has no `datatype` member: its
datatype is `rdf:langString` (RDF 1.2 Concepts §3.3, `literalWf`); every other
literal has one. A quad is a JSON
array `[s, p, o]` (default graph) or `[s, p, o, g]` (named graph `g`).

Theorems:
  * `decodeTerm_encodeTerm`  : `decodeTerm (encodeTerm t) = some t`
  * `decodeQuad_encodeQuad`  : the same for quads
  * `mem_quadList_default`, `mem_quadList_named` : `Dataset.quadList` lists
    exactly the dataset's quads
  * `toCanonicalNQuads_eq_quadList` : the order of `quadList` is the line
    order of `Dataset.toCanonicalNQuads`
  * `quadPage_append` : consecutive pages concatenate to the list
  * `decodeCheckedTerm_encodeTerm` : a term that satisfies `termChecked`
    round-trips through the checked decoder unchanged

A term may also come as text, `{"type":"nt","value":TEXT}`, where TEXT is
one RDF 1.2 N-Triples term (`readTermString`): `<IRI>`, `_:label`, a
literal, or `<<( s p o )>>`. Every decoder below reads that form through
the same reader, so a host never decides whether a string is an IRI or a
blank node (https://github.com/danbri/factoidal/issues/894).
-/
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Graph
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Serialize
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.IriSyntax
import L4Factoidal.RDF.LangTag
import L4Factoidal.JSON.Parser
import Std.Data.HashMap
import L4Factoidal.Storage.TermFold

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
  .object ([("type", .string "literal"), ("value", .string l.lexicalForm)] ++
    (match l.langTag, l.direction with
     | some tag, none => [("xml:lang", .string tag)]
     | some tag, some _ => [("datatype", .string l.datatype.val), ("xml:lang", .string tag)]
     | none, _ => [("datatype", .string l.datatype.val)]) ++
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

/-! ## What RDF requires of a term a host supplies

RDF 1.1 Concepts §3.2 (an IRI in an RDF graph is absolute), §3.3 (a
datatype is an IRI; a language tag is well-formed under BCP 47). An
ill-typed literal (a lexical form outside the datatype's lexical space)
is still a literal (§3.3), so this check reads no lexical form. -/

def literalChecked (l : Literal) : Bool :=
  isAbsoluteIri l.datatype.val &&
    (match l.langTag with
     | some t => isWellFormedLangTag t
     | none => true)

def subjectChecked : Subject → Bool
  | .iri i => isAbsoluteIri i.val
  | .bnode b => !b.isEmpty

def termChecked : Term → Bool
  | .iri i => isAbsoluteIri i.val
  | .bnode b => !b.isEmpty
  | .literal l => literalChecked l.val
  | .tripleTerm s p o => subjectChecked s && isAbsoluteIri p.val && termChecked o

/-- One RDF term written in RDF 1.2 N-Triples term syntax (RDF 1.2
N-Triples §2.4–2.6: IRIREF, BLANK_NODE_LABEL, literal, tripleTerm), with
nothing after it but spaces and tabs, that also satisfies `termChecked`.
This is the one reader of a term given as a string: `_:x` is a blank node
and `<…>` an IRI everywhere. -/
def readTermString (s : String) : Option Term :=
  let cs := s.toList
  match readObject12 (cs.length + 1) 0 cs with
  | .ok (t, _, rest) =>
      if rest.all (fun c => c == ' ' || c == '\t') && termChecked t then some t else none
  | .error _ => none

theorem termChecked_of_readTermString {s : String} {t : Term}
    (h : readTermString s = some t) : termChecked t = true := by
  unfold readTermString at h
  dsimp only at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      exact hc.2
    · exact absurd h (by simp)
  · exact absurd h (by simp)

def readSubjectString (s : String) : Option Subject :=
  match readTermString s with
  | some (.iri i) => some (.iri i)
  | some (.bnode b) => some (.bnode b)
  | _ => none

def readIriString (s : String) : Option WfIri :=
  match readTermString s with
  | some (.iri i) => some i
  | _ => none

def iriOf? (s : String) : Option WfIri := if h : isIri s then some ⟨s, h⟩ else none

theorem iriOf?_val (i : WfIri) : iriOf? i.val = some i := by
  simp [iriOf?, i.property]

def decodeIri (j : Json) : Option WfIri := do
  if j.getString? "type" == some "uri" then (j.getString? "value").bind iriOf?
  else if j.getString? "type" == some "nt" then (j.getString? "value").bind readIriString
  else none

def decodeSubject (j : Json) : Option Subject :=
  match j.getString? "type" with
  | some "uri" => ((j.getString? "value").bind iriOf?).map .iri
  | some "bnode" => (j.getString? "value").map .bnode
  | some "nt" => (j.getString? "value").bind readSubjectString
  | _ => none

/-- The literal of the members; `none` when the four do not form a
well-formed literal (`literalWf`). -/
def decodeLiteral (j : Json) : Option WfLiteral := do
  let lex ← j.getString? "value"
  let lang := j.getString? "xml:lang"
  let dir ← match j.getString? "its:dir" with
    | none => some none
    | some s => (dirOf? s).map some
  -- a language-tagged string with no direction has no `datatype` member: its
  -- datatype is rdf:langString (RDF 1.2 Concepts 3.3)
  let dt ← match lang, dir with
    | some _, none => some rdfLangString
    -- SPARQL 1.1 Results JSON 3.3: a literal with no datatype member is a simple
    -- literal, xsd:string in RDF 1.1
    | none, _ => match j.getString? "datatype" with
      | none => some xsdString
      | some d => iriOf? d
    -- a directional language-tagged string with no `datatype` member is
    -- rdf:dirLangString (RDF 1.2 Concepts 3.3), as the no-direction case is
    -- rdf:langString
    | _, _ => match j.getString? "datatype" with
      | none => some rdfDirLangString
      | some d => iriOf? d
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := lang, direction := dir }
  Literal.toWf? l

def decodeTermFuel : Nat → Json → Option Term
  | 0, _ => none
  | n + 1, j =>
    match j.getString? "type" with
    | some "uri" => ((j.getString? "value").bind iriOf?).map .iri
    | some "bnode" => (j.getString? "value").map .bnode
    | some "literal" => (decodeLiteral j).map .literal
    | some "typed-literal" => (decodeLiteral j).map .literal
    | some "triple" => do
        let v ← j.field? "value"
        let s ← (v.field? "subject").bind decodeSubject
        let p ← (v.field? "predicate").bind decodeIri
        let o ← (v.field? "object").bind (decodeTermFuel n)
        pure (.tripleTerm s p o)
    | some "nt" => (j.getString? "value").bind readTermString
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
  have hw := Literal.toWf?_of_wf h
  cases lang <;> cases dir
  · simp [decodeLiteral, literalJson, Json.getString?, Json.field?, Json.asString?,
      iriOf?_val, dirOf?_dirString, hw]
  · simp [literalWf] at h
  · have hd : dt = rdfLangString := Subtype.ext (by simp [literalWf] at h; exact h.1)
    subst hd
    simp [decodeLiteral, literalJson, Json.getString?, Json.field?, Json.asString?,
      dirOf?_dirString, hw]
  · simp [decodeLiteral, literalJson, Json.getString?, Json.field?, Json.asString?,
      dirOf?_dirString, iriOf?_val, hw]

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

/-! ## A term an application supplies

An application may answer with an exact term (an extension function's
answer, https://github.com/danbri/factoidal/issues/894): the lexical form
and the datatype IRI are kept as given. `decodeCheckedTerm` adds to
`decodeTerm` only what RDF requires (`termChecked`), and refuses a
`datatype` member that names a datatype other than the one the term has
(a language-tagged string with no direction is `rdf:langString`). -/

/-- Each `datatype` member names the datatype of its literal. -/
def datatypeAgrees : Term → Json → Bool
  | .literal l, j =>
      match j.getString? "datatype" with
      | some d => d == l.val.datatype.val
      | none => true
  | .tripleTerm _ _ o, j =>
      match (j.field? "value").bind (·.field? "object") with
      | some oj => datatypeAgrees o oj
      | none => true
  | _, _ => true

def decodeCheckedTerm (j : Json) : Option Term :=
  match decodeTerm j with
  | some t => if termChecked t && datatypeAgrees t j then some t else none
  | none => none

theorem datatypeAgrees_encodeTerm (t : Term) : datatypeAgrees t (encodeTerm t) = true := by
  induction t with
  | iri i => simp [datatypeAgrees]
  | bnode b => simp [datatypeAgrees]
  | literal l =>
      obtain ⟨⟨lex, dt, lang, dir⟩, h⟩ := l
      cases lang <;> cases dir <;>
        simp [datatypeAgrees, encodeTerm, literalJson, Json.getString?, Json.field?,
          Json.asString?]
  | tripleTerm s p o ih =>
      simp [datatypeAgrees, encodeTerm, Json.field?, ih]

/-- An application-supplied term that RDF admits comes back unchanged:
the same lexical form, datatype IRI, language tag and direction. -/
theorem decodeCheckedTerm_encodeTerm (t : Term) (h : termChecked t = true) :
    decodeCheckedTerm (encodeTerm t) = some t := by
  simp [decodeCheckedTerm, decodeTerm_encodeTerm, h, datatypeAgrees_encodeTerm]

/-- The checked decoder never answers a term RDF does not admit. -/
theorem termChecked_of_decodeCheckedTerm {j : Json} {t : Term}
    (h : decodeCheckedTerm j = some t) : termChecked t = true := by
  unfold decodeCheckedTerm at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      exact hc.1
    · exact absurd h (by simp)
  · exact absurd h (by simp)

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


/-! ## The compact form: a term table and quads of indices

For a large dataset the host builds each distinct term once: the answer is
the distinct terms (in first-occurrence order) and each quad as the indices
of its terms in that table. The table holds one entry per RDF term
(https://github.com/danbri/factoidal/issues/977): each quad is folded first
(`Storage.TermFold.foldQuad`: language tags in lower case, RDF 1.1 Concepts
section 3.3), so `"x"@en` and `"x"@EN` are one entry and the table writes
`"x"@en`. `decodeCompact_compactSpec` proves that the indices read back as
exactly the folded quads; `decodeCompact_table` is the same for any quad
list. -/

def subjectToTerm : Subject → Term
  | .iri i => .iri i
  | .bnode b => .bnode b

def termToSubject? : Term → Option Subject
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | _ => none

def termToIri? : Term → Option WfIri
  | .iri i => some i
  | _ => none

theorem toSubject?_toTerm (s : Subject) : termToSubject? (subjectToTerm s) = some s := by
  cases s <;> rfl

/-- The terms of a quad, in the order subject, predicate, object, graph. -/
def quadTerms : Quad → List Term
  | (none, t) => [subjectToTerm t.s, .iri t.p, t.o]
  | (some g, t) => [subjectToTerm t.s, .iri t.p, t.o, subjectToTerm g]

/-- Add a term to the table unless it is there. -/
def addTerm (acc : List Term) (t : Term) : List Term := if acc.contains t then acc else acc ++ [t]

/-- The table: the distinct terms of the quads, in first-occurrence order. -/
def termTable (qs : List Quad) : List Term :=
  (qs.flatMap quadTerms).foldl addTerm []

/-- The table and the index lists of a quad list, with no fold. -/
def compactOf (qs : List Quad) : List Term × List (List Nat) :=
  let tbl := termTable qs
  (tbl, qs.map fun q => (quadTerms q).map tbl.idxOf)

/-- The compact form (specification): the table and the index list of each
    folded quad. -/
def compactSpec (qs : List Quad) : List Term × List (List Nat) :=
  compactOf (qs.map Storage.TermFold.foldQuad)

/-- Read the compact form back. -/
def decodeCompact (tbl : List Term) (ixs : List (List Nat)) : Option (List Quad) :=
  ixs.mapM fun ix => do
    let ts ← ix.mapM (tbl[·]?)
    match ts with
    | [s, p, o] => pure (none, { s := ← termToSubject? s, p := ← termToIri? p, o := o })
    | [s, p, o, g] => pure (some (← termToSubject? g), { s := ← termToSubject? s, p := ← termToIri? p, o := o })
    | _ => none

theorem mem_foldl_addTerm (l acc : List Term) (t : Term) :
    t ∈ acc ∨ t ∈ l → t ∈ l.foldl addTerm acc := by
  induction l generalizing acc with
  | nil => intro h; simpa using h
  | cons x r ih =>
      intro h
      apply ih
      unfold addTerm
      rcases h with h | h
      · left; split <;> simp [h]
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · left; split
          · rename_i hc; simpa using hc
          · simp
        · right; exact h

theorem mem_termTable {qs : List Quad} {q : Quad} {t : Term} (hq : q ∈ qs) (ht : t ∈ quadTerms q) :
    t ∈ termTable qs :=
  mem_foldl_addTerm _ _ _ (Or.inr (List.mem_flatMap.mpr ⟨q, hq, ht⟩))

theorem getElem?_idxOf_of_mem {l : List Term} {t : Term} (h : t ∈ l) : l[l.idxOf t]? = some t := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h)]
  simp [List.getElem_idxOf]

theorem mapM_lookup {tbl ts : List Term} (h : ∀ t ∈ ts, t ∈ tbl) :
    (ts.map tbl.idxOf).mapM (tbl[·]?) = some ts := by
  induction ts with
  | nil => rfl
  | cons x r ih =>
      simp only [List.map_cons, List.mapM_cons]
      rw [getElem?_idxOf_of_mem (h x List.mem_cons_self), ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
      rfl

theorem mapM_some_self {α : Type} (f : α → Option α) (l : List α) (h : ∀ x ∈ l, f x = some x) :
    l.mapM f = some l := by
  induction l with
  | nil => rfl
  | cons x r ih =>
      simp only [List.mapM_cons, h x List.mem_cons_self,
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
      rfl

/-- The table and index lists of a quad list read back as the quads. -/
theorem decodeCompact_table (qs : List Quad) :
    decodeCompact (compactOf qs).1 (compactOf qs).2 = some qs := by
  unfold decodeCompact compactOf
  simp only
  rw [List.mapM_map]
  have key : ∀ q ∈ qs, (do
      let ts ← ((quadTerms q).map (termTable qs).idxOf).mapM ((termTable qs)[·]?)
      match ts with
      | [s, p, o] => pure (none, { s := ← termToSubject? s, p := ← termToIri? p, o := o })
      | [s, p, o, g] => pure (some (← termToSubject? g), { s := ← termToSubject? s, p := ← termToIri? p, o := o })
      | _ => none : Option Quad) = some q := by
    intro q hq
    rw [mapM_lookup (fun t ht => mem_termTable hq ht)]
    obtain ⟨g, ⟨s, p, o⟩⟩ := q
    cases g <;> simp [quadTerms, termToIri?, toSubject?_toTerm, bind, pure]
  exact mapM_some_self _ _ key


/-- **The compact form reads back as exactly the folded quads, in order.** -/
theorem decodeCompact_compactSpec (qs : List Quad) :
    decodeCompact (compactSpec qs).1 (compactSpec qs).2 = some (qs.map Storage.TermFold.foldQuad) :=
  decodeCompact_table _

/-! ### The executable compact form, certified

`compactFast` builds the table with a hash map. `compactCertified` keeps its
answer only when the indices read back as exactly the quads
(`decodeCompactArr`, one linear pass); so whatever it answers decodes to the
quads (`compactCertified_sound`), with no theorem about the hash map needed. -/

/-- The builder's state: an index for each IRI and each blank-node label seen,
an index for each folded literal and triple term seen, and the table. Until
2026-10-23 a literal or a triple term got a new table entry each time it
occurred (hashing them cost more than it saved), so a literal that occurred
twice had two entries (https://github.com/danbri/factoidal/issues/977). -/
structure CompactState where
  iris : Std.HashMap String Nat := {}
  bnodes : Std.HashMap String Nat := {}
  others : Std.HashMap Term Nat := {}
  tbl : Array Term := #[]

/-- The index of a term; the caller passes a folded term (`compactLoop`
folds each quad). -/
def CompactState.index (st : CompactState) (t : Term) : Nat × CompactState :=
  match t with
  | .iri i =>
      match st.iris[i.val]? with
      | some k => (k, st)
      | none => (st.tbl.size, { st with iris := st.iris.insert i.val st.tbl.size, tbl := st.tbl.push t })
  | .bnode b =>
      match st.bnodes[b]? with
      | some k => (k, st)
      | none => (st.tbl.size, { st with bnodes := st.bnodes.insert b st.tbl.size, tbl := st.tbl.push t })
  | _ =>
      match st.others[t]? with
      | some k => (k, st)
      | none => (st.tbl.size, { st with others := st.others.insert t st.tbl.size, tbl := st.tbl.push t })

/-- The indices of the terms `ts`, appended to `ix` (a loop). -/
def indexTerms (st : CompactState) : List Term → Array Nat → Array Nat × CompactState
  | [], ix => (ix, st)
  | t :: ts, ix =>
      let r := st.index t
      indexTerms r.2 ts (ix.push r.1)

/-- The index lists of the folded quads, appended to `acc` (a loop). -/
def compactLoop (st : CompactState) : List Quad → Array (List Nat) → CompactState × Array (List Nat)
  | [], acc => (st, acc)
  | q :: qs, acc =>
      let r := indexTerms st (quadTerms (Storage.TermFold.foldQuad q)) #[]
      compactLoop r.2 qs (acc.push r.1.toList)

def compactFast (qs : List Quad) : Array Term × List (List Nat) :=
  let r := compactLoop {} qs #[]
  (r.1.tbl, r.2.toList)

/-- One quad of index list `ix`. -/
def decodeIx (tbl : Array Term) (ix : List Nat) : Option Quad := do
  let ts ← ix.mapM (tbl[·]?)
  match ts with
  | [s, p, o] => pure (none, { s := ← termToSubject? s, p := ← termToIri? p, o := o })
  | [s, p, o, g] => pure (some (← termToSubject? g), { s := ← termToSubject? s, p := ← termToIri? p, o := o })
  | _ => none

/-- A loop with an accumulator: one frame however many quads there are. -/
def decodeCompactLoop (tbl : Array Term) : List (List Nat) → Array Quad → Option (List Quad)
  | [], acc => some acc.toList
  | ix :: r, acc =>
      match decodeIx tbl ix with
      | none => none
      | some q => decodeCompactLoop tbl r (acc.push q)

def decodeCompactArr (tbl : Array Term) (ixs : List (List Nat)) : Option (List Quad) :=
  decodeCompactLoop tbl ixs #[]

theorem decodeCompactLoop_eq (tbl : Array Term) (ixs : List (List Nat)) (acc : Array Quad) :
    decodeCompactLoop tbl ixs acc = (ixs.mapM (decodeIx tbl)).map (acc.toList ++ ·) := by
  induction ixs generalizing acc with
  | nil => simp [decodeCompactLoop]
  | cons ix r ih =>
      simp only [decodeCompactLoop, List.mapM_cons]
      cases h : decodeIx tbl ix with
      | none => simp [bind]
      | some q =>
          simp only [ih]
          cases r.mapM (decodeIx tbl) <;> simp [bind, pure]

/-- List equality as a loop (the derived `DecidableEq` of `List` takes one
frame per element). -/
def quadsEqLoop : List Quad → List Quad → Bool
  | [], [] => true
  | x :: xs, y :: ys => if x = y then quadsEqLoop xs ys else false
  | _, _ => false

theorem quadsEqLoop_iff (a b : List Quad) : quadsEqLoop a b = true ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [quadsEqLoop]
  | cons x xs ih =>
      cases b with
      | nil => simp [quadsEqLoop]
      | cons y ys =>
          by_cases h : x = y
          · subst h; simp [quadsEqLoop, ih]
          · simp [quadsEqLoop, h]

/-- Check, quad by quad, that each index list reads back as its quad. -/
def checkCompact (tbl : Array Term) : List Quad → List (List Nat) → Bool
  | [], [] => true
  | q :: qs, ix :: ixs => if decodeIx tbl ix = some q then checkCompact tbl qs ixs else false
  | _, _ => false

theorem checkCompact_sound (tbl : Array Term) :
    ∀ (qs : List Quad) (ixs : List (List Nat)), checkCompact tbl qs ixs = true →
      ixs.mapM (decodeIx tbl) = some qs := by
  intro qs
  induction qs with
  | nil => intro ixs h; cases ixs <;> simp_all [checkCompact]
  | cons q qs ih =>
      intro ixs h
      cases ixs with
      | nil => simp [checkCompact] at h
      | cons ix ixs =>
          simp only [checkCompact] at h
          split at h
          · rename_i hq
            simp only [List.mapM_cons, hq, ih ixs h]
            rfl
          · exact absurd h (by simp)

def compactCertified (qs : List Quad) : Option (Array Term × List (List Nat)) :=
  let c := compactFast qs
  if checkCompact c.1 (qs.map Storage.TermFold.foldQuad) c.2 then some c else none

/-- **What `compactCertified` answers reads back as exactly the folded quads.** -/
theorem compactCertified_sound {qs : List Quad} {c : Array Term × List (List Nat)}
    (h : compactCertified qs = some c) :
    decodeCompactArr c.1 c.2 = some (qs.map Storage.TermFold.foldQuad) := by
  unfold compactCertified at h
  simp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h; subst h
    rw [decodeCompactArr, decodeCompactLoop_eq, checkCompact_sound _ _ _ hc]
    simp
  · exact absurd h (by simp)

/-- The array reader is the list reader of the specification. -/
theorem decodeCompactArr_eq (tbl : Array Term) (ixs : List (List Nat)) :
    decodeCompactArr tbl ixs = decodeCompact tbl.toList ixs := by
  rw [decodeCompactArr, decodeCompactLoop_eq]
  simp only [Array.toList_empty, List.nil_append, Option.map_id']
  simp [decodeCompact, Array.getElem?_toList]
  rfl

#guard (let qs : List Quad := [(none, ⟨.bnode "a", ⟨"http://e/p", rfl⟩, .bnode "b"⟩),
                              (some (.iri ⟨"http://e/g", rfl⟩), ⟨.bnode "a", ⟨"http://e/p", rfl⟩, .bnode "c"⟩)]
        (compactCertified qs).isSome &&
        ((compactCertified qs).map (·.1.size)) == some 5)


/-! ### The JSON text of a term, written directly

`termText` appends the JSON text of `encodeTerm t` to an accumulator with no
`Json` tree; `termText_eq` proves it is `(encodeTerm t).toString`. -/

open L4Factoidal.JSON (toStringCompact toStringFields escapeString) in
/-- `"key":"value"` with both strings escaped. -/
def strMember (k v : String) : String :=
  "\"" ++ escapeString k ++ "\":" ++ "\"" ++ escapeString v ++ "\""

theorem colon_quote (x : String) : "\":" ++ ("\"" ++ x) = "\":\"" ++ x := by
  rw [← String.append_assoc]; rfl

theorem quote_comma (x : String) : "\"" ++ ("," ++ x) = "\"," ++ x := by
  rw [← String.append_assoc]; rfl

def iriText (i : WfIri) : String := "{" ++ strMember "type" "uri" ++ "," ++ strMember "value" i.val ++ "}"

def bnodeText (b : BNodeId) : String := "{" ++ strMember "type" "bnode" ++ "," ++ strMember "value" b ++ "}"

def subjectText : Subject → String
  | .iri i => iriText i
  | .bnode b => bnodeText b

def literalText (l : Literal) : String :=
  "{" ++ strMember "type" "literal" ++ "," ++ strMember "value" l.lexicalForm ++
    (match l.langTag, l.direction with
     | some tag, none => "," ++ strMember "xml:lang" tag
     | some tag, some _ => "," ++ strMember "datatype" l.datatype.val ++ "," ++ strMember "xml:lang" tag
     | none, _ => "," ++ strMember "datatype" l.datatype.val) ++
    (match l.direction with | some d => "," ++ strMember "its:dir" (dirString d) | none => "") ++ "}"

/-- The JSON text of a term. A triple term (rare in data) is written through
the `Json` tree; the other three kinds directly. -/
def termText : Term → String
  | .iri i => iriText i
  | .bnode b => bnodeText b
  | .literal l => literalText l.val
  | .tripleTerm s p o => (encodeTerm (.tripleTerm s p o)).toString

open L4Factoidal.JSON in
theorem iriText_eq (i : WfIri) : iriText i = (iriJson i).toString := by
  simp [iriText, iriJson, strMember, Json.toString, toStringCompact_object, toStringFields,
    toStringCompact, String.append_assoc, colon_quote, quote_comma]

open L4Factoidal.JSON in
theorem bnodeText_eq (b : BNodeId) : bnodeText b = (bnodeJson b).toString := by
  simp [bnodeText, bnodeJson, strMember, Json.toString, toStringCompact_object, toStringFields,
    toStringCompact, String.append_assoc, colon_quote, quote_comma]

theorem subjectText_eq (s : Subject) : subjectText s = (subjectJson s).toString := by
  cases s
  · exact iriText_eq _
  · exact bnodeText_eq _

open L4Factoidal.JSON in
theorem literalText_eq (l : Literal) : literalText l = (literalJson l).toString := by
  obtain ⟨lex, dt, lang, dir⟩ := l
  cases lang <;> cases dir <;>
    simp [literalText, literalJson, strMember, Json.toString, toStringCompact_object,
      toStringFields, toStringCompact, String.append_assoc, colon_quote, quote_comma]

open L4Factoidal.JSON in
/-- **The direct writer writes the JSON text of `encodeTerm`.** -/
theorem termText_eq (t : Term) : termText t = (encodeTerm t).toString := by
  cases t with
  | iri i => exact iriText_eq i
  | bnode b => exact bnodeText_eq b
  | literal l => exact literalText_eq l.val
  | tripleTerm s p o => rfl

/-! ## Build-time checks -/

private def exIri : WfIri := ⟨"http://e/a", rfl⟩

#guard (decodeTerm (encodeTerm (.iri exIri))) == some (.iri exIri)
#guard (decodeTerm (.object [("type", .string "uri"), ("value", .string "no-colon")])).isNone
-- with a language tag the datatype is rdf:langString, whatever member was sent
#guard match decodeTerm (.object [("type", .string "literal"), ("value", .string "x"),
          ("datatype", .string "http://www.w3.org/2001/XMLSchema#string"),
          ("xml:lang", .string "en")]) with
  | some (.literal l) => l.val.datatype == rdfLangString
  | _ => false
#guard (decodeTerm (.object [("type", .string "literal"), ("value", .string "x"),
          ("its:dir", .string "ltr")])).isNone
#guard (decodeTerm (.object [("type", .string "literal"), ("value", .string "x"),
          ("datatype", .string "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString"),
          ("xml:lang", .string "en")])).isSome
#guard (decodeTerm (.object [("type", .string "triple"), ("value", .object [
          ("subject", .object [("type", .string "literal"), ("value", .string "x"),
             ("datatype", .string "http://e/d")]),
          ("predicate", iriJson exIri), ("object", iriJson exIri)])])).isNone
#guard (decodeQuad (.array [iriJson exIri, bnodeJson "b", iriJson exIri])).isNone
#guard (decodeQuad (.array [bnodeJson "b", iriJson exIri, bnodeJson "c", bnodeJson "g"])).isSome

#guard (decodeTerm (.object [("type", .string "literal"), ("value", .string "x")])).isSome
#guard (decodeTerm (.object [("type", .string "typed-literal"), ("value", .string "1"),
          ("datatype", .string "http://www.w3.org/2001/XMLSchema#integer")])).isSome
#print axioms decodeTerm_encodeTerm
#print axioms decodeQuad_encodeQuad
#print axioms mem_quadList_default
#print axioms mem_quadList_named
#print axioms toCanonicalNQuads_eq_quadList
#print axioms quadPage_append
#print axioms decodeCompact_compactSpec
#print axioms compactCertified_sound
#print axioms decodeCompactArr_eq
#print axioms termText_eq

/-! ## Build-time checks: the term-string reader and the checked decoder -/

-- one reader: `_:x` is a blank node, `<…>` an IRI
#guard readTermString "_:x" == some (.bnode "x")
#guard (readTermString "<http://e/x>").isSome && readTermString "<http://e/x>" != some (.bnode "x")
#guard match readTermString "<http://e/x>" with | some (.iri i) => i.val == "http://e/x" | _ => false
#guard match readTermString "\"007\"^^<http://www.w3.org/2001/XMLSchema#integer>" with
  | some (.literal l) => l.val.lexicalForm == "007" &&
      l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#integer"
  | _ => false
#guard match readTermString "\"a\"@en--rtl" with
  | some (.literal l) => l.val.langTag == some "en" && l.val.direction == some .rtl
  | _ => false
#guard match readTermString "<<( _:s <http://e/p> \"o\" )>>" with
  | some (.tripleTerm (.bnode "s") _ _) => true
  | _ => false
-- negative: a bare IRI, an IRI that is not absolute, a bad language tag,
-- trailing text, an empty label, an empty string
#guard readTermString "http://e/x" == none
#guard readTermString "<x>" == none
#guard readTermString "\"a\"^^<int>" == none
#guard readTermString "\"a\"@en-" == none
#guard readTermString "\"a\"@123456789" == none
#guard readTermString "<http://e/x> ." == none
#guard readTermString "_:" == none
#guard readTermString "" == none
#guard readSubjectString "\"a\"" == none
#guard readIriString "_:x" == none

private def jsonOf (s : String) : Json := (parseJson? s).getD .null

-- the `nt` form goes through the same reader in every decoder
#guard decodeSubject (jsonOf "{\"type\":\"nt\",\"value\":\"_:g\"}") == some (.bnode "g")
#guard (decodeSubject (jsonOf "{\"type\":\"nt\",\"value\":\"<urn:g>\"}")).isSome
#guard decodeSubject (jsonOf "{\"type\":\"nt\",\"value\":\"urn:g\"}") == none
#guard (decodeIri (jsonOf "{\"type\":\"nt\",\"value\":\"_:g\"}")).isNone

-- checked decoding: exact lexical form and datatype kept
#guard match decodeCheckedTerm (jsonOf
    "{\"type\":\"literal\",\"value\":\"007\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#integer\"}") with
  | some (.literal l) => l.val.lexicalForm == "007"
  | _ => false
#guard match decodeCheckedTerm (jsonOf
    "{\"type\":\"literal\",\"value\":\"1e21\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#double\"}") with
  | some (.literal l) => l.val.lexicalForm == "1e21"
  | _ => false
#guard match decodeCheckedTerm (jsonOf
    "{\"type\":\"literal\",\"value\":\"x\",\"datatype\":\"http://example.org/dt#mine\"}") with
  | some (.literal l) => l.val.datatype.val == "http://example.org/dt#mine"
  | _ => false
#guard (decodeCheckedTerm (jsonOf
    "{\"type\":\"literal\",\"value\":\"a\",\"xml:lang\":\"ar\",\"its:dir\":\"rtl\",\"datatype\":\"http://www.w3.org/1999/02/22-rdf-syntax-ns#dirLangString\"}")).isSome
-- checked decoding: what RDF refuses
#guard (decodeCheckedTerm (jsonOf "{\"type\":\"literal\",\"value\":\"x\",\"datatype\":\"int\"}")).isNone
#guard (decodeCheckedTerm (jsonOf "{\"type\":\"literal\",\"value\":\"x\",\"datatype\":\"1x:abc\"}")).isNone
#guard (decodeCheckedTerm (jsonOf "{\"type\":\"literal\",\"value\":\"x\",\"xml:lang\":\"en_US\"}")).isNone
#guard (decodeCheckedTerm (jsonOf "{\"type\":\"literal\",\"value\":\"x\",\"xml:lang\":\"en\",\"its:dir\":\"up\"}")).isNone
#guard (decodeCheckedTerm (jsonOf
    "{\"type\":\"literal\",\"value\":\"x\",\"xml:lang\":\"en\",\"datatype\":\"http://www.w3.org/2001/XMLSchema#string\"}")).isNone
#guard (decodeCheckedTerm (jsonOf "{\"type\":\"uri\",\"value\":\"rel/x\"}")).isNone
#guard (decodeCheckedTerm (jsonOf "{\"type\":\"bnode\",\"value\":\"\"}")).isNone
#guard match decodeCheckedTerm (jsonOf "{\"type\":\"literal\",\"value\":\"a\",\"xml:lang\":\"he\",\"its:dir\":\"rtl\"}") with
  | some (.literal l) => l.val.datatype == rdfDirLangString && l.val.direction == some .rtl
  | _ => false
-- unchecked decodeTerm keeps its old behaviour for stored data
#guard (decodeTerm (jsonOf "{\"type\":\"literal\",\"value\":\"x\",\"xml:lang\":\"en_US\"}")).isSome

#print axioms decodeCheckedTerm_encodeTerm
#print axioms termChecked_of_readTermString

end L4Factoidal.RDF.TermJson
