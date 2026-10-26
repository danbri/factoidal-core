/-
L4Factoidal.RDF.Core — the RDF 1.1/1.2 term data model.

Port of `formal/fstar/RDF.Term.fsti` + `RDF.Triple.fsti` (F*) to
Lean 4. Faithful to the F* module's semantics; the F*-specific SMT
scaffolding (`assert_norm` witnesses, `Lemma` + Z3 discharge,
`decreases` annotations) is replaced by Lean-native mechanisms
(`rfl`/`decide` proofs, `theorem`s with explicit proofs, structural
recursion).

Design correspondences (F* → Lean 4):
  - `type wf_iri = s:iri{is_iri s}`        → `WfIri := {s : String // isIri s}`
  - `noeq type literal = {...}`            → `structure Literal`
  - `type wf_literal = l:literal{...}`     → `WfLiteral := {l : Literal // literalWf l}`
  - `noeq type subject` / `rdf_term`       → `inductive Subject` / `Term`
  - reflexivity `Lemma`s                   → `@[simp] theorem`s, proved
  - `assert_norm (is_iri "...")`           → `rfl` on the decidable check

Deliberately NOT ported (F*-side pragmatics, not data model):
  - `RDF.Indexed`'s bucket trees (storage pragmatics).
The `join_canon_term` hash-join key canonicaliser IS ported (2026-08-25,
as `Literal.joinKey` / `Term.joinKey` at the end of this file): the Lean
tree now has a hash join (`SPARQL/Algebra.lean`), and its key function
must identify exactly what `Term.eqb` identifies —
`Term.joinKey_eq_of_eqb` below is that guarantee.
The rdf:XMLLiteral exclusive-c14n machinery IS ported — it is part of
`literalEq`'s semantics, not scaffolding — in `RDF.XmlCanon`.
-/
import L4Factoidal.RDF.XmlCanon

namespace L4Factoidal.RDF

/-! ## Blank nodes — RDF 1.1 Concepts §3.4 -/

/-- A blank node label: a locally-scoped identifier. -/
abbrev BNodeId := String

/-! ## IRIs — RDF 1.1 Concepts §3.2 -/

/-- An IRI, represented as a plain string. -/
abbrev Iri := String

/-- The minimal syntactic well-formedness gate the F* tree applies to
every IRI before RFC 3987 logic sees it: non-empty and contains a
colon. (Port of `RDF.Term.is_iri`; the F* fuel-bounded character walk
`string_has_colon_from` becomes a list membership test.) -/
def isIri (s : String) : Bool :=
  !s.isEmpty && s.toList.contains ':'

/-- `isIri` without the character list. `String.contains` walks the UTF-8
bytes and stops at the first `:`, so a call reads about five characters of
an `http:` IRI and allocates nothing; `String.toList` built one list cell
for every character first. A call on a 50-character IRI took 653 to 706 ns
through the list and 29 to 31 ns through `String.contains` (a compiled
micro-benchmark, 2026-10-14). The list form cost 19 percent of phase 1 of
the SBM11 packer and 11.6 percent of the log replay, and 9.2 percent of the
samples of a perf profile of a DBpedia aggregate query (the key decoder and
the inline integer decoder call it for every term they rebuild;
https://github.com/danbri/factoidal/issues/792 item 5,
https://github.com/danbri/factoidal/issues/825). -/
def isIriFast (s : String) : Bool :=
  !s.isEmpty && s.contains ':'

/-- The two forms agree on every string. `isIri` stays the definition that
the types and the theorems unfold; the compiler runs `isIriFast`
(`isIri_eq_isIriFast`). -/
theorem isIri_eq_isIriFast_apply (s : String) : isIri s = isIriFast s := by
  simp [isIri, isIriFast, String.contains]

/-- The compiler calls `isIriFast` wherever the source says `isIri`. A module
that calls `isIri` gets this replacement by importing `L4Factoidal.RDF.Core`. -/
@[csimp] theorem isIri_eq_isIriFast : @isIri = @isIriFast :=
  funext isIri_eq_isIriFast_apply

/-- A well-formed IRI — the type every term constructor and predicate
position requires. F*: `s:iri{is_iri s}`. -/
abbrev WfIri := { s : Iri // isIri s }

instance : Hashable WfIri := ⟨fun s => hash s.val⟩
instance : Repr WfIri := ⟨fun s n => reprPrec s.val n⟩
instance : ToString WfIri := ⟨fun s => s.val⟩

/-- `rdf:langString` — the datatype of every (non-directional)
language-tagged literal. -/
def rdfLangString : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString", rfl⟩

/-- `rdf:dirLangString` — RDF 1.2's datatype for a directional
language-tagged string (RDF 1.2 Concepts §3.3). -/
def rdfDirLangString : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#dirLangString", rfl⟩

/-- `rdf:XMLLiteral` — value space is exclusive canonical XML
(RDF 1.1 §5.1); `literalEq` compares its lexical forms via
canonicalisation. -/
def rdfXMLLiteral : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral", rfl⟩

/-! ## Base direction — RDF 1.2 Concepts §3.3 -/

/-- Base text direction of a directional language-tagged string. -/
inductive TextDirection where
  | ltr
  | rtl
  deriving Hashable, Repr, DecidableEq

/-! ## Literals — RDF 1.1 Concepts §3.3 / RDF 1.2 Concepts §3.3 -/

/-- A literal: lexical form + datatype IRI + (for language-tagged
strings) a language tag + (RDF 1.2, for `rdf:dirLangString` only) a
base direction. All four fields are carried unconditionally;
`literalWf` is the well-formedness rule on the combination — the same
"optional field, not a new term kind" design as the F* source. -/
structure Literal where
  lexicalForm : String
  datatype    : WfIri
  langTag     : Option String
  direction   : Option TextDirection
  deriving DecidableEq

instance : Hashable Literal :=
  ⟨fun l => hash (l.lexicalForm, l.datatype.val, l.langTag,
                  l.direction.map (fun | .ltr => 0 | .rtl => 1))⟩

instance : Repr Literal :=
  ⟨fun l n => reprPrec (l.lexicalForm, l.datatype.val, l.langTag) n⟩

/-- The canonical spelling of a language tag: no upper-case letter.

RDF 1.2 Concepts §3.4: language tags are compared case-insensitively,
so `"x"@en` and `"x"@EN` are ONE RDF term, and "lexical representations
of language tags MAY be converted to lower case. The value space of
language tags is always in lower case." This port takes that option for
every term it holds: `literalWf` below accepts a tag only in its
canonical form, so one RDF term has one representation and term
equality is structural (`Term.eqb_iff_eq`).

Why this is a rule of the term model and not of each reader
(https://github.com/danbri/factoidal/issues/1001): with two spellings
of one term in a graph, the SPARQL matcher kept the spelling of the
pattern it matched first, so `FILTER(LANG(?o) = "en")` kept a row for
one pattern order and no row for the other.

BCP 47 tags are ASCII (RFC 5646 §2.1), so the case mapping is the ASCII
one, `Char.toLower` (`langTagCanonical_iff`). The definition reads the
characters, so the kernel decides it on a string literal by `rfl`. -/
def langTagCanonical (t : String) : Bool :=
  t.toList.all (fun c => !c.isUpper)

/-- The three-way well-formedness rule (RDF 1.2 extension of RDF 1.1's
"language tag iff `rdf:langString`"):
  * no tag, no direction  ↔ datatype is neither langString nor dirLangString
  * tag, no direction     ↔ datatype is `rdf:langString`
  * tag and direction     ↔ datatype is `rdf:dirLangString`
  * direction without tag — always ill-formed.
A tag must also be in its canonical (lower-case) spelling,
`langTagCanonical`. -/
def literalWf (l : Literal) : Bool :=
  match l.langTag, l.direction with
  | none,   none   => l.datatype != rdfLangString && l.datatype != rdfDirLangString
  | some t, none   => l.datatype == rdfLangString && langTagCanonical t
  | some t, some _ => l.datatype == rdfDirLangString && langTagCanonical t
  | none,   some _ => false

/-- A well-formed literal — what `Term.literal` actually carries. -/
abbrev WfLiteral := { l : Literal // literalWf l }

instance : Hashable WfLiteral := ⟨fun l => hash l.val⟩
instance : Repr WfLiteral := ⟨fun l n => reprPrec l.val n⟩

/-! ## RDF terms — RDF 1.1 Concepts §3 / RDF 1.2 Concepts §3 -/

/-- A triple's subject: an IRI or a blank node, never a literal
(RDF 1.1 Concepts §3.1). Non-recursive; declared before `Term`
because RDF 1.2's triple-term constructor uses it. -/
inductive Subject where
  | iri   (i : WfIri)
  | bnode (b : BNodeId)
  deriving DecidableEq, Hashable, Repr

/-- An RDF term: IRI, blank node, literal, or — RDF 1.2 — a triple
term `<<( s p o )>>`. The triple term bakes in two RDF 1.2
constraints structurally: its subject is a `Subject` (never a
literal) and its predicate is an IRI. Only the object slot recurses,
so structural recursion over `Term` decreases on it — the same
termination skeleton as the F* `decreases t` annotations, supplied
here by Lean automatically. -/
inductive Term where
  | iri        (i : WfIri)
  | bnode      (b : BNodeId)
  | literal    (l : WfLiteral)
  | tripleTerm (s : Subject) (p : WfIri) (o : Term)
  deriving DecidableEq, Hashable, Repr

/-! ### The hash of a term nested deep

`deriving Hashable` made `instHashableTerm.hash`, the SPECIFICATION of the hash of a term:
the index of the constructor, mixed in turn with the hash of each field (`hash_iri` to
`hash_tripleTerm` below say so, each by `rfl`). For a triple term the last field is its
object, so the function takes one native frame for each level of nesting: a triple term
nested 10,153 levels deep overflowed a stack of 512 KB when a dataset keyed its triple
(https://github.com/danbri/factoidal/issues/867). `Term.hashDown` takes the part of the hash
that does not depend on the object from each open triple term, on the way down, and mixes
the parts into the hash of the innermost term on the way back, with a loop and no frame.
`Term.hashFast_eq` proves it equal to the derived function for every term, so every hash
value is the value that the derived function gave, and the order in which a hash map lists
its keys does not change.

The loop is installed as an instance of higher priority, `instHashableTermLoop`, and not
with a `@[csimp]` theorem. The compiler inlines an instance before it replaces the constants
of a `@[csimp]` theorem, so after such a theorem a hash map that hashed its keys with
`instHashableTerm` still called the recursive function (measured 2026-10-15 in the emitted C
of `FastGraph`, which called `instHashableTerm.hash` and called `Term.joinKeyFast`, the
`@[csimp]` replacement of `Term.joinKey`, as it should). Every `Hashable Term` that is
resolved after the instance is the loop, and so is the hash of every structure that
derives `Hashable` after it (`Triple`). -/

theorem hash_iri (i : WfIri) : hash (Term.iri i) = mixHash 0 (hash i) := rfl

theorem hash_bnode (b : BNodeId) : hash (Term.bnode b) = mixHash 1 (hash b) := rfl

theorem hash_literal (l : WfLiteral) : hash (Term.literal l) = mixHash 2 (hash l) := rfl

theorem hash_tripleTerm (s : Subject) (p : WfIri) (o : Term) :
    hash (Term.tripleTerm s p o) = mixHash (mixHash (mixHash 3 (hash s)) (hash p)) (hash o) := rfl

/-- The part of the hash of a triple term that does not depend on its object. -/
def hashTripleOpen (s : Subject) (p : WfIri) : UInt64 := mixHash (mixHash 3 (hash s)) (hash p)

/-- The parts of the open triple terms, innermost first, mixed into the hash of the term
below them, innermost first. Every call of this function on itself is a tail call. -/
def hashClose : List UInt64 → UInt64 → UInt64
  | [], h => h
  | q :: qs, h => hashClose qs (mixHash q h)

/-- The hash of a term, with the parts of the open triple terms in a list. -/
def Term.hashDown : List UInt64 → Term → UInt64
  | opens, .tripleTerm s p o => Term.hashDown (hashTripleOpen s p :: opens) o
  | opens, .iri i => hashClose opens (mixHash 0 (hash i))
  | opens, .bnode b => hashClose opens (mixHash 1 (hash b))
  | opens, .literal l => hashClose opens (mixHash 2 (hash l))

theorem Term.hashDown_eq : ∀ (t : Term) (opens : List UInt64),
    Term.hashDown opens t = hashClose opens (hash t)
  | .tripleTerm s p o, opens => by
      rw [Term.hashDown, Term.hashDown_eq o, hash_tripleTerm]
      rfl
  | .iri i, opens => rfl
  | .bnode b, opens => rfl
  | .literal l, opens => rfl

/-- The hash of a term as the loop. -/
def Term.hashFast (t : Term) : UInt64 := Term.hashDown [] t

/-- The loop gives the value of the derived function, for every term. -/
theorem Term.hashFast_eq (t : Term) : Term.hashFast t = hash t := by
  rw [Term.hashFast, Term.hashDown_eq]
  rfl

/-- The hash of a term for every use after this line is the loop. -/
instance (priority := high) instHashableTermLoop : Hashable Term := ⟨Term.hashFast⟩

#print axioms Term.hashDown_eq
#print axioms Term.hashFast_eq

/-! ## XSD term-algebra constants -/

def xsdString  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#string", rfl⟩
def xsdInteger : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#integer", rfl⟩
def xsdDecimal : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#decimal", rfl⟩
def xsdDouble  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#double", rfl⟩
def xsdBoolean : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#boolean", rfl⟩

/-- Convenience constructor: a plain string literal (RDF 1.1 assigns
`xsd:string` to un-tagged, un-typed literals). -/
def Literal.string (lex : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := xsdString,
     langTag := none, direction := none }, rfl⟩

/-! ### Lower case and the canonical tag -/

theorem toLower_char_idem (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split <;> rename_i h
  · rw [dif_neg]
    intro h2
    simp only [ge_iff_le, UInt32.le_iff_toNat_le] at h h2
    simp only [UInt32.toNat_add] at h2
    have : ('A'.val).toNat = 65 := rfl
    have : ('Z'.val).toNat = 90 := rfl
    have : ('a'.val - 'A'.val).toNat = 32 := rfl
    omega
  · rfl

theorem toLower_string_idem (s : String) : s.toLower.toLower = s.toLower := by
  rw [← String.toList_inj]
  simp only [String.toLower, String.toList_map, List.map_map]
  congr 1
  funext c
  exact toLower_char_idem c

/-- A character is its own lower case exactly when it is not upper case. -/
theorem char_toLower_eq_self_iff (c : Char) : c.toLower = c ↔ c.isUpper = false := by
  have hdef : c.isUpper = decide (c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val) := rfl
  unfold Char.toLower
  by_cases h : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val
  · rw [dif_pos h, hdef, decide_eq_true h]
    simp only [Bool.true_eq_false, iff_false]
    intro he
    have hv := congrArg (fun x : Char => x.val.toNat) he
    simp only [UInt32.toNat_add] at hv
    simp only [ge_iff_le, UInt32.le_iff_toNat_le] at h
    have : ('A'.val).toNat = 65 := rfl
    have : ('Z'.val).toNat = 90 := rfl
    have : ('a'.val - 'A'.val).toNat = 32 := rfl
    omega
  · rw [dif_neg h, hdef, decide_eq_false h]; simp

/-- `langTagCanonical` is "the tag is its own lower case". -/
theorem langTagCanonical_iff (t : String) : langTagCanonical t = true ↔ t.toLower = t := by
  rw [← String.toList_inj]
  simp only [langTagCanonical, String.toLower, String.toList_map, List.all_eq_true,
    Bool.not_eq_true']
  constructor
  · intro h
    conv => rhs; rw [← List.map_id t.toList]
    apply List.map_congr_left
    intro c hc
    exact (char_toLower_eq_self_iff c).mpr (h c hc)
  · intro h c hc
    apply (char_toLower_eq_self_iff c).mp
    have hm : c.toLower ∈ t.toList.map Char.toLower := List.mem_map_of_mem hc
    rw [h] at hm
    -- every element of `t.toList` is the lower case of an element
    have key : ∀ (l : List Char), l.map Char.toLower = l → ∀ x ∈ l, x.toLower = x := by
      intro l
      induction l with
      | nil => intro _ x hx; simp at hx
      | cons a as ih =>
          intro hl x hx
          simp only [List.map_cons, List.cons.injEq] at hl
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hl.1
          · exact ih hl.2 x hx
    exact key t.toList h c hc

/-- The lower case of a tag is canonical. -/
theorem langTagCanonical_toLower (t : String) : langTagCanonical t.toLower = true :=
  (langTagCanonical_iff _).mpr (toLower_string_idem t)

/-- A canonical tag is its own lower case. -/
theorem toLower_of_langTagCanonical {t : String} (h : langTagCanonical t = true) :
    t.toLower = t :=
  (langTagCanonical_iff t).mp h

/-- Convenience constructor: a language-tagged literal. The tag is
written in its canonical (lower-case) form (RDF 1.2 Concepts §3.4). -/
def Literal.langString (lex tag : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := rdfLangString,
     langTag := some tag.toLower, direction := none },
   by simp [literalWf, langTagCanonical_toLower]⟩

/-- Convenience constructor: RDF 1.2's directional language-tagged
literal (a language tag AND a base direction, so the datatype is
`rdf:dirLangString` — the third clause of `literalWf`). The tag is
written in its canonical (lower-case) form. -/
def Literal.dirLangString (lex tag : String) (d : TextDirection) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := rdfDirLangString,
     langTag := some tag.toLower, direction := some d },
   by simp [literalWf, langTagCanonical_toLower]⟩

/-! ## Equality — the three literal-equality relations

The F* source distinguishes (and warns against conflating):
  * `literal_term_eq` — STRICT term equality (RDF 1.1 Concepts §3.3:
    every field character-by-character). In this port that is exactly
    `Eq`/`DecidableEq` on `Literal` — see
    `literalTermEq_iff_eq` below, the Lean counterpart of the F*
    `lemma_literal_term_eq_identity`.
  * `literalEq` — the comparison the SPARQL engine matches with
    (`Literal.eqb`): language tags case-insensitively (RDF 1.1 §3.3
    permits lowercasing the tag value space), every other field
    exactly. Until 2026-10-23 it also compared `rdf:XMLLiteral` lexical
    forms by exclusive canonical XML; that is value comparison, and it
    moved to `Literal.valueEqb`
    (https://github.com/danbri/factoidal/issues/963).
  * `literalValueEq` — RDF 1.1 value equality; with well-formed
    representations (plain literals already carry `xsd:string`) it
    coincides with field comparison modulo tag case. -/

/-- Case-insensitive language-tag comparison (`@en-US` ≡ `@en-us`). -/
def langTagEq (t1 t2 : String) : Bool :=
  t1.toLower == t2.toLower

def langTagOptionEq : Option String → Option String → Bool
  | none,    none    => true
  | some a,  some b  => langTagEq a b
  | _,       _       => false

/-- Structural equality on subjects (port of `subject_eq`). -/
def Subject.eqb : Subject → Subject → Bool
  | .iri i1,   .iri i2   => i1 == i2
  | .bnode b1, .bnode b2 => b1 == b2
  | _,         _         => false

/-- Engine literal equality, the RDF term equality of RDF 1.1 Concepts
§3.3: lexical form, datatype and base direction exact, language tag
case-insensitive (§3.3 permits lowercasing the tag). SPARQL 1.1 §18.3
(compatible mappings) and §18.4.1 (BGP matching) use this equality.

Until 2026-10-23 this compared two `rdf:XMLLiteral` lexical forms by
exclusive canonical XML (the F* `literal_eq` WebOnt-miscellaneous-202
fix). That is VALUE comparison: joins and BGP matching then treated
`"<x></x>"^^rdf:XMLLiteral` and `"<x/>"^^rdf:XMLLiteral` as one term
(https://github.com/danbri/factoidal/issues/963). Value comparison is
`Literal.valueEqb`; only the `=` operator and entailment call it. -/
def Literal.eqb (l1 l2 : Literal) : Bool :=
  l1.lexicalForm == l2.lexicalForm &&
  l1.datatype == l2.datatype &&
  langTagOptionEq l1.langTag l2.langTag &&
  l1.direction == l2.direction

/-- Literal VALUE equality for the datatypes this comparison knows
without numeric conversion: `Literal.eqb`, except that two
`rdf:XMLLiteral` literals compare by exclusive canonical XML (RDF 1.1
Concepts §5.1: the value space of `rdf:XMLLiteral` is the canonical
DOM). For the SPARQL `=` operator (§17.4.1.7 and the operator mapping)
and for D-entailment; never for joins or BGP matching. -/
def Literal.valueEqb (l1 l2 : Literal) : Bool :=
  (if l1.datatype == rdfXMLLiteral && l2.datatype == rdfXMLLiteral
   then XmlCanon.xmlCanonEq l1.lexicalForm l2.lexicalForm
   else l1.lexicalForm == l2.lexicalForm) &&
  l1.datatype == l2.datatype &&
  langTagOptionEq l1.langTag l2.langTag &&
  l1.direction == l2.direction

/-- STRICT literal term equality (port of `literal_term_eq`): every
field compares exactly. -/
def Literal.termEq (l1 l2 : Literal) : Bool :=
  l1.lexicalForm == l2.lexicalForm &&
  l1.datatype == l2.datatype &&
  l1.langTag == l2.langTag &&
  l1.direction == l2.direction

/-- Engine term equality (port of `rdf_term_eq`): recursive through
triple terms, literals via the coarse `Literal.eqb`. -/
def Term.eqb : Term → Term → Bool
  | .iri i1,     .iri i2     => i1 == i2
  | .bnode b1,   .bnode b2   => b1 == b2
  | .literal l1, .literal l2 => l1.val.eqb l2.val
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      s1.eqb s2 && p1 == p2 && o1.eqb o2
  | _, _ => false

/-! ## Triples — RDF 1.1 Concepts §3.1 (port of `RDF.Triple`) -/

/-- A triple: subject, predicate (always an IRI), object. -/
structure Triple where
  s : Subject
  p : WfIri
  o : Term
  deriving DecidableEq, Hashable, Repr

/-- Structural (engine) equality on triples (port of `triple_eq`). -/
def Triple.eqb (a b : Triple) : Bool :=
  a.s.eqb b.s && a.p == b.p && a.o.eqb b.o

/-- Coerce a term into a subject; literals and triple terms have no
subject form (port of `term_to_subject_opt`). -/
def Term.toSubject? : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

/-- View a subject as a term (port of `subject_to_term`). -/
def Subject.toTerm : Subject → Term
  | .iri i   => .iri i
  | .bnode b => .bnode b

/-! ## Reflexivity and identity theorems

The F* source proves these as SMT `Lemma`s; here they are ordinary
theorems with explicit proofs — no `sorry`, no `axiom`, no solver. -/

@[simp] theorem Subject.eqb_refl (s : Subject) : s.eqb s = true := by
  cases s <;> simp [Subject.eqb]

@[simp] theorem langTagEq_refl (t : String) : langTagEq t t = true := by
  simp [langTagEq]

@[simp] theorem langTagOptionEq_refl (t : Option String) :
    langTagOptionEq t t = true := by
  cases t <;> simp [langTagOptionEq]

@[simp] theorem Literal.eqb_refl (l : Literal) : l.eqb l = true := by
  simp [Literal.eqb]

/-- Term equality implies value equality. -/
theorem Literal.valueEqb_of_eqb {l1 l2 : Literal} (h : l1.eqb l2 = true) :
    l1.valueEqb l2 = true := by
  simp only [Literal.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hl, hd⟩, ht⟩, hr⟩ := h
  unfold Literal.valueEqb
  by_cases hx : (l1.datatype == rdfXMLLiteral && l2.datatype == rdfXMLLiteral) = true <;>
    simp [hx, hl, hd, ht, hr, XmlCanon.xmlCanonEq]

@[simp] theorem Literal.termEq_refl (l : Literal) : l.termEq l = true := by
  simp [Literal.termEq]

/-- Port of `lemma_literal_term_eq_identity`: the strict test decides
literal term IDENTITY — `termEq` true implies propositional equality.
(With `termEq_refl` above this makes `termEq` exactly `Eq` on
literals.) -/
theorem Literal.termEq_iff_eq (l1 l2 : Literal) :
    l1.termEq l2 = true ↔ l1 = l2 := by
  constructor
  · intro h
    unfold Literal.termEq at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hlex, hdt⟩, htag⟩, hdir⟩ := h
    cases l1; cases l2
    simp_all
  · intro h; subst h; simp

@[simp] theorem Term.eqb_refl (t : Term) : t.eqb t = true := by
  induction t with
  | iri i => simp [Term.eqb]
  | bnode b => simp [Term.eqb]
  | literal l => simp [Term.eqb]
  | tripleTerm s p o ih => simp [Term.eqb, ih]

@[simp] theorem Triple.eqb_refl (t : Triple) : t.eqb t = true := by
  simp [Triple.eqb]

/-! ## Transitivity and decomposition of the engine equality

Harvested 2026-08-22 from the rdfs-core closure proofs (where they were
first needed): `Term.eqb` is transitive, and in the positions the
closure rules match on — subjects, predicates, objects usable as
subjects — it collapses to propositional equality. -/

theorem Subject.eqb_eq {a b : Subject} (h : Subject.eqb a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [Subject.eqb, Subtype.ext_iff]

theorem langTagOptionEq_trans {a b c : Option String}
    (h1 : langTagOptionEq a b = true) (h2 : langTagOptionEq b c = true) :
    langTagOptionEq a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [langTagOptionEq, langTagEq]

theorem Literal.eqb_trans {a b c : Literal}
    (h1 : Literal.eqb a b = true) (h2 : Literal.eqb b c = true) :
    Literal.eqb a c = true := by
  simp only [Literal.eqb, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  obtain ⟨⟨⟨hx1, hd1⟩, hl1⟩, hr1⟩ := h1
  obtain ⟨⟨⟨hx2, hd2⟩, hl2⟩, hr2⟩ := h2
  exact ⟨⟨⟨hx1.trans hx2, hd1.trans hd2⟩, langTagOptionEq_trans hl1 hl2⟩, hr1.trans hr2⟩

theorem Term.eqb_trans : ∀ {a b c : Term},
    Term.eqb a b = true → Term.eqb b c = true → Term.eqb a c = true := by
  intro a
  induction a with
  | iri i =>
    intro b c h1 h2
    cases b <;> cases c <;> simp_all [Term.eqb]
  | bnode x =>
    intro b c h1 h2
    cases b <;> cases c <;> simp_all [Term.eqb]
  | literal l =>
    intro b c h1 h2
    cases b <;> cases c <;> simp only [Term.eqb] at h1 h2 ⊢ <;>
      first
        | exact Literal.eqb_trans h1 h2
        | simp at h1
        | simp at h2
  | tripleTerm s p o ih =>
    intro b c h1 h2
    cases b <;> cases c <;>
      simp only [Term.eqb, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢ <;>
      first
        | (obtain ⟨⟨hs1, hp1⟩, ho1⟩ := h1
           obtain ⟨⟨hs2, hp2⟩, ho2⟩ := h2
           refine ⟨⟨?_, hp1.trans hp2⟩, ih ho1 ho2⟩
           rw [Subject.eqb_eq hs1, Subject.eqb_eq hs2]
           exact Subject.eqb_refl _)
        | simp at h1
        | simp at h2

theorem Triple.eqb_trans {a b c : Triple}
    (h1 : Triple.eqb a b = true) (h2 : Triple.eqb b c = true) :
    Triple.eqb a c = true := by
  simp only [Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  obtain ⟨⟨hs1, hp1⟩, ho1⟩ := h1
  obtain ⟨⟨hs2, hp2⟩, ho2⟩ := h2
  refine ⟨⟨?_, hp1.trans hp2⟩, Term.eqb_trans ho1 ho2⟩
  rw [Subject.eqb_eq hs1, Subject.eqb_eq hs2]
  exact Subject.eqb_refl _

/-- Decomposition of a triple eqb-match: subject and predicate match
EXACTLY; only the object can differ, and only inside literals. -/
theorem Triple.eqb_parts {u t : Triple} (h : Triple.eqb u t = true) :
    u.s = t.s ∧ u.p = t.p ∧ Term.eqb u.o t.o = true := by
  simp only [Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  exact ⟨Subject.eqb_eq hs, hp, ho⟩

theorem Triple.eqb_of_parts {u t : Triple} (hs : u.s = t.s) (hp : u.p = t.p)
    (ho : Term.eqb u.o t.o = true) : Triple.eqb u t = true := by
  simp [Triple.eqb, hs, hp, ho]

/-- In the term position the rules match an IRI on, eqb IS equality. -/
theorem Term.eqb_iri {a : Term} {i : WfIri}
    (h : Term.eqb a (Term.iri i) = true) : a = Term.iri i := by
  cases a <;> simp_all [Term.eqb, Subtype.ext_iff]

/-- ... and likewise for an object read as a subject (an IRI or a blank
node — never a literal, so never fuzzy). -/
theorem Term.eqb_eq_of_toSubject {a b : Term} {x : Subject}
    (h : Term.eqb a b = true) (hs : b.toSubject? = some x) : a = b := by
  cases b <;> simp only [Term.toSubject?] at hs <;>
    first
      | exact Term.eqb_iri h
      | (cases a <;> simp_all [Term.eqb])
      | simp at hs

/-! ## Symmetry of the engine equality

Needed wherever a test compares a QUERY value against a STORED value
while a second test compares two stored values against each other:
bridging the two needs the equality to behave like a genuine
equivalence relation, not merely a reflexive one. Transitivity is
above; this is the other half. Harvested 2026-08-23 from the
delta-merge correctness proof, and the F\* source proves the same
lemmas about the same functions for the same reason. -/

theorem langTagEq_symm (a b : String) : langTagEq a b = langTagEq b a := by
  simp [langTagEq, BEq.comm]

theorem langTagOptionEq_symm (a b : Option String) :
    langTagOptionEq a b = langTagOptionEq b a := by
  cases a <;> cases b <;> simp [langTagOptionEq, langTagEq_symm]

theorem Subject.eqb_symm (a b : Subject) : a.eqb b = b.eqb a := by
  cases a <;> cases b <;> simp [Subject.eqb, BEq.comm]

theorem Literal.eqb_symm (a b : Literal) : a.eqb b = b.eqb a := by
  simp [Literal.eqb, BEq.comm, langTagOptionEq_symm]

theorem Term.eqb_symm : ∀ (a b : Term), a.eqb b = b.eqb a
  | .iri _, .iri _ => by simp [Term.eqb, BEq.comm]
  | .bnode _, .bnode _ => by simp [Term.eqb, BEq.comm]
  | .literal l1, .literal l2 => by simp [Term.eqb, Literal.eqb_symm]
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 => by
      simp [Term.eqb, Subject.eqb_symm s1 s2, Term.eqb_symm o1 o2, BEq.comm]
  | .iri _, .bnode _ | .iri _, .literal _ | .iri _, .tripleTerm _ _ _
  | .bnode _, .iri _ | .bnode _, .literal _ | .bnode _, .tripleTerm _ _ _
  | .literal _, .iri _ | .literal _, .bnode _ | .literal _, .tripleTerm _ _ _
  | .tripleTerm _ _ _, .iri _ | .tripleTerm _ _ _, .bnode _
  | .tripleTerm _ _ _, .literal _ => by simp [Term.eqb]

theorem Triple.eqb_symm (a b : Triple) : a.eqb b = b.eqb a := by
  simp [Triple.eqb, Subject.eqb_symm a.s b.s, Term.eqb_symm a.o b.o, BEq.comm]

/-! ## The hash-join key canonicaliser (port of `join_canon_term`)

A hash join buckets rows by STRUCTURAL equality of a key, but the
engine joins rows under `Term.eqb`, which is coarser than structural
equality in one place: language tags compare case-insensitively.
`joinKey` maps every term to a canonical representative of its
`eqb`-class — tags lowercased — so that eqb-equal terms carry
structurally equal keys (`Term.joinKey_eq_of_eqb`). That is the ONLY
property the hash join needs of it: a bucket may still hold
eqb-distinct rows (the probe re-tests compatibility in full), but no
eqb-compatible row may land in a different bucket. -/

/-- The canonical-representative literal for hash-join keys. -/
def Literal.joinKey (l : Literal) : Literal :=
  { lexicalForm := l.lexicalForm
  , datatype    := l.datatype
  , langTag     := l.langTag.map String.toLower
  , direction   := l.direction }

/-- A well-formed literal is its own join key: its tag is already in
lower case (`literalWf` requires `langTagCanonical`). -/
theorem Literal.joinKey_eq_self_of_wf {l : Literal} (h : literalWf l = true) :
    l.joinKey = l := by
  obtain ⟨lex, dt, tag, dir⟩ := l
  cases tag with
  | none => rfl
  | some t =>
      have ht : langTagCanonical t = true := by
        cases dir <;> simp_all [literalWf]
      simp [Literal.joinKey, toLower_of_langTagCanonical ht]

/-- Canonicalising for the join key keeps a well-formed literal
well-formed (it is the identity on it). -/
theorem literalWf_joinKey (l : Literal) (h : literalWf l = true) : literalWf l.joinKey = true := by
  rw [Literal.joinKey_eq_self_of_wf h]; exact h

/-- Lower-casing the tag of ANY literal (reader input, not yet checked)
makes the tag canonical and keeps the rest of the rule: the result is
well-formed exactly when the input is well-formed apart from the case
of its tag. -/
def literalWfModCase (l : Literal) : Bool :=
  match l.langTag, l.direction with
  | none,   none   => l.datatype != rdfLangString && l.datatype != rdfDirLangString
  | some _, none   => l.datatype == rdfLangString
  | some _, some _ => l.datatype == rdfDirLangString
  | none,   some _ => false

theorem literalWf_joinKey_eq (l : Literal) : literalWf l.joinKey = literalWfModCase l := by
  obtain ⟨lex, dt, tag, dir⟩ := l
  cases tag <;> cases dir <;>
    simp [literalWf, literalWfModCase, Literal.joinKey, langTagCanonical_toLower]

/-- The smart constructor every reader uses for a literal it has read:
the language tag is written in its canonical (lower-case) form first
(RDF 1.2 Concepts §3.4), then `literalWf` decides. -/
def Literal.toWf? (l : Literal) : Option WfLiteral :=
  if h : literalWf l.joinKey then some ⟨l.joinKey, h⟩ else none

theorem Literal.joinKey_joinKey (l : Literal) : l.joinKey.joinKey = l.joinKey := by
  obtain ⟨lex, dt, tag, dir⟩ := l
  cases tag <;> simp [Literal.joinKey, toLower_string_idem]

/-- Lower-casing first changes nothing: `toWf?` lower-cases anyway. -/
theorem Literal.toWf?_joinKey (l : Literal) : Literal.toWf? l.joinKey = Literal.toWf? l := by
  unfold Literal.toWf?
  rw [Literal.joinKey_joinKey]

theorem Literal.toWf?_of_wf {l : Literal} (h : literalWf l = true) :
    Literal.toWf? l = some ⟨l, h⟩ := by
  have he := Literal.joinKey_eq_self_of_wf h
  unfold Literal.toWf?
  rw [dif_pos (by rw [he]; exact h)]
  simp [he]

/-- eqb-equal literals have identical join keys — the bucket-soundness
half of the canonicaliser's contract. -/
theorem Literal.joinKey_eq_of_eqb {l1 l2 : Literal}
    (h : l1.eqb l2 = true) : l1.joinKey = l2.joinKey := by
  simp only [Literal.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hlex', hdt⟩, htag⟩, hdir⟩ := h
  have htag' : l1.langTag.map String.toLower = l2.langTag.map String.toLower := by
    cases h1 : l1.langTag with
    | none => cases h2 : l2.langTag with
      | none => rfl
      | some b => rw [h1, h2] at htag; simp [langTagOptionEq] at htag
    | some a => cases h2 : l2.langTag with
      | none => rw [h1, h2] at htag; simp [langTagOptionEq] at htag
      | some b =>
          rw [h1, h2] at htag
          simp only [langTagOptionEq, langTagEq, beq_iff_eq] at htag
          simp [htag]
  unfold Literal.joinKey
  rw [hlex', hdt, htag', hdir]

/-- The canonical-representative term for hash-join keys: literals via
`Literal.joinKey`, recursively through triple-term objects. -/
def Term.joinKey : Term → Term
  | .iri i     => .iri i
  | .bnode b   => .bnode b
  | .literal l => .literal ⟨l.val.joinKey, literalWf_joinKey l.val l.property⟩
  | .tripleTerm s p o => .tripleTerm s p o.joinKey

/-! ### The join key of a well-formed term is the term

`Term.joinKey` above is the SPECIFICATION of the key. Since `literalWf`
requires the canonical tag, every `Term` is its own join key
(`Term.joinKey_eq_self`), and `@[csimp]` makes every caller compiled
after this point use the term itself: no copy, and no native frame for
each level of triple-term nesting
(https://github.com/danbri/factoidal/issues/867). Until 2026-10-24 the
compiled key was a loop that lower-cased each tag (`Term.joinKeyLoop`). -/

/-- A term inside the triple terms of a list, the innermost first. -/
def wrapTripleTerms : List (Subject × WfIri) → Term → Term
  | [], t => t
  | (s, p) :: frames, t => wrapTripleTerms frames (.tripleTerm s p t)

/-- Every term is its own join key: no well-formed literal has an
upper-case language tag. -/
theorem Term.joinKey_eq_self : ∀ t : Term, t.joinKey = t
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal l => by
      simp only [Term.joinKey, Term.literal.injEq]
      exact Subtype.ext (Literal.joinKey_eq_self_of_wf l.property)
  | .tripleTerm s p o => by
      simp only [Term.joinKey, Term.joinKey_eq_self o]

/-- `Term.joinKey` as it runs: the term. -/
def Term.joinKeyFast (t : Term) : Term := t

/-- Any join key compiled after this line is the term itself. -/
@[csimp] theorem Term.joinKey_eq_fast : @Term.joinKey = @Term.joinKeyFast := by
  funext t
  rw [Term.joinKeyFast, Term.joinKey_eq_self]

#print axioms Term.joinKey_eq_self
#print axioms Term.joinKey_eq_fast

/-- eqb-equal terms have identical join keys: the theorem the hash
join's bucket lookup rests on. -/
theorem Term.joinKey_eq_of_eqb : ∀ {a b : Term},
    Term.eqb a b = true → a.joinKey = b.joinKey := by
  intro a
  induction a with
  | iri i => intro b h; cases b <;> simp_all [Term.eqb, Term.joinKey, Subtype.ext_iff]
  | bnode x => intro b h; cases b <;> simp_all [Term.eqb, Term.joinKey]
  | literal l =>
      intro b h
      cases b <;> simp only [Term.eqb] at h
      case literal l2 =>
        simp only [Term.joinKey, Term.literal.injEq]
        exact Subtype.ext (Literal.joinKey_eq_of_eqb h)
      all_goals simp at h
  | tripleTerm s p o ih =>
      intro b h
      cases b <;> simp only [Term.eqb, Bool.and_eq_true, beq_iff_eq] at h
      case tripleTerm s2 p2 o2 =>
        obtain ⟨⟨hs, hp⟩, ho⟩ := h
        simp only [Term.joinKey, Term.tripleTerm.injEq]
        exact ⟨Subject.eqb_eq hs, hp, ih ho⟩
      all_goals simp at h

/-! ## One representation for each RDF term

RDF 1.2 Concepts §3.4 makes `"x"@en` and `"x"@EN` one RDF term and
permits the lower-case spelling; `literalWf` requires it. So every
`Term` value is the canonical representation of its RDF term, and the
engine equality `Term.eqb` (which compares tags case-insensitively) is
structural equality (`Term.eqb_iff_eq`). A SPARQL solution therefore
binds a variable to one representation whatever the order of the
patterns that bind it (SPARQL 1.1 §18.1.7;
https://github.com/danbri/factoidal/issues/1001). -/

/-- A term is canonical when every language tag in it, inside triple
terms too, is in lower case: it is its own join key. -/
def Term.Canonical (t : Term) : Prop := t.joinKey = t

/-- Every term is canonical: the type `WfLiteral` cannot hold an
upper-case tag, so every reader and every constructor makes canonical
terms. -/
theorem Term.canonical (t : Term) : t.Canonical := Term.joinKey_eq_self t

/-- On canonical terms (all terms), the engine equality is structural
equality. -/
theorem Term.eqb_iff_eq (a b : Term) : a.eqb b = true ↔ a = b := by
  constructor
  · intro h
    have hk := Term.joinKey_eq_of_eqb h
    rwa [Term.joinKey_eq_self, Term.joinKey_eq_self] at hk
  · intro h; subst h; exact Term.eqb_refl a

theorem Term.eq_of_eqb {a b : Term} (h : a.eqb b = true) : a = b :=
  (Term.eqb_iff_eq a b).mp h

/-- The same for triples. -/
theorem Triple.eqb_iff_eq (a b : Triple) : a.eqb b = true ↔ a = b := by
  constructor
  · intro h
    obtain ⟨hs, hp, ho⟩ := Triple.eqb_parts h
    have hoe := Term.eq_of_eqb ho
    cases a; cases b
    simp_all
  · intro h; subst h; exact Triple.eqb_refl a

#print axioms Term.canonical
#print axioms Term.eqb_iff_eq
#print axioms Triple.eqb_iff_eq

end L4Factoidal.RDF
