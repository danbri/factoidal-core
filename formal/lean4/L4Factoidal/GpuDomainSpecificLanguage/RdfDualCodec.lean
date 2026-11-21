import L4Factoidal.GpuDomainSpecificLanguage.RdfTermCodebook
import L4Factoidal.SPARQL.Algebra

/-!
# A dual-codebook boundary for GPU RDF

RDF lexical/structural identity and engine term equality are not
interchangeable. A lossless serializer needs *identity codes*: its decoder
must reproduce precisely the original RDF Term, including literal details,
blank-node labels and recursive RDF 1.2 triple terms. A join needs
*equality codes* which preserve RDF.Term.eqb, not ordinary structural Eq.

This deliberately makes the two IDs distinct. A finite executable admission
check certifies identity round-trips and equality comparison agreement over
an admitted term scope, including non-IRI terms. A device implementation
cannot assume those checks passed for arbitrary other inputs or datasets.

The on-device memory layout, snapshot identity, GPU implementation and driver
are separate from this pure adapter.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.RdfDualCodec

open L4Factoidal.RDF

structure Entry where
  term : Term
  identity : UInt32
  equality : UInt32
  deriving Repr

abbrev Dictionary := List Entry

/-- Look up the structurally *exact* RDF term. This is intentionally more
    discriminating than engine equality, because the decoder is lossless. -/
def lookup? (dict : Dictionary) (term : Term) : Option Entry :=
  dict.find? (fun entry => decide (entry.term = term))

def identityCode? (dict : Dictionary) (term : Term) : Option UInt32 :=
  (lookup? dict term).map (·.identity)

def equalityCode? (dict : Dictionary) (term : Term) : Option UInt32 :=
  (lookup? dict term).map (·.equality)

/-- Decode by identity code. Duplicate codes are rejected when the
    finite-scope round-trip admission check is applied. -/
def decodeTerm? (dict : Dictionary) (identity : UInt32) : Option Term :=
  (dict.find? fun entry => entry.identity == identity).map (·.term)

def identityRoundTrip (dict : Dictionary) (term : Term) : Bool :=
  decide ((identityCode? dict term).bind (decodeTerm? dict) = some term)

/-- The second component checks the engine's comparison relation, including
    literal and nested triple-term equality, for every admitted pair. -/
def matchAgreement (dict : Dictionary) (a b : Term) : Bool :=
  match equalityCode? dict a, equalityCode? dict b with
  | some ac, some bc => ((ac == bc) == a.eqb b)
  | _, _ => false

def admit (dict : Dictionary) (scope : List Term) : Bool :=
  scope.all (identityRoundTrip dict) &&
  scope.all (fun a => scope.all (matchAgreement dict a))

theorem admitted_identity (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (term : Term) (ht : term ∈ scope) :
    (identityCode? dict term).bind (decodeTerm? dict) = some term := by
  simp only [admit, Bool.and_eq_true] at valid
  have h := List.all_eq_true.mp valid.1 term ht
  unfold identityRoundTrip at h
  exact decide_eq_true_eq.mp h

theorem admitted_equality (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (a b : Term)
    (ha : a ∈ scope) (hb : b ∈ scope) :
    ∃ ac bc, equalityCode? dict a = some ac ∧
      equalityCode? dict b = some bc ∧
      (ac == bc) = a.eqb b := by
  simp only [admit, Bool.and_eq_true] at valid
  have hall := valid.2
  have pair := List.all_eq_true.mp (List.all_eq_true.mp hall a ha) b hb
  unfold matchAgreement at pair
  cases hca : equalityCode? dict a with
  | none => simp [hca] at pair
  | some ac =>
    cases hcb : equalityCode? dict b with
    | none => simp [hca, hcb] at pair
    | some bc =>
      refine ⟨ac, bc, rfl, rfl, ?_⟩
      exact beq_iff_eq.mp (by simpa [hca, hcb] using pair)

/-- An RDF graph's source terms, including arbitrary literal and triple-term
    objects. They are opaque dictionary entries, not broken into strings or
    inexact numeric identifiers. -/
def graphTerms (g : Graph) : List Term :=
  g.flatMap fun t => [t.s.toTerm, .iri t.p, t.o]

/-- A binding's variables are untouched; only the RDF-term payloads receive
    identity codes. Variable order and duplicate association-list entries
    are therefore preserved. -/
def encodeBinding? (dict : Dictionary) : L4Factoidal.SPARQL.Binding → Option (List (String × UInt32))
  | [] => some []
  | (name, term) :: rest => do
      let code ← identityCode? dict term
      let tail ← encodeBinding? dict rest
      return (name, code) :: tail

def decodeBinding? (dict : Dictionary) : List (String × UInt32) → Option L4Factoidal.SPARQL.Binding
  | [] => some []
  | (name, code) :: rest => do
      let term ← decodeTerm? dict code
      let tail ← decodeBinding? dict rest
      return (name, term) :: tail

/-- A fixed-width RDF triple transported through three identity IDs; the
    predicate and subject are checked again at decode, not cast blindly. -/
abbrev CodedTriple := UInt32 × UInt32 × UInt32

def encodeTriple? (dict : Dictionary) (t : Triple) : Option CodedTriple := do
  let s ← identityCode? dict t.s.toTerm
  let p ← identityCode? dict (.iri t.p)
  let o ← identityCode? dict t.o
  return (s, p, o)

def decodeTriple? (dict : Dictionary) (coded : CodedTriple) : Option Triple := do
  let sTerm ← decodeTerm? dict coded.1
  let s ← sTerm.toSubject?
  let pTerm ← decodeTerm? dict coded.2.1
  let p ← match pTerm with
    | .iri iri => some iri
    | _ => none
  let o ← decodeTerm? dict coded.2.2
  return ⟨s, p, o⟩

def encodeGraph? (dict : Dictionary) (g : Graph) : Option (List CodedTriple) :=
  g.mapM (encodeTriple? dict)

def decodeGraph? (dict : Dictionary) (coded : List CodedTriple) : Option Graph :=
  coded.mapM (decodeTriple? dict)

/-- Executable end-to-end *identity* admission: no partial or lossy
    graph transport may be treated as a successful serialization. -/
def checkGraphRoundTrip (dict : Dictionary) (g : Graph) : Bool :=
  decide ((encodeGraph? dict g).bind (decodeGraph? dict) = some g)

theorem checkGraphRoundTrip_sound (dict : Dictionary) (g : Graph)
    (valid : checkGraphRoundTrip dict g = true) :
    (encodeGraph? dict g).bind (decodeGraph? dict) = some g := by
  unfold checkGraphRoundTrip at valid
  exact decide_eq_true_eq.mp valid

def checkBindingRoundTrip (dict : Dictionary) (b : L4Factoidal.SPARQL.Binding) : Bool :=
  decide ((encodeBinding? dict b).bind (decodeBinding? dict) = some b)

theorem checkBindingRoundTrip_sound (dict : Dictionary) (b : L4Factoidal.SPARQL.Binding)
    (valid : checkBindingRoundTrip dict b = true) :
    (encodeBinding? dict b).bind (decodeBinding? dict) = some b := by
  unfold checkBindingRoundTrip at valid
  exact decide_eq_true_eq.mp valid

/-- Two distinct IRIs are a minimal counterexample to an identity-code
    collision; a join may additionally need equality classes. -/
private def a : WfIri := ⟨"http://example.org/a", by decide⟩
private def b : WfIri := ⟨"http://example.org/b", by decide⟩
private def good : Dictionary :=
  [{term := .iri a, identity := 1, equality := 10},
   {term := .iri b, identity := 2, equality := 11}]
private def bad : Dictionary :=
  [{term := .iri a, identity := 1, equality := 10},
   {term := .iri b, identity := 1, equality := 10}]

#guard admit good [.iri a, .iri b]
#guard !(admit bad [.iri a, .iri b])
#guard checkGraphRoundTrip good
  [{s := .iri a, p := a, o := .iri b}]
#guard checkBindingRoundTrip good [("x", Term.iri a), ("x", Term.iri b)]

#print axioms admitted_identity
#print axioms admitted_equality
#print axioms checkGraphRoundTrip_sound
#print axioms checkBindingRoundTrip_sound

end L4Factoidal.GpuDomainSpecificLanguage.RdfDualCodec
