import L4Factoidal.GpuDomainSpecificLanguage.RdfTermCodebook
import L4Factoidal.SPARQL.Algebra

/-!
# A canonical RDF term codebook for GSSL

Factoidal's RDF term representation is canonical. In particular,
`RDF.Term.eqb_iff_eq` proves that the engine's comparison relation
agrees with structural equality on well-formed RDF terms. A *single*
injective UInt32 ID therefore serves both faithful round-trip decoding
and equality joins for the finite admitted term scope.

The executable admission check validates exact term round trips; a
Lean theorem derives all engine-equality comparison guarantees without
running an extra quadratic all-pairs check. Graph and binding round trips preserve
all term constructors and the exact association-list binding order.

This is a pure finite model, not a physical device, WGSL compiler,
snapshot identity or byte-level serialization proof.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.RdfCanonicalCodec

open L4Factoidal.RDF

structure Entry where
  term : Term
  identity : UInt32
  deriving Repr

abbrev Dictionary := List Entry

/-- Look up the structurally *exact* RDF term. This is intentionally more
    discriminating than engine equality, because the decoder is lossless. -/
def lookup? (dict : Dictionary) (term : Term) : Option Entry :=
  dict.find? (fun entry => decide (entry.term = term))

def identityCode? (dict : Dictionary) (term : Term) : Option UInt32 :=
  (lookup? dict term).map (·.identity)

/-- One canonical identity code also represents Factoidal engine equality. -/
def equalityCode? (dict : Dictionary) (term : Term) : Option UInt32 :=
  identityCode? dict term

/-- Decode by identity code. Duplicate codes are rejected when the
    finite-scope round-trip admission check is applied. -/
def decodeTerm? (dict : Dictionary) (identity : UInt32) : Option Term :=
  (dict.find? fun entry => entry.identity == identity).map (·.term)

def identityRoundTrip (dict : Dictionary) (term : Term) : Bool :=
  decide ((identityCode? dict term).bind (decodeTerm? dict) = some term)

/-- An optional executable comparison diagnostic. The theorem below proves
    this agreement from successful identity round trips, so it is not needed
    in the admission loop. -/
def matchAgreement (dict : Dictionary) (a b : Term) : Bool :=
  match equalityCode? dict a, equalityCode? dict b with
  | some ac, some bc => ((ac == bc) == a.eqb b)
  | _, _ => false

/-- O(n) dictionary lookup checks across admitted terms, not an O(n²)
    all-pairs equivalence scan. The engine's canonicality theorem lets us
    derive agreement of all equality comparisons from these round trips. -/
def admit (dict : Dictionary) (scope : List Term) : Bool :=
  scope.all (identityRoundTrip dict)

theorem admitted_identity (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (term : Term) (ht : term ∈ scope) :
    (identityCode? dict term).bind (decodeTerm? dict) = some term := by
  have h := List.all_eq_true.mp valid term ht
  unfold identityRoundTrip at h
  exact decide_eq_true_eq.mp h

private theorem admitted_code (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (term : Term) (ht : term ∈ scope) :
    ∃ code, identityCode? dict term = some code ∧
      decodeTerm? dict code = some term := by
  have h := admitted_identity dict scope valid term ht
  cases hc : identityCode? dict term with
  | none => simp [hc] at h
  | some code =>
      refine ⟨code, rfl, ?_⟩
      simpa [hc] using h

/-- Injectivity of the finite *admitted* identity codebook. -/
theorem admitted_code_eq_iff (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (a b : Term)
    (ha : a ∈ scope) (hb : b ∈ scope) (ac bc : UInt32)
    (hca : identityCode? dict a = some ac)
    (hcb : identityCode? dict b = some bc) :
    ac = bc ↔ a = b := by
  have da : decodeTerm? dict ac = some a := by
    have h := admitted_identity dict scope valid a ha
    simpa [hca] using h
  have db : decodeTerm? dict bc = some b := by
    have h := admitted_identity dict scope valid b hb
    simpa [hcb] using h
  constructor
  · intro heq
    have both : some a = some b := by
      calc
        some a = decodeTerm? dict ac := da.symm
        _ = decodeTerm? dict bc := by rw [heq]
        _ = some b := db
    exact Option.some.inj both
  · intro heq
    cases heq
    exact Option.some.inj (hca.symm.trans hcb)

/-- Because RDF.Term is canonical, its engine eqb coincides with Eq.
    The one identity ID also preserves SPARQL join-key comparisons. -/
theorem admitted_eqb_for_codes (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (a b : Term)
    (ha : a ∈ scope) (hb : b ∈ scope) (ac bc : UInt32)
    (hca : identityCode? dict a = some ac)
    (hcb : identityCode? dict b = some bc) :
    (ac == bc) = a.eqb b := by
  have equiv := admitted_code_eq_iff dict scope valid a b ha hb ac bc hca hcb
  by_cases h : ac = bc
  · have ht : a = b := equiv.mp h
    have hcode : (ac == bc) = true := beq_iff_eq.mpr h
    have hterm : a.eqb b = true := (Term.eqb_iff_eq a b).mpr ht
    rw [hcode, hterm]
  · have ht : a ≠ b := fun hab => h (equiv.mpr hab)
    have hcode : (ac == bc) = false := by
      cases hcase : (ac == bc) with
      | false => rfl
      | true => exact False.elim (h (beq_iff_eq.mp hcase))
    have hterm : a.eqb b = false := by
      cases hcase : a.eqb b with
      | false => rfl
      | true => exact False.elim (ht ((Term.eqb_iff_eq a b).mp hcase))
    rw [hcode, hterm]

theorem admitted_equality (dict : Dictionary) (scope : List Term)
    (valid : admit dict scope = true) (a b : Term)
    (ha : a ∈ scope) (hb : b ∈ scope) :
    ∃ ac bc, equalityCode? dict a = some ac ∧
      equalityCode? dict b = some bc ∧
      (ac == bc) = a.eqb b := by
  obtain ⟨ac, hca, _⟩ := admitted_code dict scope valid a ha
  obtain ⟨bc, hcb, _⟩ := admitted_code dict scope valid b hb
  exact ⟨ac, bc, hca, hcb,
    admitted_eqb_for_codes dict scope valid a b ha hb ac bc hca hcb⟩

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
    collision; the same code is used for equality joins. -/
private def a : WfIri := ⟨"http://example.org/a", by decide⟩
private def b : WfIri := ⟨"http://example.org/b", by decide⟩
private def good : Dictionary :=
  [{term := .iri a, identity := 1},
   {term := .iri b, identity := 2}]
private def bad : Dictionary :=
  [{term := .iri a, identity := 1},
   {term := .iri b, identity := 1}]

#guard admit good [.iri a, .iri b]
#guard !(admit bad [.iri a, .iri b])
#guard checkGraphRoundTrip good
  [{s := .iri a, p := a, o := .iri b}]
#guard checkBindingRoundTrip good [("x", Term.iri a), ("x", Term.iri b)]

#print axioms admitted_identity
#print axioms admitted_code_eq_iff
#print axioms admitted_eqb_for_codes
#print axioms admitted_equality
#print axioms checkGraphRoundTrip_sound
#print axioms checkBindingRoundTrip_sound

end L4Factoidal.GpuDomainSpecificLanguage.RdfCanonicalCodec
