import L4Factoidal.SPARQL.GsslBgpRefinement
import L4Factoidal.GpuDomainSpecificLanguage.RdfTermCodebook

/-!
# Exact SPARQL BGP refinement for equality-coded GSSL relations

This links three independently defined models:
1. Factoidal's actual RDF/SPARQL indexed BGP evaluator.
2. A pair of independently selected RDF relations joined in graph order.
3. The generic GSSL equality-coded join, admitted by a finite comparison
   check using *RDF engine term equality*.

No WGSL, GPU device or host result appears in this theorem. The integer-code
interpretation is a pure model with untouched RDF Binding payloads.
Term payload serialization, request snapshot identity, a verified kernel
lowering and physical execution remain distinct obligations.
-/
namespace L4Factoidal.SPARQL.GsslEncodedBgpRefinement

open L4Factoidal.RDF
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.SPARQL.GsslBgpRefinement
open L4Factoidal.SPARQL.SharedSubjectTripleRefinement
open L4Factoidal.SPARQL.SharedSubjectTriple

/-- Actual binding layout used by the engine for the first pattern. -/
def leftBinding (person colleague : VarName) (t : Triple) : Binding :=
  [(colleague, t.o), (person, t.s.toTerm)]

/-- First independently selected relation. The left key is the RDF object. -/
def leftRows (person colleague : VarName) (knows : WfIri)
    (graph : Graph) : List (RdfTermCodebook.Key × Binding) :=
  (predicateFragment knows graph).map fun t =>
    (⟨t.o⟩, leftBinding person colleague t)

/-- Right selection applies RDF subject/predicate/object constraints before
    joining; no nonmatching triples enter the right relation. -/
def rightRow (works object : WfIri) (t : Triple) :
    Option (RdfTermCodebook.Key × Unit) :=
  if works == t.p then
    match t.o with
    | .iri actual =>
        if object == actual then some (⟨t.s.toTerm⟩, ()) else none
    | _ => none
  else none

def rightRows (works object : WfIri)
    (graph : Graph) : List (RdfTermCodebook.Key × Unit) :=
  graph.filterMap (rightRow works object)

/-- Result of joining independently selected RDF relations. The Unit on
    the right records each matching right triple's multiplicity. -/
def rdfJoin (person colleague : VarName) (knows works object : WfIri)
    (graph : Graph) : SolutionSeq :=
  (EncodedJoin.joinRows
    (leftRows person colleague knows graph)
    (rightRows works object graph)).map Prod.fst

@[simp] private theorem rdfKey_beq (a b : Term) :
    ((⟨a⟩ : RdfTermCodebook.Key) == (⟨b⟩ : RdfTermCodebook.Key)) = a.eqb b := rfl

private theorem rightRow_matches_engine (colleague : VarName)
    (works object : WfIri) (binding : Binding) (key : Term)
    (bound : binding.lookup colleague = some key) (t : Triple) :
    ((rightRow works object t).bind fun r =>
      if ((⟨key⟩ : RdfTermCodebook.Key) == r.1)
        then some binding else none) =
    rightMatch colleague works object binding t := by
  unfold rightRow rightMatch
  simp only [bound]
  cases hk : key.eqb t.s.toTerm <;>
    cases hp : works == t.p <;>
    cases t.o <;>
    simp_all [rdfKey_beq]
  all_goals
    split <;> simp_all [rdfKey_beq]

/-- Stable right-side selection of a graph is equivalent to the engine's
    second-pattern matcher when its join variable is already bound. -/
private theorem rowJoin_eq_rightSelect (colleague : VarName)
    (works object : WfIri) (graph : Graph)
    (binding : Binding) (key : Term)
    (bound : binding.lookup colleague = some key) :
    (EncodedJoin.rowMatches (⟨key⟩, binding) (rightRows works object graph)).map Prod.fst =
      rightSelect colleague works object graph binding := by
  induction graph with
  | nil => rfl
  | cons t rest ih =>
      have hmatch := rightRow_matches_engine colleague works object binding key bound t
      cases hr : rightRow works object t with
      | none =>
          have he : rightMatch colleague works object binding t = none := by
            simpa [hr] using hmatch.symm
          simpa [rightRows, EncodedJoin.rowMatches, rightSelect, hr, he] using ih
      | some r =>
          cases hk : ((⟨key⟩ : RdfTermCodebook.Key) == r.1) with
          | false =>
              have he : rightMatch colleague works object binding t = none := by
                simpa [hr, hk] using hmatch.symm
              simpa [rightRows, EncodedJoin.rowMatches, rightSelect, hr, hk, he] using ih
          | true =>
              have he : rightMatch colleague works object binding t = some binding := by
                simpa [hr, hk] using hmatch.symm
              simpa [rightRows, EncodedJoin.rowMatches, rightSelect, hr, hk, he]
                using congrArg (List.cons binding) ih

private theorem joinLeft_eq_select (person colleague : VarName)
    (works object : WfIri) (graph : Graph) :
    ∀ left : List Triple,
      (EncodedJoin.joinRows
        (left.map fun t => (⟨t.o⟩, leftBinding person colleague t))
        (rightRows works object graph)).map Prod.fst =
      left.flatMap (fun t => rightSelect colleague works object graph
        (leftBinding person colleague t)) := by
  intro left
  induction left with
  | nil => rfl
  | cons t rest ih =>
      have bound : (leftBinding person colleague t).lookup colleague = some t.o := by
        simp [leftBinding, Binding.lookup]
      have row := rowJoin_eq_rightSelect colleague works object graph
        (leftBinding person colleague t) t.o bound
      calc
        (EncodedJoin.joinRows
          ((t :: rest).map fun u => (⟨u.o⟩, leftBinding person colleague u))
          (rightRows works object graph)).map Prod.fst =
          (EncodedJoin.rowMatches (⟨t.o⟩, leftBinding person colleague t)
            (rightRows works object graph)).map Prod.fst ++
          (EncodedJoin.joinRows
            (rest.map fun u => (⟨u.o⟩, leftBinding person colleague u))
            (rightRows works object graph)).map Prod.fst := by
              simp [EncodedJoin.joinRows, List.map_append]
        _ = rightSelect colleague works object graph (leftBinding person colleague t) ++
            (EncodedJoin.joinRows
              (rest.map fun u => (⟨u.o⟩, leftBinding person colleague u))
              (rightRows works object graph)).map Prod.fst := by rw [row]
        _ = rightSelect colleague works object graph (leftBinding person colleague t) ++
            rest.flatMap (fun u => rightSelect colleague works object graph
              (leftBinding person colleague u)) := by rw [ih]
        _ = (t :: rest).flatMap (fun u => rightSelect colleague works object graph
              (leftBinding person colleague u)) := by rfl

/-- The GSSL RDF relations reproduce the exact engine-side ordered right
    selection and left-major solution sequence, including multiplicity. -/
theorem rdfJoin_eq_relationalPlan (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph) :
    rdfJoin person colleague knows works object graph =
    relationalPlan person colleague knows works object graph := by
  unfold rdfJoin leftRows relationalPlan
  exact joinLeft_eq_select person colleague works object graph
    (predicateFragment knows graph)

/-- Pure integer-key interpretation of the same two relations; RDF bindings
    are retained as Lean payloads. A real GPU interface still needs a payload
    layout and round-trip theorem. -/
def encodedJoin (code : Term → UInt32) (person colleague : VarName)
    (knows works object : WfIri) (graph : Graph) : SolutionSeq :=
  (EncodedJoin.joinRows
    ((leftRows person colleague knows graph).map fun l => (code l.1.term, l.2))
    ((rightRows works object graph).map fun r => (code r.1.term, r.2))).map Prod.fst

/-- A finite, checked RDF term codebook is sufficient to preserve the exact
    indexed-engine BGP semantics for the admitted two-pattern shape.

    The proof is unconditional once the *executable* admission check accepts.
    This is a source-level integer join theorem, not a shader proof. -/
theorem encodedJoin_eq_evalBgpIdx (code : Term → UInt32)
    (person colleague : VarName) (knows works object : WfIri)
    (graph : Graph) (different : person ≠ colleague)
    (valid : RdfTermCodebook.check code
      (leftRows person colleague knows graph)
      (rightRows works object graph) = true) :
    encodedJoin code person colleague knows works object graph =
    evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩] graph := by
  calc
    encodedJoin code person colleague knows works object graph =
      rdfJoin person colleague knows works object graph := by
        unfold encodedJoin rdfJoin
        exact congrArg (List.map Prod.fst)
          (RdfTermCodebook.join_eq_of_check code _ _ valid)
    _ = relationalPlan person colleague knows works object graph :=
      rdfJoin_eq_relationalPlan person colleague knows works object graph
    _ = evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
        ⟨.var colleague, .iri works, .iri object⟩] graph :=
      relationalPlan_eq_evalBgpIdx person colleague knows works object graph different

#print axioms rdfJoin_eq_relationalPlan
#print axioms encodedJoin_eq_evalBgpIdx

end L4Factoidal.SPARQL.GsslEncodedBgpRefinement
