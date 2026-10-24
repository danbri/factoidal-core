/-
L4Factoidal.Dataflow.Reasoner — the interface type of a reasoner
(https://github.com/danbri/factoidal/issues/975, "Architecture acceptance",
item 2, kind REASONER).

## The contract

A reasoner maps a graph to a graph. `Regime` names the entailment regime it
declares: ρdf, RDFS with a datatype list `D`, or OWL 2 RL. `Regime.Entails`
gives, for each regime, the entailment relation of the FOUNDATION:

* `rhoDf`: `RhoDfEntails` (`RDFS/RhoDfCompleteness.lean`);
* `rdfs D`: `RdfsEntails` (`RDF/EntailmentRdfsModelTheory.lean`, RDF 1.1
  Semantics section 9);
* `owlRl`: `OwlRlEntails`: each output triple is derivable by the OWL 2 RL/RDF
  rules (`OWL.RL.Derives`) and, for an input without the reserved helper IRIs,
  true in every interpretation that meets the row conditions
  (`OWL/RLSemantics.lean`).

## The interface type

`SoundReasoner` holds a regime, a total `run : Graph → Graph`, and
`sound : ∀ g, regime.Entails g (run g)`. So a value cannot exist without the
soundness proof.

Completeness is a statement, not a field with a proof. `CompleteStatement reg
run` says: for every graph `g` and every triple-term-free graph `e`, if `g`
entails `e` in the regime then `e` is simply entailed by `run g`
(`SimpleEntailmentSpec`, RDF 1.1 Semantics section 5.2). The field
`assumed_completeness` is a named assumption in the style of `IOStage`: a
`Prop` that the value does NOT prove (`completeness_stmt` fixes which
statement it is). A consumer that needs completeness takes
`r.assumed_completeness` as a hypothesis. Where completeness is proved, it is
a theorem beside the instance: `rhoDfReasoner_complete` (ρdf, when the closure
is closed and in the ρdf model fragment).

## The shipped reasoners

* `rhoDfReasoner`: `RDFS.closureFix` (the `rhoDfClosure` wasm op).
* `rdfsReasoner D`: `RDFS.fullClosure D (cmpSlice g) g`, with `cmpSlice` the
  `rdf:_n` slice the graph mentions. `cmpSlice_member` proves the slice is
  made of `rdf:_n` IRIs, which `fullClosure_entails` needs; before this module
  that fact was stated as "by construction" and not proved.
* `owlRlReasoner`: `Graph.toSet (OWL.RL.closureFix g)`.

The `@[csimp]` modules (`RDFS.Closure`, `RDFS.FullClosure`,
`OWL.RLClosureIndexed`) are imported so that the compiled run is the indexed
closure.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.EntailmentRegimeSoundness
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.OWL.RLClosure
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.OWL.RLSemantics
import L4Factoidal.RDF.GraphOpsSet

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF

/-! ## The `rdf:_n` slice -/

/-- The `rdf:_n` slice of a graph: `rdf:_1` plus the container-membership IRIs
the graph mentions, without repeats. -/
def cmpSlice (g : Graph) : List WfIri :=
  (RDFS.containerMembershipIn g).foldl
    (fun acc i => if acc.contains i then acc else acc ++ [i])
    [RDFS.rdf1]

theorem memberStr_prefix : RDFS.rdfNs ++ "_" = "http://www.w3.org/1999/02/22-rdf-syntax-ns#_" := by
  decide

theorem isContainerMembershipIri_member (s : String)
    (h : RDFS.isContainerMembershipIri s = true) : ∃ n, s = rdfMemberIriStr n := by
  unfold RDFS.isContainerMembershipIri at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, _⟩ := h
  obtain ⟨t, ht⟩ := String.startsWith_string_iff.mp h1
  refine ⟨String.ofList t, ?_⟩
  unfold rdfMemberIriStr
  rw [← memberStr_prefix]
  apply String.toList_injective
  rw [← ht]
  simp only [String.toList_append, String.toList_ofList]

theorem cmpOfIri_member {i c : WfIri} (h : c ∈ RDFS.cmpOfIri i) : IsRdfMemberIri c := by
  unfold RDFS.cmpOfIri at h
  split at h
  · rename_i hc
    have : c = i := by simpa using h
    subst this
    exact isContainerMembershipIri_member _ hc
  · cases h

theorem cmpOfSubject_member {s : Subject} {c : WfIri} (h : c ∈ RDFS.cmpOfSubject s) :
    IsRdfMemberIri c := by
  cases s with
  | iri i => exact cmpOfIri_member h
  | bnode _ => cases h

theorem cmpOfTerm_member : ∀ {o : Term} {c : WfIri}, c ∈ RDFS.cmpOfTerm o → IsRdfMemberIri c
  | .iri i, c, h => cmpOfIri_member h
  | .bnode _, c, h => by cases h
  | .literal _, c, h => by cases h
  | .tripleTerm s p o, c, h => by
    simp only [RDFS.cmpOfTerm, List.mem_append] at h
    rcases h with (h | h) | h
    · exact cmpOfSubject_member h
    · exact cmpOfIri_member h
    · exact cmpOfTerm_member h

theorem foldl_dedupe_mem (l : List WfIri) (init : List WfIri) {c : WfIri} :
    c ∈ l.foldl (fun acc i => if acc.contains i then acc else acc ++ [i]) init →
      c ∈ init ∨ c ∈ l := by
  induction l generalizing init with
  | nil => intro h; exact Or.inl h
  | cons x xs ih =>
    intro h
    simp only [List.foldl_cons] at h
    split at h
    · rcases ih _ h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih _ h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp at h; subst h; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **The `rdf:_n` slice is made of `rdf:_n` IRIs.** -/
theorem cmpSlice_member (g : Graph) : ∀ c ∈ cmpSlice g, IsRdfMemberIri c := by
  intro c hc
  unfold cmpSlice at hc
  rcases foldl_dedupe_mem _ _ hc with h | h
  · have : c = RDFS.rdf1 := by simpa using h
    subst this
    exact ⟨"1", by decide⟩
  · unfold RDFS.containerMembershipIn at h
    rcases foldl_dedupe_mem _ _ h with h | h
    · cases h
    · obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp h
      simp only [List.mem_append] at ht
      rcases ht with (ht | ht) | ht
      · exact cmpOfSubject_member ht
      · exact cmpOfIri_member ht
      · exact cmpOfTerm_member ht

/-! ## Regimes -/

open L4Factoidal.OWL.RL in
/-- The OWL 2 RL entailment of the FOUNDATION as the engine proves it: each
output triple is derivable by the OWL 2 RL/RDF rules from the input and, for an
input without the reserved helper IRIs, true in every interpretation that meets
the row conditions. -/
def OwlRlEntails (g c : Graph) : Prop :=
  ∀ t ∈ c, Derives g t ∧ (RlReservedFree g → ∀ (i : Interp),
    RlConditions i → ∀ A : BnodeAssignment i.idom, HoldsAll i A g →
      TripleHolds i (rlExtend i A) t)

/-- The entailment regime a reasoner declares. -/
inductive Regime where
  | rhoDf
  | rdfs (D : List WfIri)
  | owlRl

/-- The entailment relation of the regime, from the FOUNDATION. -/
def Regime.Entails : Regime → Graph → Graph → Prop
  | .rhoDf => RhoDfEntails
  | .rdfs D => RdfsEntails (fun x => x ∈ D)
  | .owlRl => OwlRlEntails

/-- Completeness of a reasoner, as a statement: every triple-term-free graph
that the regime entails from `g` is simply entailed by the output (RDF 1.1
Semantics section 5.2). -/
def CompleteStatement (reg : Regime) (run : Graph → Graph) : Prop :=
  ∀ g e, GraphTtFree e → reg.Entails g e → SimpleEntailmentSpec (run g) e

/-! ## The interface type -/

/-- **A reasoner, with soundness against its regime as a field.** -/
structure SoundReasoner where
  /-- The entailment regime. -/
  regime : Regime
  /-- The closure. -/
  run : Graph → Graph
  /-- Every output is entailed by the input in the regime. -/
  sound : ∀ g, regime.Entails g (run g)
  /-- NAMED ASSUMPTION: completeness. Not proved by this value. -/
  assumed_completeness : Prop
  /-- Which statement `assumed_completeness` is. -/
  completeness_stmt : assumed_completeness = CompleteStatement regime run

/-! ## The shipped reasoners -/

/-- ρdf: `RDFS.closureFix`. -/
def rhoDfReasoner : SoundReasoner where
  regime := .rhoDf
  run := RDFS.closureFix
  sound g := closure_rhoDfEntails g (RDFS.closureFuelBound g)
  assumed_completeness := CompleteStatement .rhoDf RDFS.closureFix
  completeness_stmt := rfl

/-- **ρdf completeness, proved under its scope**: when the closure is closed
and in the ρdf model fragment, ρdf entailment of a triple-term-free graph is
simple entailment from the closure. The scope is a property of the closure, so
`assumed_completeness` (every graph) stays open. -/
theorem rhoDfReasoner_complete (g e : Graph) (hc : RhoDfClosed (rhoDfReasoner.run g))
    (hf : RhoDfModelFragGraph (rhoDfReasoner.run g)) (he : GraphTtFree e) :
    rhoDfReasoner.regime.Entails g e ↔ SimpleEntailmentSpec (rhoDfReasoner.run g) e :=
  closure_rhoDf_iff (RDFS.closureFuelBound g) hc hf he

/-- RDFS (RDF 1.1 Semantics section 9) for the datatype list `D`:
`RDFS.fullClosure` with the graph's own `rdf:_n` slice. -/
def rdfsReasoner (D : List WfIri) : SoundReasoner where
  regime := .rdfs D
  run g := RDFS.fullClosure D (cmpSlice g) g
  sound g := fullClosure_entails D (cmpSlice g) (cmpSlice_member g) g
  assumed_completeness := CompleteStatement (.rdfs D) (fun g => RDFS.fullClosure D (cmpSlice g) g)
  completeness_stmt := rfl

/-- OWL 2 RL: the closure as a set of triples. `OWL.RL.closureFix` adds by
structural equality, so `Graph.toSet` keeps the first of two spellings of one
triple (https://github.com/danbri/factoidal/issues/973). -/
def owlRlReasoner : SoundReasoner where
  regime := .owlRl
  run g := Graph.toSet (OWL.RL.closureFix g)
  sound g t ht :=
    have ht' := Graph.toSet_sublist _ t ht
    ⟨OWL.RL.closure_sound _ g ht', fun hres _ hc _ hA =>
      OWL.RL.rl_derives_holds hc hres hA (OWL.RL.closure_sound _ g ht')⟩
  assumed_completeness := CompleteStatement .owlRl (fun g => Graph.toSet (OWL.RL.closureFix g))
  completeness_stmt := rfl

/-- The reasoners that ship. -/
def shippedReasoners : List SoundReasoner :=
  [rhoDfReasoner, rdfsReasoner (withMinimalD []), owlRlReasoner]

#print axioms cmpSlice_member
#print axioms rhoDfReasoner
#print axioms rhoDfReasoner_complete
#print axioms rdfsReasoner
#print axioms owlRlReasoner

end L4Factoidal.Dataflow
