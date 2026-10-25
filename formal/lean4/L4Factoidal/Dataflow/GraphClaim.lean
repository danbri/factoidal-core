/-
L4Factoidal.Dataflow.GraphClaim — the RDFS claim about a DESCRIPTION, a graph
with shared blank nodes (https://github.com/danbri/factoidal/issues/1002,
first step).

## The claim

"Description `E` is RDFS-entailed by sources `S`": `RdfsEntails (· ∈ D) S E`
(RDF 1.1 Semantics section 9.2, over the interpretations of
`RDF/EntailmentRdfsModelTheory.lean`). The blank nodes of `E` are existential:
`Satisfies i E` asks for SOME assignment of them (section 5.1, "[I+A](E)").
A single triple is the case `E = [t]`.

The witness of the claim is an INSTANCE of `E` (section 5.3, Interpolation
Lemma: "G simply entails a graph E if and only if a subgraph of G is an
instance of E"), here taken over the RDFS derivations from `S` instead of over
`S`: a mapping `M` of the blank nodes of `E` to terms such that each triple of
`E`, with its blank nodes replaced by `M`, is `DerivesFull`-derivable from `S`
and the RDFS axiomatic triples. ONE mapping serves all triples of `E`, so a
blank node that two triples share is mapped to one term.
`rdfsEntails_of_derivable_instance` proves that this gives `S ⊨rdfs E`; it is
the sound direction of the interpolation lemma composed with the soundness of
the RDFS rows (`derivesFull_holds`).

## Why not one FPP0 bundle per triple

An FPP0 claim `rdfDerivable gd ad t` names ONE triple, and the kernel's
theorem gives `∃ s, … (t.scoped s)`: the blank-node scope is existential per
bundle (`FPP0.checkBundle_merge`). Two such bundles for two triples of `E`
that share a blank node of `S` may read that node in two scopes, so the
conjunction of the two theorems does not give the description. The graph
bundle below has one derivation and one mapping for the whole description.

## Scopes

`S` and `E` are graphs as given. A caller that reads them from documents
scopes the blank nodes of each document by its scope number
(`Dataset.scopeDocument`, `RDF/DocumentScope.lean`), so the sources are a
section 4.1 merge and a label in `E` is never a label of `S`. The entailment
statement does not need that: the blank nodes of `E` are bound by the
existential of `Satisfies`, whatever their labels.

## The bundle and the checker

`GraphBundle`: the sources, the description, the instance mapping (a finite
list of pairs), an RDFS `Derivation` over the sources, and for each triple of
the description the index of the step that concludes its instance.
`checkGraphRun D b` accepts when `RDFS.checkDerivation` accepts the derivation
with the axiom set `axiomaticTriples D (graphCmps …)` (computed by the
checker from the bundle, not read from it), the support has one index per
description triple, and each indexed step concludes the instance.
`checkGraphRun_sound`: accept implies `RdfsEntails (· ∈ D) S E`. No
hypothesis of the theorem mentions entailment.

## The search, and what a negative answer means

`findInstance cl E` runs the simple-entailment search of
`RDF/Entailment.lean` (`searchInstance`, backtracking, first solution) over
`cl`. `findInstance_none` proves it complete: when it returns `none`, NO mapping
sends `E` into `cl` (`¬ SimpleEntailmentSpec cl E`). With `cl` the RDFS
closure, "not entailed" then needs completeness of the closure (RDF 1.1
Semantics Appendix A, for an RDFS-consistent `S`), which this tree does not
prove (`SoundReasoner.assumed_completeness`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Reasoner
import L4Factoidal.RDFS.DerivationCheck
import L4Factoidal.RDF.EntailmentSimpleRefinement

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-! ## Instance mappings as finite lists -/

/-- A finite instance mapping: pairs of a blank-node label of the description
and the term it is replaced by. -/
abbrev InstanceMapping := Mapping

/-- The total substitution of a finite mapping: an unmapped label stays its
own blank node (`Mapping.toFun`). -/
def InstanceMapping.subst (m : InstanceMapping) : BnodeSubst := Mapping.toFun m

/-! ## RDFS entailment of a description from a derivable instance -/

/-- **RDFS entailment of a description from a derivable instance** (RDF 1.1
Semantics section 5.3, Interpolation Lemma, sound direction, composed with
section 9.2). If one mapping `M` sends every triple of `E` to a triple that is
`DerivesFull`-derivable from `S` and the RDFS axiomatic triples, then `S`
RDFS-entails `E`. -/
theorem rdfsEntails_of_derivable_instance (D cmps : List WfIri)
    (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) {S E : Graph} (M : BnodeSubst)
    (h : ∀ e ∈ E, ∃ t, DerivesFull (axiomaticTriples D cmps) S t ∧ TripleInst M e t) :
    RdfsEntails (fun x => x ∈ D) S E := by
  intro i hc hs
  obtain ⟨a, ha⟩ := hs
  have hc' := hc
  obtain ⟨⟨_, hrdfax⟩, _, _, hdt, _, _, _, _, _, _, _, _, _, _, _, _, _, hrdfsax⟩ := hc'
  refine ⟨composedAssignment i a M, fun e he => ?_⟩
  obtain ⟨t, hd, hinst⟩ := h e he
  exact subst_triple_holds i a M hinst
    (derivesFull_holds hc (axiomaticTriples_hold a D cmps hcmps hrdfax hrdfsax hdt) ha hd)

/-! ## The graph bundle -/

/-- The evidence for "description `description` is RDFS-entailed by
`sources`". -/
structure GraphBundle where
  sources : Graph
  description : Graph
  mapping : InstanceMapping
  witness : Derivation
  /-- For the `i`-th description triple, the index of the step of `witness`
  that concludes its instance. -/
  support : List Nat

/-- The claim a graph bundle supports. -/
structure GraphClaim where
  sources : Graph
  description : Graph
  deriving DecidableEq, Repr

/-- The `rdf:_n` slice of the axiom set: the membership IRIs of the sources and
of the description (`cmpSlice`). The checker computes it. -/
def graphCmps (sources description : Graph) : List WfIri := cmpSlice (sources ++ description)

/-- The axiom set the checker uses. -/
def GraphBundle.axioms (D : List WfIri) (b : GraphBundle) : Graph :=
  axiomaticTriples D (graphCmps b.sources b.description)

/-- The step `k` concludes the instance of `d` under the mapping. -/
def GraphBundle.instanceOk (b : GraphBundle) (d : Triple) (k : Nat) : Bool :=
  match b.witness[k]? with
  | some st => d.instance? b.mapping.subst == some st.conclusion
  | none => false

/-- **The graph checker.** -/
def checkGraphRun (D : List WfIri) (b : GraphBundle) : Except String GraphClaim :=
  if !checkDerivation (b.axioms D) b.sources b.witness then
    .error "the RDFS derivation is refused (RDFS.checkDerivation)"
  else if b.support.length != b.description.length then
    .error s!"the support has {b.support.length} step indices for {b.description.length} description triples"
  else if !(b.description.zip b.support).all (fun p => b.instanceOk p.1 p.2) then
    .error s!"description triple {(b.description.zip b.support).findIdx (fun p => !b.instanceOk p.1 p.2)}: the cited step does not conclude its instance under the mapping"
  else .ok ⟨b.sources, b.description⟩

/-- Accept means: the claim is the bundle's, and the sources RDFS-entail the
description. -/
def GraphCheckContract (D : List WfIri) (b : GraphBundle) (c : GraphClaim) : Prop :=
  c.sources = b.sources ∧ c.description = b.description ∧
    RdfsEntails (fun x => x ∈ D) c.sources c.description

theorem exists_mem_zip_of_length_eq {α β : Type} :
    ∀ {l1 : List α} {l2 : List β}, l2.length = l1.length → ∀ a ∈ l1, ∃ b, (a, b) ∈ l1.zip l2
  | [], _, _, a, h => by cases h
  | _ :: _, [], h, _, _ => by simp at h
  | x :: xs, y :: ys, h, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨y, by simp⟩
      · obtain ⟨b, hb⟩ := exists_mem_zip_of_length_eq (l2 := ys) (by simpa using h) a ha
        exact ⟨b, by simp [hb]⟩

/-- **Accept implies RDFS entailment of the description.** -/
theorem checkGraphRun_sound (D : List WfIri) (b : GraphBundle) (c : GraphClaim)
    (h : checkGraphRun D b = .ok c) : GraphCheckContract D b c := by
  unfold checkGraphRun at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  injection h with h
  subst h
  have h1' : checkDerivation (b.axioms D) b.sources b.witness = true := by simpa using h1
  have h2' : b.support.length = b.description.length := by simpa using h2
  have h3' : ∀ p ∈ b.description.zip b.support, b.instanceOk p.1 p.2 = true := by
    intro p hp
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at h3
    exact h3 p hp
  refine ⟨rfl, rfl, ?_⟩
  refine rdfsEntails_of_derivable_instance D (graphCmps b.sources b.description)
    (cmpSlice_member _) b.mapping.subst ?_
  intro e he
  obtain ⟨k, hk⟩ := exists_mem_zip_of_length_eq h2' e he
  have hok := h3' _ hk
  simp only [GraphBundle.instanceOk] at hok
  split at hok
  · rename_i st hst
    obtain ⟨hkl, hget⟩ := Array.getElem?_eq_some_iff.mp hst
    have hd := checkDerivation_sound h1' k hkl
    rw [getElem!_pos b.witness k hkl, hget] at hd
    exact ⟨st.conclusion, hd, (tripleInst_iff _ _ _).mpr (by simpa using hok)⟩
  · cases hok

/-! ## The instance search

The search is the simple-entailment search of `RDF/Entailment.lean`
(`searchInstance` with literal term equality, as `simpleEntails` runs it),
over the closure instead of over the sources. Its completeness is
`SimpleRefinement.simpleEntails_complete`. -/

/-- One mapping that sends every triple of `E` into `cl`. -/
def findInstance (cl E : Graph) : Option InstanceMapping :=
  searchInstance literalStrictEq (fun _ => true) cl E []

/-- **No mapping, when the search finds none.** -/
theorem findInstance_none {cl E : Graph} (h : findInstance cl E = none) :
    ¬ SimpleEntailmentSpec cl E := by
  intro hs
  have hc := SimpleRefinement.simpleEntails_complete ((spec_iff_simpleEntails cl E).mp hs)
  simp only [simpleEntails, entailsWith] at hc
  unfold findInstance at h
  rw [h] at hc
  cases hc

/-! ## Why a description has no instance -/

/-- No triple of `cl` is an instance of `d` alone. -/
def unmatchedIn (cl : Graph) (d : Triple) : Bool := !simpleEntails cl [d]

/-- The first description triple, from position `n`, that has no instance in
`cl` alone. -/
def firstUnmatchedFrom (cl : Graph) : Nat → List Triple → Option (Nat × Triple)
  | _, [] => none
  | n, d :: ds => if unmatchedIn cl d then some (n, d) else firstUnmatchedFrom cl (n + 1) ds

theorem firstUnmatchedFrom_spec (cl : Graph) :
    ∀ (n : Nat) (ds : List Triple) {i : Nat} {t : Triple}, firstUnmatchedFrom cl n ds = some (i, t) →
      n ≤ i ∧ ds[i - n]? = some t ∧ unmatchedIn cl t = true
  | _, [], _, _, h => by simp [firstUnmatchedFrom] at h
  | n, d :: ds, i, t, h => by
    simp only [firstUnmatchedFrom] at h
    split at h
    · rename_i hu
      injection h with h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, by simp, hu⟩
    · obtain ⟨hle, hget, hu⟩ := firstUnmatchedFrom_spec cl (n + 1) ds h
      refine ⟨by omega, ?_, hu⟩
      have : i - n = (i - (n + 1)) + 1 := by omega
      rw [this]
      simpa using hget

/-- **An unmatched triple has no instance in `cl`.** -/
theorem unmatchedIn_no_instance {cl : Graph} {d : Triple} (h : unmatchedIn cl d = true) :
    ∀ u ∈ cl, ∀ M : BnodeSubst, ¬ TripleInst M d u := by
  intro u hu M hinst
  have hs : SimpleEntailmentSpec cl [d] := ⟨M, fun tb htb => by
    rw [List.mem_singleton] at htb
    subst htb
    exact ⟨u, hu, hinst⟩⟩
  have hc := SimpleRefinement.simpleEntails_complete ((spec_iff_simpleEntails cl [d]).mp hs)
  simp [unmatchedIn, hc] at h

/-- With one triple that has no instance, the description has none. -/
theorem unmatchedIn_no_spec {cl E : Graph} {d : Triple} (hd : d ∈ E) (h : unmatchedIn cl d = true) :
    ¬ SimpleEntailmentSpec cl E := by
  rintro ⟨M, hM⟩
  obtain ⟨u, hu, hinst⟩ := hM d hd
  exact unmatchedIn_no_instance h u hu M hinst

#print axioms rdfsEntails_of_derivable_instance
#print axioms checkGraphRun_sound
#print axioms findInstance_none
#print axioms unmatchedIn_no_spec
#print axioms firstUnmatchedFrom_spec
#print axioms unmatchedIn_no_instance

end L4Factoidal.Dataflow
