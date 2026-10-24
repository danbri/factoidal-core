/-
L4Factoidal.Proof.RdfsProfile — the RDFS profile binding of the axiom set of
an FPP0 bundle (https://github.com/danbri/factoidal/issues/975, phase E).

## Finding

The FPP0 kernel (`Proof/Checker.lean`) checks an `axiomatic` leaf row against
the inline body of the axiom artifact that the step names. It does not compare
that body with the RDFS axiomatic triples (RDF 1.1 Semantics sections 8.2 and
9.3, and rdfs1). The `profile` field of a step is the string `fpp0/1`; it does
not fix an axiom set. So the kernel accepts a bundle whose axiom artifact is
any graph, also a graph with a name such as "axioms". `checkBundle_merge` is
correct for that bundle: the conclusion is derivable from the merge of the
cited axiom artifacts, whatever they hold. It does not say that the conclusion
is RDFS-entailed.

## The binding

`profileAxiomsOk ax b ad`: every artifact of `b` filed under the axiom digest
`ad` either has no body (it adds nothing to the merge) or has exactly the body
`ax`. This is a test of graph values, not of digests, so it needs no hash
assumption.

`checkBundle_rdfsEntails`: when the kernel accepts `b` with an empty frontier
and `profileAxiomsOk (axiomaticTriples D cmps) b ad` holds, the conclusion,
read in some blank-node scope, is RDFS-entailed (RDF 1.1 Semantics section 9)
by the merge of the graph artifacts filed under `gd`. The proof is
`checkBundle_merge`, then `derivesFull_holds` with `axiomaticTriples_hold`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Proof.Checker
import L4Factoidal.RDF.EntailmentRegimeSoundness

namespace L4Factoidal.FPP0

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-- Every artifact filed under the axiom digest `ad` has no body or the body
`ax`. -/
def profileAxiomsOk (ax : Graph) (b : Bundle) (ad : String) : Bool :=
  (b.artifacts.toList.filter (fun a => a.digest == ad)).all (fun a => a.body.all (fun g => g == ax))

theorem iriTriple_scoped (s : Scope) (a p c : WfIri) : (iriTriple a p c).scoped s = iriTriple a p c := by
  rfl

/-- The RDFS axiomatic triples have no blank node, so every scope leaves them
unchanged. -/
theorem axiomaticTriples_scoped (D cmps : List WfIri) (s : Scope) :
    ∀ u ∈ axiomaticTriples D cmps, u.scoped s = u := by
  intro u hu
  have h1 : (RDFS.rdfAxiomaticTriples []).all (fun u => u.isGround) = true := by decide
  have h2 : RDFS.rdfsAxiomaticTriplesFixed.all (fun u => u.isGround) = true := by decide
  have hsplit : RDFS.rdfAxiomaticTriples cmps
      = RDFS.rdfAxiomaticTriples [] ++ cmps.map (fun c => iriTriple c rdfType rdfProperty) := by
    simp [RDFS.rdfAxiomaticTriples]
  unfold RDFS.axiomaticTriples RDFS.rdfsAxiomaticTriples at hu
  rw [hsplit] at hu
  simp only [List.mem_append] at hu
  rcases hu with (h | h) | ((h | h) | h)
  · exact Triple.scoped_of_isGround s (List.all_eq_true.mp h1 u h)
  · obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
    exact iriTriple_scoped _ _ _ _
  · exact Triple.scoped_of_isGround s (List.all_eq_true.mp h2 u h)
  · obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact iriTriple_scoped _ _ _ _
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp h
    exact iriTriple_scoped _ _ _ _

/-- Under `profileAxiomsOk`, the merge of the axiom artifacts is a part of the
RDFS axiomatic triples. -/
theorem mem_mergeOf_profile {D cmps : List WfIri} {b : Bundle} {ad : String}
    (hax : profileAxiomsOk (axiomaticTriples D cmps) b ad = true) {u : Triple}
    (hu : u ∈ mergeOf b.artifacts.toList ad) : u ∈ axiomaticTriples D cmps := by
  unfold mergeOf at hu
  obtain ⟨art, hart, hub⟩ := List.mem_flatMap.mp hu
  have hall := List.all_eq_true.mp hax art hart
  unfold Artifact.scopedBody at hub
  cases hbody : art.body with
  | none => rw [hbody] at hub; cases hub
  | some g =>
    rw [hbody] at hub hall
    simp only [Option.all_some, beq_iff_eq] at hall
    subst hall
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hub
    rw [axiomaticTriples_scoped D cmps _ v hv]
    exact hv

/-- **Accepted, with the RDFS profile axioms: RDFS entailment from the merge of
the graph artifacts.** -/
theorem checkBundle_rdfsEntails (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    {b : Bundle} (h : (checkBundle b).foundationalOnly = true)
    {gd ad : String} {t : Triple} (hc : b.conclusion = Claim.rdfDerivable gd ad t)
    (hax : profileAxiomsOk (axiomaticTriples D cmps) b ad = true) :
    ∃ s : Scope, RdfsEntails (fun x => x ∈ D) (mergeOf b.artifacts.toList gd) [t.scoped s] := by
  obtain ⟨s, hd⟩ := checkBundle_merge h hc
  refine ⟨s, ?_⟩
  intro i hcond hsat
  obtain ⟨a, ha⟩ := hsat
  refine ⟨a, ?_⟩
  intro u hu
  rw [List.mem_singleton] at hu
  subst hu
  have hc' := hcond
  obtain ⟨⟨_, hrdfax⟩, _, _, hdt, _, _, _, _, _, _, _, _, _, _, _, _, _, hrdfsax⟩ := hc'
  refine derivesFull_holds hcond ?_ ha hd
  intro u hu
  exact axiomaticTriples_hold a D cmps hcmps hrdfax hrdfsax hdt u (mem_mergeOf_profile hax hu)

#print axioms axiomaticTriples_scoped
#print axioms mem_mergeOf_profile
#print axioms checkBundle_rdfsEntails

end L4Factoidal.FPP0
