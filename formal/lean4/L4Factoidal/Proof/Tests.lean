/-
L4Factoidal.Proof.Tests — the MATCHED PAIR that keeps
`checkBundle_sound` from being satisfied vacuously.

`checkBundle_sound` says: what the kernel accepts is
`Derives`-derivable from the frontier it reports. A kernel that
returned `valid = false` on every bundle would satisfy it and be
useless (`skills/measuring-inference` sections 3 and 4). So the gate
has two halves and both are mandatory:

* POSITIVE — bundles that MUST be accepted. Two shapes: a whole RDFS
  witness wrapped as an FPP0 bundle, reporting all-foundational with
  an EMPTY frontier; and a mixed bundle whose foundational RDFS step
  runs off ONE replay-level assumption, reporting exactly that one
  assumption.
* NEGATIVE — one mutation per defect, each built by changing ONE
  field of a bundle the kernel accepts, so the defect is the only
  difference between the accepted input and the rejected one.

If any negative were ACCEPTED it would be a finding about the kernel,
not a test to adjust.

Design: `docs/designissues/2026-08-26-proof-profile-fpp0-adoption.md`
sections 1, 2, 3, 8a, 8b;
`docs/designissues/2026-08-26-proof-certificate-v1.md` section 5.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Proof.Checker

namespace L4Factoidal.FPP0

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-! ## Vocabulary for the fixtures -/

private def exA : WfIri := ⟨"http://example.org/a", by rfl⟩
private def exB : WfIri := ⟨"http://example.org/b", by rfl⟩
private def exP : WfIri := ⟨"http://example.org/p", by rfl⟩
private def exZ : WfIri := ⟨"http://example.org/z", by rfl⟩

private def dataTriple : Triple := ⟨.iri exA, exP, .iri exB⟩
private def alienTriple : Triple := ⟨.iri exZ, exZ, .iri exZ⟩
private def dataGraph : Graph := [dataTriple]

/-! ## POSITIVE 1 — a whole RDFS witness, all foundational, empty frontier

`fullClosureWithProof [] [] dataGraph` is the 150-step witness (147 before
the RDF 1.2 axiomatic triples joined the seed table, 2026-10-09; 156 until the
two rdf:XMLLiteral seed rows left it, 2026-10-13)
`RDFS/DerivationCheckTests.lean` pins as accepted by
`checkDerivation`. `bundleOfRdfsDerivation` renames its positional
premises to ids and nothing else. Both graph artifacts carry inline
bodies, so the `base` and `axiomatic` leaf rows are checkable and
NOTHING enters the frontier. -/

private def dataWitness : Graph × Derivation := fullClosureWithProof [] [] dataGraph
private def dataAx : Graph := axiomaticTriples [] []

/- The conclusion the bundle ends at: the last step of the witness. -/
private def dataConcl : Triple := (dataWitness.2[dataWitness.2.size - 1]!).conclusion

private def rdfsBundle : Bundle :=
  bundleOfRdfsDerivation dataGraph dataAx dataWitness.2 dataConcl

/- The witness is the one the RDFS layer already pins. -/
#guard dataWitness.2.size = 150  -- 156 until the rdf:XMLLiteral rows left the seed table (2026-10-13, issue 767 gap 1)
#guard checkDerivation dataAx dataGraph dataWitness.2 = true

/- ACCEPTED, and the report says the chain rests on nothing. -/
#guard (checkBundle rdfsBundle).valid = true
#guard (checkBundle rdfsBundle).assumptions.size = 0
#guard (checkBundle rdfsBundle).foundationalOnly = true
#guard (checkBundle rdfsBundle).conclusionIsAssumption = false
#guard (checkBundle rdfsBundle).counts.verifiedReplay = 0
#guard (checkBundle rdfsBundle).counts.replay = 0
#guard (checkBundle rdfsBundle).counts.attestation = 0

/- The support of this conclusion is a PROPER PART of the bundle: 4
foundational steps out of 150. A count over the whole bundle would
have read 150 and would have said nothing about what the conclusion
uses. -/
#guard (checkBundle rdfsBundle).counts.foundational = 4
#guard rdfsBundle.steps.size = 150

/-! ## POSITIVE 2 — mixed: one replay assumption feeding a foundational row

The graph artifact carries NO inline body, so no leaf row is
checkable and the one leaf fact enters as a `replay` assumption:
"triple `t` holds in the graph whose RDFC-1.0 digest is this, under
this axiom set" — replayable by fetching the graph, checking its
digest and checking membership, which is exactly R and not F.

One foundational rdfs4a step then runs off it. The result reports
EXACTLY ONE remaining assumption. -/

private def mixGd : String := graphDigest dataGraph
private def mixAd : String := graphDigest dataAx

/- rdfs4a: `xxx aaa yyy .` entails `xxx rdf:type rdfs:Resource .` -/
private def mixConcl : Triple := ⟨.iri exA, rdfType, .iri rdfsResource⟩

private def mixAssumption : Assumption :=
  { id := "a1", subject := .rdfDerivable mixGd mixAd dataTriple, level := .replay }

private def mixStep : BundleStep :=
  { id := "s1"
    justification := .rule .rdfs4a "G" "AX"
    premises := ["a1"]
    conclusion := .rdfDerivable mixGd mixAd mixConcl
    level := .foundational
    profile := fpp0Profile
    citation := none }

private def mixedBundle : Bundle :=
  { artifacts :=
      #[ { id := "G",  kind := .graph, digest := mixGd, body := none },
         { id := "AX", kind := .graph, digest := mixAd, body := none } ]
    assumptions := #[mixAssumption]
    steps := #[mixStep]
    conclusion := .rdfDerivable mixGd mixAd mixConcl }

#guard (checkBundle mixedBundle).valid = true
#guard (checkBundle mixedBundle).assumptions.size = 1
#guard (checkBundle mixedBundle).assumptions[0]!.id = "a1"
#guard (checkBundle mixedBundle).assumptions[0]!.level = EvidenceLevel.replay
#guard (checkBundle mixedBundle).foundationalOnly = false
#guard (checkBundle mixedBundle).conclusionIsAssumption = false
#guard (checkBundle mixedBundle).counts.foundational = 1
#guard (checkBundle mixedBundle).counts.replay = 0

/-! ## POSITIVE 3 — an adapter step at R, promoted into the frontier

An `adapterEvidence` step is NOT a proof of its conclusion: the
kernel puts it in the frontier as a named assumption (adoption doc
section 3). Two frontier entries here — the declared assumption and
the promoted adapter step — and the R count over the support is 1. -/

private def adapterStep : BundleStep :=
  { id := "x1"
    justification := .adapterEvidence "sparql" "SELECT ?s WHERE { ?s ?p ?o }"
    premises := ["a1"]
    conclusion := .clif "(exists (v1) (answered v1))"
    level := .replay
    profile := fpp0Profile
    citation := none }

private def adapterBundle : Bundle :=
  { mixedBundle with
    steps := #[mixStep, adapterStep]
    conclusion := .clif "(exists (v1) (answered v1))" }

#guard (checkBundle adapterBundle).valid = true
#guard (checkBundle adapterBundle).assumptions.size = 2
#guard (checkBundle adapterBundle).foundationalOnly = false
#guard (checkBundle adapterBundle).counts.foundational = 0
#guard (checkBundle adapterBundle).counts.replay = 1

/-! ## The degenerate bundle (adoption doc section 8a)

`Derives assumptions conclusion` is trivially satisfiable by
declaring the conclusion as an assumption. The kernel does NOT reject
that bundle, because the theorem is TRUE of it — the assumption
constructor proves it, and a kernel that answered `false` would be
saying something false about its own soundness statement.

What the kernel does instead is report the shape, in three fields a
reader cannot miss: `conclusionIsAssumption = true`,
`foundational steps = 0`, and a frontier containing the conclusion.
Section 8a's requirement is "MUST be reported as such and never as a
proof", and this is that report. -/

private def degenerateBundle : Bundle :=
  { artifacts := #[]
    assumptions :=
      #[{ id := "a1", subject := .clif "(P jim)", level := .attestation }]
    steps := #[]
    conclusion := .clif "(P jim)" }

#guard (checkBundle degenerateBundle).valid = true
#guard (checkBundle degenerateBundle).counts.foundational = 0
#guard (checkBundle degenerateBundle).conclusionIsAssumption = true
#guard (checkBundle degenerateBundle).foundationalOnly = false
#guard (checkBundle degenerateBundle).assumptions.size = 1

/- Padding a degenerate bundle with foundational steps the conclusion
does not use does NOT raise its foundational count: the count is
taken over the SUPPORT of the conclusion. -/
private def paddedDegenerate : Bundle :=
  { degenerateBundle with
    artifacts := mixedBundle.artifacts
    assumptions := #[mixAssumption,
                     { id := "a2", subject := .clif "(P jim)", level := .attestation }]
    steps := #[mixStep]
    conclusion := .clif "(P jim)" }

#guard (checkBundle paddedDegenerate).valid = true
#guard (checkBundle paddedDegenerate).counts.foundational = 0
#guard (checkBundle paddedDegenerate).conclusionIsAssumption = true

/-! ## Mutation harness

Each negative changes ONE thing about a bundle pinned accepted
above. -/

private def withStep (b : Bundle) (i : Nat) (f : BundleStep → BundleStep) : Bundle :=
  { b with steps := (b.steps.toList.zipIdx.map
      (fun (st, j) => if j == i then f st else st)).toArray }

private def withArtifact (b : Bundle) (i : Nat) (f : Artifact → Artifact) : Bundle :=
  { b with artifacts := (b.artifacts.toList.zipIdx.map
      (fun (a, j) => if j == i then f a else a)).toArray }

/- Position of an rdfs7-style JOIN step of the RDFS bundle, located
rather than hard-coded. -/
private def joinIdx : Nat :=
  match rdfsBundle.steps.toList.findIdx?
      (fun st => st.premises.length == 2) with
  | some i => i
  | none => 0

-- Re-measured 2026-10-09 after the four RDF 1.2 axiomatic triples (rdf:reifies, rdfs:Proposition) joined the seed table
-- (49 and ["rdfs:9", "rdfs:1"] under the RDF 1.1 tables). 2026-10-13: 53 to 51, the two rdf:XMLLiteral seed rows
-- left the table (https://github.com/danbri/factoidal/issues/767 gap 1).
#guard joinIdx = 51
#guard (rdfsBundle.steps[joinIdx]!).premises = ["rdfs:10", "rdfs:1"]

/- CONTROL: the unmutated bundle is accepted. Every `false` below is
caused by its mutation and by nothing else. -/
#guard (checkBundle rdfsBundle).valid = true
#guard (checkBundle mixedBundle).valid = true

/-! ## NEGATIVE — one defect at a time -/

/- **1. Cycle in the step DAG.** Step `joinIdx` cites the step after
it, and that step cites step `joinIdx` back. Premises resolve only
against the ACCEPTED PREFIX, so at least one arm of any cycle names
something the prefix does not hold. -/
#guard (checkBundle
  (withStep (withStep rdfsBundle joinIdx
      (fun st => { st with premises := [rdfsStepId (joinIdx + 1), "rdfs:1"] }))
    (joinIdx + 1) (fun st => { st with premises := [rdfsStepId joinIdx] }))).valid = false

/- **2. Self-justification** — a step citing its own conclusion. -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with premises := [rdfsStepId joinIdx, "rdfs:1"] }))).valid = false

/- **3. A premise that is not an earlier step** — a forward
reference. -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with premises := [rdfsStepId (joinIdx + 30), "rdfs:1"] }))).valid = false

/- **4. A premise that names nothing at all.** -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with premises := ["nosuchstep", "rdfs:1"] }))).valid = false

/- **5. Missing artifact reference** — the step names a graph
artifact the table does not hold. -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with justification := .rule .rdfs7 "NOSUCH" "AX" }))).valid = false

/- **6. Wrong digest** — the graph artifact's digest is altered, so
it no longer agrees with the inline body it is filed under, and no
longer matches the digest the claims name. -/
#guard (checkBundle (withArtifact rdfsBundle 0
  (fun a => { a with digest := "0000000000000000000000000000000000000000000000000000000000000000" }))).valid
  = false

/- **7. An inline body swapped for a different graph**, digest
untouched — the same rejection from the other side. -/
#guard (checkBundle (withArtifact rdfsBundle 0
  (fun a => { a with body := some [alienTriple] }))).valid = false

/- **8. A rule row cited where it licenses nothing.** `RuleId` is a
closed inductive, so a rule name the kernel does not know cannot be
built — the type rejects it before the kernel sees it, exactly as
`RDFS/DerivationCheckTests.lean` records for its own layer. What CAN
be built is a REAL row cited over premises it does not apply to. -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with justification := .rule .rdfs11 "G" "AX" }))).valid = false

/- **9. A join row cited with the wrong number of premises.** -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with premises := ["rdfs:9"] }))).valid = false

/- **10. Duplicate artifact id.** -/
#guard (checkBundle
  { rdfsBundle with
    artifacts := rdfsBundle.artifacts.push
      { id := "G", kind := .graph, digest := "dup", body := none } }).valid = false

/- **11. Duplicate step id** — two steps sharing an id would make
premise resolution ambiguous. -/
#guard (checkBundle (withStep rdfsBundle 1
  (fun st => { st with id := rdfsStepId 0 }))).valid = false

/- **12. An assumption declared `.foundational`.** Requirement 4 is
enforced HERE, in the kernel, not in the type — so that the defect
can be built and its rejection pinned. -/
#guard (checkBundle
  { mixedBundle with
    assumptions := #[{ mixAssumption with level := .foundational }] }).valid = false

/- **13. A `verifiedReplay` step with no theorem citation**
(adoption doc section 8b). REJECTED, not silently accepted at
`replay`. -/
#guard (checkBundle
  { adapterBundle with
    steps := #[mixStep, { adapterStep with level := .verifiedReplay }] }).valid = false

/- ... and the same step WITH a citation is accepted, so the
rejection is attributable to the missing citation and to nothing
else. -/
private def sparqlCitation : Citation :=
  { theoremName := "L4Factoidal.SPARQL.eval_sound"
    module := "L4Factoidal.SPARQL.Invariants" }

private def citedStep : BundleStep :=
  { adapterStep with level := .verifiedReplay, citation := some sparqlCitation }

#guard (checkBundle { adapterBundle with steps := #[mixStep, citedStep] }).valid = true

/- **14. A conclusion no step produces and no assumption
declares.** -/
#guard (checkBundle { rdfsBundle with conclusion := .clif "(P jim)" }).valid = false

/- **15. A `rule` step at a non-foundational level** — the level and
the justification must agree. -/
#guard (checkBundle (withStep mixedBundle 0
  (fun st => { st with level := .replay }))).valid = false

/- **16. An `adapterEvidence` step claiming `.foundational`.** -/
#guard (checkBundle
  { adapterBundle with
    steps := #[mixStep, { adapterStep with level := .foundational }] }).valid = false

/- **17. A step written in another profile.** -/
#guard (checkBundle (withStep rdfsBundle joinIdx
  (fun st => { st with profile := "fpp0/2" }))).valid = false

/- **18. A premise about a DIFFERENT graph** — certificate v1
section 5's splice attack, at the claim level: a valid step over an
unrelated graph presented as part of this argument. -/
#guard (checkBundle
  { mixedBundle with
    assumptions := #[{ mixAssumption with
                       subject := .rdfDerivable "otherdigest" mixAd dataTriple }] }).valid
  = false

/- **19. A premise that is a CLIF proposition where the row needs a
triple.** -/
#guard (checkBundle
  { mixedBundle with
    assumptions := #[{ mixAssumption with subject := .clif "(P jim)" }] }).valid = false

/- **20. A leaf row over a graph with no inline body** — `base`
cannot be foundational when the kernel cannot see the graph, and the
kernel says so rather than trusting the reference. -/
#guard (checkBundle
  { mixedBundle with
    assumptions := #[]
    steps := #[{ mixStep with
                 justification := .rule .base "G" "AX"
                 premises := []
                 conclusion := .rdfDerivable mixGd mixAd dataTriple }]
    conclusion := .rdfDerivable mixGd mixAd dataTriple }).valid = false

/-! ## Issue 976 — blank nodes are scoped to their artifact

https://github.com/danbri/factoidal/issues/976. Reported against npm
0.12.0 and reproduced on main at f0a7e5c3 (before this section
landed, `crossBundle` below was accepted: `valid = true`,
`foundationalOnly = true`, an empty frontier, 3 steps).

`bnG1` and `bnG2` differ only by swapping the labels `_:x` and `_:y`,
so they have the same RDFC-1.0 digest. Neither entails
`:A rdfs:subClassOf :C`, and neither does their RDF 1.1 Semantics
section 5.2 merge. A bundle that takes `:A rdfs:subClassOf _:x` from
`G1` and `_:x rdfs:subClassOf :C` from `G2` and joins the raw label
`_:x` by rdfs11 must be REFUSED.

Two controls must stay ACCEPTED: the same chain inside ONE artifact,
and a chain across two artifacts through triples with no blank node. -/

private def bnA : WfIri := ⟨"http://example.org/A", by rfl⟩
private def bnB : WfIri := ⟨"http://example.org/B", by rfl⟩
private def bnC : WfIri := ⟨"http://example.org/C", by rfl⟩
private def bnQ : WfIri := ⟨"http://example.org/q", by rfl⟩

private def scAx : Triple := ⟨.iri bnA, rdfsSubClassOf, .bnode "x"⟩
private def scAy : Triple := ⟨.iri bnA, rdfsSubClassOf, .bnode "y"⟩
private def scxC : Triple := ⟨.bnode "x", rdfsSubClassOf, .iri bnC⟩
private def scyC : Triple := ⟨.bnode "y", rdfsSubClassOf, .iri bnC⟩
private def scAC : Triple := ⟨.iri bnA, rdfsSubClassOf, .iri bnC⟩

private def bnG1 : Graph := [scAx, scyC]
private def bnG2 : Graph := [scAy, scxC]
private def bnEmpty : Graph := []

/- The premise of the attack: one digest, two labellings. -/
#guard graphDigest bnG1 = graphDigest bnG2
#guard bnG1 ≠ bnG2

private def bnStep (id : String) (r : RuleId) (ga : String) (prem : List String)
    (gd : String) (t : Triple) : BundleStep :=
  { id := id, justification := .rule r ga "AX", premises := prem
    conclusion := .rdfDerivable gd (graphDigest bnEmpty) t
    level := .foundational, profile := fpp0Profile, citation := none }

private def bnArt (id : String) (g : Graph) : Artifact :=
  { id := id, kind := .graph, digest := graphDigest g, body := some g }

/-- The two-artifact bundle of issue 976. -/
private def crossBundle : Bundle :=
  let d := graphDigest bnG1
  { artifacts := #[bnArt "G1" bnG1, bnArt "G2" bnG2, bnArt "AX" bnEmpty]
    assumptions := #[]
    steps := #[bnStep "p1" .base "G1" [] d scAx,
               bnStep "p2" .base "G2" [] d scxC,
               bnStep "s" .rdfs11 "G1" ["p1", "p2"] d scAC]
    conclusion := .rdfDerivable d (graphDigest bnEmpty) scAC }

/- REFUSED, with the blank-node scope named as the reason. -/
#guard (checkBundle crossBundle).valid = false
#guard (checkBundle crossBundle).foundationalOnly = false
#guard ((checkBundle crossBundle).rejection.getD "").startsWith
  "step 's': the step joins blank nodes from different scopes"
/- The same refusal when the join step names the other artifact. -/
#guard (checkBundle (withStep crossBundle 2
  (fun st => { st with justification := .rule .rdfs11 "G2" "AX" }))).valid = false
/- The two leaf steps alone are fine: each is a triple of its own
artifact. Only the join is refused. -/
#guard (checkBundle { crossBundle with
  steps := crossBundle.steps.extract 0 2
  conclusion := .rdfDerivable (graphDigest bnG1) (graphDigest bnEmpty) scxC }).valid = true

/- CONTROL 1 — the same chain inside ONE artifact, `_:x` in both
triples: accepted, all foundational, empty frontier. -/
private def bnG0 : Graph := [scAx, scxC]

private def oneArtifactBundle : Bundle :=
  let d := graphDigest bnG0
  { artifacts := #[bnArt "G0" bnG0, bnArt "AX" bnEmpty]
    assumptions := #[]
    steps := #[bnStep "p1" .base "G0" [] d scAx,
               bnStep "p2" .base "G0" [] d scxC,
               bnStep "s" .rdfs11 "G0" ["p1", "p2"] d scAC]
    conclusion := .rdfDerivable d (graphDigest bnEmpty) scAC }

#guard (checkBundle oneArtifactBundle).valid = true
#guard (checkBundle oneArtifactBundle).foundationalOnly = true
#guard (checkBundle oneArtifactBundle).assumptions.size = 0
#guard (checkBundle oneArtifactBundle).counts.foundational = 3
#guard (checkBundle oneArtifactBundle).rejection = none

/- CONTROL 2 — a chain across TWO artifacts through IRI-only triples.
`bnH1` and `bnH2` share a digest (they differ by swapping two blank
nodes in a third triple); `:A ⊑ :B` comes from `H1`, `:B ⊑ :C` from
`H2`. A triple with no blank node is the same in every scope, so the
join is sound and is accepted. -/
private def scAB : Triple := ⟨.iri bnA, rdfsSubClassOf, .iri bnB⟩
private def scBC : Triple := ⟨.iri bnB, rdfsSubClassOf, .iri bnC⟩
private def scxy : Triple := ⟨.bnode "x", rdfsSubClassOf, .bnode "y"⟩
private def scyx : Triple := ⟨.bnode "y", rdfsSubClassOf, .bnode "x"⟩
private def bnH1 : Graph := [scAB, scBC, scxy]
private def bnH2 : Graph := [scAB, scBC, scyx]

#guard graphDigest bnH1 = graphDigest bnH2

private def iriCrossBundle : Bundle :=
  let d := graphDigest bnH1
  { artifacts := #[bnArt "H1" bnH1, bnArt "H2" bnH2, bnArt "AX" bnEmpty]
    assumptions := #[]
    steps := #[bnStep "p1" .base "H1" [] d scAB,
               bnStep "p2" .base "H2" [] d scBC,
               bnStep "s" .rdfs11 "H1" ["p1", "p2"] d scAC]
    conclusion := .rdfDerivable d (graphDigest bnEmpty) scAC }

#guard (checkBundle iriCrossBundle).valid = true
#guard (checkBundle iriCrossBundle).foundationalOnly = true
#guard (checkBundle iriCrossBundle).counts.foundational = 3

/- **NEGATIVE 21 — the collapse.** rdfs5 over `_:x ⊑p :q` from `K1`
and `:q ⊑p _:x` from `K2` would conclude the REFLEXIVE
`_:x ⊑p _:x`. Neither artifact, nor their merge, entails a node
that is a sub-property of itself. Refused. -/
private def spxq : Triple := ⟨.bnode "x", rdfsSubPropertyOf, .iri bnQ⟩
private def spyq : Triple := ⟨.bnode "y", rdfsSubPropertyOf, .iri bnQ⟩
private def spqx : Triple := ⟨.iri bnQ, rdfsSubPropertyOf, .bnode "x"⟩
private def spqy : Triple := ⟨.iri bnQ, rdfsSubPropertyOf, .bnode "y"⟩
private def spxx : Triple := ⟨.bnode "x", rdfsSubPropertyOf, .bnode "x"⟩
private def bnK1 : Graph := [spxq, spqy]
private def bnK2 : Graph := [spyq, spqx]

#guard graphDigest bnK1 = graphDigest bnK2

private def collapseBundle : Bundle :=
  let d := graphDigest bnK1
  { artifacts := #[bnArt "K1" bnK1, bnArt "K2" bnK2, bnArt "AX" bnEmpty]
    assumptions := #[]
    steps := #[bnStep "p1" .base "K1" [] d spxq,
               bnStep "p2" .base "K2" [] d spqx,
               bnStep "s" .rdfs5 "K1" ["p1", "p2"] d spxx]
    conclusion := .rdfDerivable d (graphDigest bnEmpty) spxx }

#guard (checkBundle collapseBundle).valid = false
/- CONTROL for 21: inside ONE artifact the same two premises are
`_:x ⊑p :q` and `:q ⊑p _:y`, and rdfs5 gives `_:x ⊑p _:y`. -/
private def spxy : Triple := ⟨.bnode "x", rdfsSubPropertyOf, .bnode "y"⟩
#guard (checkBundle { collapseBundle with
  steps := #[bnStep "p1" .base "K1" [] (graphDigest bnK1) spxq,
             bnStep "p2" .base "K1" [] (graphDigest bnK1) spqy,
             bnStep "s" .rdfs5 "K1" ["p1", "p2"] (graphDigest bnK1) spxy]
  conclusion := .rdfDerivable (graphDigest bnK1) (graphDigest bnEmpty) spxy }).valid = true

/- **NEGATIVE 22 — an assumption's blank node is its own.** A replay
assumption about `_:x` cannot join the `_:x` of an artifact body. -/
#guard (checkBundle { oneArtifactBundle with
  assumptions := #[{ id := "a1", level := .replay
                     subject := .rdfDerivable (graphDigest bnG0) (graphDigest bnEmpty) scxC }]
  steps := #[bnStep "p1" .base "G0" [] (graphDigest bnG0) scAx,
             bnStep "s" .rdfs11 "G0" ["p1", "a1"] (graphDigest bnG0) scAC] }).valid = false

/- The rejection text is present for every refusal pinned in this
file's mutation section, and absent for the accepted bundles. -/
#guard (checkBundle rdfsBundle).rejection = none
#guard (checkBundle mixedBundle).rejection = none
#guard (checkBundle { rdfsBundle with conclusion := .clif "(P jim)" }).rejection
  = some "no step and no assumption states the bundle's conclusion"

/-! ## `Derives` is inhabited at a non-trivial claim

What CAN be checked is that `Derives` is not an empty relation
dressed up: the term below derives an rdfs4a conclusion from an EMPTY
assumption list, through the leaf constructor and the row
constructor, with no `sorry` in it. The leaf is read in the scope of
artifact `G`; `dataGraph` is ground, so the scoped triple is the
triple itself. -/

private def dataArt : Artifact :=
  { id := "G", kind := .graph, digest := graphDigest dataGraph, body := some dataGraph }

example : Derives [dataArt] [] (Claim.rdfDerivable (graphDigest dataGraph) mixAd mixConcl) :=
  Derives.rdfsRow
    (prem := [dataTriple])
    (fun u hu => by
      rw [List.mem_singleton.1 hu]
      have h := Derives.rdfsBase (A := [dataArt]) (Γ := []) (ad := mixAd)
        (List.mem_singleton_self _) rfl rfl (List.mem_singleton_self dataTriple)
      rw [Triple.scoped_of_isGround _ (by decide)] at h
      exact h)
    (DerivesFull.rdfs4a (DerivesFull.base (List.mem_singleton_self _)))

/-! ## Axiom audit — expect propext / Classical.choice / Quot.sound only -/

#print axioms L4Factoidal.FPP0.checkBundle_sound
#print axioms L4Factoidal.FPP0.checkBundle_merge_frontier
#print axioms L4Factoidal.FPP0.checkBundle_merge
#print axioms L4Factoidal.FPP0.checkBundle_merge_ground
#print axioms L4Factoidal.FPP0.checkBundle_rejection_none_iff
#print axioms L4Factoidal.FPP0.stepValid_sound
#print axioms L4Factoidal.FPP0.checkSteps_sound
#print axioms L4Factoidal.FPP0.inferenceRowOk_sound
#print axioms L4Factoidal.FPP0.Derives.toMerge
#print axioms L4Factoidal.FPP0.Derives.weaken
#print axioms L4Factoidal.FPP0.derivesFull_axMono
#print axioms L4Factoidal.FPP0.scopeLabel_inj
#print axioms L4Factoidal.RDF.Triple.scoped_of_isGround

end L4Factoidal.FPP0
