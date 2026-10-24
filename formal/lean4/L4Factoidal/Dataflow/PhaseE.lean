/-
L4Factoidal.Dataflow.PhaseE — evidence on the wires
(https://github.com/danbri/factoidal/issues/975, phase E).

## Stages

| stage | in → out | contract | from |
|---|---|---|---|
| `rdfsExplainStage` | `Dataset × Triple` → `Bundle` | `ExplainContract`: the bundle is the RDFS witness of the target over the selected graphs, the kernel accepts it with an empty frontier, its axiom artifact is the RDFS profile axiom set | `fullClosureWithProof_graph`, `bundleOfRdfsDerivation`, `checkBundle` |
| `rdfsExplainCheckStage` | `Dataset × Triple` → `Claim` | `ExplainCheckContract`: explain, then `proofCheckStage` | `rdfsExplainCheck_sound` |
| `proofCheckRdfsStage` | `Bundle` → `Claim` | `RdfsCheckContract`: accepted with profile axioms implies RDFS entailment from the merge of the graph artifacts | `checkBundle_rdfsEntails` |
| `rdfcStage` | `Dataset` → `String × String` | `RdfcContract`: the canonical N-Quads text and its SHA-256 hex; the lines are in code point order; no §4.4 abort | `canonicalLines_sorted` |
| `vcSignStage` | `SignIn` → `String` | `SignContract`: the proofValue is the multibase-z of the signature of the hash data, and depends on the canonical forms only | `createProofValue_of_canonical_eq` |
| `vcVerifyStage` | `VerifyIn` → `Bool` | `VerifyContract`: the verdict is the primitive's verdict on the hash data; it depends on the canonical forms only; a proofValue that is not multibase-z is refused | `verifyProofValue_of_canonical_eq`, `verifyFromCanonical_not_multibase` |
| `ed25519VerifyIO` | `pk × msg × sig` → `Bool` | named assumption `Ed25519Correct` (RFC 8032 correctness of HACL* verify) | — |
| `sha256NativeIO` | `ByteArray` → `ByteArray` | named assumption `Sha256Agrees` (HACL* SHA-256 equals `Crypto.sha256`) | — |

## The explain stage

`rdfsExplainStage D cmps hcmps sel` reads the union of the selected graphs
(`Dataset.select`, phase D: one blank-node scope, RDF 1.1 Concepts section 4),
runs `fullClosureWithProof`, and wraps the witness with
`bundleOfRdfsDerivation`. It adds one body-less artifact for each selected
graph that holds a `base` premise in the support of the target (the exact
source dependencies; an empty named graph is never one). The run then calls
the kernel. The stage fails when the target is not in the closure, when the
kernel refuses the bundle, or when the digest of the selection equals the
digest of the axiom set.

So "the kernel accepts" is a check of the run, not a theorem about the
emitter. That every emitted bundle is accepted is TESTED only
(`PhaseETests.lean`, `Proof/Tests.lean`).

`rdfsExplainCheck_sound`: a successful run of explain then check gives the
claim `rdfDerivable gd ad t`; a bundle that the kernel accepts with an empty
frontier and the profile axioms; the target, read in some scope, derivable
from the merge of the cited artifacts (`checkBundle_merge`), and that merge is
the selection with its blank nodes in the scope of artifact `G`; RDFS
entailment of the scoped target from that merge (`checkBundle_rdfsEntails`);
RDFS entailment of the target from the selection itself
(`fullClosure_entails`); and each source artifact names a selected graph by
its digest.

## Findings

* The kernel binds the axiom set to the bundle, not to the RDFS profile
  (`Proof/RdfsProfile.lean`). `profileAxiomsOk` is the binding.
* A claim `rdfDerivable gd ad t` names ONE graph digest. A derivation whose
  premises come from two graphs of a dataset cites the union of the selected
  graphs as one artifact; the source graphs are cited as body-less references.
  The kernel does not check that `G` is the union of the sources; this stage
  proves it (`explainBundle_G`, `explainBundle_sources`).
* RDFC-1.0 relabelling invariance is stated only (`RelabellingInvariance`);
  the W3C RDFC-1.0 suite tests it.
* The RDFS witness of the empty-input example uses rdfs2 over two axioms, not
  rdfD2 (`PhaseETests.lean` pins both chains).
* `DerivesFull.rdfs9` takes the class as an IRI: with a blank-node class
  (`ex:alice rdf:type _:c . _:c rdfs:subClassOf ex:Person .`) the closure does
  not hold `ex:alice rdf:type ex:Person`. RDF 1.1 Semantics 9.2 has no such
  restriction (a completeness gap; soundness is not affected).
* No theorem uses collision resistance of a hash. A reader who resolves a
  body-less source reference by its digest relies on it; that is not stated.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.PhaseD
import L4Factoidal.Proof.RdfsProfile
import L4Factoidal.RDF.CanonicalTheorems
import L4Factoidal.VC.Theorems
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.Crypto.SHA2Native

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.FPP0

/-! ## Selected graphs, with their names -/

/-- The selected graphs one by one: the default graph (`none`) when selected,
then the selected named graphs. -/
def selectedGraphs (sel : GraphSelection) (ds : Dataset) : List (Option Subject × Graph) :=
  (if sel.default then [(none, ds.default)] else []) ++
    (ds.named.filter (fun ng => sel.named.contains ng.name)).map (fun ng => (some ng.name, ng.graph))

/-- The selection is the union of the selected graphs. -/
theorem select_eq_flatMap (sel : GraphSelection) (ds : Dataset) :
    ds.select sel = (selectedGraphs sel ds).flatMap (·.2) := by
  unfold Dataset.select selectedGraphs
  cases sel.default <;> simp [List.flatMap_map]

/-! ## The explain bundle -/

/-- The triples of the `base` steps in the support of the conclusion. -/
def baseTriples (b : Bundle) : List Triple :=
  let sup := supportOf b
  b.steps.toList.filterMap (fun st =>
    if sup.contains st.id then
      match st.justification, st.conclusion with
      | .rule .base _ _, .rdfDerivable _ _ u => some u
      | _, _ => none
    else none)

/-- The id of a source artifact: its position in the selection and its name. -/
def sourceId (i : Nat) (n : Option Subject) : String :=
  "source:" ++ toString i ++ ":" ++
    (match n with
     | none => "default"
     | some s => Canonical.canonSubject s)

/-- One body-less graph artifact for each selected graph that holds a used
triple. -/
def sourceArtifacts (srcs : List (Option Subject × Graph)) (used : List Triple) : List Artifact :=
  (srcs.zipIdx.filter (fun p => used.any (fun u => decide (u ∈ p.1.2)))).map
    (fun p => { id := sourceId p.2 p.1.1, kind := .graph, digest := graphDigest p.1.2, body := none })

/-- The RDFS witness of `t` over `g` with axiom set `ax`, plus the source
references. -/
def explainBundleOf (g ax : Graph) (d : Derivation) (srcs : List (Option Subject × Graph))
    (t : Triple) : Bundle :=
  let b0 := bundleOfRdfsDerivation g ax d t
  { b0 with artifacts := b0.artifacts ++ (sourceArtifacts srcs (baseTriples b0)).toArray }

def explainBundle (D cmps : List WfIri) (sel : GraphSelection) (ds : Dataset) (t : Triple) : Bundle :=
  explainBundleOf (ds.select sel) (axiomaticTriples D cmps)
    (fullClosureWithProof D cmps (ds.select sel)).2 (selectedGraphs sel ds) t

/-- The graph artifact `G` of the bundle. -/
def gArtifact (g : Graph) : Artifact :=
  { id := "G", kind := .graph, digest := graphDigest g, body := some g }

/-- The axiom artifact `AX` of the bundle. -/
def axArtifact (ax : Graph) : Artifact :=
  { id := "AX", kind := .graph, digest := graphDigest ax, body := some ax }

theorem explainBundle_artifacts (D cmps : List WfIri) (sel : GraphSelection) (ds : Dataset)
    (t : Triple) :
    ∃ srcs, (explainBundle D cmps sel ds t).artifacts.toList
      = gArtifact (ds.select sel) :: axArtifact (axiomaticTriples D cmps) :: srcs ∧
      ∀ a ∈ srcs, a.body = none ∧ ∃ p ∈ selectedGraphs sel ds, a.digest = graphDigest p.2 := by
  refine ⟨sourceArtifacts (selectedGraphs sel ds) (baseTriples (bundleOfRdfsDerivation (ds.select sel)
    (axiomaticTriples D cmps) (fullClosureWithProof D cmps (ds.select sel)).2 t)), ?_, ?_⟩
  · simp [explainBundle, explainBundleOf, bundleOfRdfsDerivation, gArtifact, axArtifact]
  · intro a ha
    unfold sourceArtifacts at ha
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    refine ⟨rfl, p.1, ?_, rfl⟩
    have hp' := (List.mem_filter.mp hp).1
    exact List.fst_mem_of_mem_zipIdx hp'

/-- **`G` is the union of the selected graphs.** -/
theorem explainBundle_G (D cmps : List WfIri) (sel : GraphSelection) (ds : Dataset) (t : Triple) :
    gArtifact (ds.select sel) ∈ (explainBundle D cmps sel ds t).artifacts.toList ∧
      (gArtifact (ds.select sel)).body = some ((selectedGraphs sel ds).flatMap (·.2)) := by
  obtain ⟨srcs, h, _⟩ := explainBundle_artifacts D cmps sel ds t
  rw [h]
  exact ⟨List.mem_cons_self .., by simp [gArtifact, select_eq_flatMap]⟩

/-- **Every source artifact names a selected graph by its digest, and has no
body.** -/
theorem explainBundle_sources (D cmps : List WfIri) (sel : GraphSelection) (ds : Dataset)
    (t : Triple) : ∀ a ∈ (explainBundle D cmps sel ds t).artifacts.toList, a.id ≠ "G" → a.id ≠ "AX" →
      a.body = none ∧ ∃ p ∈ selectedGraphs sel ds, a.digest = graphDigest p.2 := by
  obtain ⟨srcs, h, hs⟩ := explainBundle_artifacts D cmps sel ds t
  rw [h]
  intro a ha hG hAX
  rcases List.mem_cons.mp ha with rfl | ha
  · exact absurd rfl hG
  rcases List.mem_cons.mp ha with rfl | ha
  · exact absurd rfl hAX
  exact hs a ha

theorem flatMap_scopedBody_none {l : List Artifact} (h : ∀ a ∈ l, a.body = none) :
    l.flatMap Artifact.scopedBody = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons]
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp [Artifact.scopedBody, h a (List.mem_cons_self ..)]

/-- **The merge of the graph artifacts is the selection, scoped by `G`**, when
the two digests differ. -/
theorem mergeOf_explain (D cmps : List WfIri) (sel : GraphSelection) (ds : Dataset) (t : Triple)
    (hne : graphDigest (ds.select sel) ≠ graphDigest (axiomaticTriples D cmps)) :
    mergeOf (explainBundle D cmps sel ds t).artifacts.toList (graphDigest (ds.select sel))
      = (ds.select sel).map (Triple.scoped (.artifact "G")) := by
  obtain ⟨srcs, h, hs⟩ := explainBundle_artifacts D cmps sel ds t
  rw [h]
  unfold mergeOf
  have hne' : (graphDigest (axiomaticTriples D cmps) == graphDigest (ds.select sel)) = false := by
    simp only [beq_eq_false_iff_ne]; exact fun e => hne e.symm
  simp only [List.filter_cons, gArtifact, axArtifact, beq_self_eq_true, if_true, hne',
    Bool.false_eq_true, if_false, List.flatMap_cons]
  rw [flatMap_scopedBody_none (fun a ha => (hs a (List.mem_filter.mp ha).1).1)]
  simp [Artifact.scopedBody]

/-! ## The explain stage -/

/-- The contract of the explain stage. -/
def ExplainContract (D cmps : List WfIri) (sel : GraphSelection) (inp : Dataset × Triple)
    (b : Bundle) : Prop :=
  b = explainBundle D cmps sel inp.1 inp.2 ∧
  b.conclusion = .rdfDerivable (graphDigest (inp.1.select sel))
      (graphDigest (axiomaticTriples D cmps)) inp.2 ∧
  (checkBundle b).foundationalOnly = true ∧
  profileAxiomsOk (axiomaticTriples D cmps) b (graphDigest (axiomaticTriples D cmps)) = true ∧
  graphDigest (inp.1.select sel) ≠ graphDigest (axiomaticTriples D cmps) ∧
  inp.2 ∈ fullClosure D cmps (inp.1.select sel)

/-- The run of the explain stage. -/
def explainRun (D cmps : List WfIri) (sel : GraphSelection) (inp : Dataset × Triple) :
    Except String Bundle :=
  let g := inp.1.select sel
  let ax := axiomaticTriples D cmps
  let c := fullClosureWithProof D cmps g
  let b := explainBundleOf g ax c.2 (selectedGraphs sel inp.1) inp.2
  if !decide (inp.2 ∈ c.1) then .error "the target triple is not in the RDFS closure of the selected graphs"
  else if graphDigest g == graphDigest ax then
    .error "the selected graphs have the digest of the RDFS axiom set"
  else if !(checkBundle b).foundationalOnly then
    .error ("the proof checker refused the bundle: " ++ ((checkBundle b).rejection.getD "assumption frontier"))
  else if !profileAxiomsOk ax b (graphDigest ax) then
    .error "an artifact filed under the axiom digest is not the RDFS axiom set"
  else .ok b

def rdfsExplainStage (D cmps : List WfIri) (sel : GraphSelection) :
    Stage String (Dataset × Triple) Bundle where
  run := explainRun D cmps sel
  contract := ExplainContract D cmps sel
  sound := by
    intro inp b h
    unfold explainRun at h
    simp only at h
    split at h
    · cases h
    rename_i h1
    split at h
    · cases h
    rename_i h2
    split at h
    · cases h
    rename_i h3
    split at h
    · cases h
    rename_i h4
    injection h with h
    subst h
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not] at h1
    simp only [beq_iff_eq] at h2
    simp only [Bool.not_eq_true', Bool.not_eq_false] at h3 h4
    rw [fullClosureWithProof_graph] at h1
    exact ⟨rfl, rfl, h3, h4, h2, h1⟩

/-- RDFS entailment of a closure member. -/
theorem rdfsEntails_of_closure (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    {g : Graph} {t : Triple} (ht : t ∈ fullClosure D cmps g) :
    RdfsEntails (fun x => x ∈ D) g [t] := by
  intro i hc hs
  obtain ⟨a, ha⟩ := fullClosure_entails D cmps hcmps g i hc hs
  exact ⟨a, fun u hu => by rw [List.mem_singleton] at hu; subst hu; exact ha _ ht⟩

/-- The contract of explain, then check. -/
def ExplainCheckContract (D cmps : List WfIri) (sel : GraphSelection) (inp : Dataset × Triple)
    (c : Claim) : Prop :=
  let g := inp.1.select sel
  let ax := axiomaticTriples D cmps
  c = .rdfDerivable (graphDigest g) (graphDigest ax) inp.2 ∧
  (∃ b : Bundle, b = explainBundle D cmps sel inp.1 inp.2 ∧ (checkBundle b).foundationalOnly = true ∧
    profileAxiomsOk ax b (graphDigest ax) = true ∧
    mergeOf b.artifacts.toList (graphDigest g) = g.map (Triple.scoped (.artifact "G")) ∧
    (∃ s : Scope, DerivesFull (mergeOf b.artifacts.toList (graphDigest ax))
        (mergeOf b.artifacts.toList (graphDigest g)) (inp.2.scoped s)) ∧
    (∃ s : Scope, RdfsEntails (fun x => x ∈ D) (g.map (Triple.scoped (.artifact "G")))
        [inp.2.scoped s]) ∧
    (∀ a ∈ b.artifacts.toList, a.id ≠ "G" → a.id ≠ "AX" →
        a.body = none ∧ ∃ p ∈ selectedGraphs sel inp.1, a.digest = graphDigest p.2)) ∧
  RdfsEntails (fun x => x ∈ D) g [inp.2]

/-- **Explain, then check: soundness.** -/
theorem rdfsExplainCheck_sound (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (sel : GraphSelection) (inp : Dataset × Triple) (c : Claim)
    (h : ((rdfsExplainStage D cmps sel).comp proofCheckStage).run inp = .ok c) :
    ExplainCheckContract D cmps sel inp c := by
  obtain ⟨b, ⟨hb, hconc, hf, hax, hne, hmem⟩, ⟨hc, _⟩⟩ :=
    ((rdfsExplainStage D cmps sel).comp proofCheckStage).sound inp c h
  have hc' : c = .rdfDerivable (graphDigest (inp.1.select sel))
      (graphDigest (axiomaticTriples D cmps)) inp.2 := by rw [hc, hconc]
  have hmerge := mergeOf_explain D cmps sel inp.1 inp.2 hne
  rw [← hb] at hmerge
  obtain ⟨s, hd⟩ := checkBundle_merge hf hconc
  obtain ⟨s', he⟩ := checkBundle_rdfsEntails D cmps hcmps hf hconc hax
  rw [hmerge] at he
  refine ⟨hc', ⟨b, hb, hf, hax, hmerge, ⟨s, hd⟩, ⟨s', he⟩, ?_⟩,
    rdfsEntails_of_closure D cmps hcmps hmem⟩
  rw [hb]
  exact explainBundle_sources D cmps sel inp.1 inp.2

/-- Explain, then check, as one stage. -/
def rdfsExplainCheckStage (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (sel : GraphSelection) : Stage String (Dataset × Triple) Claim where
  run := ((rdfsExplainStage D cmps sel).comp proofCheckStage).run
  contract := ExplainCheckContract D cmps sel
  sound := rdfsExplainCheck_sound D cmps hcmps sel

/-! ## The checker with the RDFS profile -/

/-- Accepted with profile axioms: the claim is RDFS-entailed (in some scope) by
the merge of the graph artifacts. -/
def RdfsCheckContract (D : List WfIri) (b : Bundle) (c : Claim) : Prop :=
  c = b.conclusion ∧ ∀ gd ad t, c = Claim.rdfDerivable gd ad t →
    ∃ s : Scope, RdfsEntails (fun x => x ∈ D) (mergeOf b.artifacts.toList gd) [t.scoped s]

def proofCheckRdfsStage (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) :
    Stage String Bundle Claim where
  run b :=
    match b.conclusion with
    | .rdfDerivable _ ad _ =>
      if (checkBundle b).foundationalOnly && profileAxiomsOk (axiomaticTriples D cmps) b ad then
        .ok b.conclusion
      else .error "bundle refused, has an assumption frontier, or its axiom set is not the RDFS profile's"
    | .clif _ => .error "not an RDF claim"
  contract := RdfsCheckContract D
  sound := by
    intro b c h
    revert h
    cases hcb : b.conclusion with
    | clif _ => intro h; cases h
    | rdfDerivable gd ad t =>
      intro h
      simp only at h
      split at h
      · rename_i hok
        injection h with h
        subst h
        simp only [Bool.and_eq_true] at hok
        refine ⟨hcb.symm, fun gd' ad' t' he => ?_⟩
        simp only [Claim.rdfDerivable.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact checkBundle_rdfsEntails D cmps hcmps hok.1 hcb hok.2
      · cases h

/-! ## RDFC-1.0 -/

open L4Factoidal.RDF.Canonical in
/-- The canonical N-Quads text and its SHA-256 hex: the text is the join of
the canonical lines, the lines are in code point order (RDFC-1.0 section 3),
and the run did not hit the section 4.4 work budget. Invariance under
blank-node relabelling is NOT part of the contract: it is stated only
(`Canonical.RelabellingInvariance`). -/
def RdfcContract (ds : Dataset) (out : String × String) : Prop :=
  out.1 = ds.canonicalNQuads .sha256 ∧
  out.1 = joinStrings (ds.canonicalLines .sha256) ∧
  sortedB strLe (ds.canonicalLines .sha256) = true ∧
  out.2 = Crypto.hashHex .sha256 out.1 ∧
  (canonicalize ds .sha256).aborted = false

open L4Factoidal.RDF.Canonical in
theorem canonicalNQuads_join (ds : Dataset) (alg : Crypto.HashAlgorithm) :
    ds.canonicalNQuads alg = joinStrings (ds.canonicalLines alg) := by
  unfold Dataset.canonicalNQuads Dataset.canonicalLines canonicalize
  split <;> rfl

open L4Factoidal.RDF.Canonical in
def rdfcStage : Stage String Dataset (String × String) where
  run ds :=
    let r := canonicalize ds .sha256
    if r.aborted then .error "RDFC-1.0 section 4.4: the work budget was exceeded"
    else .ok (r.nquads, Crypto.hashHex .sha256 r.nquads)
  contract := RdfcContract
  sound := by
    intro ds out h
    simp only at h
    split at h
    · cases h
    · rename_i hab
      injection h with h
      subst h
      exact ⟨rfl, canonicalNQuads_join ds .sha256, canonicalLines_sorted ds .sha256, rfl,
        by simpa using hab⟩

/-! ## VC Data Integrity (eddsa-rdfc-2022) -/

open L4Factoidal.VC.DataIntegrity L4Factoidal.VC.Multibase

structure SignIn where
  sk : ByteArray
  document : Dataset
  proofConfig : Dataset

structure VerifyIn where
  pk : ByteArray
  document : Dataset
  proofConfig : Dataset
  proofValue : String

/-- The proofValue is the multibase-z encoding of a non-empty signature of
the hash data, and it depends on the canonical forms only. -/
def SignContract (signF : SignFn) (alg : Crypto.HashAlgorithm) (i : SignIn) (pv : String) : Prop :=
  createFromCanonical signF alg i.sk (transformDataset i.document) (transformDataset i.proofConfig)
      = some pv ∧
  (signF i.sk (hashData alg (transformDataset i.document) (transformDataset i.proofConfig))).size ≠ 0 ∧
  ∀ d c : Dataset, d.canonicalNQuads .sha256 = i.document.canonicalNQuads .sha256 →
    c.canonicalNQuads .sha256 = i.proofConfig.canonicalNQuads .sha256 →
    createProofValue signF alg i.sk d c = some pv

def vcSignStage (signF : SignFn) (alg : Crypto.HashAlgorithm) : Stage String SignIn String where
  run i :=
    match createProofValue signF alg i.sk i.document i.proofConfig with
    | some pv => .ok pv
    | none => .error "the signing primitive refused the key or the message"
  contract := SignContract signF alg
  sound := by
    intro i pv h
    revert h
    cases hc : createProofValue signF alg i.sk i.document i.proofConfig with
    | none => intro h; cases h
    | some pv' =>
      intro h
      injection h with h
      subst h
      have hc' : createFromCanonical signF alg i.sk (transformDataset i.document)
          (transformDataset i.proofConfig) = some pv' := hc
      refine ⟨hc', ?_, fun d c hd hcf => ?_⟩
      · intro h0
        unfold createFromCanonical at hc'
        simp [h0] at hc'
      · rw [createProofValue_of_canonical_eq signF alg i.sk hd hcf]
        exact hc

/-- The verdict is the primitive's verdict on the hash data of the canonical
forms; it depends on the canonical forms only; a proofValue that is not
multibase-z is refused. -/
def VerifyContract (verifyF : VerifyFn) (alg : Crypto.HashAlgorithm) (i : VerifyIn) (v : Bool) : Prop :=
  v = verifyFromCanonical verifyF alg i.pk (transformDataset i.document)
      (transformDataset i.proofConfig) i.proofValue ∧
  (multibaseDecode? i.proofValue = none → v = false) ∧
  ∀ d c : Dataset, d.canonicalNQuads .sha256 = i.document.canonicalNQuads .sha256 →
    c.canonicalNQuads .sha256 = i.proofConfig.canonicalNQuads .sha256 →
    verifyProofValue verifyF alg i.pk d c i.proofValue = v

def vcVerifyStage (verifyF : VerifyFn) (alg : Crypto.HashAlgorithm) : Stage String VerifyIn Bool :=
  Stage.ofFun (fun i => verifyProofValue verifyF alg i.pk i.document i.proofConfig i.proofValue)
    (VerifyContract verifyF alg)
    (fun i => ⟨rfl, fun h => verifyFromCanonical_not_multibase verifyF alg i.pk _ _ _ h,
      fun _ _ hd hc => verifyProofValue_of_canonical_eq verifyF alg i.pk i.proofValue hd hc⟩)

/-- **Named assumption: RFC 8032 correctness of the verify primitive.** A
signature made by `Crypto.Ed25519.sign` with a 32-byte secret key, when it is
not the empty refusal, verifies under the public key of that secret key.
HACL* proves this for its F* source; this tree does not. -/
def Ed25519Correct (inp : ByteArray × ByteArray × ByteArray) (out : Bool) : Prop :=
  ∀ sk : ByteArray, sk.size = 32 → inp.1 = Crypto.Ed25519.secretToPublic sk →
    inp.2.2 = Crypto.Ed25519.sign sk inp.2.1 → inp.2.2.size ≠ 0 → out = true

/-- The verify primitive (`Crypto.Ed25519.verify`, HACL*) at the IO boundary. -/
def ed25519VerifyIO : IOStage String (ByteArray × ByteArray × ByteArray) Bool :=
  { assumption := Ed25519Correct }

/-- **Named assumption: the native SHA-256 (HACL*) equals the specification
`Crypto.sha256`** (FIPS 180-4, pure Lean, checked against the FIPS vectors). -/
def Sha256Agrees (m d : ByteArray) : Prop := d = Crypto.sha256 m

/-- The native SHA-256 (`Crypto.sha256Hacl`) at the IO boundary. -/
def sha256NativeIO : IOStage String ByteArray ByteArray := { assumption := Sha256Agrees }

/-- **Sign, then verify.** Under `Ed25519Correct` for the verify primitive, a
proofValue made by the sign stage with a 32-byte secret key verifies, under
the public key of that secret key, over the same document and proof
configuration. -/
theorem vcSignVerify_roundTrip (alg : Crypto.HashAlgorithm) (verifyF : VerifyFn)
    (hreal : ed25519VerifyIO.Realised (fun a => .ok (verifyF a.1 a.2.1 a.2.2)))
    (sk : ByteArray) (hsk : sk.size = 32) (doc cfg : Dataset) {pv : String}
    (hs : (vcSignStage Crypto.Ed25519.sign alg).run ⟨sk, doc, cfg⟩ = .ok pv) :
    (vcVerifyStage verifyF alg).run ⟨Crypto.Ed25519.secretToPublic sk, doc, cfg, pv⟩ = .ok true := by
  obtain ⟨hcreate, hsize, _⟩ := (vcSignStage Crypto.Ed25519.sign alg).sound _ pv hs
  have hsig := hreal (Crypto.Ed25519.secretToPublic sk,
      hashData alg (transformDataset doc) (transformDataset cfg),
      Crypto.Ed25519.sign sk (hashData alg (transformDataset doc) (transformDataset cfg)))
    _ rfl sk hsk rfl rfl hsize
  have := verifyFromCanonical_createFromCanonical Crypto.Ed25519.sign verifyF alg sk
    (Crypto.Ed25519.secretToPublic sk) _ _ pv hcreate hsig
  show Except.ok (verifyProofValue verifyF alg _ doc cfg pv) = _
  unfold verifyProofValue
  rw [this]

#print axioms select_eq_flatMap
#print axioms explainBundle_G
#print axioms explainBundle_sources
#print axioms mergeOf_explain
#print axioms rdfsExplainStage
#print axioms rdfsExplainCheck_sound
#print axioms rdfsExplainCheckStage
#print axioms proofCheckRdfsStage
#print axioms rdfcStage
#print axioms vcSignStage
#print axioms vcVerifyStage
#print axioms vcSignVerify_roundTrip

end L4Factoidal.Dataflow
