/-
L4Factoidal.Proof.Checker — the FPP0 KERNEL: a total decision
procedure that reads a `Bundle` (`Proof/Syntax.lean`) and decides
whether its steps really license its conclusion, and reports the
assumption frontier the conclusion still rests on.

Design: `docs/designissues/2026-08-26-proof-profile-fpp0-adoption.md`
sections 1, 2, 3, 8a, 8b; and
`docs/designissues/2026-08-26-proof-certificate-v1.md` sections 2, 3,
5. Milestone M1.

## What it does

`checkBundle` runs three finite passes, none of them fuelled:

1. the artifact table — ids unique, and every inline body's RDFC-1.0
   digest equal to the digest it is filed under;
2. the assumption table — ids unique, and no assumption at
   `foundational`;
3. the steps, LEFT TO RIGHT, each against the prefix already
   accepted; then a RIGHT-TO-LEFT marking pass for the support of the
   conclusion, which is what the level counts are taken over.

Every pass is structurally recursive over a finite list. There is no
fuel parameter and no fixpoint, so there is no budget that can be
exhausted and no silent cap (`skills/measuring-inference` section 8).

Every claim the passes join is SCOPED (issue 976, `Proof/Syntax.lean`
section "Blank-node scope"): the environment holds each claim with its
blank nodes relabelled by the artifact, assumption or step it came
from. A refused bundle's `rejection` names the first failed check.

## The foundational rule family delegates

A `Justification.rule` step at a section 8.1 / section 9.2 inference
row is decided by `RDFS.stepOk`, the landed checker's own step test,
applied to the premise triples read out of the prefix. Its soundness
comes from `RDFS.stepOk_sound` unchanged. This module restates no
row, and adds no rule whose check would be an entailment test
(adoption doc section 2).

## What it does NOT do

* It does not resolve a digest whose artifact carries no inline body.
  A leaf fact about such a graph must enter as an ASSUMPTION, and
  then it is in the reported frontier where a reader can see it.
* It does not check the `citation` field's content. Section 8b's rule
  is enforced as PRESENCE: a `verifiedReplay` step with no citation
  is rejected. Whether the named theorem exists, and whether its
  statement covers the operation, is outside a kernel that must stay
  total and small.
* It does not check completeness — that every claim the engine could
  make has a bundle.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Proof.Syntax

namespace L4Factoidal.FPP0

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-! ## Pass 1 — the artifact table -/

/-- Look an artifact up by id. -/
def artifactById (b : Bundle) (id : String) : Option Artifact :=
  b.artifacts.toList.find? (fun a => a.id == id)

/-- One artifact is well formed when, if it carries an inline body,
that body is a graph and its RDFC-1.0 digest IS the digest the
artifact is filed under (certificate v1 section 3). An inline body
that disagrees with its digest would let a valid derivation about one
graph be presented as a proof about another. -/
def artifactOk (a : Artifact) : Bool :=
  match a.body with
  | none => true
  | some g => a.kind == ArtifactKind.graph && a.digest == graphDigest g

/-- Ids unique, and every artifact well formed. -/
def artifactsOk : List Artifact → Bool
  | [] => true
  | a :: rest => !(rest.any (fun x => x.id == a.id)) && artifactOk a && artifactsOk rest

theorem artifactOk_body {a : Artifact} {g : Graph}
    (h : artifactOk a = true) (hb : a.body = some g) : graphDigest g = a.digest := by
  unfold artifactOk at h
  rw [hb] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.symm

theorem artifactsOk_mem {l : List Artifact} (h : artifactsOk l = true)
    {a : Artifact} (ha : a ∈ l) : artifactOk a = true := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [artifactsOk, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1.2
    · exact ih h.2 ha

theorem artifactById_mem {b : Bundle} {id : String} {a : Artifact}
    (h : artifactById b id = some a) : a ∈ b.artifacts.toList :=
  List.mem_of_find?_eq_some h

theorem artifactById_id {b : Bundle} {id : String} {a : Artifact}
    (h : artifactById b id = some a) : a.id = id := by
  have := List.find?_some h
  simpa using this

/-! ## Pass 2 — the assumption table

Adoption doc section 3: assumptions are the frontier. Two conditions,
both rejections rather than silent repairs.

* Ids unique — a duplicate id makes premise resolution ambiguous.
* NO assumption at `foundational`. A fact this kernel checked is a
  step; an assumption is what enters from outside. Requirement 4 of
  the brief offers the type or the checker as the place to enforce
  this, and this is the checker. The reason is testability: made
  unrepresentable in the type, the defect could not be built, so
  `Tests.lean` could not pin that it is rejected. -/

/-- Ids all different. -/
def idsDistinct : List String → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && idsDistinct xs

/-- The assumption table is well formed: ids unique, and no
assumption at `foundational`. -/
def assumptionsOk (l : List Assumption) : Bool :=
  l.all (fun a => !(a.level == EvidenceLevel.foundational))
    && idsDistinct (l.map (·.id))

/-- The claim environment the declared assumptions contribute, each
claim read in the assumption's own blank-node scope (issue 976). Total:
malformedness is reported by `assumptionsOk`, not by an `Option`, so
the environment itself needs no case analysis anywhere. -/
def assumptionEnv (l : List Assumption) : List (String × Claim) :=
  l.map (fun a => (a.id, a.subject.scoped (.frontier a.id)))

/-- Everything the assumption environment holds comes from an
assumption of the table. -/
theorem assumptionEnv_mem {l : List Assumption} {e : String × Claim}
    (he : e ∈ assumptionEnv l) : ∃ a ∈ l, a.subject.scoped (.frontier a.id) = e.2 := by
  simp only [assumptionEnv, List.mem_map] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact ⟨a, ha, rfl⟩

/-! ## Premise resolution

A premise is an ID. It resolves against the environment built from
the declared assumptions and the steps ALREADY ACCEPTED — never the
whole step array. So a premise that names a later step, the step
itself, or nothing at all, fails to resolve, and the three collapse
into one rejection: certificate v1 section 5's first two rows and the
brief's cycle case. -/

/-- The claim an id names, if the prefix holds one. -/
def lookupClaim (env : List (String × Claim)) (id : String) : Option Claim :=
  (env.find? (fun e => e.1 == id)).map (·.2)

theorem lookupClaim_mem {env : List (String × Claim)} {id : String} {c : Claim}
    (h : lookupClaim env id = some c) : ∃ e ∈ env, e.2 = c := by
  unfold lookupClaim at h
  cases hf : env.find? (fun e => e.1 == id) with
  | none => rw [hf] at h; simp at h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨e, List.mem_of_find?_eq_some hf, h⟩

/-- Read a list of premise ids as SCOPED triples (the environment holds
scoped claims), all about the SAME graph and the SAME axiom set. A premise about a different graph, or a
premise that is a CLIF proposition rather than an RDF claim, is a
rejection — this is where certificate v1 section 5's splice attack is
closed at the claim level. -/
def premTriples (env : List (String × Claim)) (gd ad : String) :
    List String → Option (List Triple)
  | [] => some []
  | i :: is =>
      match lookupClaim env i, premTriples env gd ad is with
      | some (.rdfDerivable gd' ad' u), some ts =>
          if gd' == gd && ad' == ad then some (u :: ts) else none
      | _, _ => none

/-- Every triple `premTriples` returns was read from a claim the
environment holds, about exactly the graph and axiom set asked for. -/
theorem premTriples_spec {env : List (String × Claim)} {gd ad : String} :
    ∀ {ids : List String} {prem : List Triple},
      premTriples env gd ad ids = some prem →
      ∀ u ∈ prem, ∃ e ∈ env, e.2 = Claim.rdfDerivable gd ad u := by
  intro ids
  induction ids with
  | nil => intro prem h u hu; simp only [premTriples, Option.some.injEq] at h; subst h; cases hu
  | cons i is ih =>
    intro prem h u hu
    simp only [premTriples] at h
    split at h
    · rename_i gd' ad' u0 ts hlk hrec
      split at h
      · rename_i hmatch
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
        obtain ⟨hg, ha⟩ := hmatch
        subst hg; subst ha
        rcases List.mem_cons.1 hu with rfl | hu
        · obtain ⟨e, he, hec⟩ := lookupClaim_mem hlk
          exact ⟨e, he, hec⟩
        · exact ih hrec u hu
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-! ## The foundational rule check

Sixteen rows, three treatments, and every one of them a finite test.

* `base` — the conclusion's triple is IN the inline graph body. Needs
  the body, so a graph the bundle only REFERENCES cannot license a
  base step; that leaf has to be an assumption.
* `axiomatic` — likewise against the inline axiom-set body.
* the fourteen inference rows — decided by `RDFS.stepOk` over the
  SCOPED premise triples alone, against the conclusion read in the
  scope of the step's graph artifact. `RDFS.rowCheck` reads neither
  the graph nor the axiom set for these rows, so the check is local to
  the premises and needs no artifact body at all.

Issue 976: the row is checked on SCOPED triples, so a join on a blank
node succeeds only when both occurrences come from one scope. `_:x`
read from artifact `G1` and `_:x` read from artifact `G2` do not
match, even when `G1` and `G2` share an RDFC-1.0 digest. -/

/-- Rebuild the premise triples as RDFS steps, so the landed
`RDFS.stepOk` can be applied to them positionally. -/
def rdfsPrefix (prem : List Triple) : List Step :=
  prem.map (fun u => mkStep RuleId.base u [])

theorem rdfsPrefix_conclusion {prem : List Triple} {b : Step}
    (h : b ∈ rdfsPrefix prem) : b.conclusion ∈ prem := by
  simp only [rdfsPrefix, List.mem_map] at h
  obtain ⟨u, hu, rfl⟩ := h
  exact hu

/-- The row test for the fourteen inference rows. -/
def inferenceRowOk (r : RuleId) (prem : List Triple) (t : Triple) : Bool :=
  stepOk [] prem (rdfsPrefix prem) (mkStep r t (List.range prem.length))

/-- What an accepted inference row establishes: the conclusion
follows from the premise triples ALONE. Delegated in full to
`RDFS.stepOk_sound`. -/
theorem inferenceRowOk_sound {r : RuleId} {prem : List Triple} {t : Triple}
    (h : inferenceRowOk r prem t = true) : DerivesFull [] prem t := by
  have := stepOk_sound (ax := []) (g := prem) (pre := rdfsPrefix prem)
    (a := mkStep r t (List.range prem.length))
    (fun b hb => DerivesFull.base (rdfsPrefix_conclusion hb)) h
  simpa using this

/-- The whole `rule` justification, with the conclusion read through
`sc`. The kernel uses `ruleStepOk` (`sc := Triple.scoped`); the
identity instance serves only the rejection diagnosis, which asks
whether a refused step would have passed had raw labels joined. -/
def ruleStepOkWith (sc : Scope → Triple → Triple) (b : Bundle)
    (env : List (String × Claim)) (r : RuleId)
    (gaId aaId : String) (concl : Claim) (premIds : List String) : Bool :=
  match artifactById b gaId, artifactById b aaId with
  | some ga, some aa =>
      ga.kind == ArtifactKind.graph && aa.kind == ArtifactKind.graph &&
      (match concl with
       | .clif _ => false
       | .rdfDerivable gd ad t =>
           gd == ga.digest && ad == aa.digest &&
           (match r with
            | .base =>
                premIds.isEmpty &&
                (match ga.body with
                 | some g => decide (t ∈ g)
                 | none => false)
            | .axiomatic =>
                premIds.isEmpty &&
                (match aa.body with
                 | some ax => decide (t ∈ ax)
                 | none => false)
            | _ =>
                match premTriples env gd ad premIds with
                | none => false
                | some prem => inferenceRowOk r prem (sc (.artifact gaId) t)))
  | _, _ => false

/-- The kernel's `rule` check: conclusion read in the scope of the
graph artifact. -/
def ruleStepOk (b : Bundle) (env : List (String × Claim)) (r : RuleId)
    (gaId aaId : String) (concl : Claim) (premIds : List String) : Bool :=
  ruleStepOkWith Triple.scoped b env r gaId aaId concl premIds

/-! ## One step -/

/-- Adoption doc section 8b, as a total test: a step at
`verifiedReplay` must carry a citation. A V step with no citation is
REJECTED — not accepted at `replay`, which would silently rewrite the
producer's claim. -/
def levelEvidenceOk (st : BundleStep) : Bool :=
  match st.level with
  | .verifiedReplay => st.citation.isSome
  | _ => true

/-- One step passes when it is written in this profile, its id is new,
and its justification licenses its conclusion. -/
def stepValid (b : Bundle) (env : List (String × Claim)) (st : BundleStep) : Bool :=
  st.profile == fpp0Profile
  && !(env.any (fun e => e.1 == st.id))
  && levelEvidenceOk st
  && (match st.justification with
      | .rule r ga aa =>
          (st.level == EvidenceLevel.foundational)
            && ruleStepOk b env r ga aa st.conclusion st.premises
      | .adapterEvidence _ _ =>
          !(st.level == EvidenceLevel.foundational)
            && st.premises.all (fun p => (lookupClaim env p).isSome))

/-- The blank-node scope a step's conclusion is read in (issue 976).
A base or inference row reads its conclusion in the scope of its graph
artifact; an axiomatic row in the scope of its axiom artifact; an
adapter step's conclusion is a frontier fact in its own scope. -/
def stepScope (st : BundleStep) : Scope :=
  match st.justification with
  | .rule .axiomatic _ aa => .artifact aa
  | .rule _ ga _ => .artifact ga
  | .adapterEvidence _ _ => .frontier st.id

/-- One left-to-right pass. `env` is the claim environment of the
accepted prefix; the second argument is what is left. Structurally
recursive: no fuel, and equation lemmas the soundness proof uses. -/
def checkSteps (b : Bundle) : List (String × Claim) → List BundleStep → Bool
  | _, [] => true
  | env, st :: rest =>
      stepValid b env st
        && checkSteps b (env ++ [(st.id, st.conclusion.scoped (stepScope st))]) rest

/-! ## The frontier and the support

Adoption doc section 3: every external stage appears as a NAMED
ASSUMPTION rather than being promoted to truth. A step at V, R or A
is exactly such a stage, so the frontier is the declared assumptions
PLUS one promoted assumption per non-foundational step.

The frontier is deliberately reported over the WHOLE bundle rather
than over the support of the conclusion. Over-reporting the frontier
names external dependence the conclusion may not have; under-
reporting hides dependence it does have. Only one of those two errors
can make a bundle look stronger than it is. -/

/-- A non-foundational step, read as the assumption it really is. -/
def promoteStep (st : BundleStep) : Assumption :=
  { id := st.id, subject := st.conclusion, level := st.level }

def frontierOf (b : Bundle) : List Assumption :=
  b.assumptions.toList
    ++ (b.steps.toList.filter (fun st => !(st.level == EvidenceLevel.foundational))).map
         promoteStep

/-- The ids the conclusion depends on. One RIGHT-TO-LEFT fold: a
premise always names something earlier, so by the time the fold
reaches a step it has already seen every step that could cite it.
Finite, total, no fuel. -/
def supportOf (b : Bundle) : List String :=
  let seed := (b.steps.toList.filter (fun st => st.conclusion == b.conclusion)).map (·.id)
  b.steps.toList.foldr
    (fun st acc => if acc.contains st.id then acc ++ st.premises else acc) seed

/-- The level mix over the steps the conclusion actually depends on.
Counting over the whole bundle instead would let a degenerate bundle
(adoption doc section 8a) pad its foundational count with steps its
conclusion does not use. -/
def supportCounts (b : Bundle) : LevelCounts :=
  (b.steps.toList.filter (fun st => (supportOf b).contains st.id)).foldl
    (fun c st => c.bump st.level) LevelCounts.zero

/-- The conclusion must be reached: some step produces it, or some
assumption declares it. A bundle that reaches neither is rejected —
certificate v1 section 5's "a chain that does not reach its claim". -/
def conclusionReached (b : Bundle) : Bool :=
  b.steps.toList.any (fun st => st.conclusion == b.conclusion)
    || b.assumptions.toList.any (fun a => a.subject == b.conclusion)

/-! ## The rejection reason

Diagnosis only: `valid` is the verdict and no theorem reads the text.
It names the first check that failed, so a producer can tell a
blank-node scope conflict (issue 976) from a wrong rule row. -/

/-- The refused step would pass if raw blank-node labels joined across
scopes: its rule check succeeds when the conclusion and the premises
are read WITHOUT scoping. -/
def blankScopeConflict (b : Bundle) (rawEnv : List (String × Claim))
    (st : BundleStep) : Bool :=
  match st.justification with
  | .rule r ga aa =>
      (st.level == EvidenceLevel.foundational)
        && ruleStepOkWith (fun _ t => t) b rawEnv r ga aa st.conclusion st.premises
  | .adapterEvidence _ _ => false

/-- Text for a step that `stepValid` refused. -/
def stepRejection (b : Bundle) (env rawEnv : List (String × Claim))
    (st : BundleStep) : String :=
  if !(st.profile == fpp0Profile) then
    s!"step '{st.id}': profile is not {fpp0Profile}"
  else if env.any (fun e => e.1 == st.id) then
    s!"step '{st.id}': the id is already used by an assumption or an earlier step"
  else if !(levelEvidenceOk st) then
    s!"step '{st.id}': a verifiedReplay step must cite a theorem (adoption doc section 8b)"
  else if blankScopeConflict b rawEnv st then
    s!"step '{st.id}': the step joins blank nodes from different scopes. A blank node "
      ++ "is local to the artifact or assumption it was read from (RDF 1.1 Concepts "
      ++ "sections 3.4 and 3.5; RDF 1.1 Semantics section 5.2: a merge renames blank "
      ++ "nodes apart), so equal labels in two artifacts are different nodes, also when "
      ++ "the artifacts have the same RDFC-1.0 digest. FPP0/1 has no relabelling step: "
      ++ "a premise can cross from one artifact to another only as a triple with no "
      ++ "blank node"
  else
    s!"step '{st.id}': its justification does not license its conclusion"

/-- The first refused step, if any, by the same left-to-right pass as
`checkSteps`, carrying the raw claims beside the scoped ones. -/
def firstRejection (b : Bundle) :
    List (String × Claim) → List (String × Claim) → List BundleStep → Option String
  | _, _, [] => none
  | env, raw, st :: rest =>
      if stepValid b env st then
        firstRejection b (env ++ [(st.id, st.conclusion.scoped (stepScope st))])
          (raw ++ [(st.id, st.conclusion)]) rest
      else some (stepRejection b env raw st)

theorem firstRejection_none_iff (b : Bundle) :
    ∀ (rest : List BundleStep) (env raw : List (String × Claim)),
      firstRejection b env raw rest = none ↔ checkSteps b env rest = true := by
  intro rest
  induction rest with
  | nil => intro env raw; simp [firstRejection, checkSteps]
  | cons st rest ih =>
      intro env raw
      by_cases h : stepValid b env st = true
      · simp only [firstRejection, checkSteps, h, if_true, Bool.true_and]
        exact ih _ _
      · simp [firstRejection, checkSteps, h]

/-- Why `checkBundle` refuses `b`, or `none` when it accepts. -/
def rejectionOf (b : Bundle) : Option String :=
  if !(artifactsOk b.artifacts.toList) then
    some ("artifact table: a duplicate id, or an inline body whose RDFC-1.0 digest "
      ++ "is not the declared digest")
  else if !(assumptionsOk b.assumptions.toList) then
    some "assumption table: a duplicate id, or an assumption at foundational"
  else
    match firstRejection b (assumptionEnv b.assumptions.toList)
        (b.assumptions.toList.map (fun a => (a.id, a.subject))) b.steps.toList with
    | some r => some r
    | none =>
        if conclusionReached b then none
        else some "no step and no assumption states the bundle's conclusion"

/-! ## The kernel -/

/-- **The FPP0 kernel.** Total: three structural passes over finite
lists, no fuel, no fixpoint.

⚠️ `valid = true` is NOT "this was proved". Adoption doc section 8a:
a bundle that declares its own conclusion as an assumption is valid
and proves nothing, and the fields that say so are
`conclusionIsAssumption`, `assumptions` and `counts.foundational`.
This kernel reports that shape rather than rejecting it, because
`Derives artifacts assumptions conclusion` genuinely HOLDS of it —
what the result must not do is let a reader mistake it for a proof,
and `foundational steps: 0` beside a non-empty frontier is that
statement. -/
def checkBundle (b : Bundle) : CheckResult :=
  let ok :=
    artifactsOk b.artifacts.toList
      && assumptionsOk b.assumptions.toList
      && checkSteps b (assumptionEnv b.assumptions.toList) b.steps.toList
      && conclusionReached b
  { valid := ok
    conclusion := b.conclusion
    assumptions := (frontierOf b).toArray
    counts := supportCounts b
    foundationalOnly := ok && (frontierOf b).isEmpty
    conclusionIsAssumption := b.assumptions.toList.any (fun a => a.subject == b.conclusion)
    rejection := rejectionOf b }

/-- The rejection text is present exactly when the bundle is refused. -/
theorem checkBundle_rejection_none_iff (b : Bundle) :
    (checkBundle b).rejection = none ↔ (checkBundle b).valid = true := by
  simp only [checkBundle, rejectionOf]
  by_cases ha : artifactsOk b.artifacts.toList = true
  · by_cases hs : assumptionsOk b.assumptions.toList = true
    · simp only [ha, hs, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
      cases hf : firstRejection b (assumptionEnv b.assumptions.toList)
          (b.assumptions.toList.map (fun a => (a.id, a.subject))) b.steps.toList with
      | some r =>
          have hc : checkSteps b (assumptionEnv b.assumptions.toList) b.steps.toList = false := by
            cases hcs : checkSteps b (assumptionEnv b.assumptions.toList) b.steps.toList
            · rfl
            · rw [← firstRejection_none_iff] at hcs; rw [hcs] at hf; cases hf
          simp [hc]
      | none =>
          have hc := (firstRejection_none_iff b _ _ _).1 hf
          by_cases hr : conclusionReached b = true <;> simp [hc, hr]
    · simp [ha, hs]
  · simp [ha]

/-! ## Soundness

The shape mirrors `RDFS.checkSteps_sound`: an environment invariant
carried left to right, discharged one step at a time. Every claim in
the environment is a SCOPED claim (issue 976), and `Derives` is taken
over the bundle's own artifact table. -/

/-- Γ, as `checkBundle` reports it. -/
abbrev Frontier (b : Bundle) : List Assumption := frontierOf b

/-- The artifact table, as the list `Derives` is indexed by. -/
abbrev Arts (b : Bundle) : List Artifact := b.artifacts.toList

theorem mem_frontier_of_assumption {b : Bundle} {a : Assumption}
    (h : a ∈ b.assumptions.toList) : a ∈ Frontier b :=
  List.mem_append.2 (Or.inl h)

theorem mem_frontier_of_step {b : Bundle} {st : BundleStep}
    (h : st ∈ b.steps.toList) (hlvl : (st.level == EvidenceLevel.foundational) = false) :
    promoteStep st ∈ Frontier b := by
  refine List.mem_append.2 (Or.inr ?_)
  exact List.mem_map_of_mem (List.mem_filter.2 ⟨h, by simp [hlvl]⟩)

/-- One accepted step's conclusion, read in the step's scope, is
`Derives`-derivable from the frontier. Three cases: the fourteen
inference rows delegate to `RDFS.stepOk_sound` through
`inferenceRowOk_sound`; the two leaf rows read the inline body of the
artifact they name; an adapter step is its own assumption. -/
theorem stepValid_sound {b : Bundle} {env : List (String × Claim)} {st : BundleStep}
    (henv : ∀ e ∈ env, Derives (Arts b) (Frontier b) e.2)
    (hpromo : (st.level == EvidenceLevel.foundational) = false → promoteStep st ∈ Frontier b)
    (h : stepValid b env st = true) :
    Derives (Arts b) (Frontier b) (st.conclusion.scoped (stepScope st)) := by
  simp only [stepValid, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, _⟩, hjust⟩ := h
  cases hj : st.justification with
  | adapterEvidence adp det =>
      rw [hj] at hjust
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hjust
      have := Derives.assumption (A := Arts b) (Γ := Frontier b) (hpromo hjust.1)
      have hsc : stepScope st = .frontier st.id := by simp [stepScope, hj]
      rw [hsc]
      simpa [promoteStep] using this
  | rule r gaId aaId =>
      rw [hj] at hjust
      simp only [Bool.and_eq_true] at hjust
      obtain ⟨_, hrule⟩ := hjust
      unfold ruleStepOk ruleStepOkWith at hrule
      split at hrule
      · rename_i ga aa hga haa
        simp only [Bool.and_eq_true] at hrule
        obtain ⟨⟨hkg, hka⟩, hcl⟩ := hrule
        split at hcl
        · exact absurd hcl (by simp)
        · rename_i gd ad t hconcl
          simp only [Bool.and_eq_true, beq_iff_eq] at hcl
          obtain ⟨⟨hgd, had⟩, hrow⟩ := hcl
          rw [hconcl]
          -- the three row treatments
          cases hr : r with
          | base =>
              rw [hr] at hrow
              have hsc : stepScope st = .artifact gaId := by simp [stepScope, hj, hr]
              rw [hsc]
              simp only [Bool.and_eq_true] at hrow
              obtain ⟨_, hbody⟩ := hrow
              cases hbb : ga.body with
              | none => rw [hbb] at hbody; exact absurd hbody (by simp)
              | some g =>
                  rw [hbb] at hbody
                  simp only [decide_eq_true_eq] at hbody
                  have := Derives.rdfsBase (A := Arts b) (Γ := Frontier b) (ad := ad)
                    (artifactById_mem hga) hbb hgd.symm hbody
                  rw [artifactById_id hga] at this
                  exact this
          | axiomatic =>
              rw [hr] at hrow
              have hsc : stepScope st = .artifact aaId := by simp [stepScope, hj, hr]
              rw [hsc]
              simp only [Bool.and_eq_true] at hrow
              obtain ⟨_, hbody⟩ := hrow
              cases hbb : aa.body with
              | none => rw [hbb] at hbody; exact absurd hbody (by simp)
              | some ax =>
                  rw [hbb] at hbody
                  simp only [decide_eq_true_eq] at hbody
                  have := Derives.rdfsAxiom (A := Arts b) (Γ := Frontier b) (gd := gd)
                    (artifactById_mem haa) hbb had.symm hbody
                  rw [artifactById_id haa] at this
                  exact this
          | _ =>
              rw [hr] at hrow
              have hsc : stepScope st = .artifact gaId := by simp [stepScope, hj, hr]
              rw [hsc]
              (cases hpt : premTriples env gd ad st.premises with
               | none => rw [hpt] at hrow; exact absurd hrow (by simp)
               | some prem =>
                   rw [hpt] at hrow
                   refine Derives.rdfsRow (prem := prem) ?_ (inferenceRowOk_sound hrow)
                   intro u hu
                   obtain ⟨e, he, hec⟩ := premTriples_spec hpt u hu
                   have := henv e he
                   rw [hec] at this
                   exact this)
      · exact absurd hrule (by simp)

/-- The pass, as an induction. -/
theorem checkSteps_sound {b : Bundle} :
    ∀ (rest : List BundleStep) (env : List (String × Claim)),
      (∀ e ∈ env, Derives (Arts b) (Frontier b) e.2) →
      (∀ st ∈ rest, (st.level == EvidenceLevel.foundational) = false →
          promoteStep st ∈ Frontier b) →
      checkSteps b env rest = true →
      ∀ st ∈ rest, Derives (Arts b) (Frontier b) (st.conclusion.scoped (stepScope st)) := by
  intro rest
  induction rest with
  | nil => intro env _ _ _ st hst; cases hst
  | cons a as ih =>
    intro env henv hpromo h st hst
    simp only [checkSteps, Bool.and_eq_true] at h
    obtain ⟨ha, has⟩ := h
    have hader : Derives (Arts b) (Frontier b) (a.conclusion.scoped (stepScope a)) :=
      stepValid_sound henv (hpromo a (List.mem_cons_self ..)) ha
    rcases List.mem_cons.1 hst with rfl | hst
    · exact hader
    · refine ih (env ++ [(a.id, a.conclusion.scoped (stepScope a))]) ?_
        (fun x hx => hpromo x (List.mem_cons_of_mem _ hx)) has st hst
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact henv e he
      · rw [List.mem_singleton.1 he]; exact hader

/-- **Soundness of the FPP0 kernel** (adoption doc section 3), with
blank nodes scoped by artifact (issue 976).

If `checkBundle b` reports `valid`, then the conclusion it reports,
read in SOME scope `s` — the scope of the step or assumption that
states it — is `Derives`-derivable over the bundle's artifact table
from the frontier it reports.

UNCONDITIONAL: no hypothesis on `b`, and in particular no hypothesis
that the bundle came from this engine.

⚠️ Read with `checkBundle`'s own warning. This theorem is what
adoption-doc section 8a calls trivially satisfiable by a bundle that
declares its own conclusion: such a bundle IS valid and the theorem
IS true of it. The theorem is a statement about the frontier, not a
verdict that something was proved; `foundationalOnly`, `counts` and
`conclusionIsAssumption` are what carry the verdict. -/
theorem checkBundle_sound {b : Bundle} (h : (checkBundle b).valid = true) :
    ∃ s : Scope, Derives b.artifacts.toList (checkBundle b).assumptions.toList
      ((checkBundle b).conclusion.scoped s) := by
  simp only [checkBundle, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_hart, _hasm⟩, hsteps⟩, hconc⟩ := h
  have hfront : ((frontierOf b).toArray).toList = Frontier b := by simp
  simp only [checkBundle, hfront]
  -- every step's conclusion is derivable, in the step's scope
  have hall : ∀ st ∈ b.steps.toList,
      Derives (Arts b) (Frontier b) (st.conclusion.scoped (stepScope st)) := by
    refine checkSteps_sound b.steps.toList
      (assumptionEnv b.assumptions.toList) ?_ ?_ hsteps
    · intro e he
      obtain ⟨a, ha, hae⟩ := assumptionEnv_mem he
      have := Derives.assumption (A := Arts b) (Γ := Frontier b) (mem_frontier_of_assumption ha)
      rw [hae] at this
      exact this
    · intro st hst hlvl
      exact mem_frontier_of_step hst hlvl
  -- and the conclusion is one of them, or an assumption
  unfold conclusionReached at hconc
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hconc
  rcases hconc with ⟨st, hst, hsc⟩ | ⟨a, ha, hac⟩
  · exact ⟨stepScope st, by rw [← hsc]; exact hall st hst⟩
  · refine ⟨.frontier a.id, ?_⟩
    have := Derives.assumption (A := Arts b) (Γ := Frontier b) (mem_frontier_of_assumption ha)
    rw [hac] at this
    exact this

/-- **Acceptance gives a derivation from the MERGE of the cited
artifacts** (issue 976). For a valid bundle whose conclusion is
`rdfDerivable gd ad t`: there is a scope `s` such that `t`, read in
`s`, is `DerivesFull`-derivable with the RDF 1.1 Semantics section 5.2
merge of the artifacts filed under `ad` as the axiom set and the
merge of the artifacts filed under `gd` as the graph (blank nodes
renamed apart by artifact id, `scopeLabel_inj`).

`hΓ` is about the reported FRONTIER only; `checkBundle_merge` is the
case with an empty frontier, where it is vacuous. -/
theorem checkBundle_merge_frontier {b : Bundle} (h : (checkBundle b).valid = true)
    (hΓ : ∀ a ∈ (checkBundle b).assumptions.toList, ∀ (gd ad : String) (u : Triple),
        a.subject = Claim.rdfDerivable gd ad u →
        DerivesFull (mergeOf b.artifacts.toList ad) (mergeOf b.artifacts.toList gd)
          (u.scoped (.frontier a.id)))
    {gd ad : String} {t : Triple} (hc : b.conclusion = Claim.rdfDerivable gd ad t) :
    ∃ s : Scope, DerivesFull (mergeOf b.artifacts.toList ad)
      (mergeOf b.artifacts.toList gd) (t.scoped s) := by
  obtain ⟨s, hd⟩ := checkBundle_sound h
  refine ⟨s, Derives.toMerge hΓ hd gd ad (t.scoped s) ?_⟩
  show b.conclusion.scoped s = _
  rw [hc]
  rfl

/-- The assumption-free case: `foundationalOnly` gives the merge
derivation with no hypothesis at all. -/
theorem checkBundle_merge {b : Bundle} (h : (checkBundle b).foundationalOnly = true)
    {gd ad : String} {t : Triple} (hc : b.conclusion = Claim.rdfDerivable gd ad t) :
    ∃ s : Scope, DerivesFull (mergeOf b.artifacts.toList ad)
      (mergeOf b.artifacts.toList gd) (t.scoped s) := by
  have hv : (checkBundle b).valid = true := by
    simp only [checkBundle, Bool.and_eq_true] at h ⊢
    exact h.1
  have hempty : (checkBundle b).assumptions.toList = [] := by
    simp only [checkBundle, Bool.and_eq_true, List.isEmpty_iff] at h ⊢
    simp [h.2]
  refine checkBundle_merge_frontier hv ?_ hc
  intro a ha
  rw [hempty] at ha
  cases ha

/-- For a conclusion with no blank node, the scope drops out: the
triple itself is derivable from the merge. This is the statement the
issue 976 bundle violates — `:A rdfs:subClassOf :C` is not derivable
from the merge of its two artifacts, so the kernel must refuse it
(`Proof/Tests.lean`, issue 976 pins). -/
theorem checkBundle_merge_ground {b : Bundle} (h : (checkBundle b).foundationalOnly = true)
    {gd ad : String} {t : Triple} (hc : b.conclusion = Claim.rdfDerivable gd ad t)
    (hg : t.isGround = true) :
    DerivesFull (mergeOf b.artifacts.toList ad) (mergeOf b.artifacts.toList gd) t := by
  obtain ⟨s, hd⟩ := checkBundle_merge h hc
  rw [Triple.scoped_of_isGround s hg] at hd
  exact hd


/-! ## Wrapping an RDFS witness as an FPP0 bundle

The RDFS emitter (`RDFS.fullClosureWithProof`) already produces a
`Derivation` whose premises are POSITIONS in the step array. FPP0
premises are IDS, so the wrapper below is a renaming and nothing
else: it invents no step, drops no step, and changes no rule row. The
bundle it builds is checked by `checkBundle` through the same
`RDFS.stepOk` the RDFS checker uses, which is what "wraps rather than
reimplements" means here.

The two graph artifacts carry INLINE bodies, so the `base` and
`axiomatic` leaf rows are checkable and the resulting bundle has an
EMPTY frontier — the assumption-free special case adoption doc
section 3 names. -/

/-- Positional premise `p` of an RDFS derivation, as an FPP0 step id. -/
def rdfsStepId (i : Nat) : String := "rdfs:" ++ toString i

/-- One RDFS step, renamed into FPP0. -/
def ofRdfsStep (gaId aaId gd ad : String) (i : Nat) (st : Step) : BundleStep :=
  { id := rdfsStepId i
    justification := .rule st.rule gaId aaId
    premises := st.premises.map rdfsStepId
    conclusion := .rdfDerivable gd ad st.conclusion
    level := .foundational
    profile := fpp0Profile
    citation := none }

/-- A whole RDFS witness as an FPP0 bundle over the graph `g` and the
axiom set `ax` it was emitted for, concluding at `concl`. -/
def bundleOfRdfsDerivation (g ax : Graph) (d : Derivation) (concl : Triple) : Bundle :=
  let gd := graphDigest g
  let ad := graphDigest ax
  { artifacts :=
      #[ { id := "G",  kind := .graph, digest := gd, body := some g },
         { id := "AX", kind := .graph, digest := ad, body := some ax } ]
    assumptions := #[]
    steps := (d.toList.zipIdx.map (fun (st, i) => ofRdfsStep "G" "AX" gd ad i st)).toArray
    conclusion := .rdfDerivable gd ad concl }

end L4Factoidal.FPP0
