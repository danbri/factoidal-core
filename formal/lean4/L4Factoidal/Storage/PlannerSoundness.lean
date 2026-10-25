/-
L4Factoidal.Storage.PlannerSoundness — the storage half of the
planner-soundness theorem
(`docs/designissues/2026-09-06-planner-soundness-theorem.md`).

`SPARQL/DatasetRestriction.lean` proves the evaluator half: a fragment
query answers the same over a restricted dataset as over the whole one.
This module turns that into the statement the design record asks for —
that reading only the manifest entries
`ShardManifest.quadEntriesForQueryWithKeys` keeps answers the query as
if every entry had been read — by

* naming the canonical restriction of a dataset (`restrictDataset`) and
  proving it satisfies `DatasetRestricted`;
* composing the evaluator theorem TWICE, once for each of the two
  entry sets, so the only storage obligation left is an equality
  between two RESTRICTED datasets rather than between two answers.

## Why the composition takes that shape

The design record's section 3 states the restriction as
`D S = restrictPred P (D E)`. That is not what the planner produces: an
entry the planner KEEPS may still hold rows the restriction drops — a
block selected by its predicate carries rows whose subject lies outside
the query's zone bounds, and they are read. `D S` is therefore a dataset
BETWEEN `restrict keep (D E)` and `D E`, not the restriction itself.

The repair is to apply the evaluator theorem to each side:

```
eval Q (D S) = eval Q (restrict keep (D S))
             = eval Q (restrict keep (D E))     -- the storage obligation
             = eval Q (D E)
```

so the storage side has to prove an equality of DATASETS, which is a
statement about which quads survive, and never mentions the evaluator.

## Against the denotation (https://github.com/danbri/factoidal/issues/975, B2)

Section 4 states the storage obligation against `Dataset.den`
(`RDF/DatasetDenotation.lean`): `plannerSoundnessSelectDen` and
`plannerSoundnessAskDen` replace the list equality `hagree` by `hcover`, "every
kept quad of the denotation of `dE` is a quad of the denotation of `dS`", plus
`SubEntries dS dE` (the kept entries keep their order), `dE.IsSet`, and a
`keep` that respects RDF term equality. `restrictDataset_eq_of_cover` derives
`hagree` from these, so the old theorems stay and the new ones are corollaries
of them. `indexedDatasetBackend_exact`: the dataset record both theorems
evaluate over is lawful (`DatasetBackendExact`) with the denotation `d.den`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.DatasetRestriction
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.SPARQL.StoreBackendDenotation

namespace L4Factoidal.Storage.PlannerSoundness

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.DatasetRestriction

/-! ## 1. The canonical restriction -/

def restrictDataset (keep : Triple → Bool) (d : Dataset) : Dataset :=
  { default := d.default.filter keep
  , named := restrictNamed keep d.named }

/-- No two named graphs share a name. A dataset that is a set has this
(`Dataset.IsSet.names`, `distinctNames_of_nodup`); `Storage/QuadDataset.lean`'s
`datasetOfQuads` gives it too: it records each graph name once, at its first
occurrence. Until 2026-10-25 the relation compared the key strings of the
names, where an IRI and a blank-node label could spell one key
(https://github.com/danbri/factoidal/issues/975). -/
def distinctNames : List NamedGraph → Prop
  | [] => True
  | ng :: rest => (∀ x ∈ rest, x.name ≠ ng.name) ∧ distinctNames rest

/-- Graph names without a repeat are distinct names. -/
theorem distinctNames_of_nodup : ∀ {l : List NamedGraph}, (l.map (·.name)).Nodup → distinctNames l
  | [], _ => trivial
  | ng :: rest, h => by
      rw [List.map_cons, List.nodup_cons] at h
      exact ⟨fun x hx e => h.1 (e ▸ List.mem_map_of_mem hx), distinctNames_of_nodup h.2⟩

/-- Two graph names that are both the IRI `n` are one name. -/
theorem iriNamed_unique {a b : Subject} {n : Iri} (ha : iriNamed a n = true)
    (hb : iriNamed b n = true) : a = b := by
  cases a with
  | bnode _ => simp [iriNamed] at ha
  | iri i =>
    cases b with
    | bnode _ => simp [iriNamed] at hb
    | iri j =>
      simp only [iriNamed, beq_iff_eq] at ha hb
      exact congrArg Subject.iri (Subtype.ext (ha.trans hb.symm))

theorem lookupGraph_none_of_keys (n : Iri) :
    ∀ l : List NamedGraph, (∀ x ∈ l, iriNamed x.name n = false) → lookupGraph l n = none
  | [], _ => rfl
  | ng :: rest, h => by
      simp only [lookupGraph]
      rw [if_neg (by rw [h ng List.mem_cons_self]; exact Bool.false_ne_true)]
      exact lookupGraph_none_of_keys n rest (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem restrictNamed_keys {keep : Triple → Bool} (n : Iri) :
    ∀ l : List NamedGraph, (∀ x ∈ l, iriNamed x.name n = false) →
      ∀ x ∈ restrictNamed keep l, iriNamed x.name n = false
  | [], _ => by intro x hx; simp [restrictNamed] at hx
  | ng :: rest, h => by
      intro x hx
      rw [restrictNamed_cons] at hx
      split at hx
      · exact restrictNamed_keys n rest
          (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx
      · rcases List.mem_cons.mp hx with hx | hx
        · rw [hx, name_graph]
          exact h ng List.mem_cons_self
        · exact restrictNamed_keys n rest
            (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

theorem lookupGraph_cons_pos {ng : NamedGraph} {rest : List NamedGraph} {n : Iri}
    (hk : iriNamed ng.name n = true) : lookupGraph (ng :: rest) n = some ng.graph := by
  simp only [lookupGraph]
  rw [if_pos hk]

theorem lookupGraph_cons_neg {ng : NamedGraph} {rest : List NamedGraph} {n : Iri}
    (hk : ¬ iriNamed ng.name n = true) : lookupGraph (ng :: rest) n = lookupGraph rest n := by
  simp only [lookupGraph]
  rw [if_neg hk]

/-- The named-graph half of `DatasetRestricted`, for the canonical
restriction. -/
theorem lookupGraph_restrictNamed (keep : Triple → Bool) (n : Iri) :
    ∀ l : List NamedGraph, distinctNames l →
      lookupGraph (restrictNamed keep l) n
          = (lookupGraph l n).map (fun g => g.filter keep)
      ∨ (lookupGraph (restrictNamed keep l) n = none ∧
         ∀ g, lookupGraph l n = some g → g.filter keep = [])
  | [], _ => Or.inl rfl
  | ng :: rest, hdist => by
      rw [restrictNamed_cons]
      by_cases hk : iriNamed ng.name n = true
      · have hlook : lookupGraph (ng :: rest) n = some ng.graph := lookupGraph_cons_pos hk
        have hnone : lookupGraph (restrictNamed keep rest) n = none := by
          refine lookupGraph_none_of_keys n _ (restrictNamed_keys n rest ?_)
          intro x hx
          cases hkx : iriNamed x.name n with
          | false => rfl
          | true => exact absurd (iriNamed_unique hkx hk) (hdist.1 x hx)
        by_cases hz : (ng.graph.filter keep).isEmpty = true
        · refine Or.inr ⟨by rw [if_pos hz]; exact hnone, ?_⟩
          intro g hg
          rw [hlook] at hg
          rw [← Option.some.inj hg]
          exact List.isEmpty_iff.mp hz
        · refine Or.inl ?_
          rw [if_neg hz, hlook,
            lookupGraph_cons_pos (ng := { ng with graph := ng.graph.filter keep })
              (rest := restrictNamed keep rest) (by rw [name_graph]; exact hk)]
          rfl
      · rw [lookupGraph_cons_neg hk]
        by_cases hz : (ng.graph.filter keep).isEmpty = true
        · rw [if_pos hz]
          exact lookupGraph_restrictNamed keep n rest hdist.2
        · rw [if_neg hz,
            lookupGraph_cons_neg (ng := { ng with graph := ng.graph.filter keep })
              (rest := restrictNamed keep rest) (by rw [name_graph]; exact hk)]
          exact lookupGraph_restrictNamed keep n rest hdist.2

/-- **The canonical restriction satisfies the relation.** -/
theorem datasetRestricted_restrictDataset (keep : Triple → Bool)
    (readable : Option (List WfIri)) (d : Dataset)
    (hdist : distinctNames d.named) (hne : ∀ ng ∈ d.named, ng.graph ≠ []) :
    DatasetRestricted keep readable d (restrictDataset keep d) :=
  { dflt := rfl
  , named := fun i _ => by
      rcases lookupGraph_restrictNamed keep i.val d.named hdist with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨h1, fun g hg => ⟨h2 g hg, ?_⟩⟩
        obtain ⟨ng, hng, hngg⟩ := lookupGraph_mem d.named i.val g hg
        rw [← hngg]
        exact hne ng hng
  , namedList := fun _ => namedRestricted_restrictNamed keep d.named hne }

/-! ## 2. The composition -/

/-- **Planner soundness for SELECT.** `dE` is the dataset every manifest entry
denotes, `dS` the dataset the entries the planner keeps denote. The storage
obligation is `hagree`: the two datasets carry the same quads once the
restriction is applied — which is what "a skipped entry cannot contribute a
row" says, with no evaluator in it. -/
theorem plannerSoundnessSelect (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {dE dS : Dataset} (q : Query)
    (hdistE : distinctNames dE.named) (hneE : ∀ ng ∈ dE.named, ng.graph ≠ [])
    (hdistS : distinctNames dS.named) (hneS : ∀ ng ∈ dS.named, ng.graph ≠ [])
    (hagree : restrictDataset keep dS = restrictDataset keep dE)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runSelectQueryBackendDataset env q (indexedDatasetBackend dS)
      = runSelectQueryBackendDataset env q (indexedDatasetBackend dE) := by
  have hS := runSelectQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dS hdistS hneS) q hf hk hn hv
  have hE := runSelectQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dE hdistE hneE) q hf hk hn hv
  rw [← hS, ← hE, hagree]

/-- **Planner soundness for ASK.** -/
theorem plannerSoundnessAsk (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {dE dS : Dataset} (q : Query)
    (hdistE : distinctNames dE.named) (hneE : ∀ ng ∈ dE.named, ng.graph ≠ [])
    (hdistS : distinctNames dS.named) (hneS : ∀ ng ∈ dS.named, ng.graph ≠ [])
    (hagree : restrictDataset keep dS = restrictDataset keep dE)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runAskQueryBackendDataset env q (indexedDatasetBackend dS)
      = runAskQueryBackendDataset env q (indexedDatasetBackend dE) := by
  have hS := runAskQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dS hdistS hneS) q hf hk hn hv
  have hE := runAskQueryBackendDataset_restrict env
    (datasetRestricted_restrictDataset keep readable dE hdistE hneE) q hf hk hn hv
  rw [← hS, ← hE, hagree]

/-! ## 3. The predicate collector establishes `PatternKept`

`keepPred P` is the restriction the predicate collector justifies: keep the
triples whose predicate is in `P`. What has to be shown is that a pattern the
collector admits presents only bounds this restriction keeps, which is the
`PatternKept` hypothesis of the evaluator theorem. -/

def keepPred (P : List WfIri) (t : Triple) : Bool := P.contains t.p

theorem tpKept_of_constPred {P : List WfIri} {tp : TriplePattern} {pred : WfIri}
    (hp : tp.p = .iri pred) (hm : P.contains pred = true) : TpKept (keepPred P) tp := by
  intro mu t hb
  simp only [boundMatches, patternBoundFor, boundPredicateOfPattern, hp,
    Bool.and_eq_true] at hb
  have heq : pred = t.p := Subtype.ext (by simpa using hb.1.2)
  simp only [keepPred, ← heq, hm]

theorem TpKept_mono {keep keep' : Triple → Bool}
    (h : ∀ t, keep t = true → keep' t = true) {tp : TriplePattern} :
    TpKept keep tp → TpKept keep' tp :=
  fun hk mu t hb => h t (hk mu t hb)

theorem PatternKept_mono {keep keep' : Triple → Bool}
    (h : ∀ t, keep t = true → keep' t = true) :
    ∀ p : QueryPattern, PatternKept keep p → PatternKept keep' p
  | .bgp [], hk => fun t => h t (hk t)
  | .bgp (tp :: rest), hk => fun x hx => TpKept_mono h (hk x hx)
  | .empty, hk => fun t => h t (hk t)
  | .join a b, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .union a b, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .minus a b, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .leftJoin a b _, hk =>
      ⟨PatternKept_mono h a hk.1, PatternKept_mono h b hk.2⟩
  | .filter _ p, hk => PatternKept_mono h p hk
  | .bind _ _ p, hk => PatternKept_mono h p hk
  | .graph _ p, hk => PatternKept_mono h p hk
  | .lateral _ _, _ => trivial
  | .values _ _, _ => trivial
  | .service _ _ _, _ => trivial
  | .serviceVar _ _ _, _ => trivial
  | .subSelect _, _ => trivial
  | .propertyPath _ _ _, _ => trivial

theorem keepPred_mono_append_left (P Q : List WfIri) :
    ∀ t, keepPred P t = true → keepPred (P ++ Q) t = true := by
  intro t h
  simp only [keepPred, List.contains_append, Bool.or_eq_true]
  exact Or.inl h

theorem keepPred_mono_append_right (P Q : List WfIri) :
    ∀ t, keepPred Q t = true → keepPred (P ++ Q) t = true := by
  intro t h
  simp only [keepPred, List.contains_append, Bool.or_eq_true]
  exact Or.inr h

/-- The fold `quadNativeConstantPredicates?` runs over a BGP. -/
def predsOf (ps : Bgp) : Option (List WfIri) :=
  ps.foldr (fun pattern rest => do
    let predicates ← rest
    match pattern.p with
    | .iri predicate => some (predicate :: predicates)
    | _ => none) (some [])

theorem predsOf_cons (tp : TriplePattern) (rest : Bgp) :
    predsOf (tp :: rest)
      = (do
          let preds ← predsOf rest
          match tp.p with
          | .iri predicate => some (predicate :: preds)
          | _ => none) := rfl

theorem quadNativeConstantPredicates_bgp (ps : Bgp) :
    ShardManifest.quadNativeConstantPredicates? (.bgp ps)
      = if ps.isEmpty then none else predsOf ps := by
  cases ps <;> rfl

theorem predsOf_mem : ∀ (ps : Bgp) (P : List WfIri), predsOf ps = some P →
    ∀ tp ∈ ps, ∃ pred, tp.p = .iri pred ∧ P.contains pred = true
  | [], P, h => by
      intro _tp htp
      simp at htp
  | tp :: rest, P, h => by
      intro x hx
      rw [predsOf_cons] at h
      cases hr : predsOf rest with
      | none => rw [hr] at h; simp at h
      | some P' =>
          rw [hr] at h
          simp only [bind, Option.bind] at h
          cases hp : tp.p with
          | iri pred =>
              rw [hp] at h
              simp only [Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp hx with hx | hx
              · exact ⟨pred, by rw [hx, hp], by simp⟩
              · obtain ⟨q, hq1, hq2⟩ := predsOf_mem rest P' hr x hx
                exact ⟨q, hq1, by simp only [List.contains_cons, Bool.or_eq_true]; exact Or.inr hq2⟩
          | var _ => rw [hp] at h; simp at h
          | bnode _ => rw [hp] at h; simp at h
          | literal _ => rw [hp] at h; simp at h
          | tripleTerm _ _ _ => rw [hp] at h; simp at h

/-- **The predicate collector's guarantee.** -/
theorem patternKept_of_quadPredicates :
    ∀ (p : QueryPattern) (P : List WfIri),
      ShardManifest.quadNativeConstantPredicates? p = some P → PatternKept (keepPred P) p
  | .bgp ps, P, h => by
      rw [quadNativeConstantPredicates_bgp] at h
      cases hps : ps with
      | nil => rw [hps] at h; simp at h
      | cons tp rest =>
          rw [hps] at h
          simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
          intro x hx
          obtain ⟨pred, h1, h2⟩ := predsOf_mem (tp :: rest) P h x hx
          exact tpKept_of_constPred h1 h2
  | .join a b, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      cases ha : ShardManifest.quadNativeConstantPredicates? a with
      | none => rw [ha] at h; simp at h
      | some l =>
          cases hb : ShardManifest.quadNativeConstantPredicates? b with
          | none => rw [ha, hb] at h; simp at h
          | some r =>
              rw [ha, hb] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              subst h
              exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                       (patternKept_of_quadPredicates a l ha),
                     PatternKept_mono (keepPred_mono_append_right l r) b
                       (patternKept_of_quadPredicates b r hb)⟩
  | .union a b, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      cases ha : ShardManifest.quadNativeConstantPredicates? a with
      | none => rw [ha] at h; simp at h
      | some l =>
          cases hb : ShardManifest.quadNativeConstantPredicates? b with
          | none => rw [ha, hb] at h; simp at h
          | some r =>
              rw [ha, hb] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              subst h
              exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                       (patternKept_of_quadPredicates a l ha),
                     PatternKept_mono (keepPred_mono_append_right l r) b
                       (patternKept_of_quadPredicates b r hb)⟩
  | .minus a b, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      cases ha : ShardManifest.quadNativeConstantPredicates? a with
      | none => rw [ha] at h; simp at h
      | some l =>
          cases hb : ShardManifest.quadNativeConstantPredicates? b with
          | none => rw [ha, hb] at h; simp at h
          | some r =>
              rw [ha, hb] at h
              simp only [bind, Option.bind, Option.some.injEq] at h
              subst h
              exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                       (patternKept_of_quadPredicates a l ha),
                     PatternKept_mono (keepPred_mono_append_right l r) b
                       (patternKept_of_quadPredicates b r hb)⟩
  | .leftJoin a b c, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      split at h
      · cases ha : ShardManifest.quadNativeConstantPredicates? a with
        | none => rw [ha] at h; simp at h
        | some l =>
            cases hb : ShardManifest.quadNativeConstantPredicates? b with
            | none => rw [ha, hb] at h; simp at h
            | some r =>
                rw [ha, hb] at h
                simp only [bind, Option.bind, Option.some.injEq] at h
                subst h
                exact ⟨PatternKept_mono (keepPred_mono_append_left l r) a
                         (patternKept_of_quadPredicates a l ha),
                       PatternKept_mono (keepPred_mono_append_right l r) b
                         (patternKept_of_quadPredicates b r hb)⟩
      · simp at h
  | .filter c p, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      split at h
      · exact patternKept_of_quadPredicates p P h
      · simp at h
  | .bind _ _ p, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      split at h
      · exact patternKept_of_quadPredicates p P h
      · simp at h
  | .graph n p, P, h => by
      simp only [ShardManifest.quadNativeConstantPredicates?] at h
      exact patternKept_of_quadPredicates p P h
  | .propertyPath _ _ _, _, _ => trivial
  | .lateral _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .values _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .service _ _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .serviceVar _ _ _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .subSelect _, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h
  | .empty, _, h => by simp [ShardManifest.quadNativeConstantPredicates?] at h

/-- The query-level form: what the planner's guard establishes. -/
theorem patternKept_of_queryPredicates (q : Query) (P : List WfIri)
    (h : ShardManifest.queryQuadConstantPredicates? q = some P) :
    PatternKept (keepPred P) q.pattern.rewriteBnodes := by
  simp only [ShardManifest.queryQuadConstantPredicates?] at h
  split at h
  · exact patternKept_of_quadPredicates _ P h
  · simp at h

/-! ## 4. The storage obligation against the denotation (issue 975, step B2)

`plannerSoundnessSelect` and `plannerSoundnessAsk` take the storage obligation
as a LIST equality, `restrictDataset keep dS = restrictDataset keep dE`. That
is a statement about representations. Here it is derived from a statement
about denotations (`Dataset.den`, `RDF/DatasetDenotation.lean`):

* `hcover`: every quad of the denotation of `dE` that `keep` keeps is a quad of
  the denotation of `dS`. This is "a skipped entry cannot contribute a row",
  with no list in it;
* `hsub` (`SubEntries dS dE`): the lists of `dS` are sublists of those of
  `dE`, in order. This is what reading a subset of the entries gives;
* `hset`: `dE` is a set (`Dataset.IsSet`);
* `hkeep`: `keep` respects RDF term equality (`keepPred P` does:
  `keepPred_key`).

`restrictDataset_eq_of_cover` derives the list equality from these.
`plannerSoundnessSelectDen` and `plannerSoundnessAskDen` are the two planner
theorems with `hcover` in place of `hagree`; the old theorems stay, and the new
ones are proved from them.

A premise about denotations alone cannot give the conclusion. The conclusion
equates two solution SEQUENCES, and a sequence depends on the order of the
rows the store returns; two lists with one denotation are a permutation of each
other (`Dataset.IsSet.default_perm_of_den_eq`), not one list. `hsub` is the
premise that fixes the order: the kept entries keep the order of all entries.

`indexedDatasetBackend_exact`: the dataset record the planner theorems
evaluate over, `indexedDatasetBackend d`, is lawful with the denotation
`d.den` (`DatasetBackendExact`), for a set with distinct graph-name keys. -/

/-- `l₁` keeps some of the named graphs of `l₂`, in order, each with a
sublist of its triples. -/
inductive NamedSub : List NamedGraph → List NamedGraph → Prop
  | nil : NamedSub [] []
  | skip {l₁ l₂ : List NamedGraph} (ng : NamedGraph) : NamedSub l₁ l₂ → NamedSub l₁ (ng :: l₂)
  | cons {l₁ l₂ : List NamedGraph} (ng ng' : NamedGraph) (hn : ng.name = ng'.name)
      (hg : ng.graph.Sublist ng'.graph) : NamedSub l₁ l₂ → NamedSub (ng :: l₁) (ng' :: l₂)

/-- The lists of `dS` keep some entries of the lists of `dE`, in order. -/
def SubEntries (dS dE : Dataset) : Prop :=
  dS.default.Sublist dE.default ∧ NamedSub dS.named dE.named

theorem NamedSub.names_sub : ∀ {l₁ l₂ : List NamedGraph}, NamedSub l₁ l₂ →
    ∀ y ∈ l₁, y.name ∈ l₂.map (·.name)
  | _, _, .nil, y, hy => absurd hy List.not_mem_nil
  | _, _, .skip _ h, y, hy => List.mem_cons_of_mem _ (h.names_sub y hy)
  | _, _, .cons ng ng' hn _ h, y, hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · rw [hn]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h.names_sub y hy)

/-- A sublist that holds every entry of a list without RDF-term-equal entries,
up to RDF term equality, is the list. -/
theorem eq_of_sublist_keyCover : ∀ {l₁ l₂ : Graph}, l₁.Sublist l₂ → l₂.KeyNodup →
    (∀ t ∈ l₂, KeyMem l₁ t) → l₁ = l₂
  | _, _, .slnil, _, _ => rfl
  | _, _, @List.Sublist.cons _ _ l₂ a h, hn, hc => by
      obtain ⟨u, hu, e⟩ := hc a List.mem_cons_self
      have hn' : a.key ∉ l₂.map Triple.key := (List.nodup_cons.mp hn).1
      exact absurd (List.mem_map.mpr ⟨u, h.subset hu, e⟩) hn'
  | _, _, .cons_cons a h, hn, hc => by
      have hn' := List.nodup_cons.mp hn
      congr 1
      refine eq_of_sublist_keyCover h hn'.2 (fun t ht => ?_)
      obtain ⟨u, hu, e⟩ := hc t (List.mem_cons_of_mem _ ht)
      rcases List.mem_cons.mp hu with rfl | hu
      · exact absurd (List.mem_map.mpr ⟨t, ht, e.symm⟩) hn'.1
      · exact ⟨u, hu, e⟩

/-- A `NamedSub` of a list with distinct names and set graphs that holds each
name and each triple of each graph is the list. -/
theorem eq_of_namedSub : ∀ {l₁ l₂ : List NamedGraph}, NamedSub l₁ l₂ →
    (l₂.map (·.name)).Nodup → (∀ x ∈ l₂, x.graph.KeyNodup) →
    (∀ x ∈ l₂, ∃ y ∈ l₁, y.name = x.name) →
    (∀ x ∈ l₂, ∀ t ∈ x.graph, ∃ y ∈ l₁, y.name = x.name ∧ KeyMem y.graph t) → l₁ = l₂
  | _, _, .nil, _, _, _, _ => rfl
  | _, _, .skip ng h, hnd, _, hnm, _ => by
      obtain ⟨y, hy, e⟩ := hnm ng List.mem_cons_self
      have := h.names_sub y hy
      rw [e] at this
      exact absurd this (List.nodup_cons.mp hnd).1
  | _, _, @NamedSub.cons l₁ _ ng ng' hn hg h, hnd, hk, hnm, hcv => by
      have hnd' := List.nodup_cons.mp hnd
      simp only at hnd'
      have notTail : ∀ y ∈ l₁, y.name ≠ ng'.name := by
        intro y hy e
        have hm := h.names_sub y hy
        rw [e] at hm
        exact hnd'.1 hm
      have hgr : ng.graph = ng'.graph := by
        refine eq_of_sublist_keyCover hg (hk ng' List.mem_cons_self) (fun t ht => ?_)
        obtain ⟨y, hy, e, hm⟩ := hcv ng' List.mem_cons_self t ht
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hm
        · exact absurd e (notTail y hy)
      have hhead : ng = ng' := by
        obtain ⟨n1, g1⟩ := ng
        obtain ⟨n2, g2⟩ := ng'
        simp only at hn hgr
        rw [hn, hgr]
      rw [hhead]
      congr 1
      refine eq_of_namedSub h hnd'.2 (fun x hx => hk x (List.mem_cons_of_mem _ hx)) ?_ ?_
      · intro x hx
        obtain ⟨y, hy, e⟩ := hnm x (List.mem_cons_of_mem _ hx)
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [hn] at e
          have hm : x.name ∈ _ := List.mem_map_of_mem (f := fun x : NamedGraph => x.name) hx
          rw [← e] at hm
          exact absurd hm hnd'.1
        · exact ⟨y, hy, e⟩
      · intro x hx t ht
        obtain ⟨y, hy, e, hm⟩ := hcv x (List.mem_cons_of_mem _ hx) t ht
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [hn] at e
          have hm' : x.name ∈ _ := List.mem_map_of_mem (f := fun x : NamedGraph => x.name) hx
          rw [← e] at hm'
          exact absurd hm' hnd'.1
        · exact ⟨y, hy, e, hm⟩

theorem mem_restrictNamed {keep : Triple → Bool} : ∀ {l : List NamedGraph} {x : NamedGraph},
    x ∈ restrictNamed keep l →
      ∃ ng ∈ l, x = { ng with graph := ng.graph.filter keep } ∧ ng.graph.filter keep ≠ []
  | [], _, hx => by simp [restrictNamed] at hx
  | ng :: rest, x, hx => by
      rw [restrictNamed_cons] at hx
      split at hx
      · obtain ⟨y, hy, e, hne⟩ := mem_restrictNamed hx
        exact ⟨y, List.mem_cons_of_mem _ hy, e, hne⟩
      · rename_i hz
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨ng, List.mem_cons_self, rfl, by simpa using hz⟩
        · obtain ⟨y, hy, e, hne⟩ := mem_restrictNamed hx
          exact ⟨y, List.mem_cons_of_mem _ hy, e, hne⟩

theorem restrictNamed_mem {keep : Triple → Bool} : ∀ {l : List NamedGraph} {ng : NamedGraph},
    ng ∈ l → ng.graph.filter keep ≠ [] →
      { ng with graph := ng.graph.filter keep } ∈ restrictNamed keep l
  | [], _, h, _ => absurd h List.not_mem_nil
  | y :: rest, ng, h, hne => by
      rw [restrictNamed_cons]
      rcases List.mem_cons.mp h with rfl | h
      · rw [if_neg (by simpa using hne)]
        exact List.mem_cons_self
      · split
        · exact restrictNamed_mem h hne
        · exact List.mem_cons_of_mem _ (restrictNamed_mem h hne)

theorem restrictNamed_names_sublist (keep : Triple → Bool) : ∀ l : List NamedGraph,
    ((restrictNamed keep l).map (·.name)).Sublist (l.map (·.name))
  | [] => by simp [restrictNamed]
  | ng :: rest => by
      rw [restrictNamed_cons]
      split
      · exact (restrictNamed_names_sublist keep rest).cons _
      · exact (restrictNamed_names_sublist keep rest).cons_cons _

theorem NamedSub.restrict (keep : Triple → Bool) : ∀ {l₁ l₂ : List NamedGraph}, NamedSub l₁ l₂ →
    NamedSub (restrictNamed keep l₁) (restrictNamed keep l₂)
  | _, _, .nil => .nil
  | _, _, .skip ng h => by
      rw [restrictNamed_cons]
      split
      · exact h.restrict keep
      · exact .skip _ (h.restrict keep)
  | _, _, .cons ng ng' hn hg h => by
      rw [restrictNamed_cons, restrictNamed_cons]
      have hsub : (ng.graph.filter keep).Sublist (ng'.graph.filter keep) := hg.filter keep
      by_cases h2 : (ng'.graph.filter keep).isEmpty = true
      · have h1 : (ng.graph.filter keep).isEmpty = true := by
          rw [List.isEmpty_iff] at h2 ⊢
          rw [h2] at hsub
          exact List.eq_nil_of_sublist_nil hsub
        rw [if_pos h1, if_pos h2]
        exact h.restrict keep
      · rw [if_neg h2]
        split
        · exact .skip _ (h.restrict keep)
        · exact .cons _ _ hn hsub (h.restrict keep)

/-- `keepPred P` respects RDF term equality: the key does not change the
predicate. -/
theorem keepPred_key (P : List WfIri) (t u : Triple) (e : t.key = u.key) :
    keepPred P t = keepPred P u := by
  have : t.p = u.p := show t.key.p = u.key.p from congrArg Triple.p e
  simp [keepPred, this]

/-- **The storage obligation from the denotation.** -/
theorem restrictDataset_eq_of_cover {keep : Triple → Bool} {dS dE : Dataset}
    (hsub : SubEntries dS dE) (hset : dE.IsSet)
    (hkeep : ∀ t u, t.key = u.key → keep t = keep u)
    (hcover : ∀ gn t, keep t = true → dE.den.graph gn t → dS.den.graph gn t) :
    restrictDataset keep dS = restrictDataset keep dE := by
  unfold restrictDataset
  congr 1
  · refine eq_of_sublist_keyCover (hsub.1.filter keep) (keyNodup_filter hset.default keep) ?_
    intro t ht
    obtain ⟨htE, hkt⟩ := List.mem_filter.mp ht
    have hS := hcover none t hkt (Dataset.den_graph_of_listQuad htE)
    obtain ⟨u, hu, e⟩ := (Dataset.den_graph_iff dS none t).mp hS
    exact ⟨u, List.mem_filter.mpr ⟨hu, (hkeep u t e).trans hkt⟩, e⟩
  · have hcv : ∀ x ∈ restrictNamed keep dE.named, ∀ t ∈ x.graph,
        ∃ y ∈ restrictNamed keep dS.named, y.name = x.name ∧ KeyMem y.graph t := by
      intro x hx t ht
      obtain ⟨ng, hng, rfl, _⟩ := mem_restrictNamed hx
      obtain ⟨htE, hkt⟩ := List.mem_filter.mp ht
      have hS := hcover (some ng.name) t hkt
        (Dataset.den_graph_of_listQuad (ds := dE) ⟨ng, hng, rfl, htE⟩)
      obtain ⟨u, ⟨ng₂, hng₂, hn₂, hu⟩, e⟩ := (Dataset.den_graph_iff dS _ t).mp hS
      have hku : keep u = true := (hkeep u t e).trans hkt
      have hne : ng₂.graph.filter keep ≠ [] :=
        List.ne_nil_of_mem (List.mem_filter.mpr ⟨hu, hku⟩)
      exact ⟨_, restrictNamed_mem hng₂ hne, hn₂, u, List.mem_filter.mpr ⟨hu, hku⟩, e⟩
    refine eq_of_namedSub (hsub.2.restrict keep)
      (List.Nodup.sublist (restrictNamed_names_sublist keep dE.named) hset.names)
      (fun x hx => ?_) (fun x hx => ?_) hcv
    · obtain ⟨ng, hng, rfl, _⟩ := mem_restrictNamed hx
      exact keyNodup_filter (hset.graphs ng hng) keep
    · obtain ⟨ng, hng, rfl, hne⟩ := mem_restrictNamed hx
      obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ hne
      obtain ⟨y, hy, e, _⟩ := hcv _ hx t ht
      exact ⟨y, hy, e⟩

/-- **Planner soundness for SELECT, against the denotation.** -/
theorem plannerSoundnessSelectDen (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {dE dS : Dataset} (q : Query)
    (hdistE : distinctNames dE.named) (hneE : ∀ ng ∈ dE.named, ng.graph ≠ [])
    (hdistS : distinctNames dS.named) (hneS : ∀ ng ∈ dS.named, ng.graph ≠ [])
    (hsub : SubEntries dS dE) (hset : dE.IsSet)
    (hkeep : ∀ t u, t.key = u.key → keep t = keep u)
    (hcover : ∀ gn t, keep t = true → dE.den.graph gn t → dS.den.graph gn t)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runSelectQueryBackendDataset env q (indexedDatasetBackend dS)
      = runSelectQueryBackendDataset env q (indexedDatasetBackend dE) :=
  plannerSoundnessSelect env q hdistE hneE hdistS hneS
    (restrictDataset_eq_of_cover hsub hset hkeep hcover) hf hk hn hv

/-- **Planner soundness for ASK, against the denotation.** -/
theorem plannerSoundnessAskDen (env : EvalEnv) {keep : Triple → Bool}
    {readable : Option (List WfIri)} {dE dS : Dataset} (q : Query)
    (hdistE : distinctNames dE.named) (hneE : ∀ ng ∈ dE.named, ng.graph ≠ [])
    (hdistS : distinctNames dS.named) (hneS : ∀ ng ∈ dS.named, ng.graph ≠ [])
    (hsub : SubEntries dS dE) (hset : dE.IsSet)
    (hkeep : ∀ t u, t.key = u.key → keep t = keep u)
    (hcover : ∀ gn t, keep t = true → dE.den.graph gn t → dS.den.graph gn t)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes)
    (hn : ∀ i ∈ graphNamesIn q.pattern.rewriteBnodes, readableName readable i)
    (hv : graphVarIn q.pattern.rewriteBnodes = true → readable = none) :
    runAskQueryBackendDataset env q (indexedDatasetBackend dS)
      = runAskQueryBackendDataset env q (indexedDatasetBackend dE) :=
  plannerSoundnessAsk env q hdistE hneE hdistS hneS
    (restrictDataset_eq_of_cover hsub hset hkeep hcover) hf hk hn hv

/-! ### The dataset record is lawful -/

open L4Factoidal.SPARQL.StoreBackend (BackendExact)

/-- A dataset record reads the dataset denotation `D`: the default backend
reads the default graph; each named backend reads the graph of a name of `D`,
the backend's name; every name of `D` has a backend; no two backends share a
name. -/
structure DatasetBackendExact (D : DatasetDen) (dsb : DatasetBackend) : Prop where
  default : BackendExact dsb.default (D.graph none)
  named : ∀ ngb ∈ dsb.named, ∃ n, D.names n ∧ n = ngb.name ∧
    BackendExact ngb.backend (D.graph (some n))
  names : ∀ n, D.names n → ∃ ngb ∈ dsb.named, n = ngb.name
  namesNodup : (dsb.named.map (·.name)).Nodup

theorem distinctNames_nodup : ∀ {l : List NamedGraph}, distinctNames l → (l.map (·.name)).Nodup
  | [], _ => List.nodup_nil
  | ng :: rest, h => by
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, distinctNames_nodup h.2⟩
      obtain ⟨x, hx, e⟩ := List.mem_map.mp hm
      exact h.1 x hx e

/-- **The planner's dataset record is lawful**: `indexedDatasetBackend d`
reads `d.den`, for every dataset that is a set. Until 2026-10-25 this also
took `distinctNames d.named`, because the record keyed a blank-node graph name
by its label string (https://github.com/danbri/factoidal/issues/975). -/
theorem indexedDatasetBackend_exact {d : Dataset} (hset : d.IsSet) :
    DatasetBackendExact d.den (indexedDatasetBackend d) where
  default := ⟨d.default, OWL.RL.Index.Wf.ofGraph _, hset.default,
    Dataset.den_default_iff_keyMem (ds := d)⟩
  named ngb hngb := by
    rw [indexedDatasetBackend_named] at hngb
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.mp hngb
    exact ⟨ng.name, List.mem_map.mpr ⟨ng, hng, rfl⟩, rfl,
      ⟨ng.graph, OWL.RL.Index.Wf.ofGraph _, hset.graphs ng hng,
        Dataset.IsSet.graph_iff_keyMem_named hset hng⟩⟩
  names n hn := by
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.mp hn
    refine ⟨⟨ng.name, indexedGraphBackend ng.graph⟩, ?_, rfl⟩
    rw [indexedDatasetBackend_named]
    exact List.mem_map.mpr ⟨ng, hng, rfl⟩
  namesNodup := by
    rw [indexedDatasetBackend_named, List.map_map]
    exact hset.names

#print axioms PatternKept_mono
#print axioms patternKept_of_quadPredicates
#print axioms patternKept_of_queryPredicates
#print axioms plannerSoundnessSelect
#print axioms plannerSoundnessAsk
#print axioms eq_of_sublist_keyCover
#print axioms eq_of_namedSub
#print axioms restrictDataset_eq_of_cover
#print axioms indexedDatasetBackend_exact
#print axioms distinctNames_of_nodup
#print axioms iriNamed_unique
#print axioms plannerSoundnessSelectDen
#print axioms plannerSoundnessAskDen

end L4Factoidal.Storage.PlannerSoundness
