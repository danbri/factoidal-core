/-
L4Factoidal.Dataflow.ExplainGraph — the stage `rdfsExplainGraphStage`:
sources and a description in, a verdict with its evidence out
(https://github.com/danbri/factoidal/issues/1002, first step).

| stage | in → out | contract |
|---|---|---|
| `rdfsExplainGraphStage D sel` | `Dataset × Graph` → `ExplainGraphResult` | `ExplainGraphContract` |

## The run

`explainGraphOf D g E`, with `g` the union of the selected graphs
(`Dataset.select`, one blank-node scope) and `E` the description:

1. close `g` with its derivation (`fullClosureWithProof`, the `rdf:_n` slice
   of `g` and `E`);
2. look for one instance mapping of `E` into the closure (`findInstance`);
3. found: emit a `GraphBundle` (the mapping, the derivation cut down to the
   steps the instance uses, one step index per triple of `E`), and run the
   graph checker `checkGraphRun` on it. Accepted: `entailed = true`;
4. not found: `entailed = false`, and the rejection says why: `noMatch i t`
   when triple `i` of `E` has no instance in the closure alone,
   `noJointMapping` when every triple has one but no single mapping serves
   all of them (a shared blank node).

## The contract

* `entailed = true`: the bundle is returned, the graph checker accepts it,
  and `RdfsEntails (· ∈ D) g E`. Proved; no assumption.
* `entailed = false` with `noMatch` or `noJointMapping`: NO instance of `E`
  is in the closure (`¬ SimpleEntailmentSpec (fullClosure …) E`). Proved.
  Reading this as "not RDFS-entailed" also needs completeness of the closure
  (RDF 1.1 Semantics Appendix A, for an RDFS-consistent `g`). That is not
  proved here; `assumptions` names it (`notEntailedAssumptions`).
* `entailed = false` with `checkerRefused`: the emitted bundle was refused.
  That is an emitter defect; the verdict says nothing about entailment. That
  every emitted bundle is accepted is TESTED only (`ExplainGraphTests.lean`).

## Not done

* Completeness of explain (`E` entailed implies `entailed = true`) needs the
  completeness of the RDFS closure and a proof that the cut derivation is
  accepted; neither is proved.
* The bundle is a Lean value and a JSON form of the wasm op
  (`Wasm/Ops/Explain.lean`); it is not an FPP0 bundle, so npm `proofCheck`
  does not read it (`Dataflow/GraphClaim.lean` says why one FPP0 bundle per
  triple does not give the description).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Checker

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-! ## Cutting a derivation down to the steps a set of roots uses -/

/-- Mark index `i` of `a` when it is in range. -/
def markIdx (a : Array Bool) (i : Nat) : Array Bool := if i < a.size then a.set! i true else a

/-- The steps the roots use: one backward pass (premise indices point
backwards in an accepted derivation). -/
def usedMask (d : Derivation) (roots : List Nat) : Array Bool :=
  let init := roots.foldl markIdx (Array.replicate d.size false)
  (List.range d.size).reverse.foldl (fun acc i =>
    if acc[i]! then (d[i]!).premises.foldl markIdx acc else acc) init

/-- The position of `i` in `l` (`l.length` when absent). -/
def posIn (l : List Nat) (i : Nat) : Nat := (l.findIdx? (· == i)).getD l.length

/-- The used steps, renumbered, and the renumbering. -/
def cutDerivation (d : Derivation) (roots : List Nat) : Derivation × (Nat → Nat) :=
  let mask := usedMask d roots
  let kept := (List.range d.size).filter (fun i => mask[i]!)
  ((kept.map (fun i => let st := d[i]!; { st with premises := st.premises.map (posIn kept) })).toArray,
    posIn kept)

/-! ## The emitted bundle -/

/-- The bundle for the mapping `m`: the derivation `full` cut down to the
steps that conclude the instances of the description triples. -/
def emitGraphBundle (g E : Graph) (m : InstanceMapping) (full : Derivation) : GraphBundle :=
  let roots := E.map (fun d =>
    match d.instance? m.subst with
    | some t => (full.findIdx? (fun st => st.conclusion == t)).getD full.size
    | none => full.size)
  let cut := cutDerivation full roots
  { sources := g, description := E, mapping := m, witness := cut.1, support := roots.map cut.2 }

/-! ## The result -/

/-- Why no bundle was returned. -/
inductive GraphRejection where
  /-- Triple `index` of the description has no instance in the closure. -/
  | noMatch (index : Nat) (triple : Triple)
  /-- Every triple has an instance in the closure, but no one mapping of the
  blank nodes serves all of them. -/
  | noJointMapping
  /-- The emitted bundle was refused by the graph checker (an emitter
  defect). -/
  | checkerRefused (reason : String)
  deriving DecidableEq, Repr

/-- The result of explain. -/
structure ExplainGraphResult where
  entailed : Bool
  bundle : Option GraphBundle
  /-- The statements a reader of the verdict relies on that are not proved. -/
  assumptions : List String
  rejection : Option GraphRejection

/-- What `entailed = false` from the search relies on, to be read as "not
RDFS-entailed". -/
def notEntailedAssumptions : List String :=
  ["RDFS closure completeness (RDF 1.1 Semantics Appendix A; rdfsReasoner.assumed_completeness): an RDFS-entailed description has an instance in fullClosure"]

/-- What `checkerRefused` relies on. -/
def emitterAssumptions : List String :=
  ["the explain emitter produced a bundle the graph checker refused; the verdict says nothing about entailment"]

/-- **Explain a description.** -/
def explainGraphOf (D : List WfIri) (g E : Graph) : ExplainGraphResult :=
  let c := fullClosureWithProof D (graphCmps g E) g
  match findInstance c.1 E with
  | none =>
    { entailed := false, bundle := none, assumptions := notEntailedAssumptions,
      rejection := some (match firstUnmatchedFrom c.1 0 E with
        | some (i, t) => .noMatch i t
        | none => .noJointMapping) }
  | some m =>
    let b := emitGraphBundle g E m c.2
    match checkGraphRun D b with
    | .ok _ => { entailed := true, bundle := some b, assumptions := [], rejection := none }
    | .error e =>
      { entailed := false, bundle := none, assumptions := emitterAssumptions,
        rejection := some (.checkerRefused e) }

/-- The contract of explain over the graph `g` and the description `E`. -/
def ExplainGraphSpec (D : List WfIri) (g E : Graph) (r : ExplainGraphResult) : Prop :=
  (r.entailed = true → ∃ b c, r.bundle = some b ∧ b.sources = g ∧ b.description = E ∧
      (rdfsGraphChecker D).run b = .ok c ∧ RdfsEntails (fun x => x ∈ D) g E ∧
      r.assumptions = [] ∧ r.rejection = none) ∧
  (r.entailed = false → r.bundle = none ∧ ∃ why, r.rejection = some why) ∧
  (∀ i t, r.rejection = some (.noMatch i t) →
      E[i]? = some t ∧ (∀ u ∈ fullClosure D (graphCmps g E) g, ∀ M, ¬ TripleInst M t u) ∧
      ¬ SimpleEntailmentSpec (fullClosure D (graphCmps g E) g) E ∧
      r.assumptions = notEntailedAssumptions) ∧
  (r.rejection = some .noJointMapping →
      ¬ SimpleEntailmentSpec (fullClosure D (graphCmps g E) g) E ∧
      r.assumptions = notEntailedAssumptions)

theorem explainGraphOf_spec (D : List WfIri) (g E : Graph) :
    ExplainGraphSpec D g E (explainGraphOf D g E) := by
  have hcl := fullClosureWithProof_graph D (graphCmps g E) g
  generalize hc0 : fullClosureWithProof D (graphCmps g E) g = c0 at hcl
  have hrun : explainGraphOf D g E =
      (match findInstance c0.1 E with
        | none =>
          { entailed := false, bundle := none, assumptions := notEntailedAssumptions,
            rejection := some (match firstUnmatchedFrom c0.1 0 E with
              | some (i, t) => .noMatch i t
              | none => .noJointMapping) }
        | some m =>
          match checkGraphRun D (emitGraphBundle g E m c0.2) with
          | .ok _ => { entailed := true, bundle := some (emitGraphBundle g E m c0.2),
                       assumptions := [], rejection := none }
          | .error e =>
            { entailed := false, bundle := none, assumptions := emitterAssumptions,
              rejection := some (.checkerRefused e) } : ExplainGraphResult) := by
    unfold explainGraphOf
    rw [hc0]
  rw [hrun, hcl]
  cases hs : findInstance (fullClosure D (graphCmps g E) g) E with
  | none =>
    dsimp only
    have hno := findInstance_none hs
    cases hf : firstUnmatchedFrom (fullClosure D (graphCmps g E) g) 0 E with
    | none =>
      dsimp only
      refine ⟨(fun h => by simp at h), fun _ => ⟨rfl, _, rfl⟩, ?_, fun _ => ⟨hno, rfl⟩⟩
      intro i t h
      simp at h
    | some p =>
      dsimp only
      obtain ⟨i, t⟩ := p
      obtain ⟨_, hget, hu⟩ := firstUnmatchedFrom_spec _ 0 E hf
      simp only [Nat.sub_zero] at hget
      refine ⟨(fun h => by simp at h), fun _ => ⟨rfl, _, rfl⟩, ?_, (fun h => by simp at h)⟩
      intro i' t' h
      simp only [Option.some.injEq, GraphRejection.noMatch.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hget, unmatchedIn_no_instance hu, hno, rfl⟩
  | some m =>
    dsimp only
    cases hc : checkGraphRun D (emitGraphBundle g E m c0.2) with
    | error e =>
      dsimp only
      refine ⟨(fun h => by simp at h), fun _ => ⟨rfl, _, rfl⟩, ?_, (fun h => by simp at h)⟩
      intro i t h
      simp at h
    | ok c =>
      dsimp only
      obtain ⟨hs1, hd1, he⟩ := checkGraphRun_sound D _ c hc
      have hsrc : (emitGraphBundle g E m c0.2).sources = g := rfl
      have hdesc : (emitGraphBundle g E m c0.2).description = E := rfl
      rw [hs1, hsrc, hd1, hdesc] at he
      refine ⟨fun _ => ⟨emitGraphBundle g E m c0.2, c, rfl, hsrc, hdesc, hc, he, rfl, rfl⟩,
        (fun h => by simp at h), ?_, (fun h => by simp at h)⟩
      intro i t h
      simp at h

/-- The contract of the stage. -/
def ExplainGraphContract (D : List WfIri) (sel : GraphSelection) (inp : Dataset × Graph)
    (r : ExplainGraphResult) : Prop :=
  ExplainGraphSpec D (inp.1.select sel) inp.2 r

/-- **Explain a description over the selected graphs.** -/
def rdfsExplainGraphStage (D : List WfIri) (sel : GraphSelection) :
    Stage String (Dataset × Graph) ExplainGraphResult :=
  Stage.ofFun (fun inp => explainGraphOf D (inp.1.select sel) inp.2) (ExplainGraphContract D sel)
    (fun inp => explainGraphOf_spec D (inp.1.select sel) inp.2)

#print axioms explainGraphOf_spec
#print axioms rdfsExplainGraphStage

end L4Factoidal.Dataflow
