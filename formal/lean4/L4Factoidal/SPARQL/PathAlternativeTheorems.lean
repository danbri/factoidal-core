/-
L4Factoidal.SPARQL.PathAlternativeTheorems — the rewrite of an alternative of
IRIs into a UNION of triple patterns preserves the evaluation
(https://github.com/danbri/factoidal/issues/1008).

The rewrite is `QueryPattern.expandIriAlternatives`
(`SPARQL/PathAlternative.lean`). The evaluator is the reference one: the
lowering `QueryPattern.lowerWith` followed by `GraphPattern.evalIn`, with
`GraphPattern.serviceFailure` as its error channel (Federated Query §2.3).

## Statements

* `linkPath_evalTP` — §18.4 and §18.2.2.4 for one triple: the solutions of the
  triple pattern `s p o` are the solutions of the link path `p` between `s`
  and `o`, as lists. The object must not be a triple-term pattern.
* `iriAlternativeUnion_evalIn` — for an alternative of IRIs, the rewritten
  UNION evaluates to the solutions of the path pairs, as lists:
  `evalPath (.alternative a b) = evalPath a ++ evalPath b` is the multiset
  union of §18.4, and `SPARQL.union` is `++` (§18.5 Union), so the
  multiplicities and the order agree.
* `expandIriAlternatives_lowerWith` and
  `expandIriAlternatives_serviceFailure` — the whole pattern: for every
  environment, seed binding, dataset and active graph, the rewritten pattern
  answers the same list of solutions and the same SERVICE failure.
* `expandIriAlternatives_rewriteBnodes` and `Query.expandIriAlternatives_eval`
  — the rewrite commutes with the blank-node rewrite the evaluator applies at
  its entry (`QueryPattern.rewriteBnodes`, §18.2.4), so the statement holds of
  the pattern the evaluator runs.

Multiplicity was checked, not assumed (the brief of issue 1008 asks for it):
a triple matched by both operands, such as `<b> :name "x"` together with
`<b> :size "x"` under `:name|:size`, gives two equal solutions on both sides.
`Wasm/StorePlanGateTests.lean` pins that case through the store.

No hypothesis of these theorems restates its conclusion: the hypotheses are a
syntactic condition on the object (`isTripleTerm = false`) and the equation
that defines the rewrite's output.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.PathAlternative
import L4Factoidal.SPARQL.IndexedEvalRefinement

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## 1. One link path is one triple pattern -/

/-- The solution of one path pair: the inner function of
`pathResultToSolutions`. -/
def pathPairSolution (ps : PatternSubject) (pt : PatternTerm) (pr : Term × Term) :
    Option Binding :=
  let s := pr.1
  let o := pr.2
  let muS : Option Binding :=
    match ps with
    | .var v            => some [(v, s)]
    | .iri i            => if (Term.iri i).eqb s then some [] else none
    | .bnode b          => if (Term.bnode b).eqb s then some [] else none
    | .tripleTerm _ _ _ => none
  match muS with
  | none => none
  | some bs =>
      match pt with
      | .var v =>
          match bs.lookup v with
          | some existing => if existing.eqb o then some bs else none
          | none          => some ((v, o) :: bs)
      | .iri i            => if (Term.iri i).eqb o then some bs else none
      | .bnode b          => if (Term.bnode b).eqb o then some bs else none
      | .literal l        => if (Term.literal l).eqb o then some bs else none
      | .tripleTerm _ _ _ => none

theorem pathResultToSolutions_eq (ps : PatternSubject) (pt : PatternTerm) (pairs : PathResult) :
    pathResultToSolutions ps pt pairs = pairs.filterMap (pathPairSolution ps pt) := rfl

/-- One triple: matching the triple pattern `s p o` from the empty mapping is
the solution of the pair the link path `p` gives for that triple. -/
theorem tpMatch_link (s : PatternSubject) (p : WfIri) (o : PatternTerm)
    (ho : o.isTripleTerm = false) (t : Triple) :
    tpMatch { s := s, p := .iri p, o := o } t Binding.empty =
      (if t.p == p then some (t.s.toTerm, t.o) else none).bind (pathPairSolution s o) := by
  obtain ⟨ts, tp, to⟩ := t
  by_cases hp : tp = p
  · subst hp
    cases s <;> cases o <;> simp [PatternTerm.isTripleTerm] at ho <;>
      cases ts <;>
      simp [tpMatch, tryBindSubject, tryBindTerm, pathPairSolution, Binding.lookup,
        Binding.bind, Binding.empty, Term.eqb, Subject.toTerm] <;>
      first
        | rfl
        | (cases to <;> simp [Term.eqb] <;> rfl)
  · have hv : ¬ tp.val = p.val := fun h => hp (Subtype.ext h)
    have hp' : (p == tp) = false := by simp; exact fun h => hv h.symm
    have hp'' : (tp == p) = false := by simp; exact hv
    cases s <;> cases ts <;>
      simp [tpMatch, tryBindSubject, tryBindTerm, Binding.lookup, Binding.bind,
        Binding.empty, hp', hp'', Subject.toTerm] <;>
      split <;> rfl

/-- §18.2.2.4 with §18.4: the triple pattern `s p o`, matched from the empty
mapping over a graph, gives the solutions of the link path `p` between `s` and
`o`, as lists. -/
theorem linkPath_evalTP (s : PatternSubject) (p : WfIri) (o : PatternTerm)
    (ho : o.isTripleTerm = false) (g : Graph) :
    evalTP { s := s, p := .iri p, o := o } g Binding.empty =
      pathResultToSolutions s o (evalPath (.iri p) g) := by
  simp only [evalTP, pathResultToSolutions_eq, evalPath, List.filterMap_filterMap]
  congr 1
  funext t
  exact tpMatch_link s p o ho t

/-- `substPatternTerm` never makes a triple-term pattern and never removes one. -/
theorem substPatternTerm_isTripleTerm (mu : Binding) (o : PatternTerm) :
    (substPatternTerm mu o).isTripleTerm = o.isTripleTerm := by
  cases o with
  | var v =>
      simp only [substPatternTerm]
      split <;> rfl
  | _ => rfl

/-- A triple pattern whose predicate is an IRI other than `text:query` is no
full-text search. -/
theorem fulltext?_of_iri (s : PatternSubject) (p : WfIri) (o : PatternTerm)
    (hf : (p == fulltextQueryPred) = false) :
    TriplePattern.fulltext? { s := s, p := .iri p, o := o } = none := by
  cases o <;> simp [TriplePattern.fulltext?, hf]

/-! ## 2. An alternative of IRIs is the UNION of its triple patterns -/

theorem iriAlternativeUnion_evalIn (env : EvalEnv) (mu : Binding) (ds : Dataset)
    (active : Graph) (s : PatternSubject) (o : PatternTerm) (ho : o.isTripleTerm = false) :
    ∀ (path : PropertyPath) (u : QueryPattern), iriAlternativeUnion s o path = some u →
      (u.lowerWith env mu).evalIn ds active =
        pathResultToSolutions (substPatternSubject mu s) (substPatternTerm mu o)
          (evalPath path active)
  | .iri p, u, h => by
      by_cases hf : (p == fulltextQueryPred) = true
      · simp [iriAlternativeUnion, hf] at h
      · simp only [Bool.not_eq_true] at hf
        simp only [iriAlternativeUnion, hf, Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        have hnf : bgpHasFulltext (substBgp mu [{ s := s, p := .iri p, o := o }]) = false := by
          simp [bgpHasFulltext, substBgp, substTriplePattern, substPatternTerm,
            fulltext?_of_iri _ _ _ hf]
        have hso : (substPatternTerm mu o).isTripleTerm = false := by
          rw [substPatternTerm_isTripleTerm]; exact ho
        rw [QueryPattern.lowerWith, lowerBgp_of_no_fulltext _ hnf]
        simp only [GraphPattern.evalIn, evalBgpIdx_eq_evalBgp, evalBgp, substBgp, List.map,
          substTriplePattern, evalBgpFrom]
        rw [show substPatternTerm mu (.iri p) = .iri p from rfl]
        rw [← linkPath_evalTP _ p _ hso active]
        simp
  | .alternative a b, u, h => by
      simp only [iriAlternativeUnion] at h
      split at h
      · rename_i l r hl hr
        cases h
        simp only [QueryPattern.lowerWith, GraphPattern.evalIn, SPARQL.union, evalPath,
          pathResultToSolutions_eq, List.filterMap_append]
        rw [iriAlternativeUnion_evalIn env mu ds active s o ho a l hl,
          iriAlternativeUnion_evalIn env mu ds active s o ho b r hr]
        rfl
      · cases h
  | .inverse _, u, h => by simp [iriAlternativeUnion] at h
  | .sequence _ _, u, h => by simp [iriAlternativeUnion] at h
  | .zeroOrMore _, u, h => by simp [iriAlternativeUnion] at h
  | .oneOrMore _, u, h => by simp [iriAlternativeUnion] at h
  | .zeroOrOne _, u, h => by simp [iriAlternativeUnion] at h
  | .negatedSet _, u, h => by simp [iriAlternativeUnion] at h

/-- The rewritten UNION invokes no SERVICE. -/
theorem iriAlternativeUnion_serviceFailure (env : EvalEnv) (mu : Binding) (ds : Dataset)
    (active : Graph) (s : PatternSubject) (o : PatternTerm) :
    ∀ (path : PropertyPath) (u : QueryPattern), iriAlternativeUnion s o path = some u →
      (u.lowerWith env mu).serviceFailure ds active = none
  | .iri p, u, h => by
      by_cases hf : (p == fulltextQueryPred) = true
      · simp [iriAlternativeUnion, hf] at h
      · simp only [Bool.not_eq_true] at hf
        simp only [iriAlternativeUnion, hf, Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        have hnf : bgpHasFulltext (substBgp mu [{ s := s, p := .iri p, o := o }]) = false := by
          simp [bgpHasFulltext, substBgp, substTriplePattern, substPatternTerm,
            fulltext?_of_iri _ _ _ hf]
        rw [QueryPattern.lowerWith, lowerBgp_of_no_fulltext _ hnf]
        rfl
  | .alternative a b, u, h => by
      simp only [iriAlternativeUnion] at h
      split at h
      · rename_i l r hl hr
        cases h
        simp only [QueryPattern.lowerWith, GraphPattern.serviceFailure,
          iriAlternativeUnion_serviceFailure env mu ds active s o a l hl,
          iriAlternativeUnion_serviceFailure env mu ds active s o b r hr]
        rfl
      · cases h
  | .inverse _, u, h => by simp [iriAlternativeUnion] at h
  | .sequence _ _, u, h => by simp [iriAlternativeUnion] at h
  | .zeroOrMore _, u, h => by simp [iriAlternativeUnion] at h
  | .oneOrMore _, u, h => by simp [iriAlternativeUnion] at h
  | .zeroOrOne _, u, h => by simp [iriAlternativeUnion] at h
  | .negatedSet _, u, h => by simp [iriAlternativeUnion] at h

/-- `addConstantReflexivity` changes only `p*` and `p?`, which no alternative
of IRIs is. -/
theorem addConstantReflexivity_of_union {s : PatternSubject} {o : PatternTerm}
    {path : PropertyPath} {u : QueryPattern} (h : iriAlternativeUnion s o path = some u)
    (s' : PatternSubject) (o' : PatternTerm) (pairs : PathResult) :
    addConstantReflexivity s' o' path pairs = pairs := by
  cases path <;> simp [iriAlternativeUnion] at h <;> rfl

/-! ## 3. Congruence of the reference evaluator

`EvalAgree X Y`: the two lowered patterns answer the same solution list and
the same SERVICE failure over every dataset and every active graph.
`GraphPattern.evalIn` has two arms for a join with a `SERVICE ?v` operand
(Federated Query §4), so the join congruence carries a side condition: an
operand that changed is not such a SERVICE. -/

def EvalAgree (X Y : GraphPattern) : Prop :=
  (∀ ds active, X.evalIn ds active = Y.evalIn ds active) ∧
  (∀ ds active, X.serviceFailure ds active = Y.serviceFailure ds active)

theorem EvalAgree.refl (X : GraphPattern) : EvalAgree X X :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Is this lowered pattern a `SERVICE ?v` whose endpoint waits for a row? -/
def GraphPattern.isServiceVar : GraphPattern → Bool
  | .serviceVar _ _ _ _ => true
  | _ => false

theorem evalIn_join_plain {X Y : GraphPattern} (hX : X.isServiceVar = false)
    (hY : Y.isServiceVar = false) (ds : Dataset) (active : Graph) :
    (GraphPattern.join X Y).evalIn ds active =
      SPARQL.hashJoin (X.evalIn ds active) (Y.evalIn ds active) := by
  cases X <;> cases Y <;>
    first
      | rfl
      | (simp [GraphPattern.isServiceVar] at hX <;> done)
      | (simp [GraphPattern.isServiceVar] at hY <;> done)

theorem serviceFailure_join_plain {X Y : GraphPattern} (hX : X.isServiceVar = false)
    (hY : Y.isServiceVar = false) (ds : Dataset) (active : Graph) :
    (GraphPattern.join X Y).serviceFailure ds active =
      (X.serviceFailure ds active).or (Y.serviceFailure ds active) := by
  cases X <;> cases Y <;>
    first
      | rfl
      | (simp [GraphPattern.isServiceVar] at hX <;> done)
      | (simp [GraphPattern.isServiceVar] at hY <;> done)

/-- The `SERVICE ?v` on the LEFT of a join arm of `evalIn`, for a right
operand that is no `SERVICE ?v`. -/
theorem evalIn_join_serviceVar_left (v : VarName) (resolve : Iri → Option Graph)
    (silent : Bool) (inner : GraphPattern) {Y : GraphPattern} (hY : Y.isServiceVar = false)
    (ds : Dataset) (active : Graph) :
    (GraphPattern.join (.serviceVar v resolve silent inner) Y).evalIn ds active =
      (GraphPattern.evalIn ds active Y).flatMap (fun mu =>
        match mu.lookup v with
        | some (.iri i) =>
            match resolve i.val with
            | some remote =>
                if silent && (GraphPattern.serviceFailure ds remote inner).isSome then [mu]
                else
                  (GraphPattern.evalIn ds remote inner).filterMap (fun mu1 =>
                    if mu.compatible mu1 then some (mu.merge mu1) else none)
            | none => if silent then [mu] else []
        | _ => if silent then [mu] else []) := by
  cases Y <;> first | rfl | (simp [GraphPattern.isServiceVar] at hY <;> done)

theorem serviceFailure_join_serviceVar_left (v : VarName) (resolve : Iri → Option Graph)
    (silent : Bool) (inner : GraphPattern) {Y : GraphPattern} (hY : Y.isServiceVar = false)
    (ds : Dataset) (active : Graph) :
    (GraphPattern.join (.serviceVar v resolve silent inner) Y).serviceFailure ds active =
      (GraphPattern.serviceFailure ds active Y).or
        ((GraphPattern.evalIn ds active Y).findSome? (fun mu =>
          match mu.lookup v with
          | some (.iri i) =>
              match resolve i.val with
              | some remote => if silent then none else GraphPattern.serviceFailure ds remote inner
              | none => if silent then none else some (.unreachable i.val)
          | _ => if silent then none else some (.noEndpoint v))) := by
  cases Y <;> first | rfl | (simp [GraphPattern.isServiceVar] at hY <;> done)

/-- The `SERVICE ?v` on the RIGHT of a join arm, whatever the left operand. -/
theorem evalIn_join_serviceVar_right (X : GraphPattern) (v : VarName)
    (resolve : Iri → Option Graph) (silent : Bool) (inner : GraphPattern)
    (ds : Dataset) (active : Graph) :
    (GraphPattern.join X (.serviceVar v resolve silent inner)).evalIn ds active =
      (GraphPattern.evalIn ds active X).flatMap (fun mu =>
        match mu.lookup v with
        | some (.iri i) =>
            match resolve i.val with
            | some remote =>
                if silent && (GraphPattern.serviceFailure ds remote inner).isSome then [mu]
                else
                  (GraphPattern.evalIn ds remote inner).filterMap (fun mu1 =>
                    if mu.compatible mu1 then some (mu.merge mu1) else none)
            | none => if silent then [mu] else []
        | _ => if silent then [mu] else []) := by
  cases X <;> rfl

theorem serviceFailure_join_serviceVar_right (X : GraphPattern) (v : VarName)
    (resolve : Iri → Option Graph) (silent : Bool) (inner : GraphPattern)
    (ds : Dataset) (active : Graph) :
    (GraphPattern.join X (.serviceVar v resolve silent inner)).serviceFailure ds active =
      (GraphPattern.serviceFailure ds active X).or
        ((GraphPattern.evalIn ds active X).findSome? (fun mu =>
          match mu.lookup v with
          | some (.iri i) =>
              match resolve i.val with
              | some remote => if silent then none else GraphPattern.serviceFailure ds remote inner
              | none => if silent then none else some (.unreachable i.val)
          | _ => if silent then none else some (.noEndpoint v))) := by
  cases X <;> rfl

/-- Join congruence. Each operand either is unchanged or is, before and after,
no `SERVICE ?v`. -/
theorem join_agree {X X' Y Y' : GraphPattern} (hX : EvalAgree X' X) (hY : EvalAgree Y' Y)
    (sX : X' = X ∨ (X'.isServiceVar = false ∧ X.isServiceVar = false))
    (sY : Y' = Y ∨ (Y'.isServiceVar = false ∧ Y.isServiceVar = false)) :
    EvalAgree (.join X' Y') (.join X Y) := by
  obtain ⟨hXe, hXf⟩ := hX
  obtain ⟨hYe, hYf⟩ := hY
  -- The right operand decides the arm first.
  have plainY : Y'.isServiceVar = false ∧ Y.isServiceVar = false ∨
      (Y' = Y ∧ Y.isServiceVar = true) := by
    rcases sY with h | h
    · by_cases hy : Y.isServiceVar = true
      · exact Or.inr ⟨h, hy⟩
      · have hy0 : Y.isServiceVar = false := by simpa using hy
        exact Or.inl ⟨by rw [h]; exact hy0, hy0⟩
    · exact Or.inl h
  rcases plainY with ⟨hy', hy⟩ | ⟨hyy, hy⟩
  · -- No SERVICE ?v on the right: the left operand decides.
    have plainX : X'.isServiceVar = false ∧ X.isServiceVar = false ∨
        (X' = X ∧ X.isServiceVar = true) := by
      rcases sX with h | h
      · by_cases hx : X.isServiceVar = true
        · exact Or.inr ⟨h, hx⟩
        · have hx0 : X.isServiceVar = false := by simpa using hx
          exact Or.inl ⟨by rw [h]; exact hx0, hx0⟩
      · exact Or.inl h
    rcases plainX with ⟨hx', hx⟩ | ⟨hxx, hx⟩
    · constructor
      · intro ds active
        rw [evalIn_join_plain hx' hy', evalIn_join_plain hx hy, hXe, hYe]
      · intro ds active
        rw [serviceFailure_join_plain hx' hy', serviceFailure_join_plain hx hy, hXf, hYf]
    · subst hxx
      cases X' with
      | serviceVar v resolve silent inner =>
          constructor
          · intro ds active
            rw [evalIn_join_serviceVar_left v resolve silent inner hy',
              evalIn_join_serviceVar_left v resolve silent inner hy, hYe]
          · intro ds active
            rw [serviceFailure_join_serviceVar_left v resolve silent inner hy',
              serviceFailure_join_serviceVar_left v resolve silent inner hy, hYe, hYf]
      | _ => simp [GraphPattern.isServiceVar] at hx
  · -- A SERVICE ?v on the right, the same on both sides.
    subst hyy
    cases Y' with
    | serviceVar v resolve silent inner =>
        constructor
        · intro ds active
          rw [evalIn_join_serviceVar_right X' v resolve silent inner,
            evalIn_join_serviceVar_right X v resolve silent inner, hXe]
        · intro ds active
          rw [serviceFailure_join_serviceVar_right X' v resolve silent inner,
            serviceFailure_join_serviceVar_right X v resolve silent inner, hXe, hXf]
    | _ => simp [GraphPattern.isServiceVar] at hy

/-! ## 4. The whole pattern -/

/-- The lowered UNION is no `SERVICE ?v`. -/
theorem iriAlternativeUnion_lower_notServiceVar (env : EvalEnv) (mu : Binding)
    (s : PatternSubject) (o : PatternTerm) :
    ∀ (path : PropertyPath) (u : QueryPattern), iriAlternativeUnion s o path = some u →
      (u.lowerWith env mu).isServiceVar = false
  | .iri p, u, h => by
      by_cases hf : (p == fulltextQueryPred) = true
      · simp [iriAlternativeUnion, hf] at h
      · simp only [Bool.not_eq_true] at hf
        simp only [iriAlternativeUnion, hf, Bool.false_eq_true, if_false, Option.some.injEq] at h
        subst h
        have hnf : bgpHasFulltext (substBgp mu [{ s := s, p := .iri p, o := o }]) = false := by
          simp [bgpHasFulltext, substBgp, substTriplePattern, substPatternTerm,
            fulltext?_of_iri _ _ _ hf]
        rw [QueryPattern.lowerWith, lowerBgp_of_no_fulltext _ hnf]
        rfl
  | .alternative a b, u, h => by
      simp only [iriAlternativeUnion] at h
      split at h
      · cases h; rfl
      · cases h
  | .inverse _, u, h => by simp [iriAlternativeUnion] at h
  | .sequence _ _, u, h => by simp [iriAlternativeUnion] at h
  | .zeroOrMore _, u, h => by simp [iriAlternativeUnion] at h
  | .oneOrMore _, u, h => by simp [iriAlternativeUnion] at h
  | .zeroOrOne _, u, h => by simp [iriAlternativeUnion] at h
  | .negatedSet _, u, h => by simp [iriAlternativeUnion] at h

/-- The rewrite either leaves a pattern's lowering unchanged or gives, before
and after, a lowering that is no `SERVICE ?v`. -/
theorem expandIriAlternatives_lower_shape (env : EvalEnv) (mu : Binding) (p : QueryPattern) :
    p.expandIriAlternatives.lowerWith env mu = p.lowerWith env mu ∨
      ((p.expandIriAlternatives.lowerWith env mu).isServiceVar = false ∧
        (p.lowerWith env mu).isServiceVar = false) := by
  cases p with
  | propertyPath s path o =>
      simp only [QueryPattern.expandIriAlternatives]
      split
      · exact Or.inl rfl
      · split
        · rename_i u hu
          exact Or.inr ⟨iriAlternativeUnion_lower_notServiceVar env mu s o path u hu, rfl⟩
        · exact Or.inl rfl
  | filter c q =>
      refine Or.inr ⟨?_, ?_⟩ <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith, filterLowered] <;>
        split <;> rfl
  | join _ _ | union _ _ | minus _ _ | leftJoin _ _ _ | bind _ _ _ | graph _ _ =>
      exact Or.inr ⟨rfl, rfl⟩
  | bgp _ | lateral _ _ | values _ _ | service _ _ _ | serviceVar _ _ _ | subSelect _ | empty =>
      exact Or.inl rfl

/-- **The rewrite preserves the evaluation**, solutions and SERVICE failure,
for every environment, seed binding, dataset and active graph. -/
theorem expandIriAlternatives_agree (env : EvalEnv) (mu : Binding) :
    ∀ p : QueryPattern, EvalAgree (p.expandIriAlternatives.lowerWith env mu) (p.lowerWith env mu)
  | .propertyPath s path o => by
      simp only [QueryPattern.expandIriAlternatives]
      split
      · exact EvalAgree.refl _
      · rename_i ho
        simp only [Bool.not_eq_true] at ho
        split
        · rename_i u hu
          constructor
          · intro ds active
            rw [iriAlternativeUnion_evalIn env mu ds active s o ho path u hu]
            simp only [QueryPattern.lowerWith, GraphPattern.evalIn]
            rw [addConstantReflexivity_of_union hu]
          · intro ds active
            rw [iriAlternativeUnion_serviceFailure env mu ds active s o path u hu]
            rfl
        · exact EvalAgree.refl _
  | .join l r => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith]
      exact join_agree (expandIriAlternatives_agree env mu l) (expandIriAlternatives_agree env mu r)
        (expandIriAlternatives_lower_shape env mu l) (expandIriAlternatives_lower_shape env mu r)
  | .union l r => by
      obtain ⟨hle, hlf⟩ := expandIriAlternatives_agree env mu l
      obtain ⟨hre, hrf⟩ := expandIriAlternatives_agree env mu r
      constructor <;> intro ds active <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith,
          GraphPattern.evalIn, GraphPattern.serviceFailure, hle, hre, hlf, hrf]
  | .minus l r => by
      obtain ⟨hle, hlf⟩ := expandIriAlternatives_agree env mu l
      obtain ⟨hre, hrf⟩ := expandIriAlternatives_agree env mu r
      constructor <;> intro ds active <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith,
          GraphPattern.evalIn, GraphPattern.serviceFailure, hle, hre, hlf, hrf]
  | .leftJoin l r c => by
      obtain ⟨hle, hlf⟩ := expandIriAlternatives_agree env mu l
      obtain ⟨hre, hrf⟩ := expandIriAlternatives_agree env mu r
      constructor <;> intro ds active <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith,
          GraphPattern.evalIn, GraphPattern.serviceFailure, hle, hre, hlf, hrf]
  | .filter c q => by
      obtain ⟨hqe, hqf⟩ := expandIriAlternatives_agree env mu q
      constructor <;> intro ds active <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith, filterLowered] <;>
        split <;>
        simp only [GraphPattern.evalIn, GraphPattern.serviceFailure, hqe, hqf]
  | .bind e v q => by
      obtain ⟨hqe, hqf⟩ := expandIriAlternatives_agree env mu q
      constructor <;> intro ds active <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith,
          GraphPattern.evalIn, GraphPattern.serviceFailure, hqe, hqf]
  | .graph n q => by
      obtain ⟨hqe, hqf⟩ := expandIriAlternatives_agree env mu q
      constructor <;> intro ds active <;>
        simp only [QueryPattern.expandIriAlternatives, QueryPattern.lowerWith] <;>
        cases substPatternTerm mu n <;>
        simp only [GraphPattern.evalIn, GraphPattern.serviceFailure, hqe, hqf]
  | .bgp _ => EvalAgree.refl _
  | .lateral _ _ => EvalAgree.refl _
  | .values _ _ => EvalAgree.refl _
  | .service _ _ _ => EvalAgree.refl _
  | .serviceVar _ _ _ => EvalAgree.refl _
  | .subSelect _ => EvalAgree.refl _
  | .empty => EvalAgree.refl _

/-- **The solutions are unchanged** (SPARQL 1.1 §18.4 with §18.2.2.4): the
rewritten pattern answers the same list — the same solutions, each as often,
in the same order. -/
theorem expandIriAlternatives_lowerWith (env : EvalEnv) (mu : Binding) (p : QueryPattern)
    (ds : Dataset) (active : Graph) :
    (p.expandIriAlternatives.lowerWith env mu).evalIn ds active =
      (p.lowerWith env mu).evalIn ds active :=
  (expandIriAlternatives_agree env mu p).1 ds active

/-- **The SERVICE failure is unchanged** (Federated Query §2.3). -/
theorem expandIriAlternatives_serviceFailure (env : EvalEnv) (mu : Binding) (p : QueryPattern)
    (ds : Dataset) (active : Graph) :
    (p.expandIriAlternatives.lowerWith env mu).serviceFailure ds active =
      (p.lowerWith env mu).serviceFailure ds active :=
  (expandIriAlternatives_agree env mu p).2 ds active

/-! ## 5. The pattern the evaluator runs

The evaluator rewrites the WHERE pattern's blank nodes to variables at its
entry (`QueryPattern.rewriteBnodes`, §18.2.4). The two rewrites commute, so
the statement above holds of that pattern too. -/

theorem rewriteBnodeTerm_isTripleTerm (o : PatternTerm) :
    (rewriteBnodeTerm o).isTripleTerm = o.isTripleTerm := by
  cases o <;> rfl

theorem iriAlternativeUnion_rewriteBnodes (s : PatternSubject) (o : PatternTerm) :
    ∀ path : PropertyPath,
      iriAlternativeUnion (rewriteBnodeSubject s) (rewriteBnodeTerm o) path =
        (iriAlternativeUnion s o path).map QueryPattern.rewriteBnodes
  | .iri p => by
      by_cases hf : (p == fulltextQueryPred) = true
      · simp [iriAlternativeUnion, hf]
      · simp only [Bool.not_eq_true] at hf
        simp [iriAlternativeUnion, hf, QueryPattern.rewriteBnodes, rewriteBnodeTriple,
          rewriteBnodeTerm]
  | .alternative a b => by
      simp only [iriAlternativeUnion, iriAlternativeUnion_rewriteBnodes s o a,
        iriAlternativeUnion_rewriteBnodes s o b]
      cases iriAlternativeUnion s o a <;> cases iriAlternativeUnion s o b <;> rfl
  | .inverse _ => rfl
  | .sequence _ _ => rfl
  | .zeroOrMore _ => rfl
  | .oneOrMore _ => rfl
  | .zeroOrOne _ => rfl
  | .negatedSet _ => rfl

theorem expandIriAlternatives_rewriteBnodes :
    ∀ p : QueryPattern,
      p.expandIriAlternatives.rewriteBnodes = p.rewriteBnodes.expandIriAlternatives
  | .propertyPath s path o => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        rewriteBnodeTerm_isTripleTerm, iriAlternativeUnion_rewriteBnodes]
      split
      · rfl
      · cases iriAlternativeUnion s o path <;> rfl
  | .join l r => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes l, expandIriAlternatives_rewriteBnodes r]
  | .union l r => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes l, expandIriAlternatives_rewriteBnodes r]
  | .minus l r => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes l, expandIriAlternatives_rewriteBnodes r]
  | .leftJoin l r c => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes l, expandIriAlternatives_rewriteBnodes r]
  | .filter c q => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes q]
  | .bind e v q => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes q]
  | .graph n q => by
      simp only [QueryPattern.expandIriAlternatives, QueryPattern.rewriteBnodes,
        expandIriAlternatives_rewriteBnodes q]
  | .bgp _ => rfl
  | .lateral _ _ => rfl
  | .values _ _ => rfl
  | .service _ _ _ => rfl
  | .serviceVar _ _ _ => rfl
  | .subSelect _ => rfl
  | .empty => rfl

/-- **The query-level statement.** The WHERE pattern of the rewritten query,
as the evaluator runs it (blank nodes rewritten, then lowered), answers the
same solution list as the WHERE pattern of the query as parsed. -/
theorem Query.expandIriAlternatives_eval (q : Query) (env : EvalEnv) (mu : Binding)
    (ds : Dataset) (active : Graph) :
    (q.expandIriAlternatives.pattern.rewriteBnodes.lowerWith env mu).evalIn ds active =
      (q.pattern.rewriteBnodes.lowerWith env mu).evalIn ds active := by
  rw [Query.expandIriAlternatives_pattern, expandIriAlternatives_rewriteBnodes,
    expandIriAlternatives_lowerWith]

theorem Query.expandIriAlternatives_serviceFailure (q : Query) (env : EvalEnv) (mu : Binding)
    (ds : Dataset) (active : Graph) :
    (q.expandIriAlternatives.pattern.rewriteBnodes.lowerWith env mu).serviceFailure ds active =
      (q.pattern.rewriteBnodes.lowerWith env mu).serviceFailure ds active := by
  rw [Query.expandIriAlternatives_pattern, expandIriAlternatives_rewriteBnodes,
    L4Factoidal.SPARQL.expandIriAlternatives_serviceFailure]

/-! ## 6. Executable checks

The rewrite fires on an alternative of IRIs, nested or not, and keeps the
path for the cases the module header lists. -/

private def gP : WfIri := ⟨"http://ex.org/p", by decide⟩
private def gQ : WfIri := ⟨"http://ex.org/q", by decide⟩
private def gR : WfIri := ⟨"http://ex.org/r", by decide⟩

private def isUnionOfBgps : QueryPattern → Bool
  | .union l r => isUnionOfBgps l && isUnionOfBgps r
  | .bgp [_] => true
  | _ => false

private def isPath : QueryPattern → Bool
  | .propertyPath _ _ _ => true
  | _ => false

#guard isUnionOfBgps
  (QueryPattern.propertyPath (.var "s") (.alternative (.iri gP) (.iri gQ)) (.var "o")).expandIriAlternatives
#guard isUnionOfBgps
  (QueryPattern.propertyPath (.var "s")
    (.alternative (.alternative (.iri gP) (.iri gQ)) (.iri gR)) (.var "o")).expandIriAlternatives
-- A sequence step keeps the path.
#guard isPath
  (QueryPattern.propertyPath (.var "s")
    (.alternative (.iri gP) (.sequence (.iri gQ) (.iri gR))) (.var "o")).expandIriAlternatives
-- `p|q*` keeps the path: a zero-length step is no triple pattern.
#guard isPath
  (QueryPattern.propertyPath (.var "s")
    (.alternative (.iri gP) (.zeroOrMore (.iri gQ))) (.var "o")).expandIriAlternatives
-- The `text:query` IRI keeps the path.
#guard isPath
  (QueryPattern.propertyPath (.var "s")
    (.alternative (.iri gP) (.iri fulltextQueryPred)) (.var "o")).expandIriAlternatives
-- A triple-term object keeps the path.
#guard isPath
  (QueryPattern.propertyPath (.var "s") (.alternative (.iri gP) (.iri gQ))
    (.tripleTerm (.var "a") (.var "b") (.var "c"))).expandIriAlternatives

#print axioms linkPath_evalTP
#print axioms iriAlternativeUnion_evalIn
#print axioms expandIriAlternatives_lowerWith
#print axioms expandIriAlternatives_serviceFailure
#print axioms expandIriAlternatives_rewriteBnodes
#print axioms Query.expandIriAlternatives_eval

end L4Factoidal.SPARQL
