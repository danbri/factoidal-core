/-
L4Factoidal.Storage.Sbm11.IdAllowedTheorems — the answers SPARQL 1.1 allows
for a group graph pattern, and the id path's answer as one of them
(https://github.com/danbri/factoidal/issues/776).

## Why not list equality

The id path does not produce its rows in the order of the reference
evaluator: a scan reads a pattern in the key order of a permutation, the
planner joins the patterns of a basic graph pattern in the order of their
estimates, and the hash join of a smaller left table probes with the right
rows (`TableTheorems.hashJoin_rows`). Inside a row the pairs come in column
order. SPARQL 1.1 fixes no order of solutions without ORDER BY (section
15.1), none among the rows that the ORDER BY keys do not separate, and none
of the values that GROUP_CONCAT and SAMPLE read (section 18.5.1). A slice
(LIMIT, OFFSET) of a sub-SELECT therefore has more than one correct answer.
The correct statement is: the id path's answer is an answer that the
specification allows.

## The definitions

* `BindEq μ ν`: the same solution mapping (every variable has the same
  lookup). The order of the pairs in a `Binding` is not part of the
  mapping.
* `PermPw R A B`: `A` is a permutation of a list that is `B` element for
  element up to `R`. `SolEquiv := PermPw BindEq`: the same multiset of
  solution mappings. An equivalence relation (`PermPw.refl`, `.symm`,
  `.trans`).
* `Allowed env ds p a ans`: `ans` is an answer of the group graph pattern
  `p` in the active graph `a` that SPARQL 1.1 allows. Inductive: each
  operator is the reference evaluator's own function (`SPARQL.join`,
  `leftJoin` with the condition `filterFn`, `List.filter`, `++`, `minus`,
  GRAPH, `bindRowsFresh`, `evalValues`, `selectPost`), applied to allowed
  answers of the operands; the leaves (basic graph pattern, property path)
  are the reference's solutions; and every node's answer may be replaced
  by a `SolEquiv` list (rule `equiv`). So `Allowed` is "the reference
  evaluator over some order of each intermediate multiset", which is
  choice (a) of issue 776: a sub-SELECT with LIMIT or OFFSET, GROUP_CONCAT
  or SAMPLE gets the answer of `selectPost` over SOME order of its input.
  No query is refused for this (census cost 0).

## The theorems

* `allowed_ref`: the reference evaluator's own answer is allowed, for every
  pattern of `InIdFragment` (the definition is not empty and not weaker
  than the reference at any node).
* Permutation congruence of the order-free operators (the output of
  permuted inputs is a permutation of the output): `join_perm`,
  `leftJoin_perm`, `union_perm`, `minus_perm`, `filter_perm`,
  `bindRowsFresh_perm` (when the binder does not read the row index of the
  freshness context: the id path refuses the others, `IdGroup` header),
  `graphVar_perm`. A sub-SELECT with a slice and the order-sensitive
  aggregates are not congruent; `Allowed` covers them by its rule
  `subSelect` over any allowed order of the input.
* `evalGroupIds_allowed`: for every pattern of `InIdFragment`, decoding the
  rows of `IdGroup.evalGroupIds` gives an allowed answer, and every id is in
  `ok`, under `hdec` (`Term.eqb` of two decoded ids is id equality on `ok`)
  and `HypsW LeafRel`: each leaf's rows decode to a `SolEquiv` list of the
  reference leaf (`LeafRel`), and each term the evaluator encodes gets an id
  in `ok` that decodes back. The leaf part (`LeafRel`) is a hypothesis
  here; it is the scans' property, not a composition step.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdGroupTheorems

namespace L4Factoidal.Storage.Sbm11.IdGroup

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds lookup_decRow)
open L4Factoidal.Storage.Sbm11.IdJoin (idJoin idValues join_decode values_decode union_decode)
open L4Factoidal.Storage.Sbm11.IdMinus (idMinus minus_decode)
open L4Factoidal.Storage.Sbm11.IdBind (idExtendRows)

/-! ## Lists equal up to order and up to a relation on the elements -/

/-- `R` element for element. -/
inductive Pw {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | nil : Pw R [] []
  | cons {a b : α} {l l' : List α} : R a b → Pw R l l' → Pw R (a :: l) (b :: l')

namespace Pw

variable {α : Type} {R : α → α → Prop}

theorem refl (hR : ∀ a, R a a) : ∀ (l : List α), Pw R l l
  | [] => .nil
  | a :: l => .cons (hR a) (refl hR l)

theorem symm (hR : ∀ a b, R a b → R b a) : ∀ {l l' : List α}, Pw R l l' → Pw R l' l
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hR _ _ h) (symm hR t)

theorem trans (hR : ∀ a b c, R a b → R b c → R a c) :
    ∀ {l l' l'' : List α}, Pw R l l' → Pw R l' l'' → Pw R l l''
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (hR _ _ _ h h') (trans hR t t')

theorem append : ∀ {l1 l1' l2 l2' : List α}, Pw R l1 l1' → Pw R l2 l2' → Pw R (l1 ++ l2) (l1' ++ l2')
  | _, _, _, _, .nil, h2 => h2
  | _, _, _, _, .cons h t, h2 => .cons h (append t h2)

theorem length_eq : ∀ {l l' : List α}, Pw R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [length_eq t]

/-- A permutation on the right side moves to the left side. -/
theorem perm_right : ∀ {A B C : List α}, Pw R A B → B.Perm C → ∃ A', A.Perm A' ∧ Pw R A' C := by
  intro A B C hpw hp
  induction hp generalizing A with
  | nil => exact ⟨A, List.Perm.refl _, hpw⟩
  | cons x _ ih =>
    cases hpw with
    | cons h t =>
      obtain ⟨A1, p1, w1⟩ := ih t
      exact ⟨_, p1.cons _, .cons h w1⟩
  | swap x y l =>
    cases hpw with
    | cons h1 t1 =>
      cases t1 with
      | cons h2 t2 => exact ⟨_, List.Perm.swap _ _ _, .cons h2 (.cons h1 t2)⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨A1, p1, w1⟩ := ih1 hpw
    obtain ⟨A2, p2, w2⟩ := ih2 w1
    exact ⟨A2, p1.trans p2, w2⟩

end Pw

/-- `A` is a permutation of a list that is `B` element for element up to
    `R`. -/
def PermPw {α : Type} (R : α → α → Prop) (A B : List α) : Prop := ∃ C, A.Perm C ∧ Pw R C B

namespace PermPw

variable {α : Type} {R : α → α → Prop}

theorem refl (hR : ∀ a, R a a) (A : List α) : PermPw R A A := ⟨A, List.Perm.refl _, Pw.refl hR A⟩

theorem of_perm (hR : ∀ a, R a a) {A B : List α} (h : A.Perm B) : PermPw R A B := ⟨B, h, Pw.refl hR B⟩

theorem of_pw {A B : List α} (h : Pw R A B) : PermPw R A B := ⟨A, List.Perm.refl _, h⟩

theorem symm (hR : ∀ a b, R a b → R b a) {A B : List α} : PermPw R A B → PermPw R B A := by
  rintro ⟨C, p, w⟩
  obtain ⟨B', p', w'⟩ := Pw.perm_right (Pw.symm hR w) p.symm
  exact ⟨B', p', w'⟩

theorem trans (hT : ∀ a b c, R a b → R b c → R a c) {A B D : List α} :
    PermPw R A B → PermPw R B D → PermPw R A D := by
  rintro ⟨C1, p1, w1⟩ ⟨C2, p2, w2⟩
  obtain ⟨C1', p1', w1'⟩ := Pw.perm_right w1 p2
  exact ⟨C1', p1.trans p1', Pw.trans hT w1' w2⟩

theorem append {A A' B B' : List α} : PermPw R A A' → PermPw R B B' → PermPw R (A ++ B) (A' ++ B') := by
  rintro ⟨C, p, w⟩ ⟨D, q, v⟩
  exact ⟨C ++ D, p.append q, Pw.append w v⟩

theorem nil_cons {a b : α} {A B : List α} (h : R a b) (t : PermPw R A B) : PermPw R (a :: A) (b :: B) := by
  obtain ⟨C, p, w⟩ := t
  exact ⟨a :: C, p.cons a, .cons h w⟩

/-- `flatMap` with element-wise related results. -/
theorem flatMap {β : Type} (f g : β → List α) :
    ∀ (L : List β), (∀ x ∈ L, PermPw R (f x) (g x)) → PermPw R (L.flatMap f) (L.flatMap g)
  | [], _ => ⟨[], List.Perm.refl _, .nil⟩
  | x :: L, h => by
    simp only [List.flatMap_cons]
    exact append (h x (List.mem_cons_self ..)) (flatMap f g L fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem map {β : Type} {S : β → β → Prop} (f : α → β) (hf : ∀ {a b}, R a b → S (f a) (f b))
    {A B : List α} : PermPw R A B → PermPw S (A.map f) (B.map f) := by
  rintro ⟨C, p, w⟩
  refine ⟨C.map f, p.map f, ?_⟩
  clear p
  induction w with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hf h) ih

end PermPw

/-! ## Solution mappings and multisets of them -/

/-- The same solution mapping: every variable has the same lookup. -/
def BindEq (mu nu : Binding) : Prop := ∀ v, mu.lookup v = nu.lookup v

theorem BindEq.refl (mu : Binding) : BindEq mu mu := fun _ => rfl
theorem BindEq.symm {mu nu : Binding} (h : BindEq mu nu) : BindEq nu mu := fun v => (h v).symm
theorem BindEq.trans {mu nu xi : Binding} (h1 : BindEq mu nu) (h2 : BindEq nu xi) : BindEq mu xi :=
  fun v => (h1 v).trans (h2 v)

/-- The same multiset of solution mappings. -/
def SolEquiv (A B : SolutionSeq) : Prop := PermPw BindEq A B

theorem SolEquiv.refl (A : SolutionSeq) : SolEquiv A A := PermPw.refl BindEq.refl A
theorem SolEquiv.symm {A B : SolutionSeq} (h : SolEquiv A B) : SolEquiv B A :=
  PermPw.symm (R := BindEq) (fun _ _ h => BindEq.symm h) h
theorem SolEquiv.trans {A B C : SolutionSeq} (h1 : SolEquiv A B) (h2 : SolEquiv B C) : SolEquiv A C :=
  PermPw.trans (R := BindEq) (fun _ _ _ h h' => BindEq.trans h h') h1 h2
theorem SolEquiv.of_perm {A B : SolutionSeq} (h : A.Perm B) : SolEquiv A B := PermPw.of_perm BindEq.refl h

/-! ## The answers SPARQL 1.1 allows -/

/-- The reference evaluator's solutions of a pattern in an active graph. -/
def refSol (env : EvalEnv) (ds : Dataset) (p : QueryPattern) (a : Graph) : SolutionSeq :=
  (QueryPattern.lowerWith env Binding.empty p).evalIn ds a

/-- `ans` is an answer of `p` in the active graph `a` that SPARQL 1.1
    allows (module header): each operator is the reference's function on
    allowed answers of its operands, the leaves are the reference's
    solutions, and any answer may be replaced by the same multiset of
    solution mappings in another order (`equiv`). -/
inductive Allowed (env : EvalEnv) (ds : Dataset) : QueryPattern → Graph → SolutionSeq → Prop
  | bgp (b : Bgp) (a : Graph) : Allowed env ds (.bgp b) a (refSol env ds (.bgp b) a)
  | path (s : PatternSubject) (path : PropertyPath) (o : PatternTerm) (a : Graph) :
      Allowed env ds (.propertyPath s path o) a (refSol env ds (.propertyPath s path o) a)
  | join {l r : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      Allowed env ds l a A → Allowed env ds r a B → Allowed env ds (.join l r) a (join A B)
  | leftJoin {l r : QueryPattern} {c : Expr} {a : Graph} {A B : SolutionSeq} :
      Allowed env ds l a A → Allowed env ds r a B →
        Allowed env ds (.leftJoin l r c) a (leftJoin A B (filterFn env c a))
  | filter {c : Expr} {q : QueryPattern} {a : Graph} {A : SolutionSeq} :
      Allowed env ds q a A → Allowed env ds (.filter c q) a (A.filter (filterFn env c a))
  | union {l r : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      Allowed env ds l a A → Allowed env ds r a B → Allowed env ds (.union l r) a (A ++ B)
  | minus {l r : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      Allowed env ds l a A → Allowed env ds r a B → Allowed env ds (.minus l r) a (minus A B)
  | graphIri {i : WfIri} {q : QueryPattern} {a g : Graph} {A : SolutionSeq} :
      ds.lookupNamedIri i.val = some g → Allowed env ds q g A → Allowed env ds (.graph (.iri i) q) a A
  | graphIriNone {i : WfIri} {q : QueryPattern} {a : Graph} :
      ds.lookupNamedIri i.val = none → Allowed env ds (.graph (.iri i) q) a []
  | graphVar {v : VarName} {q : QueryPattern} {a : Graph} (F : NamedGraph → SolutionSeq) :
      (∀ ng ∈ ds.named, Allowed env ds q ng.graph (F ng)) →
        Allowed env ds (.graph (.var v) q) a
          (ds.named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
  | graphBnode {b : BNodeId} {q : QueryPattern} {a : Graph} {A : SolutionSeq} :
      Allowed env ds q a A → Allowed env ds (.graph (.bnode b) q) a A
  | graphLiteral {l : WfLiteral} {q : QueryPattern} {a : Graph} {A : SolutionSeq} :
      Allowed env ds q a A → Allowed env ds (.graph (.literal l) q) a A
  | graphTriple {s p o : PatternTerm} {q : QueryPattern} {a : Graph} {A : SolutionSeq} :
      Allowed env ds q a A → Allowed env ds (.graph (.tripleTerm s p o) q) a A
  | bind {e : Expr} {v : VarName} {q : QueryPattern} {a : Graph} {A : SolutionSeq} :
      Allowed env ds q a A → Allowed env ds (.bind e v q) a (bindRowsFresh (binderFn env e) a v A 0)
  | values (vars : List VarName) (rows : List (List (Option Term))) (a : Graph) :
      Allowed env ds (.values vars rows) a (evalValues vars rows)
  | subSelect {form : QueryForm} {dcs : List DatasetClause} {inner : QueryPattern}
      {gb : Option (List GroupCondition)} {hv : List Expr} {md : SolutionModifier}
      {pv : Option (List Binding)} {bs : Option String} {a : Graph} {A : SolutionSeq} :
      Allowed env ds inner a A →
        Allowed env ds (.subSelect (.mk form dcs inner gb hv md pv bs)) a
          (selectPost env a (.mk form dcs inner gb hv md pv bs) A)
  | empty (a : Graph) : Allowed env ds .empty a [Binding.empty]
  | equiv {p : QueryPattern} {a : Graph} {A B : SolutionSeq} :
      Allowed env ds p a A → SolEquiv A B → Allowed env ds p a B

/-! ## The reference's answer is allowed -/

/-- The reference evaluator's answer is an allowed answer, for every
    pattern of the fragment: `Allowed` is not weaker than the reference at
    any node. Structural recursion on the pattern. -/
theorem allowed_ref (env : EvalEnv) (ds : Dataset) :
    ∀ (p : QueryPattern) (a : Graph), InIdFragment p → Allowed env ds p a (refSol env ds p a)
  | .bgp b, a, _ => .bgp b a
  | .propertyPath s path o, a, _ => .path s path o a
  | .join l r, a, hp => by
    have il := allowed_ref env ds l a hp.1
    have ir := allowed_ref env ds r a hp.2
    have e : refSol env ds (.join l r) a = join (refSol env ds l a) (refSol env ds r a) := by
      show (GraphPattern.join _ _).evalIn ds a = _
      rw [evalIn_join ds a _ _ (lower_ne_serviceVar env l hp.1) (lower_ne_serviceVar env r hp.2),
        hashJoin_eq_join]
      rfl
    rw [e]
    exact .join il ir
  | .leftJoin l r c, a, hp => by
    have il := allowed_ref env ds l a hp.1
    have ir := allowed_ref env ds r a hp.2
    have e : refSol env ds (.leftJoin l r c) a =
        leftJoin (refSol env ds l a) (refSol env ds r a) (filterFn env c a) := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn, hashLeftJoin_eq_leftJoin]
      rfl
    rw [e]
    exact .leftJoin il ir
  | .filter c q, a, hp => by
    have iq := allowed_ref env ds q a hp
    have e : refSol env ds (.filter c q) a = (refSol env ds q a).filter (filterFn env c a) := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [filterLowered_evalIn]
      rfl
    rw [e]
    exact .filter iq
  | .union l r, a, hp => by
    have il := allowed_ref env ds l a hp.1
    have ir := allowed_ref env ds r a hp.2
    have e : refSol env ds (.union l r) a = refSol env ds l a ++ refSol env ds r a := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn]
      rfl
    rw [e]
    exact .union il ir
  | .minus l r, a, hp => by
    have il := allowed_ref env ds l a hp.1
    have ir := allowed_ref env ds r a hp.2
    have e : refSol env ds (.minus l r) a = minus (refSol env ds l a) (refSol env ds r a) := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn, hashMinus_eq_minus]
    rw [e]
    exact .minus il ir
  | .graph (.iri i) q, a, hp => by
    have e : refSol env ds (.graph (.iri i) q) a =
        match ds.lookupNamedIri i.val with
        | some g => refSol env ds q g
        | none => [] := by
      show (GraphPattern.graph (.iri i) (QueryPattern.lowerWith env Binding.empty q)).evalIn ds a = _
      rw [GraphPattern.evalIn]
      rfl
    rw [e]
    cases hg : ds.lookupNamedIri i.val with
    | none => exact .graphIriNone hg
    | some g => exact .graphIri hg (allowed_ref env ds q g hp)
  | .graph (.var v) q, a, hp => by
    have e : refSol env ds (.graph (.var v) q) a =
        ds.named.flatMap fun ng => (refSol env ds q ng.graph).filterMap
          (Binding.bindIfCompatible v ng.name.toTerm) := by
      show (GraphPattern.graph (.var v) (QueryPattern.lowerWith env Binding.empty q)).evalIn ds a = _
      rw [GraphPattern.evalIn]
      rfl
    rw [e]
    exact .graphVar (fun ng => refSol env ds q ng.graph) fun ng _ => allowed_ref env ds q ng.graph hp
  | .graph (.bnode b) q, a, hp => by
    have e : refSol env ds (.graph (.bnode b) q) a = refSol env ds q a := by
      show (GraphPattern.graph (.bnode b) (QueryPattern.lowerWith env Binding.empty q)).evalIn ds a = _
      rw [GraphPattern.evalIn]
      · rfl
      · intro _ h'; cases h'
      · intro _ h'; cases h'
    rw [e]
    exact .graphBnode (allowed_ref env ds q a hp)
  | .graph (.literal l) q, a, hp => by
    have e : refSol env ds (.graph (.literal l) q) a = refSol env ds q a := by
      show (GraphPattern.graph (.literal l) (QueryPattern.lowerWith env Binding.empty q)).evalIn ds a = _
      rw [GraphPattern.evalIn]
      · rfl
      · intro _ h'; cases h'
      · intro _ h'; cases h'
    rw [e]
    exact .graphLiteral (allowed_ref env ds q a hp)
  | .graph (.tripleTerm s' p' o') q, a, hp => by
    have e : refSol env ds (.graph (.tripleTerm s' p' o') q) a = refSol env ds q a := by
      show (GraphPattern.graph (.tripleTerm s' p' o') (QueryPattern.lowerWith env Binding.empty q)).evalIn
        ds a = _
      rw [GraphPattern.evalIn]
      · rfl
      · intro _ h'; cases h'
      · intro _ h'; cases h'
    rw [e]
    exact .graphTriple (allowed_ref env ds q a hp)
  | .bind e v q, a, hp => by
    have eq : refSol env ds (.bind e v q) a = bindRowsFresh (binderFn env e) a v (refSol env ds q a) 0 := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn]
      rfl
    rw [eq]
    exact .bind (allowed_ref env ds q a hp)
  | .values vars rows, a, _ => by
    have e : refSol env ds (.values vars rows) a = evalValues vars rows := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn]
    rw [e]
    exact .values vars rows a
  | .subSelect (.mk form dcs inner gb hv md pv bs), a, hp => by
    have e : refSol env ds (.subSelect (.mk form dcs inner gb hv md pv bs)) a =
        selectPost env a (.mk form dcs inner gb hv md pv bs) (refSol env ds inner a) := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn]
      have hmu : lateralVisibleMu Binding.empty form inner = Binding.empty := by
        unfold lateralVisibleMu
        cases lateralVisibleVars form <;> rfl
      rw [hmu]
    rw [e]
    exact .subSelect (allowed_ref env ds inner a hp)
  | .empty, a, _ => by
    have e : refSol env ds .empty a = [Binding.empty] := by
      simp only [refSol, QueryPattern.lowerWith]
      rw [GraphPattern.evalIn]
    rw [e]
    exact .empty a
  | .lateral _ _, _, hp => absurd hp id
  | .service _ _ _, _, hp => absurd hp id
  | .serviceVar _ _ _, _, hp => absurd hp id

/-! ## Permutation congruence of the order-free operators -/

theorem perm_flatMap_left {α β : Type} (f g : α → List β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).Perm (g a)) → (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact (h a (List.mem_cons_self ..)).append
      (perm_flatMap_left f g l fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Join (SPARQL 1.1 section 18.5): permuted inputs give a permutation of
    the output. -/
theorem join_perm {A A' B B' : SolutionSeq} (hA : A.Perm A') (hB : B.Perm B') :
    (join A B).Perm (join A' B') := by
  unfold join
  refine List.Perm.trans (List.Perm.flatMap_right _ hA) ?_
  exact perm_flatMap_left _ _ A' fun mu1 _ => List.Perm.filterMap _ hB

/-- LeftJoin: permuted inputs give a permutation of the output. -/
theorem leftJoin_perm {A A' B B' : SolutionSeq} (cond : Binding → Bool) (hA : A.Perm A')
    (hB : B.Perm B') : (leftJoin A B cond).Perm (leftJoin A' B' cond) := by
  unfold leftJoin
  refine List.Perm.trans (List.Perm.flatMap_right _ hA) ?_
  apply perm_flatMap_left _ _ A'
  intro mu1 _
  have hp := List.Perm.filterMap (fun mu2 =>
      if mu1.compatible mu2 then
        (if cond (mu1.merge mu2) then some (mu1.merge mu2) else none) else none) hB
  dsimp only
  rw [hp.isEmpty_eq]
  split
  · exact List.Perm.refl _
  · exact hp

/-- Union: permuted inputs give a permutation of the output. -/
theorem union_perm {A A' B B' : SolutionSeq} (hA : A.Perm A') (hB : B.Perm B') :
    (A ++ B).Perm (A' ++ B') := hA.append hB

/-- Minus: permuted inputs give a permutation of the output. -/
theorem minus_perm {A A' B B' : SolutionSeq} (hA : A.Perm A') (hB : B.Perm B') :
    (minus A B).Perm (minus A' B') := by
  unfold minus
  have e : (fun mu1 => !B.any fun mu2 => mu1.compatible mu2 && !domainsDisjoint mu1 mu2) =
      (fun mu1 => !B'.any fun mu2 => mu1.compatible mu2 && !domainsDisjoint mu1 mu2) := by
    funext mu1
    rw [hB.any_eq]
  rw [e]
  exact List.Perm.filter _ hA

/-- Filter: a permuted input gives a permutation of the output. -/
theorem filter_perm {A A' : SolutionSeq} (cond : Binding → Bool) (hA : A.Perm A') :
    (A.filter cond).Perm (A'.filter cond) := List.Perm.filter _ hA

/-- One row of `bindRowsFresh` with freshness context `i`. -/
def bindRow (binder : Graph → Binding → Option Term) (active : Graph) (v : VarName) (i : Nat)
    (mu : Binding) : Binding :=
  match binder active (mu.withFreshnessCtx (toString i) v) with
  | some t => match mu.lookup v with
              | some _ => mu
              | none => mu.bind v t
  | none => mu

theorem bindRowsFresh_map (binder : Graph → Binding → Option Term) (active : Graph) (v : VarName)
    (hfree : ∀ (mu : Binding) (i j : Nat), binder active (mu.withFreshnessCtx (toString i) v) =
      binder active (mu.withFreshnessCtx (toString j) v)) :
    ∀ (A : SolutionSeq) (i : Nat), bindRowsFresh binder active v A i = A.map (bindRow binder active v 0)
  | [], _ => rfl
  | mu :: rest, i => by
    simp only [bindRowsFresh, List.map_cons]
    rw [bindRowsFresh_map binder active v hfree rest (i + 1)]
    congr 1
    unfold bindRow
    rw [hfree mu i 0]
    rfl

/-- Extend: a permuted input gives a permutation of the output, when the
    binder does not read the row index of the freshness context (BNODE(),
    UUID() and STRUUID() do; the id path refuses such a BIND). -/
theorem bindRowsFresh_perm (binder : Graph → Binding → Option Term) (active : Graph) (v : VarName)
    (hfree : ∀ (mu : Binding) (i j : Nat), binder active (mu.withFreshnessCtx (toString i) v) =
      binder active (mu.withFreshnessCtx (toString j) v))
    {A A' : SolutionSeq} (hA : A.Perm A') (i : Nat) :
    (bindRowsFresh binder active v A i).Perm (bindRowsFresh binder active v A' i) := by
  rw [bindRowsFresh_map binder active v hfree, bindRowsFresh_map binder active v hfree]
  exact hA.map _

/-- GRAPH ?g: permuted inputs per named graph give a permutation of the
    output. -/
theorem graphVar_perm (named : List NamedGraph) (v : VarName) (F F' : NamedGraph → SolutionSeq)
    (h : ∀ ng ∈ named, (F ng).Perm (F' ng)) :
    (named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)).Perm
      (named.flatMap fun ng => (F' ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)) :=
  perm_flatMap_left _ _ named fun ng hng => List.Perm.filterMap _ (h ng hng)

/-! ## The id path's answer is allowed -/

/-- The leaves' rows decode to the same multiset of solution mappings as
    the reference leaf, with ids in `ok`. -/
def LeafRel (env : EvalEnv) (ds : Dataset) (σ : Leaves) (dec : UInt64 → Term) (ok : UInt64 → Prop) :
    QueryPattern → Graph → Prop
  | .bgp b, a =>
    SolEquiv (refSol env ds (.bgp b) a) ((σ.bgp a b).map (decRow dec)) ∧ ∀ r ∈ σ.bgp a b, RowIds ok r
  | .propertyPath s path o, a =>
    SolEquiv (refSol env ds (.propertyPath s path o) a) ((σ.path a s path o).map (decRow dec)) ∧
      ∀ r ∈ σ.path a s path o, RowIds ok r
  | _, _ => True

/-- The hypotheses of the id evaluator, with a condition `LP` at the leaves
    (basic graph patterns and property paths): `LP` at each leaf, and each
    term the evaluator encodes (a graph name, a BIND value, a VALUES term, a
    value of a sub-SELECT; only the terms of the rows produced) gets an id
    in `ok` that decodes back to it. -/
def HypsW (LP : QueryPattern → Graph → Prop) (env : EvalEnv) (ds : Dataset) (σ : Leaves)
    (dec : UInt64 → Term) (idv : Term → UInt64) (ok : UInt64 → Prop) : QueryPattern → Graph → Prop
  | .bgp b, a => LP (.bgp b) a
  | .propertyPath s path o, a => LP (.propertyPath s path o) a
  | .join l r, a | .leftJoin l r _, a | .union l r, a | .minus l r, a =>
    HypsW LP env ds σ dec idv ok l a ∧ HypsW LP env ds σ dec idv ok r a
  | .filter _ q, a => HypsW LP env ds σ dec idv ok q a
  | .graph (.iri i) q, _ =>
    match ds.lookupNamedIri i.val with
    | some g => HypsW LP env ds σ dec idv ok q g
    | none => True
  | .graph (.var _) q, _ =>
    ∀ ng ∈ ds.named, HypsW LP env ds σ dec idv ok q ng.graph ∧ TermOk dec ok idv ng.name.toTerm
  | .graph (.bnode _) q, a | .graph (.literal _) q, a | .graph (.tripleTerm _ _ _) q, a =>
    HypsW LP env ds σ dec idv ok q a
  | .bind e v q, a =>
    HypsW LP env ds σ dec idv ok q a ∧
      ∀ j (hj : j < (evalGroupIds env ds σ dec idv q a).length) (t : Term),
        binderFn env e a ((decRow dec (evalGroupIds env ds σ dec idv q a)[j]).withFreshnessCtx
          (toString j) v) = some t → TermOk dec ok idv t
  | .values _ rows, _ => ∀ row ∈ rows, ∀ t, some t ∈ row → TermOk dec ok idv t
  | .subSelect (.mk form dcs inner gb hv md pv bs), a =>
    HypsW LP env ds σ dec idv ok inner a ∧
      ∀ mu ∈ selectPost env a (.mk form dcs inner gb hv md pv bs)
          ((evalGroupIds env ds σ dec idv inner a).map (decRow dec)),
        ∀ p ∈ mu, TermOk dec ok idv p.2
  | .empty, _ | .lateral _ _, _ | .service _ _ _, _ | .serviceVar _ _ _, _ => True

/-- `HypsW` is monotone in the leaf condition. -/
theorem HypsW.mono {LP LQ : QueryPattern → Graph → Prop} (env : EvalEnv) (ds : Dataset) (σ : Leaves)
    (dec : UInt64 → Term) (idv : Term → UInt64) (ok : UInt64 → Prop)
    (hm : ∀ p a, LP p a → LQ p a) :
    ∀ (p : QueryPattern) (a : Graph), HypsW LP env ds σ dec idv ok p a → HypsW LQ env ds σ dec idv ok p a
  | .bgp b, a, h => hm _ a h
  | .propertyPath s path o, a, h => hm _ a h
  | .join l r, a, h => ⟨HypsW.mono env ds σ dec idv ok hm l a h.1, HypsW.mono env ds σ dec idv ok hm r a h.2⟩
  | .leftJoin l r _, a, h =>
    ⟨HypsW.mono env ds σ dec idv ok hm l a h.1, HypsW.mono env ds σ dec idv ok hm r a h.2⟩
  | .union l r, a, h => ⟨HypsW.mono env ds σ dec idv ok hm l a h.1, HypsW.mono env ds σ dec idv ok hm r a h.2⟩
  | .minus l r, a, h => ⟨HypsW.mono env ds σ dec idv ok hm l a h.1, HypsW.mono env ds σ dec idv ok hm r a h.2⟩
  | .filter _ q, a, h => HypsW.mono env ds σ dec idv ok hm q a h
  | .graph (.iri i) q, a, h => by
    unfold HypsW at h ⊢
    split
    · next g hg => rw [hg] at h; exact HypsW.mono env ds σ dec idv ok hm q g h
    · trivial
  | .graph (.var _) q, _, h => fun ng hng => ⟨HypsW.mono env ds σ dec idv ok hm q ng.graph (h ng hng).1, (h ng hng).2⟩
  | .graph (.bnode _) q, a, h => HypsW.mono env ds σ dec idv ok hm q a h
  | .graph (.literal _) q, a, h => HypsW.mono env ds σ dec idv ok hm q a h
  | .graph (.tripleTerm _ _ _) q, a, h => HypsW.mono env ds σ dec idv ok hm q a h
  | .bind _ _ q, a, h => ⟨HypsW.mono env ds σ dec idv ok hm q a h.1, h.2⟩
  | .values _ _, _, h => h
  | .subSelect (.mk _ _ inner _ _ _ _ _), a, h => ⟨HypsW.mono env ds σ dec idv ok hm inner a h.1, h.2⟩
  | .empty, _, h => h
  | .lateral _ _, _, h => h
  | .service _ _ _, _, h => h
  | .serviceVar _ _ _, _, h => h

/-- **Nested groups on ids, up to order.** For every pattern of the
    fragment, decoding the rows of `evalGroupIds` gives an answer SPARQL 1.1
    allows (`Allowed`), and the rows hold ids in `ok` only; under `hdec` and
    `HypsW LeafRel`. Each operator's step is the decoding lemma of its id
    form (`join_decode`, `leftJoinC_decode`, `union_decode`,
    `minus_decode`, `bindG_decode`, `extendAt_decode`, `values_decode`,
    `decRow_encRow`), so the order freedom enters at the leaves only.
    Structural recursion on the pattern. -/
theorem evalGroupIds_allowed (env : EvalEnv) (ds : Dataset) (σ : Leaves) (dec : UInt64 → Term)
    (idv : Term → UInt64) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) :
    ∀ (p : QueryPattern) (a : Graph), InIdFragment p →
      HypsW (LeafRel env ds σ dec ok) env ds σ dec idv ok p a →
      Allowed env ds p a ((evalGroupIds env ds σ dec idv p a).map (decRow dec)) ∧
        ∀ r ∈ evalGroupIds env ds σ dec idv p a, RowIds ok r
  | .bgp b, a, _, h => ⟨.equiv (.bgp b a) h.1, h.2⟩
  | .propertyPath s path o, a, _, h => ⟨.equiv (.path s path o a) h.1, h.2⟩
  | .join l r, a, hp, h => by
    obtain ⟨il, ir⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec l a hp.1 h.1
    obtain ⟨jl, jr⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec r a hp.2 h.2
    refine ⟨?_, rowIds_idJoin ok _ _ ir jr⟩
    show Allowed env ds _ a ((idJoin _ _).map (decRow dec))
    rw [join_decode dec ok hdec _ _ ir jr]
    exact .join il jl
  | .leftJoin l r c, a, hp, h => by
    obtain ⟨il, ir⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec l a hp.1 h.1
    obtain ⟨jl, jr⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec r a hp.2 h.2
    refine ⟨?_, rowIds_idLeftJoinC ok _ _ _ ir jr⟩
    show Allowed env ds _ a ((idLeftJoinC _ _ _).map (decRow dec))
    rw [leftJoinC_decode dec ok hdec (filterFn env c a) _ _ ir jr]
    exact .leftJoin il jl
  | .filter c q, a, hp, h => by
    obtain ⟨iq, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q a hp h
    refine ⟨?_, fun r hr => jq r ((List.mem_filter.mp hr).1)⟩
    have e : ((evalGroupIds env ds σ dec idv q a).filter fun r => filterFn env c a (decRow dec r)).map
        (decRow dec) = ((evalGroupIds env ds σ dec idv q a).map (decRow dec)).filter (filterFn env c a) := by
      rw [List.filter_map]
      rfl
    show Allowed env ds _ a (((evalGroupIds env ds σ dec idv q a).filter _).map (decRow dec))
    rw [e]
    exact .filter iq
  | .union l r, a, hp, h => by
    obtain ⟨il, ir⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec l a hp.1 h.1
    obtain ⟨jl, jr⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec r a hp.2 h.2
    refine ⟨?_, ?_⟩
    · show Allowed env ds _ a (List.map (decRow dec) (_ ++ _))
      rw [List.map_append]
      exact .union il jl
    · intro x hx
      rcases List.mem_append.mp hx with e | e
      · exact ir x e
      · exact jr x e
  | .minus l r, a, hp, h => by
    obtain ⟨il, ir⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec l a hp.1 h.1
    obtain ⟨jl, jr⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec r a hp.2 h.2
    refine ⟨?_, fun x hx => ir x ((List.mem_filter.mp hx).1)⟩
    show Allowed env ds _ a ((idMinus _ _).map (decRow dec))
    rw [minus_decode dec ok hdec _ _ ir jr]
    exact .minus il jl
  | .graph (.iri i) q, a, hp, h => by
    rw [HypsW] at h
    rw [evalGroupIds]
    cases hg : ds.lookupNamedIri i.val with
    | none => exact ⟨.graphIriNone hg, fun r hr => by cases hr⟩
    | some g =>
      rw [hg] at h
      obtain ⟨iq, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q g hp h
      exact ⟨.graphIri hg iq, jq⟩
  | .graph (.var v) q, a, hp, h => by
    rw [HypsW] at h
    rw [evalGroupIds]
    refine ⟨?_, ?_⟩
    · have e : (ds.named.flatMap fun ng =>
            (evalGroupIds env ds σ dec idv q ng.graph).filterMap (idBindG v (idv ng.name.toTerm))).map
            (decRow dec) =
          ds.named.flatMap fun ng =>
            ((evalGroupIds env ds σ dec idv q ng.graph).map (decRow dec)).filterMap
              (Binding.bindIfCompatible v ng.name.toTerm) := by
        rw [List.map_flatMap]
        apply L4Factoidal.Qlvr.flatMap_congr'
        intro ng hng
        obtain ⟨hq, hok, hd⟩ := h ng hng
        obtain ⟨_, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q ng.graph hp hq
        rw [List.filterMap_map, List.map_filterMap]
        apply OptJoin.filterMap_congr'
        intro r hr
        simp only [Function.comp_def]
        rw [bindG_decode dec ok hdec v _ hok r (jq r hr), hd]
      rw [e]
      exact .graphVar (fun ng => (evalGroupIds env ds σ dec idv q ng.graph).map (decRow dec))
        fun ng hng => (evalGroupIds_allowed env ds σ dec idv ok hdec q ng.graph hp (h ng hng).1).1
    · intro r hr
      rw [List.mem_flatMap] at hr
      obtain ⟨ng, hng, hr⟩ := hr
      obtain ⟨hq, hok, _⟩ := h ng hng
      obtain ⟨_, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q ng.graph hp hq
      rw [List.mem_filterMap] at hr
      obtain ⟨r0, h0, e0⟩ := hr
      exact rowIds_idBindG ok v _ hok r0 r (jq r0 h0) e0
  | .graph (.bnode b) q, a, hp, h => by
    obtain ⟨iq, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q a hp h
    exact ⟨.graphBnode iq, jq⟩
  | .graph (.literal l) q, a, hp, h => by
    obtain ⟨iq, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q a hp h
    exact ⟨.graphLiteral iq, jq⟩
  | .graph (.tripleTerm s' p' o') q, a, hp, h => by
    obtain ⟨iq, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q a hp h
    exact ⟨.graphTriple iq, jq⟩
  | .bind e v q, a, hp, h => by
    obtain ⟨iq, jq⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec q a hp h.1
    have hT : ∀ j (hj : j < (evalGroupIds env ds σ dec idv q a).length) (t : Term),
        binderFn env e a ((decRow dec (evalGroupIds env ds σ dec idv q a)[j]).withFreshnessCtx
          (toString (0 + j)) v) = some t → TermOk dec ok idv t := by
      intro j hj t ht
      rw [Nat.zero_add] at ht
      exact h.2 j hj t ht
    obtain ⟨d1, d2⟩ := extendAt_decode dec ok idv (binderFn env e a) (binderFn env e) a
      (fun _ => rfl) v (evalGroupIds env ds σ dec idv q a) 0 jq hT
    refine ⟨?_, d2⟩
    show Allowed env ds _ a ((idExtendRows _ v _ 0).map (decRow dec))
    rw [d1]
    exact .bind iq
  | .values vars rows, a, _, h => by
    refine ⟨?_, ?_⟩
    · show Allowed env ds _ a ((idValues vars _).map (decRow dec))
      rw [values_decode dec idv vars rows fun row hrow t ht => (h row hrow t ht).2]
      exact .values vars rows a
    · intro r hr
      simp only [evalGroupIds, idValues, List.map_map, List.mem_map] at hr
      obtain ⟨row, hrow, e⟩ := hr
      subst e
      exact rowIds_idZip ok idv vars row [] (fun t ht => (h row hrow t ht).1) (fun _ h => by cases h)
  | .subSelect (.mk form dcs inner gb hv md pv bs), a, hp, h => by
    obtain ⟨iq, _⟩ := evalGroupIds_allowed env ds σ dec idv ok hdec inner a hp h.1
    refine ⟨?_, ?_⟩
    · show Allowed env ds _ a (((selectPost env a _
          ((evalGroupIds env ds σ dec idv inner a).map (decRow dec))).map (encRow idv)).map (decRow dec))
      rw [List.map_map]
      have e : ((selectPost env a (.mk form dcs inner gb hv md pv bs)
            ((evalGroupIds env ds σ dec idv inner a).map (decRow dec))).map (decRow dec ∘ encRow idv)) =
          selectPost env a (.mk form dcs inner gb hv md pv bs)
            ((evalGroupIds env ds σ dec idv inner a).map (decRow dec)) := by
        conv => rhs; rw [← List.map_id (selectPost env a _ _)]
        apply List.map_congr_left
        intro mu hmu'
        exact decRow_encRow dec idv mu fun p hp' => (h.2 mu hmu' p hp').2
      rw [e]
      exact .subSelect iq
    · intro r hr
      simp only [evalGroupIds, List.mem_map] at hr
      obtain ⟨mu, hmu, e⟩ := hr
      subst e
      intro b hb
      simp only [encRow, List.mem_map] at hb
      obtain ⟨p, hp', e⟩ := hb
      subst e
      exact (h.2 mu hmu p hp').1
  | .empty, a, _, _ => by
    refine ⟨.empty a, ?_⟩
    intro r hr
    simp only [evalGroupIds, List.mem_singleton] at hr
    subst hr
    intro b hb; cases hb
  | .lateral _ _, _, hp, _ => absurd hp id
  | .service _ _ _, _, hp, _ => absurd hp id
  | .serviceVar _ _ _, _, hp, _ => absurd hp id

end L4Factoidal.Storage.Sbm11.IdGroup

#print axioms L4Factoidal.Storage.Sbm11.IdGroup.allowed_ref
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.evalGroupIds_allowed
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.join_perm
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.leftJoin_perm
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.minus_perm
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.bindRowsFresh_perm
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.graphVar_perm
#print axioms L4Factoidal.Storage.Sbm11.IdGroup.PermPw.trans
