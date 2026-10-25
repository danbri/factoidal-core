/-
L4Factoidal.Storage.Sbm11.AllowedPermTheorems — the answers SPARQL 1.1
allows (`IdGroup.Allowed`) do not depend on the order of the triples of a
graph (https://github.com/danbri/factoidal/issues/776; row L3c of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

An RDF graph is a set of triples (RDF 1.1 Concepts section 3); the
reference evaluator reads a `Graph` as a list. The generation of the packer
denotes its input as sets (`PackSpecTheorems.packSpec_default`,
`packSpec_named`, `packSpec_names`), in the SPO row order and without
repeats. This module shows that the order does not matter:

* `evalBgp_perm`: the solutions of a basic graph pattern over a permuted
  graph are a permutation;
* `evalPath_perm`: the pairs of a property path over a permuted graph are a
  permutation, when every object of the graph is its own join key
  (`Term.joinKey t = t`: no language tag with an upper-case letter), so that
  `Term.eqb` is equality on the pairs and `dedupPath` keeps one pair of each
  value;
* `allowed_perm`: `Allowed env ds p a A` gives `Allowed env ds' p a' A` when
  `a'` is a permutation of `a`, every named graph of `ds'` is a permutation
  of the named graph of `ds` with the same name (`NamedPerm`), the graphs
  are `GraphFixed`, and `p` is `PermOk`: no full-text basic graph pattern,
  and no EXISTS in a FILTER, OPTIONAL or BIND condition or outside the WHERE
  clause of a sub-SELECT (those read the active graph through
  `substituteExistentials`; not covered here).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdLeafTheorems
import L4Factoidal.Storage.Sbm11.SubSelectTableTheorems
import L4Factoidal.RDF.GraphIndex

namespace L4Factoidal.Storage.Sbm11.AllowedPerm

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdGroup

/-! ## Lists -/

theorem perm_flatMap {α β : Type} {l l' : List α} (h : l.Perm l') (f g : α → List β)
    (hfg : ∀ a ∈ l', (f a).Perm (g a)) : (l.flatMap f).Perm (l'.flatMap g) :=
  (List.Perm.flatMap_right f h).trans (perm_flatMap_left f g l' hfg)

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## Basic graph patterns -/

theorem evalBgpFrom_perm {g g' : Graph} (h : g.Perm g') :
    ∀ (b : Bgp) (mu : Binding), (evalBgpFrom g b mu).Perm (evalBgpFrom g' b mu)
  | [], mu => List.Perm.refl _
  | tp :: rest, mu => by
    simp only [evalBgpFrom, evalTP]
    exact perm_flatMap (List.Perm.filterMap _ h) _ _ fun mu' _ => evalBgpFrom_perm h rest mu'

theorem evalBgp_perm {g g' : Graph} (h : g.Perm g') (b : Bgp) : (evalBgp b g).Perm (evalBgp b g') :=
  evalBgpFrom_perm h b Binding.empty

/-! ## Terms that are their own join key -/

/-- A pair of terms that are their own join keys. -/
def PairFixed (pr : Term × Term) : Prop := pr.1.joinKey = pr.1 ∧ pr.2.joinKey = pr.2

/-- Every object of the graph is its own join key (subjects are IRIs or
    blank nodes, which always are). -/
def GraphFixed (g : Graph) : Prop := ∀ t ∈ g, t.o.joinKey = t.o

/-- Every graph is `GraphFixed`: no well-formed literal has an upper-case
    language tag (`RDF.literalWf`, `Term.joinKey_eq_self`;
    https://github.com/danbri/factoidal/issues/1001). -/
theorem graphFixed (g : Graph) : GraphFixed g := fun t _ => Term.joinKey_eq_self t.o

theorem subject_fixed (s : Subject) : s.toTerm.joinKey = s.toTerm := by
  cases s <;> rfl

theorem pathPairEq_eq {x y : Term × Term} (hx : PairFixed x) (hy : PairFixed y) (h : pathPairEq x y = true) :
    x = y := by
  unfold pathPairEq at h
  simp only [Bool.and_eq_true] at h
  have h1 := (Term.eqb_iff_joinKey _ _).1 h.1
  have h2 := (Term.eqb_iff_joinKey _ _).1 h.2
  rw [hx.1, hy.1] at h1
  rw [hx.2, hy.2] at h2
  exact Prod.ext h1 h2

theorem pathPairEq_refl (x : Term × Term) : pathPairEq x x = true := by
  simp [pathPairEq]

/-! ## `dedupPath` -/

theorem mem_dedupPath : ∀ (l : PathResult) (x : Term × Term), x ∈ dedupPath l → x ∈ l
  | [], x, h => by simp [dedupPath] at h
  | y :: ys, x, h => by
    unfold dedupPath at h
    split at h
    · exact List.mem_cons_of_mem _ (mem_dedupPath ys x h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupPath ys x h)

theorem dedupPath_nodup : ∀ (l : PathResult), (dedupPath l).Nodup
  | [] => by simp [dedupPath]
  | y :: ys => by
    unfold dedupPath
    split
    · exact dedupPath_nodup ys
    · rename_i hn
      refine List.nodup_cons.2 ⟨fun hm => hn ?_, dedupPath_nodup ys⟩
      exact List.any_eq_true.2 ⟨y, mem_dedupPath ys y hm, pathPairEq_refl y⟩

theorem mem_dedupPath_of : ∀ (l : PathResult), (∀ x ∈ l, PairFixed x) → ∀ x ∈ l, x ∈ dedupPath l
  | [], _, x, h => by simp at h
  | y :: ys, hf, x, h => by
    have hf' : ∀ z ∈ ys, PairFixed z := fun z hz => hf z (List.mem_cons_of_mem _ hz)
    unfold dedupPath
    split
    · rename_i hany
      rcases List.mem_cons.1 h with rfl | h
      · obtain ⟨z, hz, hxz⟩ := List.any_eq_true.1 hany
        have := pathPairEq_eq (hf x List.mem_cons_self) (hf' z hz) hxz
        subst this
        exact mem_dedupPath_of ys hf' x hz
      · exact mem_dedupPath_of ys hf' x h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupPath_of ys hf' x h)

/-- `dedupPath` of permuted lists of fixed pairs: a permutation. -/
theorem dedupPath_perm {l l' : PathResult} (h : l.Perm l') (hf : ∀ x ∈ l, PairFixed x) :
    (dedupPath l).Perm (dedupPath l') := by
  have hf' : ∀ x ∈ l', PairFixed x := fun x hx => hf x (h.mem_iff.2 hx)
  apply (List.perm_ext_iff_of_nodup (dedupPath_nodup l) (dedupPath_nodup l')).2
  intro x
  constructor
  · intro hx
    exact mem_dedupPath_of l' hf' x (h.mem_iff.1 (mem_dedupPath l x hx))
  · intro hx
    exact mem_dedupPath_of l hf x (h.mem_iff.2 (mem_dedupPath l' x hx))

/-! ## Property paths -/

theorem graphNodes_fixed (g : Graph) (hg : GraphFixed g) :
    ∀ n ∈ (g.map fun t => t.s.toTerm) ++ (g.map fun t => t.o), PairFixed (n, n) := by
  intro n hn
  rcases List.mem_append.1 hn with hn | hn
  · obtain ⟨t, _, rfl⟩ := List.mem_map.1 hn
    exact ⟨subject_fixed _, subject_fixed _⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
    exact ⟨hg t ht, hg t ht⟩

theorem mem_graphNodes (g : Graph) (n : Term) (h : n ∈ graphNodes g) :
    n ∈ (g.map fun t => t.s.toTerm) ++ (g.map fun t => t.o) := by
  unfold graphNodes at h
  obtain ⟨pr, hpr, rfl⟩ := List.mem_map.1 h
  have := mem_dedupPath _ _ hpr
  obtain ⟨n', hn', e⟩ := List.mem_map.1 this
  rw [← e]
  exact hn'

theorem graphNodes_perm {g g' : Graph} (h : g.Perm g') (hg : GraphFixed g) :
    (graphNodes g).Perm (graphNodes g') := by
  unfold graphNodes
  apply List.Perm.map
  apply dedupPath_perm
  · exact ((h.map _).append (h.map _)).map _
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
    exact graphNodes_fixed g hg n hn

theorem pathExtend_fixed (step cur : PathResult) (hs : ∀ x ∈ step, PairFixed x)
    (hc : ∀ x ∈ cur, PairFixed x) : ∀ x ∈ pathExtend step cur, PairFixed x := by
  intro x hx
  unfold pathExtend at hx
  rcases List.mem_append.1 (mem_dedupPath _ _ hx) with h | h
  · exact hc x h
  · obtain ⟨p1, hp1, h⟩ := List.mem_flatMap.1 h
    obtain ⟨p2, hp2, h⟩ := List.mem_filterMap.1 h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨(hc p1 hp1).1, (hs p2 hp2).2⟩
    · cases h

theorem pathFixpoint_fixed (step : PathResult) (hs : ∀ x ∈ step, PairFixed x) :
    ∀ (n : Nat) (cur : PathResult), (∀ x ∈ cur, PairFixed x) → ∀ x ∈ pathFixpoint step cur n, PairFixed x
  | 0, cur, hc => hc
  | n + 1, cur, hc => by
    unfold pathFixpoint
    dsimp only
    split
    · exact hc
    · exact pathFixpoint_fixed step hs n _ (pathExtend_fixed step cur hs hc)

theorem pathExtend_perm {step step' cur cur' : PathResult} (hs : step.Perm step') (hc : cur.Perm cur')
    (hsf : ∀ x ∈ step, PairFixed x) (hcf : ∀ x ∈ cur, PairFixed x) :
    (pathExtend step cur).Perm (pathExtend step' cur') := by
  unfold pathExtend
  apply dedupPath_perm
  · exact hc.append (perm_flatMap hc _ _ fun p1 _ => List.Perm.filterMap _ hs)
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hcf x h
    · obtain ⟨p1, hp1, h⟩ := List.mem_flatMap.1 h
      obtain ⟨p2, hp2, h⟩ := List.mem_filterMap.1 h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨(hcf p1 hp1).1, (hsf p2 hp2).2⟩
      · cases h

theorem pathFixpoint_perm {step step' : PathResult} (hs : step.Perm step') (hsf : ∀ x ∈ step, PairFixed x) :
    ∀ (n : Nat) {cur cur' : PathResult}, cur.Perm cur' → (∀ x ∈ cur, PairFixed x) →
      (pathFixpoint step cur n).Perm (pathFixpoint step' cur' n)
  | 0, _, _, hc, _ => hc
  | n + 1, cur, cur', hc, hcf => by
    have hn := pathExtend_perm hs hc hsf hcf
    unfold pathFixpoint
    dsimp only
    rw [hn.length_eq, hc.length_eq]
    split
    · exact hc
    · exact pathFixpoint_perm hs hsf n hn (pathExtend_fixed step cur hsf hcf)

/-- The pairs of a path over a graph of fixed terms are fixed. -/
theorem evalPath_fixed (g : Graph) (hg : GraphFixed g) :
    ∀ (path : PropertyPath), ∀ x ∈ evalPath path g, PairFixed x
  | .iri i, x, hx => by
    simp only [evalPath] at hx
    obtain ⟨t, ht, h⟩ := List.mem_filterMap.1 hx
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨subject_fixed _, hg t ht⟩
    · cases h
  | .inverse p, x, hx => by
    simp only [evalPath] at hx
    obtain ⟨pr, hpr, h⟩ := List.mem_map.1 hx
    subst h
    have := evalPath_fixed g hg p pr hpr
    exact ⟨this.2, this.1⟩
  | .sequence p1 p2, x, hx => by
    simp only [evalPath] at hx
    obtain ⟨a, ha, h⟩ := List.mem_flatMap.1 hx
    obtain ⟨b, hb, h⟩ := List.mem_filterMap.1 h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨(evalPath_fixed g hg p1 a ha).1, (evalPath_fixed g hg p2 b hb).2⟩
    · cases h
  | .alternative p1 p2, x, hx => by
    simp only [evalPath] at hx
    rcases List.mem_append.1 hx with h | h
    · exact evalPath_fixed g hg p1 x h
    · exact evalPath_fixed g hg p2 x h
  | .zeroOrOne p, x, hx => by
    simp only [evalPath] at hx
    rcases List.mem_append.1 (mem_dedupPath _ _ hx) with h | h
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 h
      exact graphNodes_fixed g hg n (mem_graphNodes g n hn)
    · exact evalPath_fixed g hg p x h
  | .zeroOrMore p, x, hx => by
    simp only [evalPath] at hx
    refine pathFixpoint_fixed _ (evalPath_fixed g hg p) _ _ ?_ x hx
    intro y hy
    rcases List.mem_append.1 (mem_dedupPath _ _ hy) with h | h
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 h
      exact graphNodes_fixed g hg n (mem_graphNodes g n hn)
    · exact evalPath_fixed g hg p y h
  | .oneOrMore p, x, hx => by
    simp only [evalPath] at hx
    refine pathFixpoint_fixed _ (evalPath_fixed g hg p) _ _ ?_ x hx
    intro y hy
    exact evalPath_fixed g hg p y (mem_dedupPath _ _ hy)
  | .negatedSet ps, x, hx => by
    simp only [evalPath] at hx
    rcases List.mem_append.1 hx with h | h
    · split at h
      · simp at h
      · obtain ⟨t, ht, h⟩ := List.mem_filterMap.1 h
        split at h
        · cases h
        · simp only [Option.some.injEq] at h; subst h; exact ⟨subject_fixed _, hg t ht⟩
    · split at h
      · simp at h
      · obtain ⟨t, ht, h⟩ := List.mem_filterMap.1 h
        split at h
        · cases h
        · simp only [Option.some.injEq] at h; subst h; exact ⟨hg t ht, subject_fixed _⟩

/-- The pairs of a path over a permuted graph of fixed terms: a
    permutation. -/
theorem evalPath_perm {g g' : Graph} (h : g.Perm g') (hg : GraphFixed g) :
    ∀ (path : PropertyPath), (evalPath path g).Perm (evalPath path g')
  | .iri i => by simp only [evalPath]; exact List.Perm.filterMap _ h
  | .inverse p => by simp only [evalPath]; exact List.Perm.map _ (evalPath_perm h hg p)
  | .sequence p1 p2 => by
    simp only [evalPath]
    exact perm_flatMap (evalPath_perm h hg p1) _ _ fun a _ => List.Perm.filterMap _ (evalPath_perm h hg p2)
  | .alternative p1 p2 => by
    simp only [evalPath]
    exact (evalPath_perm h hg p1).append (evalPath_perm h hg p2)
  | .zeroOrOne p => by
    simp only [evalPath]
    apply dedupPath_perm (((graphNodes_perm h hg).map _).append (evalPath_perm h hg p))
    intro y hy
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 h
      exact graphNodes_fixed g hg n (mem_graphNodes g n hn)
    · exact evalPath_fixed g hg p y h
  | .zeroOrMore p => by
    simp only [evalPath]
    rw [(graphNodes_perm h hg).length_eq]
    have hseed : ∀ y ∈ (graphNodes g).map (fun n => (n, n)) ++ evalPath p g, PairFixed y := by
      intro y hy
      rcases List.mem_append.1 hy with h | h
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 h
        exact graphNodes_fixed g hg n (mem_graphNodes g n hn)
      · exact evalPath_fixed g hg p y h
    exact pathFixpoint_perm (evalPath_perm h hg p) (evalPath_fixed g hg p) _
      (dedupPath_perm (((graphNodes_perm h hg).map _).append (evalPath_perm h hg p)) hseed)
      (fun y hy => hseed y (mem_dedupPath _ _ hy))
  | .oneOrMore p => by
    simp only [evalPath]
    rw [(graphNodes_perm h hg).length_eq]
    exact pathFixpoint_perm (evalPath_perm h hg p) (evalPath_fixed g hg p) _
      (dedupPath_perm (evalPath_perm h hg p) (evalPath_fixed g hg p))
      (fun y hy => evalPath_fixed g hg p y (mem_dedupPath _ _ hy))
  | .negatedSet ps => by
    simp only [evalPath]
    apply List.Perm.append
    · split
      · exact List.Perm.refl _
      · exact List.Perm.filterMap _ h
    · split
      · exact List.Perm.refl _
      · exact List.Perm.filterMap _ h

/-! ## The leaves of `Allowed` -/

theorem addConstantReflexivity_perm (s : PatternSubject) (o : PatternTerm) (path : PropertyPath)
    {P P' : PathResult} (h : P.Perm P') :
    (addConstantReflexivity s o path P).Perm (addConstantReflexivity s o path P') := by
  have hmiss : ∀ (Q Q' : PathResult), Q.Perm Q' →
      ((pathPatternConstants s o).filter fun t => !Q.any fun pr => pr.1.eqb t && pr.2.eqb t) =
        ((pathPatternConstants s o).filter fun t => !Q'.any fun pr => pr.1.eqb t && pr.2.eqb t) := by
    intro Q Q' hq
    congr 1
    funext t
    rw [hq.any_eq]
  cases path <;> simp only [addConstantReflexivity] <;>
    first
    | exact h
    | (rw [hmiss P P' h]; exact h.append (List.Perm.refl _))

theorem refSol_bgp_perm (env : EvalEnv) (ds ds' : Dataset) (b : Bgp) (hf : bgpHasFulltext b = false)
    {a a' : Graph} (h : a.Perm a') : SolEquiv (refSol env ds' (.bgp b) a') (refSol env ds (.bgp b) a) := by
  rw [IdLeaf.refSol_bgp env ds' b a' hf, IdLeaf.refSol_bgp env ds b a hf]
  exact SolEquiv.of_perm (evalBgp_perm h b).symm

theorem refSol_path_perm (env : EvalEnv) (ds ds' : Dataset) (s : PatternSubject) (path : PropertyPath)
    (o : PatternTerm) {a a' : Graph} (h : a.Perm a') (hg : GraphFixed a) :
    SolEquiv (refSol env ds' (.propertyPath s path o) a') (refSol env ds (.propertyPath s path o) a) := by
  rw [IdLeaf.refSol_path env ds' s path o a', IdLeaf.refSol_path env ds s path o a]
  unfold pathResultToSolutions
  exact SolEquiv.of_perm (List.Perm.filterMap _ (addConstantReflexivity_perm s o path
    (evalPath_perm h hg path))).symm

/-! ## Conditions with no EXISTS do not read the active graph -/

theorem filterFn_agree {env env' : EvalEnv} (he : ExprLocalTheorems.EnvAgree env env') (c : Expr)
    (hc : c.existsFree = true) (a a' : Graph) : filterFn env c a = filterFn env' c a' := by
  funext row
  unfold filterFn
  simp only [IdPostTheorems.substituteExistentials_existsFree _ _ _ c hc, ExprLocalTheorems.evalIn_agree he]

theorem binderFn_agree {env env' : EvalEnv} (he : ExprLocalTheorems.EnvAgree env env') (e : Expr)
    (hx : e.existsFree = true) (a : Graph) : binderFn env e a = binderFn env' e a := by
  funext row
  unfold binderFn
  simp only [IdPostTheorems.substituteExistentials_existsFree _ _ _ e hx, ExprLocalTheorems.evalIn_agree he]

theorem binderFn_active (env : EvalEnv) (e : Expr) (hx : e.existsFree = true) (a a' : Graph) :
    binderFn env e a = binderFn env e a' := by
  funext row
  unfold binderFn
  simp only [IdPostTheorems.substituteExistentials_existsFree _ _ _ e hx]

theorem bindRowsFresh_congr (binder binder' : Graph → Binding → Option Term) (a a' : Graph) (v : VarName)
    (h : binder a = binder' a') : ∀ (A : SolutionSeq) (i : Nat),
      bindRowsFresh binder a v A i = bindRowsFresh binder' a' v A i
  | [], _ => rfl
  | mu :: rest, i => by
    simp only [bindRowsFresh, h, bindRowsFresh_congr binder binder' a a' v h rest (i + 1)]

/-! ## The patterns covered -/

/-- The patterns of `allowed_perm`: no full-text basic graph pattern, no
    EXISTS in a FILTER, OPTIONAL or BIND condition or outside the WHERE
    clause of a sub-SELECT, no LATERAL and no SERVICE. -/
inductive PermOk : QueryPattern → Prop
  | bgp {b : Bgp} : bgpHasFulltext b = false → PermOk (.bgp b)
  | path {s : PatternSubject} {path : PropertyPath} {o : PatternTerm} : PermOk (.propertyPath s path o)
  | join {l r : QueryPattern} : PermOk l → PermOk r → PermOk (.join l r)
  | leftJoin {l r : QueryPattern} {c : Expr} : PermOk l → PermOk r → c.existsFree = true →
      PermOk (.leftJoin l r c)
  | filter {c : Expr} {q : QueryPattern} : PermOk q → c.existsFree = true → PermOk (.filter c q)
  | union {l r : QueryPattern} : PermOk l → PermOk r → PermOk (.union l r)
  | minus {l r : QueryPattern} : PermOk l → PermOk r → PermOk (.minus l r)
  | graph {n : PatternTerm} {q : QueryPattern} : PermOk q → PermOk (.graph n q)
  | bind {e : Expr} {v : VarName} {q : QueryPattern} : PermOk q → e.existsFree = true → PermOk (.bind e v q)
  | values {vars : List VarName} {rows : List (List (Option Term))} : PermOk (.values vars rows)
  | subSelect {form : QueryForm} {dcs : List DatasetClause} {inner : QueryPattern}
      {gb : Option (List GroupCondition)} {hv : List Expr} {md : SolutionModifier}
      {pv : Option (List Binding)} {bs : Option String} :
      (Query.mk form dcs inner gb hv md pv bs).expressionsOutsidePatternExistsFree = true → PermOk inner →
        PermOk (.subSelect (.mk form dcs inner gb hv md pv bs))
  | empty : PermOk .empty

/-! ## Named graphs -/

/-- `ds'` has the named graphs of `ds`: the same names, distinct in both,
    and the graphs of one name are permutations of each other; the graphs
    of `ds` are `GraphFixed`. -/
structure NamedPerm (ds ds' : Dataset) : Prop where
  names : (ds.named.map (·.name)).Nodup
  names' : (ds'.named.map (·.name)).Nodup
  same : ∀ n, (∃ ng ∈ ds.named, ng.name = n) ↔ (∃ ng' ∈ ds'.named, ng'.name = n)
  graphs : ∀ ng ∈ ds.named, ∀ ng' ∈ ds'.named, ng.name = ng'.name → ng.graph.Perm ng'.graph
  fixed : ∀ ng ∈ ds.named, GraphFixed ng.graph

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rw [List.map_cons, List.nodup_cons] at h
    refine List.nodup_cons.2 ⟨fun hx => h.1 (List.mem_map_of_mem hx), nodup_of_map f h.2⟩

theorem nodup_map_of_inj {α β : Type} (f : α → β) : ∀ {l : List α},
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hi, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_of_inj f (fun a ha b hb => hi a (List.mem_cons_of_mem _ ha) b
      (List.mem_cons_of_mem _ hb)) h.2⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
    exact h.1 (hi y (List.mem_cons_of_mem _ hy) x List.mem_cons_self e ▸ hy)

theorem eq_of_name {l : List NamedGraph} (h : (l.map (·.name)).Nodup) :
    ∀ {a b : NamedGraph}, a ∈ l → b ∈ l → a.name = b.name → a = b := by
  induction l with
  | nil => intro a b ha; simp at ha
  | cons x xs ih =>
    intro a b ha hb hn
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with ea | ha' <;> rcases List.mem_cons.1 hb with eb | hb'
    · rw [ea, eb]
    · subst ea
      exact absurd (hn ▸ List.mem_map_of_mem (f := NamedGraph.name) hb') h.1
    · subst eb
      exact absurd (hn.symm ▸ List.mem_map_of_mem (f := NamedGraph.name) ha') h.1
    · exact ih h.2 ha' hb' hn

theorem lookupNamed_some (ds : Dataset) (n : Subject) (g : Graph) (h : ds.lookupNamed n = some g) :
    ∃ ng ∈ ds.named, ng.name = n ∧ ng.graph = g := by
  unfold Dataset.lookupNamed at h
  split at h
  · rename_i ng hf
    simp only [Option.some.injEq] at h
    exact ⟨ng, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf, h⟩
  · cases h

theorem lookupNamed_of (ds : Dataset) (hn : (ds.named.map (·.name)).Nodup) (ng : NamedGraph)
    (hm : ng ∈ ds.named) : ds.lookupNamed ng.name = some ng.graph := by
  unfold Dataset.lookupNamed
  cases hf : ds.named.find? (fun x => x.name == ng.name) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 hf ng hm
    simp at this
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hxn : x.name = ng.name := by simpa using List.find?_some hf
    rw [eq_of_name hn hx hm hxn]

theorem lookupNamedIri_some (ds : Dataset) (i : Iri) (g : Graph) (h : ds.lookupNamedIri i = some g) :
    ∃ (hi : isIri i = true), ∃ ng ∈ ds.named, ng.name = .iri ⟨i, hi⟩ ∧ ng.graph = g := by
  unfold Dataset.lookupNamedIri at h
  split at h
  · rename_i hi
    exact ⟨hi, lookupNamed_some ds _ g h⟩
  · cases h

theorem lookupNamedIri_of (ds : Dataset) (hn : (ds.named.map (·.name)).Nodup) (i : Iri) (hi : isIri i = true)
    (ng : NamedGraph) (hm : ng ∈ ds.named) (hname : ng.name = .iri ⟨i, hi⟩) :
    ds.lookupNamedIri i = some ng.graph := by
  unfold Dataset.lookupNamedIri
  rw [dif_pos hi, ← hname]
  exact lookupNamed_of ds hn ng hm

section named
variable {ds ds' : Dataset} (hd : NamedPerm ds ds')
include hd

theorem NamedPerm.fwd (ng : NamedGraph) (hm : ng ∈ ds.named) :
    ∃ ng' ∈ ds'.named, ng'.name = ng.name ∧ ng.graph.Perm ng'.graph := by
  obtain ⟨ng', hm', hn⟩ := (hd.same ng.name).1 ⟨ng, hm, rfl⟩
  exact ⟨ng', hm', hn, hd.graphs ng hm ng' hm' hn.symm⟩

theorem NamedPerm.bwd (ng' : NamedGraph) (hm : ng' ∈ ds'.named) :
    ∃ ng ∈ ds.named, ng.name = ng'.name ∧ ng.graph.Perm ng'.graph := by
  obtain ⟨ng, hm1, hn⟩ := (hd.same ng'.name).2 ⟨ng', hm, rfl⟩
  exact ⟨ng, hm1, hn, hd.graphs ng hm1 ng' hm hn⟩

theorem NamedPerm.lookup_some (i : Iri) (g : Graph) (h : ds.lookupNamedIri i = some g) :
    ∃ g', ds'.lookupNamedIri i = some g' ∧ g.Perm g' ∧ GraphFixed g := by
  obtain ⟨hi, ng, hm, hname, rfl⟩ := lookupNamedIri_some ds i g h
  obtain ⟨ng', hm', hn', hp⟩ := hd.fwd ng hm
  exact ⟨ng'.graph, lookupNamedIri_of ds' hd.names' i hi ng' hm' (hn'.trans hname), hp, hd.fixed ng hm⟩

theorem NamedPerm.lookup_none (i : Iri) (h : ds.lookupNamedIri i = none) : ds'.lookupNamedIri i = none := by
  cases h' : ds'.lookupNamedIri i with
  | none => rfl
  | some g' =>
    exfalso
    obtain ⟨hi, ng', hm', hname, _⟩ := lookupNamedIri_some ds' i g' h'
    obtain ⟨ng, hm, hn, _⟩ := hd.bwd ng' hm'
    rw [lookupNamedIri_of ds hd.names i hi ng hm (hn.trans hname)] at h
    cases h

end named

/-! ## The theorem -/

/-- **`Allowed` does not depend on the order of the triples of a graph.**
    An answer that SPARQL 1.1 allows for `p` in the active graph `a` over the
    named graphs of `ds` is also allowed in a permutation `a'` of `a` over
    the named graphs of `ds'`, for a pattern of `PermOk` and graphs whose
    objects are their own join keys. -/
theorem allowed_perm {env env' : EvalEnv} (he : ExprLocalTheorems.EnvAgree env env') {ds ds' : Dataset}
    (hd : NamedPerm ds ds') :
    ∀ {p : QueryPattern} {a : Graph} {A : SolutionSeq}, Allowed env ds p a A →
      ∀ {a' : Graph}, a.Perm a' → GraphFixed a → PermOk p → Allowed env' ds' p a' A := by
  intro p a A hA
  induction hA with
  | bgp b a =>
    intro a' h _ hok
    cases hok with
    | bgp hf => exact .equiv (.bgp b a') (refSol_bgp_perm env ds ds' b hf h)
  | path s path o a =>
    intro a' h hg _
    exact .equiv (.path s path o a') (refSol_path_perm env ds ds' s path o h hg)
  | join _ _ ihl ihr =>
    intro a' h hg hok
    cases hok with
    | join hl hr => exact .join (ihl h hg hl) (ihr h hg hr)
  | @leftJoin l r c a A B _ _ ihl ihr =>
    intro a' h hg hok
    cases hok with
    | leftJoin hl hr hc =>
      rw [filterFn_agree he c hc a a']
      exact .leftJoin (ihl h hg hl) (ihr h hg hr)
  | @filter c q a A _ ih =>
    intro a' h hg hok
    cases hok with
    | filter hq hc =>
      rw [filterFn_agree he c hc a a']
      exact .filter (ih h hg hq)
  | union _ _ ihl ihr =>
    intro a' h hg hok
    cases hok with
    | union hl hr => exact .union (ihl h hg hl) (ihr h hg hr)
  | minus _ _ ihl ihr =>
    intro a' h hg hok
    cases hok with
    | minus hl hr => exact .minus (ihl h hg hl) (ihr h hg hr)
  | @graphIri i q a g A hg _ ih =>
    intro a' _ _ hok
    cases hok with
    | graph hq =>
      obtain ⟨g', hg', hp, hf⟩ := hd.lookup_some i.val g hg
      exact .graphIri hg' (ih hp hf hq)
  | @graphIriNone i q a hg =>
    intro a' _ _ _
    exact .graphIriNone (hd.lookup_none i.val hg)
  | @graphVar v q a F _ ih =>
    intro a' _ _ hok
    cases hok with
    | graph hq =>
      -- the answers of the named graphs of `ds'`: those of the graph of `ds`
      -- with the same name
      let F' : NamedGraph → SolutionSeq := fun ng' =>
        match ds.named.find? (fun ng => ng.name == ng'.name) with
        | some ng => F ng
        | none => []
      have hF' : ∀ ng ∈ ds.named, ∀ ng' ∈ ds'.named, ng.name = ng'.name → F' ng' = F ng := by
        intro ng hm ng' _ hn
        simp only [F']
        cases hf : ds.named.find? (fun x => x.name == ng'.name) with
        | none =>
          have := List.find?_eq_none.1 hf ng hm
          simp [hn] at this
        | some x =>
          have hx := List.mem_of_find?_eq_some hf
          have hxn : x.name = ng'.name := by simpa using List.find?_some hf
          rw [eq_of_name hd.names hx hm (hxn.trans hn.symm)]
      have hall : ∀ ng' ∈ ds'.named, Allowed env' ds' q ng'.graph (F' ng') := by
        intro ng' hm'
        obtain ⟨ng, hm, hn, hp⟩ := hd.bwd ng' hm'
        rw [hF' ng hm ng' hm' hn]
        exact ih ng hm hp (hd.fixed ng hm) hq
      refine .equiv (.graphVar F' hall) (SolEquiv.of_perm ?_)
      -- the graph of `ds'` with the name of a graph of `ds`
      let σ : NamedGraph → NamedGraph := fun ng =>
        (ds'.named.find? (fun ng' => ng'.name == ng.name)).getD ng
      have hσ : ∀ ng ∈ ds.named, σ ng ∈ ds'.named ∧ (σ ng).name = ng.name := by
        intro ng hm
        obtain ⟨ng', hm', hn, _⟩ := hd.fwd ng hm
        simp only [σ]
        cases hf : ds'.named.find? (fun x => x.name == ng.name) with
        | none =>
          have := List.find?_eq_none.1 hf ng' hm'
          simp [hn] at this
        | some x =>
          exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
      have hnd' : ds'.named.Nodup := nodup_of_map _ hd.names'
      have hndσ : (ds.named.map σ).Nodup := by
        refine nodup_map_of_inj σ ?_ (nodup_of_map _ hd.names)
        intro x hx y hy he
        have e : x.name = y.name := by rw [← (hσ x hx).2, ← (hσ y hy).2, he]
        exact eq_of_name hd.names hx hy e
      have hpσ : (ds.named.map σ).Perm ds'.named := by
        apply (List.perm_ext_iff_of_nodup hndσ hnd').2
        intro y
        constructor
        · intro hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          exact (hσ x hx).1
        · intro hy
          obtain ⟨x, hx, hn, _⟩ := hd.bwd y hy
          refine List.mem_map.2 ⟨x, hx, ?_⟩
          exact eq_of_name hd.names' (hσ x hx).1 hy ((hσ x hx).2.trans hn)
      refine List.Perm.trans (List.Perm.flatMap_right _ hpσ.symm) ?_
      rw [List.flatMap_map]
      apply List.Perm.of_eq
      apply flatMap_congr_mem
      intro ng hm
      rw [(hσ ng hm).2, hF' ng hm (σ ng) (hσ ng hm).1 (hσ ng hm).2.symm]
  | graphBnode _ ih =>
    intro a' h hg hok
    cases hok with
    | graph hq => exact .graphBnode (ih h hg hq)
  | graphLiteral _ ih =>
    intro a' h hg hok
    cases hok with
    | graph hq => exact .graphLiteral (ih h hg hq)
  | graphTriple _ ih =>
    intro a' h hg hok
    cases hok with
    | graph hq => exact .graphTriple (ih h hg hq)
  | @bind e v q a A _ ih =>
    intro a' h hg hok
    cases hok with
    | bind hq he' =>
      rw [bindRowsFresh_congr (binderFn env e) (binderFn env' e) a a' v
        ((binderFn_active env e he' a a').trans (binderFn_agree he e he' a')) A 0]
      exact .bind (ih h hg hq)
  | values vars rows a =>
    intro a' _ _ _
    exact .values vars rows a'
  | @subSelect form dcs inner gb hv md pv bs a A _ ih =>
    intro a' h hg hok
    cases hok with
    | subSelect hq hi =>
      rw [SubSelect.selectPost_agree he a a' _ hq A]
      exact .subSelect (ih h hg hi)
  | empty a =>
    intro a' _ _ _
    exact .empty a'
  | equiv _ hs ih =>
    intro a' h hg hok
    exact .equiv (ih h hg hok) hs

end L4Factoidal.Storage.Sbm11.AllowedPerm
