/-
L4Factoidal.Storage.Sbm11.IdGroupTheorems — nested group graph patterns on
the SBM11 id path (https://github.com/danbri/factoidal/issues/959, parent
https://github.com/danbri/factoidal/issues/775).

`IdQuery.translate` accepts WHERE clauses of fixed top-level shapes. A WHERE
clause outside them (a nested OPTIONAL, a UNION inside GRAPH, a MINUS whose
right side is a group, a sub-SELECT, ...) is evaluated by the recursive
evaluator `IdQuery.evalGroupM`, which follows the pattern the parser builds
(`QueryPattern`, the SPARQL 1.1 section 18.2 translation) node by node. This
file states that evaluator over rows of ids (`OptJoinTheorems.IdRow`) and
proves it equal to the reference evaluator.

## The evaluator over rows of ids

`evalGroupIds` recurses on the `QueryPattern` structurally. Each arm is the
id form of the arm of `QueryPattern.lowerWith env Binding.empty` followed by
`GraphPattern.evalIn` (SPARQL 1.1 sections 18.5 and 18.6):

| pattern                 | rows of ids                                         |
|-------------------------|-----------------------------------------------------|
| BGP, property path      | the scans (`Leaves`)                                |
| Join(P1, P2)            | `IdJoin.idJoin` (`join_decode`)                     |
| LeftJoin(P1, P2, e)     | `idLeftJoinC`: the merges that pass `e` (`leftJoinC_decode`) |
| Filter(e, P)            | the rows that pass `e`                              |
| Union(P1, P2)           | concatenation (`IdJoin.union_decode`)               |
| Minus(P1, P2)           | `IdMinus.idMinus` (`minus_decode`)                  |
| Graph(<iri>, P)         | `P` in the named graph, or no row                   |
| Graph(?g, P)            | per named graph, `P` in it, `?g` bound (`idBindG`)  |
| Extend(P, ?v, e)        | `IdBind.idExtendRows` (`extendAt_decode`)           |
| VALUES                  | `IdJoin.idValues` (`values_decode`)                 |
| sub-SELECT              | the reference post-processing, values re-encoded    |
| {}                      | one row with no binding                             |

FILTER, the LeftJoin condition and the BIND expression are the reference's
own functions (the closures `lowerWith` builds), applied to the decoded row.

## The theorem (in `IdAllowedTheorems`)

`IdAllowedTheorems.evalGroupIds_allowed`: for every pattern `p` with
`InIdFragment p` (every constructor but LATERAL, SERVICE and SERVICE ?v, at
any depth of nesting), the rows of `evalGroupIds` decode to an answer that
SPARQL 1.1 allows for `p` (`Allowed`: the reference evaluator's functions
over some order of each intermediate multiset), and every id they hold
satisfies `ok`. Until 2026-10-23 this file stated list equality with the
reference (`evalGroupIds_decode`) under a hypothesis that each leaf's rows
decode to the reference leaf as a list; the id path's scans do not give
that list (issue 776: permutation key order, join order, hash-join probe
side), and for a leaf that statement was its own hypothesis. The
operator lemmas below are the steps of the new theorem; its leaf hypothesis
(`LeafRel`: each leaf's rows decode to the same multiset of solution
mappings as the reference leaf) is open there.

Not proved here (the step of lemma L5g″ of the design record): that the
`Table` operators `IdQuery.evalGroupM` runs (`IdJoin.joinIds`,
`IdQuery.leftJoinCondM`, `IdJoin.unionIds`, `IdQuery.semiMatches`,
`IdQuery.extendM`, `IdQuery.applyFilters`) denote these list operators.
Tested by the gate queries `tests/sbm11/gate/ids-nest-*.rq` and the W3C
census (`tests/sbm11/census.sh`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdMinusTheorems
import L4Factoidal.Storage.Sbm11.IdBindTheorems
import L4Factoidal.Storage.Sbm11.IdJoinTheorems
import L4Factoidal.SPARQL.IndexedEvalRefinement

namespace L4Factoidal.Storage.Sbm11.IdGroup

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge decRow RowIds
  compatible_decRow merge_decRow lookup_decRow idLookup_mem filterMap_congr')
open L4Factoidal.Storage.Sbm11.IdJoin (idJoin idZip idValues join_decode values_decode union_decode)
open L4Factoidal.Storage.Sbm11.IdMinus (idMinus minus_decode)
open L4Factoidal.Storage.Sbm11.IdBind (idExtendRows)

/-! ## The operators over rows of ids -/

/-- LeftJoin(Ω1, Ω2, expr) over ids (SPARQL 1.1 section 18.5, `leftJoin`):
    per left row, the merges with the compatible right rows that pass
    `cond`, in order, else the left row. -/
def idLeftJoinC (cond : IdRow → Bool) (L R : List IdRow) : List IdRow :=
  L.flatMap fun r1 =>
    let ext := R.filterMap fun r2 =>
      if idCompatible r1 r2 then
        if cond (idMerge r1 r2) then some (idMerge r1 r2) else none
      else none
    if ext.isEmpty then [r1] else ext

/-- `Binding.bindIfCompatible` over ids: bind `v` to `x` unless the row binds
    it to another id. -/
def idBindG (v : String) (x : UInt64) (r : IdRow) : Option IdRow :=
  match idLookup v r with
  | some y => if y == x then some r else none
  | none => some ((v, x) :: r)

/-- A solution mapping encoded: each term by `idv`. -/
def encRow (idv : Term → UInt64) (mu : Binding) : IdRow := mu.map fun (v, t) => (v, idv t)

/-- The FILTER and LeftJoin condition `QueryPattern.lowerWith env
    Binding.empty` builds for `c`. -/
def filterFn (env : EvalEnv) (c : Expr) : Graph → Binding → Bool := fun active row =>
  let mu' := Binding.empty.merge row
  ebvOrFalse (Expr.evalIn env mu' (substituteExistentials env active mu' c))

/-- The BIND binder `QueryPattern.lowerWith env Binding.empty` builds for
    `e`. -/
def binderFn (env : EvalEnv) (e : Expr) : Graph → Binding → Option Term := fun active row =>
  let mu' := Binding.empty.merge row
  (Expr.evalIn env mu' (substituteExistentials env active mu' e)).toTerm?

/-- The scans at the leaves: the rows of ids of a basic graph pattern and of a
    property path pattern in an active graph. -/
structure Leaves where
  bgp : Graph → Bgp → List IdRow
  path : Graph → PatternSubject → PropertyPath → PatternTerm → List IdRow

/-! ## The evaluator -/

/-- The solutions of a group graph pattern over rows of ids, in the active
    graph `active` (module header). `dec` decodes an id (the store's
    `termOf`), `idv` encodes a term (`Store.idOf`, else a query-local id). -/
def evalGroupIds (env : EvalEnv) (ds : Dataset) (σ : Leaves) (dec : UInt64 → Term)
    (idv : Term → UInt64) : QueryPattern → Graph → List IdRow
  | .bgp b, a => σ.bgp a b
  | .join l r, a => idJoin (evalGroupIds env ds σ dec idv l a) (evalGroupIds env ds σ dec idv r a)
  | .leftJoin l r c, a =>
    idLeftJoinC (fun m => filterFn env c a (decRow dec m))
      (evalGroupIds env ds σ dec idv l a) (evalGroupIds env ds σ dec idv r a)
  | .filter c q, a => (evalGroupIds env ds σ dec idv q a).filter fun r => filterFn env c a (decRow dec r)
  | .union l r, a => evalGroupIds env ds σ dec idv l a ++ evalGroupIds env ds σ dec idv r a
  | .minus l r, a => idMinus (evalGroupIds env ds σ dec idv l a) (evalGroupIds env ds σ dec idv r a)
  | .graph (.iri i) q, _ =>
    match ds.lookupNamedIri i.val with
    | some g => evalGroupIds env ds σ dec idv q g
    | none => []
  | .graph (.var v) q, _ =>
    ds.named.flatMap fun ng =>
      (evalGroupIds env ds σ dec idv q ng.graph).filterMap (idBindG v (idv ng.name.toTerm))
  | .graph (.bnode _) q, a => evalGroupIds env ds σ dec idv q a
  | .graph (.literal _) q, a => evalGroupIds env ds σ dec idv q a
  | .graph (.tripleTerm _ _ _) q, a => evalGroupIds env ds σ dec idv q a
  | .bind e v q, a =>
    idExtendRows (fun r j => (binderFn env e a ((decRow dec r).withFreshnessCtx (toString j) v)).map idv)
      v (evalGroupIds env ds σ dec idv q a) 0
  | .values vars rows, _ => idValues vars (rows.map fun row => row.map (·.map idv))
  | .subSelect (.mk form dcs inner gb hv md pv bs), a =>
    (selectPost env a (.mk form dcs inner gb hv md pv bs)
      ((evalGroupIds env ds σ dec idv inner a).map (decRow dec))).map (encRow idv)
  | .propertyPath s path o, a => σ.path a s path o
  | .empty, _ => [[]]
  | .lateral _ _, _ => []
  | .service _ _ _, _ => []
  | .serviceVar _ _ _, _ => []

/-- The fragment: every constructor but LATERAL, SERVICE and SERVICE ?v, at
    any depth. -/
def InIdFragment : QueryPattern → Prop
  | .bgp _ | .values _ _ | .propertyPath _ _ _ | .empty => True
  | .join l r | .leftJoin l r _ | .union l r | .minus l r => InIdFragment l ∧ InIdFragment r
  | .filter _ q | .bind _ _ q | .graph _ q => InIdFragment q
  | .subSelect (.mk _ _ inner _ _ _ _ _) => InIdFragment inner
  | .lateral _ _ | .service _ _ _ | .serviceVar _ _ _ => False

/-- A term the evaluator encodes gets an id in `ok` that decodes to it. -/
def TermOk (dec : UInt64 → Term) (ok : UInt64 → Prop) (idv : Term → UInt64) (t : Term) : Prop :=
  ok (idv t) ∧ dec (idv t) = t

/-! ## Lemmas on the operators -/

theorem rowIds_idMerge (ok : UInt64 → Prop) :
    ∀ (r2 r1 : IdRow), RowIds ok r1 → RowIds ok r2 → RowIds ok (idMerge r1 r2)
  | [], _, h1, _ => h1
  | (v, x) :: rest, r1, h1, h2 => by
    have hrest : RowIds ok rest := fun b hb => h2 b (List.mem_cons_of_mem _ hb)
    simp only [idMerge]
    cases idLookup v r1 with
    | some _ => exact rowIds_idMerge ok rest r1 h1 hrest
    | none =>
      apply rowIds_idMerge ok rest ((v, x) :: r1) _ hrest
      intro b hb
      rcases List.mem_cons.mp hb with e | e
      · subst e; exact h2 (v, x) (List.mem_cons_self ..)
      · exact h1 b e

theorem rowIds_idJoin (ok : UInt64 → Prop) (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r)
    (hR : ∀ r ∈ R, RowIds ok r) : ∀ r ∈ idJoin L R, RowIds ok r := by
  intro r hr
  unfold idJoin at hr
  simp only [List.mem_flatMap, List.mem_filterMap] at hr
  obtain ⟨r1, h1, r2, h2, e⟩ := hr
  by_cases hc : idCompatible r1 r2 = true
  · rw [if_pos hc] at e
    cases e
    exact rowIds_idMerge ok r2 r1 (hL r1 h1) (hR r2 h2)
  · rw [if_neg hc] at e
    cases e

/-- Decoding `idLeftJoinC` gives SPARQL 1.1 LeftJoin(Ω1, Ω2, cond) of the
    decoded rows, row for row, when the id condition is `cond` on the
    decoded merge. -/
theorem leftJoinC_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (cond : Binding → Bool)
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    (idLeftJoinC (fun m => cond (decRow dec m)) L R).map (decRow dec) =
      leftJoin (L.map (decRow dec)) (R.map (decRow dec)) cond := by
  unfold idLeftJoinC leftJoin
  rw [List.map_flatMap, List.flatMap_map]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro r1 h1
  rw [List.filterMap_map]
  have hfm : (R.filterMap fun r2 => if idCompatible r1 r2 then
        (if cond (decRow dec (idMerge r1 r2)) then some (idMerge r1 r2) else none) else none).map (decRow dec) =
      R.filterMap ((fun mu2 => if Binding.compatible (decRow dec r1) mu2 then
          (if cond (Binding.merge (decRow dec r1) mu2) then some (Binding.merge (decRow dec r1) mu2) else none)
        else none) ∘ decRow dec) := by
    rw [List.map_filterMap]
    apply filterMap_congr'
    intro r2 h2
    simp only [Function.comp_def]
    rw [compatible_decRow dec ok hdec r1 r2 (hL r1 h1) (hR r2 h2), merge_decRow]
    cases idCompatible r1 r2 <;> simp only [Bool.false_eq_true, if_false, if_true, Option.map_none]
    cases cond (decRow dec (idMerge r1 r2)) <;> simp
  rw [← hfm]
  cases (R.filterMap fun r2 => if idCompatible r1 r2 = true then
      (if cond (decRow dec (idMerge r1 r2)) = true then some (idMerge r1 r2) else none) else none) <;> simp

theorem rowIds_idLeftJoinC (ok : UInt64 → Prop) (cond : IdRow → Bool) (L R : List IdRow)
    (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    ∀ r ∈ idLeftJoinC cond L R, RowIds ok r := by
  intro r hr
  unfold idLeftJoinC at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hext : ∀ x ∈ (R.filterMap fun r2 => if idCompatible r1 r2 then
      (if cond (idMerge r1 r2) then some (idMerge r1 r2) else none) else none), RowIds ok x := by
    intro x hx
    rw [List.mem_filterMap] at hx
    obtain ⟨r2, h2, e⟩ := hx
    by_cases hc : idCompatible r1 r2 = true
    · rw [if_pos hc] at e
      by_cases hk : cond (idMerge r1 r2) = true
      · rw [if_pos hk] at e
        cases e
        exact rowIds_idMerge ok r2 r1 (hL r1 h1) (hR r2 h2)
      · rw [if_neg hk] at e; cases e
    · rw [if_neg hc] at e; cases e
  dsimp only at hr
  split at hr
  · rw [List.mem_singleton] at hr
    rw [hr]
    exact hL r1 h1
  · exact hext r hr

theorem bindG_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (v : String) (x : UInt64) (hx : ok x)
    (r : IdRow) (hr : RowIds ok r) :
    (idBindG v x r).map (decRow dec) = (decRow dec r).bindIfCompatible v (dec x) := by
  unfold idBindG Binding.bindIfCompatible
  rw [lookup_decRow]
  cases hl : idLookup v r with
  | none => rfl
  | some y =>
    have hy : ok y := hr (v, y) (idLookup_mem hl)
    simp only [Option.map_some]
    rw [hdec y x hy hx]
    cases y == x <;> rfl

theorem rowIds_idBindG (ok : UInt64 → Prop) (v : String) (x : UInt64) (hx : ok x) (r r' : IdRow)
    (hr : RowIds ok r) (h : idBindG v x r = some r') : RowIds ok r' := by
  unfold idBindG at h
  cases hl : idLookup v r with
  | some y =>
    rw [hl] at h
    simp only at h
    by_cases hyx : (y == x) = true
    · rw [if_pos hyx] at h; cases h; exact hr
    · rw [if_neg hyx] at h; cases h
  | none =>
    rw [hl] at h
    simp only [Option.some.injEq] at h
    subst h
    intro b hb
    rcases List.mem_cons.mp hb with e | e
    · subst e; exact hx
    · exact hr b e

/-- Extend over ids, decoded, is `bindRowsFresh` of the decoded rows, when
    each value the binder gives on these rows gets an id in `ok` that decodes
    back to it. -/
theorem extendAt_decode (dec : UInt64 → Term) (ok : UInt64 → Prop) (idv : Term → UInt64)
    (binder : Binding → Option Term) (bf : Graph → Binding → Option Term) (active : Graph)
    (hb : ∀ mu, bf active mu = binder mu) (v : String) :
    ∀ (L : List IdRow) (i : Nat),
      (∀ r ∈ L, RowIds ok r) →
      (∀ j (hj : j < L.length) (t : Term),
        binder ((decRow dec L[j]).withFreshnessCtx (toString (i + j)) v) = some t →
          TermOk dec ok idv t) →
      (idExtendRows (fun r j => (binder ((decRow dec r).withFreshnessCtx (toString j) v)).map idv)
          v L i).map (decRow dec) = bindRowsFresh bf active v (L.map (decRow dec)) i ∧
      ∀ r ∈ idExtendRows (fun r j => (binder ((decRow dec r).withFreshnessCtx (toString j) v)).map idv)
          v L i, RowIds ok r
  | [], _, _, _ => ⟨rfl, by intro r hr; cases hr⟩
  | r :: rest, i, hL, hT => by
    have hr : RowIds ok r := hL r (List.mem_cons_self ..)
    have hrest : ∀ x ∈ rest, RowIds ok x := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    have hT0 : ∀ t, binder ((decRow dec r).withFreshnessCtx (toString i) v) = some t → TermOk dec ok idv t := by
      intro t ht
      exact hT 0 (by simp) t (by simpa using ht)
    have hTr : ∀ j (hj : j < rest.length) (t : Term),
        binder ((decRow dec rest[j]).withFreshnessCtx (toString (i + 1 + j)) v) = some t →
          TermOk dec ok idv t := by
      intro j hj t ht
      have e : i + 1 + j = i + (j + 1) := by omega
      rw [e] at ht
      exact hT (j + 1) (by simp; omega) t (by simpa using ht)
    obtain ⟨ih1, ih2⟩ := extendAt_decode dec ok idv binder bf active hb v rest (i + 1) hrest hTr
    refine ⟨?_, ?_⟩
    · simp only [idExtendRows, List.map_cons, bindRowsFresh, hb]
      rw [ih1]
      congr 1
      cases hbv : binder ((decRow dec r).withFreshnessCtx (toString i) v) with
      | none => rfl
      | some t =>
        simp only [Option.map_some, lookup_decRow]
        cases hl : idLookup v r with
        | some _ => rfl
        | none => simp [decRow, Binding.bind, (hT0 t hbv).2]
    · intro x hx
      simp only [idExtendRows, List.mem_cons] at hx
      rcases hx with e | e
      · subst e
        cases hbv : binder ((decRow dec r).withFreshnessCtx (toString i) v) with
        | none => simpa [hbv] using hr
        | some t =>
          simp only [Option.map_some]
          cases hl : idLookup v r with
          | some _ => exact hr
          | none =>
            intro b hb'
            rcases List.mem_cons.mp hb' with e | e
            · subst e; exact (hT0 t hbv).1
            · exact hr b e
      · exact ih2 x e

theorem rowIds_idZip (ok : UInt64 → Prop) (idv : Term → UInt64) :
    ∀ (vars : List String) (row : List (Option Term)) (r : IdRow),
      (∀ t, some t ∈ row → ok (idv t)) → RowIds ok r → RowIds ok (idZip vars (row.map (·.map idv)) r)
  | [], row, r, _, hr => by cases row <;> exact hr
  | _ :: _, [], r, _, hr => hr
  | v :: vs, c :: cs, r, h, hr => by
    have hcs : ∀ t, some t ∈ cs → ok (idv t) := fun t ht => h t (List.mem_cons_of_mem _ ht)
    cases c with
    | none => exact rowIds_idZip ok idv vs cs r hcs hr
    | some t =>
      simp only [List.map_cons, Option.map_some, idZip]
      apply rowIds_idZip ok idv vs cs _ hcs
      intro b hb
      rcases List.mem_cons.mp hb with e | e
      · subst e; exact h t (List.mem_cons_self ..)
      · exact hr b e

theorem decRow_encRow (dec : UInt64 → Term) (idv : Term → UInt64) :
    ∀ (mu : Binding), (∀ p ∈ mu, dec (idv p.2) = p.2) → decRow dec (encRow idv mu) = mu
  | [], _ => rfl
  | (v, t) :: rest, h => by
    have ht : dec (idv t) = t := h (v, t) (List.mem_cons_self ..)
    have hrest := decRow_encRow dec idv rest fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [encRow, decRow, List.map_cons] at hrest ⊢
    rw [ht, hrest]

/-! ## The reference arms -/

theorem lowerBgp_ne_serviceVar (b : Bgp) (v : VarName) (res : Iri → Option Graph) (s : Bool)
    (q : GraphPattern) : lowerBgp b ≠ .serviceVar v res s q := by
  unfold lowerBgp
  split
  · have key : ∀ (xs : Bgp) (acc : GraphPattern), acc ≠ .serviceVar v res s q →
        xs.foldl (fun acc tp => match tp.fulltext? with
          | some ftq => GraphPattern.join acc (.modified (fun active _ => fulltextSolutions ftq tp.s active) .empty)
          | none => acc) acc ≠ .serviceVar v res s q := by
      intro xs
      induction xs with
      | nil => intro acc h; exact h
      | cons tp rest ih =>
        intro acc h
        rw [List.foldl_cons]
        apply ih
        split
        · intro e; cases e
        · exact h
    exact key b _ (by intro e; cases e)
  · intro e; cases e

theorem lower_ne_serviceVar (env : EvalEnv) (p : QueryPattern) (hp : InIdFragment p)
    (v : VarName) (res : Iri → Option Graph) (s : Bool) (q : GraphPattern) :
    QueryPattern.lowerWith env Binding.empty p ≠ .serviceVar v res s q := by
  cases p with
  | bgp b => simp only [QueryPattern.lowerWith]; exact lowerBgp_ne_serviceVar _ v res s q
  | filter c q' =>
    simp only [QueryPattern.lowerWith, filterLowered]
    split <;> (intro e; cases e)
  | lateral _ _ => exact absurd hp id
  | service _ _ _ => exact absurd hp id
  | serviceVar _ _ _ => exact absurd hp id
  | subSelect sq =>
    intro e
    rw [QueryPattern.lowerWith.eq_def] at e
    cases e
  | _ => intro e; rw [QueryPattern.lowerWith] at e; cases e

theorem evalIn_join (ds : Dataset) (a : Graph) (l r : GraphPattern)
    (hl : ∀ v res s q, l ≠ .serviceVar v res s q) (hr : ∀ v res s q, r ≠ .serviceVar v res s q) :
    (GraphPattern.join l r).evalIn ds a = hashJoin (l.evalIn ds a) (r.evalIn ds a) := by
  rw [GraphPattern.evalIn]
  · intro v res s q h; exact hr v res s q h
  · intro v res s q h; exact hl v res s q h

end L4Factoidal.Storage.Sbm11.IdGroup
