/-
L4Factoidal.Storage.Sbm11.GraphBgpTableTheorems — `GRAPH ?g` over a basic
graph pattern as the nested evaluator runs it: one scan per triple pattern
with the graph as a column (https://github.com/danbri/factoidal/issues/776;
lemma L4u of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`IdGroup.bgpGraphVarM` resolves each triple pattern with the graph slot the
variable `?g` over the named graphs (`Pat.named`) and runs `IdQuery.evalBgpM`
on them: each scan keeps the rows of every named graph (graph id not 0) and
binds `?g` to the graph id, and the joins compare `?g` like any variable.

* `named_rows_perm`, `named_scanStore`: over a store whose rows with a
  graph id other than 0 are in the graphs `G` (distinct, none 0), the matches
  of one permutation's rows (`ScanTableTheorems.rowM`) are a permutation of
  `gS v G L t`: per graph `x` of `G`, the pattern's matches in the listing
  `L x` of that graph from the mapping `{?g ↦ x}` (`perm_keys`: a list is a
  permutation of its parts per key). This is the `BgpTableTheorems.ScanStore`
  of the named graphs.
* `join_graph`, `joinL_graph`, `joinL_graph_top`: the joins of the loop
  (`BgpTableTheorems.joinL`) of such scans are, up to order, per graph `x`
  the sequential evaluation of the patterns in `L x` from `{?g ↦ x}`: a row
  that binds `?g` to `x` joins no row of another graph (`seed_other`), and
  with a row of the same graph the join is one step of the evaluation
  (`seed_join`, from `IdLeaf.matchSlots_merge`).
* `seed_bgp`, `seed_top`: the evaluation from `{?g ↦ x}` is the evaluation
  from `{}` with `?g` then bound to `x` (`IdGroup.idBindG`), up to order
  (`bind_last`: matching `?g` first or last gives the same mapping).
* `bgpGraphVarM_rows`: `bgpGraphVarM` returns a well-formed table whose rows
  are `IdEquiv` to per graph `x` of `G`, `idBgpFrom (L x)` of the patterns
  from `{?g ↦ x}`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ExecLeafTheorems

namespace L4Factoidal.Storage.Sbm11.GraphBgp

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd OptRowEq IPat ISlot idEvalTP idBgpFrom matchSlots slotMatch
  idTpMatch optCont cm ipat)
open L4Factoidal.Storage.Sbm11.IdJoin (idJoin)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (ipatOf rowM permListing tripleOf Fits GSlot)
open L4Factoidal.Storage.Sbm11.BgpTableTheorems (ScanStore joinL)
open L4Factoidal.Storage.Sbm11.IdGroup (idBindG NCx NSt)
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple)

/-! ## Lists -/

theorem flatMap_one {α β : Type} [DecidableEq α] (f : α → List β) :
    ∀ (G : List α) (x : α), x ∈ G → G.Nodup → (∀ y ∈ G, y ≠ x → f y = []) → G.flatMap f = f x
  | [], _, hx, _, _ => by cases hx
  | y :: G, x, hx, hnd, h => by
    rw [List.flatMap_cons]
    rw [List.nodup_cons] at hnd
    by_cases hyx : y = x
    · subst hyx
      have : G.flatMap f = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro z hz
        exact h z (List.mem_cons_of_mem _ hz) (fun e => hnd.1 (e ▸ hz))
      rw [this, List.append_nil]
    · rw [h y List.mem_cons_self hyx, List.nil_append]
      exact flatMap_one f G x ((List.mem_cons.mp hx).resolve_left (fun e => hyx e.symm)) hnd.2
        (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- A list whose keys are in `G` (distinct) is a permutation of its parts
    per key, in the order of `G`. -/
theorem perm_keys {α : Type} (key : α → UInt64) :
    ∀ (G : List UInt64), G.Nodup → ∀ (R : List α), (∀ a ∈ R, key a ∈ G) →
      R.Perm (G.flatMap fun x => R.filter fun a => decide (key a = x))
  | [], _, R, h => by
    cases R with
    | nil => exact List.Perm.refl _
    | cons a _ => exact absurd (h a List.mem_cons_self) (by simp)
  | x :: G, hnd, R, h => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons]
    have hsplit := (List.filter_append_perm (fun a => decide (key a = x)) R).symm
    refine hsplit.trans (List.Perm.append_left _ ?_)
    have hR' : ∀ a ∈ R.filter (fun a => !decide (key a = x)), key a ∈ G := by
      intro a ha
      obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
      have := h a h1
      rcases List.mem_cons.mp this with e | e
      · simp [e] at h2
      · exact e
    refine (perm_keys key G hnd.2 _ hR').trans (List.Perm.of_eq ?_)
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro y hy
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    have hyx : y ≠ x := fun e => hnd.1 (e ▸ hy)
    by_cases hk : key a = y
    · simp [hk, hyx]
    · simp [hk]

/-! ## Matching from the mapping `{?g ↦ x}` -/

theorem lookup_seed (S : List (ISlot × UInt64)) (v : String) (x : UInt64) {m : IdRow}
    (h : matchSlots S [(v, x)] = some m) : idLookup v m = some x :=
  IdLeaf.matchSlots_mono S h (by simp [idLookup])

theorem idMerge_seed (r : IdRow) (v : String) (x : UInt64) (h : idLookup v r = some x) :
    idMerge r [(v, x)] = r := by
  simp [idMerge, h]

theorem compat_seed (r : IdRow) (v : String) (x : UInt64) (hnd : Nd r) (h : idLookup v r = some x) :
    idCompatible r [(v, x)] = true :=
  IdLeaf.compat_cons_same hnd (IdLeaf.compat_nil r) h

/-- A row that binds `?g` to `x` joins the matches from `{?g ↦ x}` as one
    step of the evaluation from the row. -/
theorem seed_join (t : IPat) (T : List IdTriple) (v : String) (x : UInt64) (r : IdRow) (hnd : Nd r)
    (h : idLookup v r = some x) :
    IdGroup.Pw RowEq ((idEvalTP t T [(v, x)]).filterMap (cm r)) (idEvalTP t T r) := by
  unfold idEvalTP
  rw [List.filterMap_filterMap]
  apply IdLeaf.pw_filterMap
  intro tr _
  have hm := IdLeaf.matchSlots_merge r hnd (t.slots tr) [(v, x)] (compat_seed r v x hnd h)
  rw [idMerge_seed r v x h] at hm
  apply IdLeaf.OptRowEq.symm
  unfold idTpMatch
  cases e : matchSlots (t.slots tr) [(v, x)] with
  | none => rw [e] at hm; simpa [e] using hm
  | some m => rw [e] at hm; simpa [e] using hm

/-- A row that binds `?g` to `x` joins no match from `{?g ↦ y}`, `y ≠ x`. -/
theorem seed_other (t : IPat) (T : List IdTriple) (v : String) (x y : UInt64) (r : IdRow) (hne : y ≠ x)
    (h : idLookup v r = some x) : (idEvalTP t T [(v, y)]).filterMap (cm r) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro m hm
  obtain ⟨tr, _, e⟩ := List.mem_filterMap.mp hm
  have hl := lookup_seed _ v y e
  unfold cm
  have : idCompatible r m = false := by
    cases hc : idCompatible r m with
    | false => rfl
    | true => exact absurd (IdLeaf.compat_lookup hc h hl) (fun e' => hne e'.symm)
  rw [this]
  rfl

theorem rows_step (t : IPat) (T : List IdTriple) (v : String) (x : UInt64) (r : IdRow) (hnd : Nd r)
    (h : idLookup v r = some x) : ∀ m ∈ idEvalTP t T r, Nd m ∧ idLookup v m = some x := by
  intro m hm
  obtain ⟨tr, _, e⟩ := List.mem_filterMap.mp hm
  exact ⟨IdLeaf.nd_matchSlots _ hnd e, IdLeaf.matchSlots_mono _ e h⟩

theorem nd_seed (v : String) (x : UInt64) : Nd [(v, x)] := by
  unfold Nd; simp

/-! ## The joins of the scans over the named graphs -/

/-- The model of one scan over the named graphs: per graph `x` of `G`, the
    pattern's matches in the listing `L x` from the mapping `{?g ↦ x}`. -/
def gS (v : String) (G : List UInt64) (L : UInt64 → List IdTriple) (t : Pat) : List IdRow :=
  G.flatMap fun y => idEvalTP (ipatOf t) (L y) [(v, y)]

/-- **One join of the loop.** -/
theorem join_graph (t : IPat) (v : String) (G : List UInt64) (L : UInt64 → List IdTriple)
    (A : UInt64 → List IdRow) (hG : G.Nodup) (hA : ∀ x ∈ G, ∀ r ∈ A x, Nd r ∧ idLookup v r = some x) :
    IdEquiv (idJoin (G.flatMap A) (G.flatMap fun y => idEvalTP t (L y) [(v, y)]))
      (G.flatMap fun x => (A x).flatMap (idEvalTP t (L x))) := by
  unfold idJoin
  rw [List.flatMap_assoc]
  apply IdLeaf.flatMap_equiv
  intro x hx
  apply IdLeaf.flatMap_equiv
  intro r hr
  obtain ⟨hnd, hl⟩ := hA x hx r hr
  rw [List.filterMap_flatMap]
  have e := flatMap_one (fun y => (idEvalTP t (L y) [(v, y)]).filterMap (cm r)) G x hx hG
    (fun y _ hyx => seed_other t (L y) v x y r hyx hl)
  show IdEquiv (G.flatMap fun y => (idEvalTP t (L y) [(v, y)]).filterMap (cm r)) _
  rw [e]
  exact IdEquiv.of_pw (seed_join t (L x) v x r hnd hl)

theorem joinL_equiv (S : Pat → List IdRow) : ∀ (ps : List Pat) {L L' : List IdRow}, IdEquiv L L' →
    (∀ r ∈ L, Nd r) → (∀ r ∈ L', Nd r) → IdEquiv (joinL S ps L) (joinL S ps L')
  | [], _, _, h, _, _ => h
  | t :: ps, L, L', h, h1, h2 =>
    joinL_equiv S ps (BgpTableTheorems.idJoin_equiv h (IdEquiv.refl (S t)) h1 h2) (IdLeaf.nd_idJoin L _ h1)
      (IdLeaf.nd_idJoin L' _ h2)

theorem joinL_graph (v : String) (G : List UInt64) (L : UInt64 → List IdTriple) (hG : G.Nodup) :
    ∀ (ps : List Pat) (A : UInt64 → List IdRow), (∀ x ∈ G, ∀ r ∈ A x, Nd r ∧ idLookup v r = some x) →
      IdEquiv (joinL (gS v G L) ps (G.flatMap A))
        (G.flatMap fun x => (A x).flatMap (idBgpFrom (L x) (ps.map ipatOf)))
  | [], A, _ => by
    show IdEquiv (G.flatMap A) _
    have e : ∀ x, (A x).flatMap (idBgpFrom (L x) (([] : List Pat).map ipatOf)) = A x := by
      intro x
      simp [IdLeaf.idBgpFrom]
    simp only [e]
    exact IdEquiv.refl _
  | t :: ps, A, hA => by
    have hnd : ∀ r ∈ G.flatMap A, Nd r := by
      intro r hr
      obtain ⟨x, hx, hr'⟩ := List.mem_flatMap.mp hr
      exact (hA x hx r hr').1
    let A' : UInt64 → List IdRow := fun x => (A x).flatMap (idEvalTP (ipatOf t) (L x))
    have hA' : ∀ x ∈ G, ∀ r ∈ A' x, Nd r ∧ idLookup v r = some x := by
      intro x hx r hr
      obtain ⟨r0, h0, hr0⟩ := List.mem_flatMap.mp hr
      obtain ⟨hn0, hl0⟩ := hA x hx r0 h0
      exact rows_step _ _ v x r0 hn0 hl0 r hr0
    have hnd' : ∀ r ∈ G.flatMap A', Nd r := by
      intro r hr
      obtain ⟨x, hx, hr'⟩ := List.mem_flatMap.mp hr
      exact (hA' x hx r hr').1
    have hj := join_graph (ipatOf t) v G L A hG hA
    show IdEquiv (joinL (gS v G L) ps (idJoin (G.flatMap A) (gS v G L t))) _
    refine IdEquiv.trans (joinL_equiv _ ps hj (IdLeaf.nd_idJoin _ _ hnd) hnd') ?_
    refine IdEquiv.trans (joinL_graph v G L hG ps A' hA') ?_
    have e : ∀ x, (A' x).flatMap (idBgpFrom (L x) (ps.map ipatOf)) =
        (A x).flatMap (idBgpFrom (L x) ((t :: ps).map ipatOf)) := by
      intro x
      simp only [A', List.flatMap_assoc, List.map_cons]
      rfl
    simp only [e]
    exact IdEquiv.refl _

/-- **The joins of the loop.** -/
theorem joinL_graph_top (v : String) (G : List UInt64) (L : UInt64 → List IdTriple) (hG : G.Nodup)
    (t : Pat) (ps : List Pat) :
    IdEquiv (joinL (gS v G L) (t :: ps) [[]])
      (G.flatMap fun x => idBgpFrom (L x) ((t :: ps).map ipatOf) [(v, x)]) := by
  have hA0 : ∀ x ∈ G, ∀ r ∈ idEvalTP (ipatOf t) (L x) [(v, x)], Nd r ∧ idLookup v r = some x :=
    fun x _ => rows_step _ _ v x _ (nd_seed v x) (by simp [idLookup])
  have hndS : ∀ r ∈ gS v G L t, Nd r := by
    intro r hr
    obtain ⟨x, hx, hr'⟩ := List.mem_flatMap.mp hr
    exact (hA0 x hx r hr').1
  have hnd0 : ∀ r ∈ ([[]] : List IdRow), Nd r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact List.nodup_nil
  show IdEquiv (joinL (gS v G L) ps (idJoin [[]] (gS v G L t))) _
  refine IdEquiv.trans (joinL_equiv _ ps (BgpTableTheorems.idJoin_unit _) (IdLeaf.nd_idJoin _ _ hnd0) hndS) ?_
  exact joinL_graph v G L hG ps (fun x => idEvalTP (ipatOf t) (L x) [(v, x)]) hA0

/-! ## The mapping `{?g ↦ x}` first or last -/

theorem idBindG_slot (v : String) (x : UInt64) (r : IdRow) : idBindG v x r = slotMatch (.var v) x r := by
  unfold idBindG slotMatch
  rfl

theorem bind_last (S : List (ISlot × UInt64)) (v : String) (x : UInt64) (r : IdRow) :
    OptRowEq ((matchSlots S r).bind (idBindG v x)) ((idBindG v x r).bind (matchSlots S)) := by
  have h1 : (matchSlots S r).bind (idBindG v x) = matchSlots (S ++ [(.var v, x)]) r := by
    rw [IdLeaf.matchSlots_append]
    cases matchSlots S r with
    | none => rfl
    | some r1 =>
      simp only [Option.bind_some, matchSlots, idBindG_slot]
      cases slotMatch (.var v) x r1 <;> rfl
  have h2 : (idBindG v x r).bind (matchSlots S) = matchSlots ((.var v, x) :: S) r := by
    simp only [matchSlots, idBindG_slot]
    cases slotMatch (.var v) x r <;> rfl
  rw [h1, h2]
  exact IdLeaf.matchSlots_perm (List.perm_append_singleton _ _) r

theorem optCont_bind (o : Option IdRow) (g : IdRow → Option IdRow) (F : IdRow → List IdRow) :
    optCont o (fun m => optCont (g m) F) = optCont (o.bind g) F := by
  cases o <;> rfl

/-- The evaluation from `r`, then `?g` bound to `x`, is the evaluation from
    `r` with `?g` bound to `x`, up to order. -/
theorem seed_bgp (T : List IdTriple) (v : String) (x : UInt64) :
    ∀ (ps : List IPat) (r : IdRow),
      IdEquiv ((idBgpFrom T ps r).filterMap (idBindG v x)) (optCont (idBindG v x r) (idBgpFrom T ps))
  | [], r => by
    show IdEquiv ([r].filterMap (idBindG v x)) (optCont (idBindG v x r) fun r => [r])
    cases h : idBindG v x r <;> simp [h, optCont] <;> exact IdEquiv.refl _
  | t :: ps, r => by
    show IdEquiv (((idEvalTP t T r).flatMap (idBgpFrom T ps)).filterMap (idBindG v x))
      (optCont (idBindG v x r) fun r' => (idEvalTP t T r').flatMap (idBgpFrom T ps))
    rw [List.filterMap_flatMap]
    refine IdEquiv.trans (IdLeaf.flatMap_equiv _ (fun m => optCont (idBindG v x m) (idBgpFrom T ps)) _
      (fun m _ => seed_bgp T v x ps m)) ?_
    unfold idEvalTP
    rw [IdLeaf.filterMap_flatMap]
    have e : (fun r' => (T.filterMap fun tr => idTpMatch t tr r').flatMap (idBgpFrom T ps)) =
        fun r' => T.flatMap fun tr => optCont (idTpMatch t tr r') (idBgpFrom T ps) := by
      funext r'
      exact IdLeaf.filterMap_flatMap _ _ T
    rw [e, IdLeaf.optCont_flatMap]
    apply IdLeaf.flatMap_equiv
    intro tr _
    rw [optCont_bind]
    apply IdLeaf.optCont_equiv _ (fun a b h => IdEquiv.of_pw (IdLeaf.idBgpFrom_congr T ps h))
    have := bind_last (t.slots tr) v x r
    unfold idTpMatch
    cases h : idBindG v x r with
    | none => rw [h] at this; exact this
    | some r1 => rw [h] at this; exact this

theorem seed_top (T : List IdTriple) (v : String) (x : UInt64) (ps : List IPat) :
    IdEquiv ((idBgpFrom T ps []).filterMap (idBindG v x)) (idBgpFrom T ps [(v, x)]) :=
  seed_bgp T v x ps []

/-- `idBindG` respects `RowEq`. -/
theorem optRowEq_bindG (v : String) (x : UInt64) {a b : IdRow} (h : RowEq a b) :
    OptRowEq (idBindG v x a) (idBindG v x b) := by
  rw [idBindG_slot, idBindG_slot]
  have := IdLeaf.matchSlots_congr [(.var v, x)] h
  simp only [matchSlots] at this
  revert this
  cases slotMatch (.var v) x a <;> cases slotMatch (.var v) x b <;> simp [OptRowEq]

theorem idEquiv_bindG (v : String) (x : UInt64) {A B : List IdRow} (h : IdEquiv A B) :
    IdEquiv (A.filterMap (idBindG v x)) (B.filterMap (idBindG v x)) := by
  obtain ⟨C, hp, hw⟩ := h
  exact ⟨C.filterMap (idBindG v x), hp.filterMap _,
    BgpTableTheorems.pw_filterMap2 _ _ hw (fun _ _ hab => optRowEq_bindG v x hab)⟩

/-! ## The scans over the named graphs -/

/-- The matches of a permutation's rows for a pattern over the named graphs
    (`?g` its graph slot), per graph of `G`. -/
theorem named_rows_perm (t : Pat) (perm : Nat) (v : String) (htg : t.g = .var v) (R : List Row)
    (hfit : ∀ r ∈ R, Fits r) (G : List UInt64) (hG : G.Nodup) (hG0 : ∀ x ∈ G, x ≠ 0)
    (hin : ∀ r ∈ R, r.g ≠ 0 → r.g.toUInt64 ∈ G) :
    (R.filterMap (rowM t perm)).Perm (G.flatMap fun x => idEvalTP (ipatOf t) (permListing perm x R) [(v, x)]) := by
  have e1 : R.filterMap (rowM t perm) = (R.filter fun r => r.g != 0).filterMap (rowM t perm) := by
    rw [ScanTableTheorems.filterMap_filter_eq]
    apply OptJoin.filterMap_congr'
    intro r _
    unfold rowM
    rw [htg]
    by_cases h : r.g = 0 <;> simp [h]
  have hp := perm_keys (fun r : Row => r.g.toUInt64) G hG (R.filter fun r => r.g != 0) (fun a ha => by
    obtain ⟨h1, h2⟩ := List.mem_filter.mp ha
    exact hin a h1 (by simpa using h2))
  rw [e1]
  refine (hp.filterMap _).trans (List.Perm.of_eq ?_)
  rw [List.filterMap_flatMap]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro x hx
  unfold IdLeaf.idEvalTP permListing
  rw [List.filter_filter, List.filterMap_map, ScanTableTheorems.filterMap_filter_eq,
    ScanTableTheorems.filterMap_filter_eq]
  apply OptJoin.filterMap_congr'
  intro r hr
  have hg := hfit r hr 3 (by omega)
  have hx0 := hG0 x hx
  have hiff : r.g.toUInt64 = x ↔ r.g = x.toNat := by
    constructor
    · intro e; rw [← e]; exact (ScanFoldTheorems.uint64_toNat_toUInt64 _ hg).symm
    · intro e; rw [e]; simp
  unfold rowM
  rw [htg]
  by_cases h : r.g = x.toNat
  · have hr0 : r.g ≠ 0 := by
      intro e
      apply hx0
      apply UInt64.toNat_inj.mp
      rw [← h, e]; rfl
    have hx00 : x.toNat ≠ 0 := by rw [← h]; exact hr0
    simp [h, hx00, Function.comp]
  · have hx' : ¬ r.g.toUInt64 = x := fun e => h (hiff.mp e)
    simp [h, hx']

/-- **The store of the named graphs.** Over the four permutations in memory,
    whose rows with a graph id other than 0 are in the graphs `G` (distinct,
    none 0), and whose listing of each graph `x` of `G` is a permutation of
    `L x`, the model of a pattern over the named graphs (`?g` its graph slot)
    is `gS v G L`. -/
theorem named_scanStore (st : Store Id) (prb : Nat → ByteArray) (ms : Nat → List BlockMeta)
    (hpm : ∀ k, k < 4 → ScanTableTheorems.PermMem st k (prb k) (ms k)) (hscan : st.scanTable = none)
    (v : String) (G : List UInt64) (hG : G.Nodup) (hG0 : ∀ x ∈ G, x ≠ 0)
    (hin : ∀ k, k < 4 → ∀ r ∈ (ms k).flatMap (ScanFoldTheorems.blockRows (prb k)), r.g ≠ 0 → r.g.toUInt64 ∈ G)
    (L : UInt64 → List IdTriple)
    (hL : ∀ x ∈ G, ∀ k, k < 4 → (permListing k x ((ms k).flatMap (ScanFoldTheorems.blockRows (prb k)))).Perm (L x)) :
    ScanStore st (fun t => t.g = .var v ∧ t.named = true) (gS v G L) := by
  refine ⟨fun k hk => ⟨prb k, ms k, hpm k hk, fun t ⟨htg, _⟩ => ?_⟩, hscan⟩
  refine (named_rows_perm t k v htg _ (ScanTableTheorems.rows_fit (prb k) (ms k)) G hG hG0 (hin k hk)).trans ?_
  exact IdGroup.perm_flatMap_left _ _ G fun x hx => List.Perm.filterMap _ (hL x hx k hk)

/-! ## `bgpGraphVarM` -/

open L4Factoidal.Storage.Sbm11.ExecLeafTheorems (ExecTp specE patOfSpec slotOfArg patSpecsOf_run resolvePat_eq
  ipatOf_spec)

theorem iMiss_var (t : Pat) (v : String) (hg : t.g = .var v) (h : t.hasMissing = true) :
    BgpTableTheorems.IMiss (ipatOf t) := by
  unfold Pat.hasMissing at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · left; show ScanTableTheorems.islot t.s = _; rw [BgpTableTheorems.slot_beq_missing _ h]; rfl
  · right; left; show ScanTableTheorems.islot t.p = _; rw [BgpTableTheorems.slot_beq_missing _ h]; rfl
  · right; right; show ScanTableTheorems.islot t.o = _; rw [BgpTableTheorems.slot_beq_missing _ h]; rfl
  · rw [BgpTableTheorems.slot_beq_missing _ h] at hg; cases hg

/-- The pattern `bgpGraphVarM` resolves for a triple pattern. -/
def patVar (cid : Term → Option UInt64) (v : String) (tp : TriplePattern) : Pat :=
  patOfSpec cid .dflt { specE tp with g := .var v }

theorem ipatOf_var (cid : Term → Option UInt64) (v : String) (tp : TriplePattern) (h : ExecTp tp) :
    ipatOf (patVar cid v tp) = ipat cid tp := by
  rw [← ipatOf_spec cid .dflt tp h]
  rfl

/-- **The rows of `IdGroup.bgpGraphVarM`.** Over a store of the named graphs
    (`named_scanStore`) whose dictionary lookup is `cid`, with no dataset
    clause, `GRAPH ?v { B }` for a nonempty basic graph pattern `B` whose
    positions are variables, IRIs or literals returns a well-formed table
    whose rows bind no variable twice and are `IdEquiv` to, per graph `x` of
    `G`, the sequential evaluation of the triple patterns over `L x` from the
    mapping `{?v ↦ x}`; the state's vocabulary is unchanged. -/
theorem bgpGraphVarM_rows (cx : NCx Id) (cid : Term → Option UInt64) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hds : cx.ds = none) (v : String) (G : List UInt64) (L : UInt64 → List IdTriple) (hG : G.Nodup)
    (hst : ScanStore cx.st (fun t => t.g = .var v ∧ t.named = true) (gS v G L))
    (tps : List TriplePattern) (htp : ∀ tp ∈ tps, ExecTp tp) (hne : tps ≠ []) (nst : NSt) :
    ∃ tab nst', (IdGroup.bgpGraphVarM cx v tps).run nst = pure (tab, nst') ∧ nst'.vocab = nst.vocab ∧
      nst'.localIdx = nst.localIdx ∧ tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧
      IdEquiv tab.idRows (G.flatMap fun x => idBgpFrom (L x) (tps.map (ipat cid)) [(v, x)]) := by
  unfold IdGroup.bgpGraphVarM
  rw [StateT.run_bind, patSpecsOf_run tps htp nst, pure_bind]
  simp only []
  have hmap : Array.mapM (fun p => resolvePatIn cx.st cx.ds { p with g := GArg.var v }) (tps.map specE).toArray =
      pure ((tps.map specE).toArray.map fun p => patOfSpec cid .dflt { p with g := GArg.var v }) := by
    have : (fun p : PatSpec => resolvePatIn cx.st cx.ds { p with g := GArg.var v }) =
        fun p => pure (patOfSpec cid .dflt { p with g := GArg.var v }) := by
      funext p
      unfold resolvePatIn
      rw [hds]
      exact resolvePat_eq cx.st cid hid _
    rw [this, Array.mapM_pure]
  rw [StateT.run_bind]
  unfold IdGroup.liftE
  rw [StateT.run_lift, hmap, pure_bind, pure_bind]
  simp only []
  generalize hpats : (tps.map specE).toArray.map (fun p => patOfSpec cid .dflt { p with g := GArg.var v }) = pats
  have hsz : 0 < pats.size := by
    rw [← hpats]
    cases tps with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hsize : pats.size = tps.length := by rw [← hpats]; simp
  have hget : ∀ n (hn : n < pats.size) (hnt : n < tps.length), pats[n] = patVar cid v tps[n] := by
    intro n hn hnt
    have := congrArg (fun a : Array Pat => a[n]?) hpats
    simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hnt,
      Option.map_some, Array.getElem?_eq_getElem hn] at this
    exact (Option.some.inj this).symm
  have hpv : ∀ i, i < pats.size → ∃ tp ∈ tps, pats[i]! = patVar cid v tp := by
    intro i hi
    have hit : i < tps.length := by rw [← hsize]; exact hi
    rw [getElem!_pos pats i hi]
    exact ⟨tps[i], List.getElem_mem hit, hget i hi hit⟩
  have hpats' : ∀ i, i < pats.size → (pats[i]!.g = .var v ∧ pats[i]!.named = true) ∧ GSlot pats[i]! ∧
      pats[i]!.plain = true := by
    intro i hi
    obtain ⟨tp, _, e⟩ := hpv i hi
    rw [e]
    exact ⟨⟨rfl, rfl⟩, Or.inr ⟨v, rfl, rfl⟩, rfl⟩
  have hmissS : ∀ t, (t.g = .var v ∧ t.named = true) → t.hasMissing = true → gS v G L t = [] := by
    intro t ⟨htg, _⟩ hm
    unfold gS
    rw [List.flatMap_eq_nil_iff]
    intro x _
    exact BgpTableTheorems.idEvalTP_missing _ (iMiss_var t v htg hm) _ _
  obtain ⟨tab, lines, stats, he, hwf, hnd, vis, hvis, heq⟩ :=
    BgpTableTheorems.evalBgpM_modelS cx.st pats hsz _ (gS v G L) hst hpats' hmissS
  rw [StateT.run_bind, StateT.run_lift, he, pure_bind, pure_bind]
  refine ⟨tab, ?_⟩
  apply Exists.intro
  refine ⟨?_, ?_, ?_, hwf, hnd, ?_⟩
  · simp only [IdGroup.addStats, IdGroup.note, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure]
    rfl
  · rfl
  · rfl
  · -- the order of the patterns
    cases hv : vis with
    | nil =>
      rw [hv] at hvis
      have := hvis.length_eq
      simp at this
      omega
    | cons i0 rest =>
      rw [hv] at heq
      refine IdEquiv.trans heq (IdEquiv.trans (joinL_graph_top v G L hG _ _) ?_)
      apply IdLeaf.flatMap_equiv
      intro x _
      have hps : ((pats[i0]! :: rest.map fun i => pats[i]!).map ipatOf).Perm (tps.map (ipat cid)) := by
        have h1 : (pats[i0]! :: rest.map fun i => pats[i]!) = (i0 :: rest).map fun i => pats[i]! := rfl
        rw [h1, ← hv, List.map_map]
        have h2 : tps.map (ipat cid) = (List.range pats.size).map (ipatOf ∘ fun i => pats[i]!) := by
          apply List.ext_getElem
          · simp [hsize]
          · intro n h1 h2
            have hnt : n < tps.length := by simpa using h1
            have hn : n < pats.size := by simpa using h2
            simp only [List.getElem_map, List.getElem_range, Function.comp]
            rw [getElem!_pos pats n hn, hget n hn hnt, ipatOf_var cid v tps[n] (htp _ (List.getElem_mem hnt))]
        rw [h2]
        exact hvis.map _
      exact IdLeaf.idBgpFrom_perm (L x) hps [(v, x)] [(v, x)] (TableTheorems.RowEq.refl _)

end L4Factoidal.Storage.Sbm11.GraphBgp

#print axioms L4Factoidal.Storage.Sbm11.GraphBgp.bgpGraphVarM_rows
#print axioms L4Factoidal.Storage.Sbm11.GraphBgp.named_scanStore
#print axioms L4Factoidal.Storage.Sbm11.GraphBgp.joinL_graph_top
#print axioms L4Factoidal.Storage.Sbm11.GraphBgp.seed_top
#print axioms L4Factoidal.Storage.Sbm11.GraphBgp.idEquiv_bindG
