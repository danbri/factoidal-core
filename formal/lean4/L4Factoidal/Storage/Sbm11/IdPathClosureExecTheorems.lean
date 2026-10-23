/-
L4Factoidal.Storage.Sbm11.IdPathClosureExecTheorems — the closures `p*` and
`p+` as the id path executes them (`IdQuery.closureM`: `closureEdgesM`,
`closureRoundsM`, `closureEmitM`) against the reference's closure over ids
(https://github.com/danbri/factoidal/issues/776; part of lemma L4n of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

The step relation is any program `stepM` that answers, for a direction and a
restriction whose values are increasing (`RGood`), a relation whose pairs are,
up to order, the pairs of a relation `E` the restriction keeps
(`IdPathScanTheorems.Restr`). `E` is the step relation of the model
(`idEvalPath p T`); its pairs are pairs of nodes of the graph.

* `emit_spec`: the pairs `closureEmitM` emits for the start nodes, from the
  worklist (`IdPath.reachPlus`, against `reachModel` by `reachPlus_eq`).
* `rounds_spec`: the rounds from a restriction collect, within the round
  bound of `pathFuelM` (`IdPathScanTheorems.pathFuel_ge`), the pairs of `E`
  whose subject (object, for an object restriction) is reached from the
  restriction, and the reached nodes are closed under steps.
* `closureM_spec`: the pairs of `closureM`, each once, are the pairs of the
  reference's closure (`p*`: `a` a node and `Reach E a c`; `p+`:
  `Reach1 E a c`) that the restriction keeps.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPathScanTheorems

namespace L4Factoidal.Storage.Sbm11.IdPathClosureExec

open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple IdPairs Pairs idGraphNodes Reach Reach1 reachModel
  reachPlus adjOf)
open L4Factoidal.Storage.Sbm11.IdPathScanTheorems (Restr contains_iff)

/-! ## The emission per start node -/

/-- The pairs `closureEmitM` appends for start node `a` with the worklist
    output `r`. -/
def emitList (r : List UInt64) (self dirFwd : Bool) (a : UInt64) : IdPairs :=
  (if self then [(a, a)] else []) ++
    (r.filter (fun c => !(self && c == a))).map (fun c => if dirFwd then (a, c) else (c, a))

theorem foldl_emit (self dirFwd : Bool) (a : UInt64) (r : List UInt64) :
    ∀ (out : Pairs), (r.foldl (fun out c => if !(self && c == a) then out.push (if dirFwd then (a, c) else (c, a))
      else out) out).toList =
      out.toList ++ (r.filter (fun c => !(self && c == a))).map (fun c => if dirFwd then (a, c) else (c, a)) := by
  induction r with
  | nil => intro out; simp
  | cons c cs ih =>
    intro out
    rw [List.foldl_cons, ih]
    by_cases h : (!(self && c == a)) = true
    · rw [if_pos h, List.filter_cons, if_pos h]; simp
    · rw [if_neg h, List.filter_cons, if_neg h]

theorem emit_eq (adj : Std.HashMap UInt64 (Array UInt64)) (nodeSet : Std.HashSet UInt64) (zero dirFwd : Bool)
    (fuel : Nat) (out : Pairs) (a : UInt64) (r : Array UInt64) (hr : reachPlus adj a fuel = some r) :
    ∃ out', closureEmitM (m := Id) adj nodeSet zero dirFwd fuel out a = pure out' ∧
      out'.toList = out.toList ++ emitList r.toList (zero && nodeSet.contains a) dirFwd a := by
  refine ⟨r.foldl (fun out c => if !((zero && nodeSet.contains a) && c == a) then
      out.push (if dirFwd then (a, c) else (c, a)) else out)
      (if (zero && nodeSet.contains a) then out.push (a, a) else out), ?_, ?_⟩
  · unfold closureEmitM
    rw [hr]
  · rw [← Array.foldl_toList, foldl_emit]
    unfold emitList
    by_cases hs : (zero && nodeSet.contains a) = true
    · simp [hs]
    · simp only [Bool.not_eq_true] at hs
      simp [hs]

/-- **The emission over the start nodes.** -/
theorem emit_all (adj : Std.HashMap UInt64 (Array UInt64)) (nodeSet : Std.HashSet UInt64) (zero dirFwd : Bool)
    (fuel : Nat) (sources : Array UInt64) (hreach : ∀ a ∈ sources.toList, (reachPlus adj a fuel).isSome) :
    ∃ out, sources.foldlM (m := ExceptT String Id) (closureEmitM adj nodeSet zero dirFwd fuel) #[] = pure out ∧
      out.toList = sources.toList.flatMap (fun a =>
        emitList ((reachPlus adj a fuel).getD #[]).toList (zero && nodeSet.contains a) dirFwd a) := by
  rw [← Array.foldlM_toList]
  suffices ∀ (l : List UInt64), (∀ a ∈ l, (reachPlus adj a fuel).isSome) → ∀ (out0 : Pairs),
      ∃ out, l.foldlM (m := ExceptT String Id) (closureEmitM adj nodeSet zero dirFwd fuel) out0 = pure out ∧
        out.toList = out0.toList ++ l.flatMap (fun a =>
          emitList ((reachPlus adj a fuel).getD #[]).toList (zero && nodeSet.contains a) dirFwd a) by
    obtain ⟨out, h1, h2⟩ := this sources.toList hreach #[]
    exact ⟨out, h1, by rw [h2]; simp⟩
  intro l
  induction l with
  | nil => intro _ out0; exact ⟨out0, rfl, by simp⟩
  | cons a l ih =>
    intro h out0
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    obtain ⟨out1, he1, ht1⟩ := emit_eq adj nodeSet zero dirFwd fuel out0 a r hr
    obtain ⟨out, he, ht⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) out1
    refine ⟨out, ?_, ?_⟩
    · rw [List.foldlM_cons, he1]
      exact he
    · rw [ht, ht1, List.flatMap_cons, hr]
      simp

/-- The start node of an emitted pair: its subject in the forward direction,
    its object in the backward one. -/
def keyOf (dirFwd : Bool) (x : UInt64 × UInt64) : UInt64 := if dirFwd then x.1 else x.2

/-- The other end of an emitted pair. -/
def otherOf (dirFwd : Bool) (x : UInt64 × UInt64) : UInt64 := if dirFwd then x.2 else x.1

theorem key_other (dirFwd : Bool) (a c : UInt64) :
    keyOf dirFwd (if dirFwd then (a, c) else (c, a)) = a ∧ otherOf dirFwd (if dirFwd then (a, c) else (c, a)) = c := by
  cases dirFwd <;> simp [keyOf, otherOf]

theorem eq_of_key_other (dirFwd : Bool) (x : UInt64 × UInt64) :
    x = (if dirFwd then (keyOf dirFwd x, otherOf dirFwd x) else (otherOf dirFwd x, keyOf dirFwd x)) := by
  cases dirFwd <;> simp [keyOf, otherOf]

theorem mem_emitList (r : List UInt64) (self dirFwd : Bool) (a : UInt64) (x : UInt64 × UInt64) :
    x ∈ emitList r self dirFwd a ↔ keyOf dirFwd x = a ∧ ((self = true ∧ otherOf dirFwd x = a) ∨ otherOf dirFwd x ∈ r) := by
  unfold emitList
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · split at h
      · rename_i hs
        rw [List.mem_singleton] at h
        subst h
        cases dirFwd <;> exact ⟨by simp [keyOf], Or.inl ⟨hs, by simp [otherOf]⟩⟩
      · cases h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      obtain ⟨k, o⟩ := key_other dirFwd a c
      rw [k, o]
      exact ⟨rfl, Or.inr (List.mem_filter.mp hc).1⟩
  · rintro ⟨hk, h⟩
    have hx := eq_of_key_other dirFwd x
    rw [hk] at hx
    by_cases hs : self = true ∧ otherOf dirFwd x = a
    · apply List.mem_append_left
      rw [if_pos hs.1, List.mem_singleton, hx, hs.2]
      cases dirFwd <;> rfl
    · rcases h with h | h
      · exact absurd h hs
      · apply List.mem_append_right
        refine List.mem_map.mpr ⟨otherOf dirFwd x, List.mem_filter.mpr ⟨h, ?_⟩, hx.symm⟩
        cases hself : self
        · rfl
        · have : otherOf dirFwd x ≠ a := fun e => hs ⟨hself, e⟩
          simp [this]

theorem nodup_map_inj {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (l : List α), l.Nodup → (l.map f).Nodup
  | [], _ => by simp
  | a :: l, h => by
    have ⟨ha, hl⟩ := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, nodup_map_inj f hf l hl⟩
    intro hm
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    exact ha (hf _ _ e ▸ hb)

theorem emitList_nodup (r : List UInt64) (hr : r.Nodup) (self dirFwd : Bool) (a : UInt64) :
    (emitList r self dirFwd a).Nodup := by
  unfold emitList
  rw [List.nodup_append]
  refine ⟨by split <;> simp, ?_, ?_⟩
  · apply nodup_map_inj _ _ _ (hr.filter _)
    intro c1 c2 h
    have := congrArg (otherOf dirFwd) h
    rwa [(key_other dirFwd a c1).2, (key_other dirFwd a c2).2] at this
  · intro y hy z hz e
    subst e
    split at hy
    · rename_i hs
      rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨c, hc, he⟩ := List.mem_map.mp hz
      have h2 := (key_other dirFwd a c).2
      rw [he] at h2
      have hca : c = a := by rw [← h2]; cases dirFwd <;> rfl
      have := (List.mem_filter.mp hc).2
      simp [hs, hca] at this
    · cases hy

theorem mem_flatMap_emit (dirFwd : Bool) (srcs : List UInt64) (rf : UInt64 → List UInt64) (selff : UInt64 → Bool)
    (x : UInt64 × UInt64) :
    x ∈ srcs.flatMap (fun a => emitList (rf a) (selff a) dirFwd a) ↔
      keyOf dirFwd x ∈ srcs ∧ ((selff (keyOf dirFwd x) = true ∧ otherOf dirFwd x = keyOf dirFwd x) ∨
        otherOf dirFwd x ∈ rf (keyOf dirFwd x)) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨hk, h⟩ := (mem_emitList _ _ _ _ x).mp h
    subst hk
    exact ⟨ha, h⟩
  · rintro ⟨ha, h⟩
    exact ⟨_, ha, (mem_emitList _ _ _ _ x).mpr ⟨rfl, h⟩⟩

theorem flatMap_emit_nodup (dirFwd : Bool) (srcs : List UInt64) (hs : srcs.Nodup) (rf : UInt64 → List UInt64)
    (selff : UInt64 → Bool) (hr : ∀ a ∈ srcs, (rf a).Nodup) :
    (srcs.flatMap (fun a => emitList (rf a) (selff a) dirFwd a)).Nodup := by
  induction srcs with
  | nil => simp
  | cons a l ih =>
    have ⟨ha, hl⟩ := List.nodup_cons.mp hs
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨emitList_nodup _ (hr a List.mem_cons_self) _ _ _, ih hl (fun b hb => hr b (List.mem_cons_of_mem _ hb)), ?_⟩
    intro y hy z hz e
    subst e
    have k1 := ((mem_emitList _ _ _ _ y).mp hy).1
    have k2 := ((mem_flatMap_emit dirFwd l rf selff y).mp hz).1
    rw [k1] at k2
    exact ha k2

/-! ## The rounds from a restriction -/

/-- A restriction a step accepts: its values increasing (so in order and each
    once). -/
def RGood (R : Option (Array UInt64)) : Prop := ∀ cs, R = some cs → cs.toList.Pairwise (· < ·)

theorem restr_some (f : Bool) (F : Array UInt64) (p : UInt64 × UInt64) :
    Restr f (some F) p = F.contains (keyOf f p) := by
  cases f <;> rfl

theorem length_filter_split {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h]; omega
    · simp [List.filter_cons, h]; omega

theorem contains_foldl_insert (arr : Array UInt64) (hs : Std.HashSet UInt64) (y : UInt64) :
    (arr.foldl (fun h x => h.insert x) hs).contains y = true ↔ hs.contains y = true ∨ y ∈ arr.toList := by
  rw [← Array.foldl_toList]
  induction arr.toList generalizing hs with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h

/-- The nodes of `N` not yet visited. -/
def unvisited (N V : List UInt64) : Nat := (N.filter (fun n => decide (n ∉ V))).length

theorem unvisited_step (N V nx : List UInt64) (hN : N.Nodup) (hnx : nx.Nodup) (hsub : ∀ x ∈ nx, x ∈ N)
    (hdis : ∀ x ∈ nx, x ∉ V) : unvisited N (V ++ nx) + nx.length = unvisited N V := by
  unfold unvisited
  have hA : ((N.filter (fun n => decide (n ∉ V))).filter (fun n => decide (n ∈ nx))).Perm nx := by
    apply (List.perm_ext_iff_of_nodup ((hN.filter _).filter _) hnx).mpr
    intro x
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨⟨hsub x h, hdis x h⟩, h⟩
  have hB : (N.filter (fun n => decide (n ∉ V))).filter (fun n => !decide (n ∈ nx)) =
      N.filter (fun n => decide (n ∉ V ++ nx)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    by_cases h1 : x ∈ V <;> by_cases h2 : x ∈ nx <;> simp [h1, h2]
  have := length_filter_split (N.filter (fun n => decide (n ∉ V))) (fun n => decide (n ∈ nx))
  rw [hB, hA.length_eq] at this
  omega

section
variable (E : IdPairs) (N : List UInt64) (hN : N.Nodup) (hEN : ∀ p ∈ E, p.1 ∈ N ∧ p.2 ∈ N)
  (stepM : Bool → Option (Array UInt64) → ExceptT String Id (Pairs × ScanStats))
  (hstep : ∀ f R, RGood R → ∃ e s, stepM f R = pure (e, s) ∧ e.toList.Perm (E.filter (Restr f R)))
include hN hEN hstep

theorem other_mem (fwd : Bool) (p : UInt64 × UInt64) (hp : p ∈ E) : otherOf fwd p ∈ N := by
  cases fwd
  · exact (hEN p hp).1
  · exact (hEN p hp).2

/-- **The rounds of `closureRoundsM`.** From visited nodes `V` and a frontier
    `F` (increasing, visited), with the pairs of `E` from the visited nodes
    off the frontier collected and their other ends visited, within the
    round bound, the rounds end with every pair of `E` from a node they
    reach, and the nodes they reach closed under steps. -/
theorem rounds_spec (fwd : Bool) :
    ∀ (fuel : Nat) (visited : Std.HashSet UInt64) (F : Array UInt64) (edges : Pairs) (total : ScanStats)
      (V : List UInt64),
      (∀ x, visited.contains x = true ↔ x ∈ V) → F.toList.Pairwise (· < ·) → (∀ x ∈ F.toList, x ∈ V) →
      (∀ p, p ∈ edges.toList ↔ p ∈ E ∧ keyOf fwd p ∈ V ∧ keyOf fwd p ∉ F.toList) →
      (∀ v ∈ V, v ∉ F.toList → ∀ p ∈ E, keyOf fwd p = v → otherOf fwd p ∈ V) →
      (F.toList = [] ∨ unvisited N V < fuel) →
      ∃ edges' total', closureRoundsM stepM fwd fuel visited F edges total = pure (edges', total') ∧
        ∃ V' : List UInt64, (∀ x ∈ V, x ∈ V') ∧ (∀ p, p ∈ edges'.toList ↔ p ∈ E ∧ keyOf fwd p ∈ V') ∧
          (∀ v ∈ V', ∀ p ∈ E, keyOf fwd p = v → otherOf fwd p ∈ V') := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited F edges total V _ _ _ hed hcl hfu
    have hF : F.toList = [] := by rcases hfu with h | h; exact h; omega
    have hFe : F.isEmpty = true := by simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, hF]
    refine ⟨edges, total, by simp [closureRoundsM, hFe], V, fun _ h => h, ?_, ?_⟩
    · intro p; rw [hed p, hF]; simp
    · intro v hv p hp hk; exact hcl v hv (by rw [hF]; simp) p hp hk
  | succ n ih =>
    intro visited F edges total V hvis hFs hFV hed hcl hfu
    by_cases hFe : F.isEmpty = true
    · have hF : F.toList = [] := by simpa [Array.isEmpty_iff, ← Array.toList_eq_nil_iff] using hFe
      refine ⟨edges, total, by simp [closureRoundsM, hFe], V, fun _ h => h, ?_, ?_⟩
      · intro p; rw [hed p, hF]; simp
      · intro v hv p hp hk; exact hcl v hv (by rw [hF]; simp) p hp hk
    · have hFne : F.toList ≠ [] := fun h => hFe (by simp [Array.isEmpty_iff, ← Array.toList_eq_nil_iff, h])
      obtain ⟨e, s, hse, hep⟩ := hstep fwd (some F) (fun cs h => by cases h; exact hFs)
      -- the new frontier
      generalize hsd : (if fwd then IdPath.seconds e else IdPath.firsts e) = sd
      have hsd_spec : sd.toList.Pairwise (· < ·) ∧ ∀ x, x ∈ sd.toList ↔ ∃ p ∈ e.toList, otherOf fwd p = x := by
        rw [← hsd]
        cases fwd
        · exact ⟨(IdPath.sortedDistinct_spec _).1, fun x => by
            simp only [Bool.false_eq_true, if_false]; rw [IdPath.firsts_mem]; rfl⟩
        · exact ⟨(IdPath.sortedDistinct_spec _).1, fun x => by
            simp only [if_true]; rw [IdPath.seconds_mem]; rfl⟩
      generalize hnx : sd.filter (fun x => !visited.contains x) = nx
      have hnxl : nx.toList = sd.toList.filter (fun x => !visited.contains x) := by rw [← hnx, Array.toList_filter]
      have he_mem : ∀ p, p ∈ e.toList ↔ p ∈ E ∧ keyOf fwd p ∈ F.toList := by
        intro p
        rw [hep.mem_iff, List.mem_filter, restr_some, contains_iff]
      have hnx_mem : ∀ x, x ∈ nx.toList ↔ (∃ p ∈ e.toList, otherOf fwd p = x) ∧ x ∉ V := by
        intro x
        rw [hnxl, List.mem_filter, hsd_spec.2, Bool.not_eq_true', ← Bool.not_eq_true, hvis]
      have hnx_pw : nx.toList.Pairwise (· < ·) := by rw [hnxl]; exact hsd_spec.1.filter _
      have hnx_nd : nx.toList.Nodup := hnx_pw.imp (fun h => UInt64.ne_of_lt h)
      have hnx_N : ∀ x ∈ nx.toList, x ∈ N := by
        intro x hx
        obtain ⟨⟨p, hp, rfl⟩, _⟩ := (hnx_mem x).mp hx
        exact other_mem E N hN hEN stepM hstep fwd p ((he_mem p).mp hp).1
      have hnx_V : ∀ x ∈ nx.toList, x ∉ V := fun x hx => ((hnx_mem x).mp hx).2
      have hvis' : ∀ x, (nx.foldl (fun h x => h.insert x) visited).contains x = true ↔ x ∈ V ++ nx.toList := by
        intro x
        rw [contains_foldl_insert, hvis, List.mem_append]
      obtain ⟨edges', total', hr, V', hsub, hed', hcl'⟩ := ih (nx.foldl (fun h x => h.insert x) visited) nx
        (edges ++ e) (total.add s) (V ++ nx.toList) hvis' hnx_pw (fun x hx => List.mem_append_right _ hx)
        (by
          intro p
          rw [Array.toList_append, List.mem_append, hed p, he_mem p, List.mem_append]
          constructor
          · rintro (⟨hp, hv, hf⟩ | ⟨hp, hf⟩)
            · exact ⟨hp, Or.inl hv, fun h => hnx_V _ h hv⟩
            · exact ⟨hp, Or.inl (hFV _ hf), fun h => hnx_V _ h (hFV _ hf)⟩
          · rintro ⟨hp, hv | hv, hn⟩
            · by_cases hf : keyOf fwd p ∈ F.toList
              · exact Or.inr ⟨hp, hf⟩
              · exact Or.inl ⟨hp, hv, hf⟩
            · exact absurd hv hn)
        (by
          intro v hv hvn p hp hk
          rw [List.mem_append] at hv ⊢
          rcases hv with hv | hv
          · by_cases hf : v ∈ F.toList
            · have hpe : p ∈ e.toList := (he_mem p).mpr ⟨hp, hk ▸ hf⟩
              by_cases hoV : otherOf fwd p ∈ V
              · exact Or.inl hoV
              · exact Or.inr ((hnx_mem _).mpr ⟨⟨p, hpe, rfl⟩, hoV⟩)
            · exact Or.inl (hcl v hv hf p hp hk)
          · exact absurd hv hvn)
        (by
          by_cases h0 : nx.toList = []
          · exact Or.inl h0
          · right
            have hstp := unvisited_step N V nx.toList hN hnx_nd hnx_N hnx_V
            have hlen : 0 < nx.toList.length := List.length_pos_iff.mpr h0
            rcases hfu with h | h
            · exact absurd h hFne
            · omega)
      refine ⟨edges', total', ?_, V', fun x hx => hsub x (List.mem_append_left _ hx), hed', hcl'⟩
      simp only [closureRoundsM, hFe, if_false, Bool.false_eq_true]
      rw [hse]
      simp only [pure_bind]
      rw [hsd, hnx]
      exact hr

end

/-! ## Reaching over a part of the relation -/

theorem reach_mono {A B : IdPairs} (h : ∀ q ∈ A, q ∈ B) {a c : UInt64} (r : Reach A a c) : Reach B a c := by
  induction r with
  | refl => exact .refl _
  | tail _ h2 ih => exact .tail ih (h _ h2)

theorem reach1_congr {A B : IdPairs} (h : ∀ q, q ∈ A ↔ q ∈ B) (a c : UInt64) : Reach1 A a c ↔ Reach1 B a c := by
  constructor
  · rintro ⟨b, hb, r⟩; exact ⟨b, (h _).mp hb, reach_mono (fun q hq => (h q).mp hq) r⟩
  · rintro ⟨b, hb, r⟩; exact ⟨b, (h _).mpr hb, reach_mono (fun q hq => (h q).mpr hq) r⟩

theorem reach1_of_last {E : IdPairs} {c b a : UInt64} (r : Reach E c b) (h : (b, a) ∈ E) : Reach1 E c a := by
  rcases IdPath.reach_cases r with rfl | ⟨b', h1, r1⟩
  · exact ⟨a, h, .refl _⟩
  · exact ⟨b', h1, .tail r1 h⟩

theorem last_of_reach1 {E : IdPairs} {c a : UInt64} (h : Reach1 E c a) : ∃ b, Reach E c b ∧ (b, a) ∈ E := by
  obtain ⟨b, hb, r⟩ := h
  induction r with
  | refl => exact ⟨c, .refl _, hb⟩
  | @tail b2 a2 r' h2 _ => exact ⟨b2, Reach.head hb r', h2⟩

/-- Reaching in one or more steps over the converse relation. -/
theorem reach1_swap (E : IdPairs) (a c : UInt64) :
    Reach1 (E.map (fun p => (p.2, p.1))) a c ↔ Reach1 E c a := by
  constructor
  · rintro ⟨b, hb, r⟩
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hb
    have e1 : q.2 = a := (Prod.mk.inj he).1
    have e2 : q.1 = b := (Prod.mk.inj he).2
    have hq' : (b, a) ∈ E := by rw [← e1, ← e2]; exact hq
    exact reach1_of_last ((IdPath.reach_swap E b c).mp r) hq'
  · intro h
    obtain ⟨b, r, hb⟩ := last_of_reach1 h
    exact ⟨b, List.mem_map.mpr ⟨(b, a), hb, rfl⟩, (IdPath.reach_swap E b c).mpr r⟩

theorem reach_closed {D : IdPairs} {V : List UInt64} (hcl : ∀ v ∈ V, ∀ w, (v, w) ∈ D → w ∈ V) {a x : UInt64}
    (ha : a ∈ V) (r : Reach D a x) : x ∈ V := by
  induction r with
  | refl => exact ha
  | tail _ h ih => exact hcl _ ih _ h

/-- Over the pairs of `D` from a set `V` closed under `D`, a node of `V`
    reaches what it reaches over `D`. -/
theorem reach1_restrict (D E' : IdPairs) (V : List UInt64) (hE' : ∀ p, p ∈ E' ↔ p ∈ D ∧ p.1 ∈ V)
    (hcl : ∀ v ∈ V, ∀ w, (v, w) ∈ D → w ∈ V) (a : UInt64) (ha : a ∈ V) (c : UInt64) :
    Reach1 E' a c ↔ Reach1 D a c := by
  constructor
  · rintro ⟨b, hb, r⟩
    exact ⟨b, ((hE' _).mp hb).1, reach_mono (fun q hq => ((hE' q).mp hq).1) r⟩
  · rintro ⟨b, hb, r⟩
    have hbV : b ∈ V := hcl a ha b hb
    refine ⟨b, (hE' _).mpr ⟨hb, ha⟩, ?_⟩
    exact (IdPath.reach_restrict D E' b (fun q hq => ((hE' q).mp hq).1)
      (fun x y rx hxy => (hE' _).mpr ⟨hxy, reach_closed hcl hbV rx⟩) c).mp r

/-! ## `closureEdgesM` and `closureM` -/

/-- The converse of a relation, as a list. -/
def swapL (l : IdPairs) : IdPairs := l.map (fun p => (p.2, p.1))

theorem swap_toList (r : Pairs) : (IdPath.swap r).toList = swapL r.toList := by
  unfold IdPath.swap swapL
  rw [Array.toList_map]

theorem mem_swapL (l : IdPairs) (p : UInt64 × UInt64) : p ∈ swapL l ↔ (p.2, p.1) ∈ l := by
  unfold swapL
  rw [List.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact hq
  · intro h; exact ⟨(p.2, p.1), h, rfl⟩

open L4Factoidal.Storage.Sbm11.BgpTableTheorems (BgpStore)

section
variable (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T) (E : IdPairs)
  (hEN : ∀ p ∈ E, p.1 ∈ idGraphNodes T ∧ p.2 ∈ idGraphNodes T)
  (stepM : Bool → Option (Array UInt64) → ExceptT String Id (Pairs × ScanStats))
  (hstep : ∀ f R, RGood R → ∃ e s, stepM f R = pure (e, s) ∧ e.toList.Perm (E.filter (Restr f R)))
include hst hEN hstep

/-- The start nodes `closureEdgesM` gives. -/
def SrcSpec (E : IdPairs) (N : List UInt64) (R : Option (Array UInt64)) (zero : Bool) (a : UInt64) : Prop :=
  match R with
  | none => if zero then a ∈ N else ∃ b, (a, b) ∈ E
  | some rs => a ∈ rs.toList

/-- **`closureEdgesM`**: start nodes each once, the reflexive nodes among
    them, and pairs over which every start node reaches what it reaches
    over `E` (over the converse for an object restriction). -/
theorem closureEdges_spec (fwd : Bool) (R : Option (Array UInt64)) (hR : RGood R) (zero : Bool) :
    ∃ edges sources nodes total, closureEdgesM st (some g) stepM fwd R zero = pure (edges, sources, nodes, total) ∧
      sources.toList.Nodup ∧
      (∀ n, n ∈ nodes.toList ↔ zero = true ∧ n ∈ idGraphNodes T ∧ n ∈ sources.toList) ∧
      (∀ a ∈ sources.toList, ∀ c, Reach1 (if R.isNone || fwd then edges.toList else swapL edges.toList) a c ↔
        Reach1 (if R.isNone || fwd then E else swapL E) a c) ∧
      (∀ a, a ∈ sources.toList ↔ SrcSpec E (idGraphNodes T) R zero a) := by
  have hN := IdPath.nodes_nodup T
  cases R with
  | none =>
    obtain ⟨e, s, hse, hep⟩ := hstep true none (fun _ h => by cases h)
    have hem : ∀ q, q ∈ e.toList ↔ q ∈ E := by
      intro q; rw [hep.mem_iff, List.mem_filter]; simp [Restr]
    have hreach : ∀ a c, Reach1 e.toList a c ↔ Reach1 E a c := fun a c => reach1_congr hem a c
    cases zero with
    | true =>
      obtain ⟨ns, s0, hns, hpw, hmem⟩ := IdPathScanTheorems.allNodes_spec st g T hst
      refine ⟨e, ns, ns, s.add s0, ?_, hpw.imp (fun h => UInt64.ne_of_lt h), ?_, ?_, ?_⟩
      · unfold closureEdgesM
        simp only []
        rw [hse]
        simp only [pure_bind, if_true]
        rw [hns]
        rfl
      · intro n; rw [hmem]; simp
      · intro a _ c; exact hreach a c
      · intro a; rw [hmem]; rfl
    | false =>
      refine ⟨e, IdPath.firsts e, #[], s, ?_, IdPath.sortedDistinct_nodup _, ?_, ?_, ?_⟩
      · unfold closureEdgesM
        simp only []
        rw [hse]
        rfl
      · intro n; simp
      · intro a _ c; exact hreach a c
      · intro a
        rw [IdPath.firsts_mem]
        show _ ↔ ∃ b, (a, b) ∈ E
        constructor
        · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, (hem p).mp hp⟩
        · rintro ⟨b, hb⟩; exact ⟨(a, b), (hem _).mpr hb, rfl⟩
  | some rs =>
    have hrs : rs.toList.Pairwise (· < ·) := hR rs rfl
    have hrsS : Sip.Sorted rs := IdPath.sorted_of_pairwise rs hrs
    -- the reflexive nodes
    obtain ⟨nodes, s0, hnodes, hnmem⟩ : ∃ nodes s0, (if zero then nodesAmongM st (some g) rs else pure (#[], {}) :
        ExceptT String Id (Array UInt64 × ScanStats)) = pure (nodes, s0) ∧
        ∀ n, n ∈ nodes.toList ↔ zero = true ∧ n ∈ idGraphNodes T ∧ n ∈ rs.toList := by
      cases zero with
      | true =>
        obtain ⟨ns, s0, h1, _, h3⟩ := IdPathScanTheorems.nodesAmong_spec st g T hst rs hrsS
        exact ⟨ns, s0, h1, fun n => by rw [h3]; simp [and_comm]⟩
      | false => exact ⟨#[], {}, rfl, fun n => by simp⟩
    obtain ⟨fuel, hfuel, hfle⟩ := IdPathScanTheorems.pathFuel_ge st g T hst rs.size
    have hvis : ∀ x, (rs.foldl (fun h x => h.insert x) ({} : Std.HashSet UInt64)).contains x = true ↔
        x ∈ rs.toList := by
      intro x; rw [contains_foldl_insert]; simp
    have hstep' := hstep
    obtain ⟨edges, total, hr, V', hsub, hed, hcl⟩ := rounds_spec E (idGraphNodes T) hN hEN stepM hstep' fwd fuel
      _ rs #[] s0 rs.toList hvis hrs (fun _ h => h) (by intro p; simp) (by intro v hv hn; exact absurd hv hn)
      (by
        right
        have : IdPathClosureExec.unvisited (idGraphNodes T) rs.toList ≤ (idGraphNodes T).length :=
          List.length_filter_le _ _
        omega)
    refine ⟨edges, rs, nodes, total, ?_, hrs.imp (fun h => UInt64.ne_of_lt h), hnmem, ?_, fun a => Iff.rfl⟩
    · unfold closureEdgesM
      simp only []
      cases zero <;> simp only [if_true, if_false, Bool.false_eq_true] at hnodes ⊢ <;>
        (rw [hnodes]; simp only [pure_bind]; rw [hfuel]; simp only [pure_bind]; rw [hr]; rfl)
    · intro a ha c
      have haV : a ∈ V' := hsub a ha
      cases fwd with
      | true =>
        simp only [Option.isNone_some, Bool.false_or, if_true]
        exact reach1_restrict E edges.toList V' (fun p => by rw [hed p]; rfl)
          (fun v hv w hw => hcl v hv (v, w) hw rfl) a haV c
      | false =>
        simp only [Option.isNone_some, Bool.false_or, Bool.false_eq_true, if_false]
        refine reach1_restrict (swapL E) (swapL edges.toList) V' (fun p => ?_) (fun v hv w hw => ?_) a haV c
        · rw [mem_swapL, hed, mem_swapL]; rfl
        · rw [mem_swapL] at hw
          exact hcl v hv (w, v) hw rfl

end

/-- The pairs of the reference's closure over ids (`IdPathClosureTheorems`:
    `star_mem` for `p*`, `plus_mem` for `p+`). -/
def ClosMem (E : IdPairs) (N : List UInt64) (zero : Bool) (x : UInt64 × UInt64) : Prop :=
  if zero then x.1 ∈ N ∧ Reach E x.1 x.2 else Reach1 E x.1 x.2

theorem reach_iff {E : IdPairs} {a c : UInt64} : Reach E a c ↔ a = c ∨ Reach1 E a c :=
  ⟨IdPath.reach_cases, fun h => h.elim (fun e => e ▸ .refl _) IdPath.reach1_reach⟩

theorem reach1_first {E : IdPairs} {N : List UInt64} (hEN : ∀ p ∈ E, p.1 ∈ N ∧ p.2 ∈ N) {a c : UInt64}
    (h : Reach1 E a c) : a ∈ N := by
  obtain ⟨b, hb, _⟩ := h; exact (hEN _ hb).1

theorem reach1_last {E : IdPairs} {N : List UInt64} (hEN : ∀ p ∈ E, p.1 ∈ N ∧ p.2 ∈ N) {a c : UInt64}
    (h : Reach1 E a c) : c ∈ N := by
  obtain ⟨b, _, hb⟩ := last_of_reach1 h; exact (hEN _ hb).2

theorem closMem_fwd (E : IdPairs) (N : List UInt64) (hEN : ∀ p ∈ E, p.1 ∈ N ∧ p.2 ∈ N) (zero : Bool)
    (a c : UInt64) (inS : Prop) :
    (inS ∧ ((zero = true ∧ a ∈ N ∧ inS) ∧ c = a ∨ Reach1 E a c)) ↔ ClosMem E N zero (a, c) ∧ inS := by
  unfold ClosMem
  cases zero with
  | true =>
    simp only [if_true, true_and]
    rw [reach_iff]
    constructor
    · rintro ⟨hi, ⟨⟨ha, _⟩, rfl⟩ | h⟩
      · exact ⟨⟨ha, .inl rfl⟩, hi⟩
      · exact ⟨⟨reach1_first hEN h, .inr h⟩, hi⟩
    · rintro ⟨⟨ha, rfl | h⟩, hi⟩
      · exact ⟨hi, .inl ⟨⟨ha, hi⟩, rfl⟩⟩
      · exact ⟨hi, .inr h⟩
  | false =>
    simp only [Bool.false_eq_true, if_false, false_and, false_or]
    constructor
    · rintro ⟨hi, h⟩; exact ⟨h, hi⟩
    · rintro ⟨h, hi⟩; exact ⟨hi, h⟩

theorem closMem_bwd (E : IdPairs) (N : List UInt64) (hEN : ∀ p ∈ E, p.1 ∈ N ∧ p.2 ∈ N) (zero : Bool)
    (a c : UInt64) (inS : Prop) :
    (inS ∧ ((zero = true ∧ c ∈ N ∧ inS) ∧ a = c ∨ Reach1 E a c)) ↔ ClosMem E N zero (a, c) ∧ inS := by
  unfold ClosMem
  cases zero with
  | true =>
    simp only [if_true, true_and]
    rw [reach_iff]
    constructor
    · rintro ⟨hi, ⟨⟨hc, _⟩, rfl⟩ | h⟩
      · exact ⟨⟨hc, .inl rfl⟩, hi⟩
      · exact ⟨⟨reach1_first hEN h, .inr h⟩, hi⟩
    · rintro ⟨⟨ha, rfl | h⟩, hi⟩
      · exact ⟨hi, .inl ⟨⟨ha, hi⟩, rfl⟩⟩
      · exact ⟨hi, .inr h⟩
  | false =>
    simp only [Bool.false_eq_true, if_false, false_and, false_or]
    constructor
    · rintro ⟨hi, h⟩; exact ⟨h, hi⟩
    · rintro ⟨h, hi⟩; exact ⟨hi, h⟩

section
variable (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T) (E : IdPairs)
  (hEN : ∀ p ∈ E, p.1 ∈ idGraphNodes T ∧ p.2 ∈ idGraphNodes T)
  (stepM : Bool → Option (Array UInt64) → ExceptT String Id (Pairs × ScanStats))
  (hstep : ∀ f R, RGood R → ∃ e s, stepM f R = pure (e, s) ∧ e.toList.Perm (E.filter (Restr f R)))
include hst hEN hstep

/-- **`closureM`**: each pair once, and exactly the pairs of the reference's
    closure that the restriction keeps. -/
theorem closureM_spec (fwd : Bool) (R : Option (Array UInt64)) (hR : RGood R) (zero : Bool) :
    ∃ out s, closureM st (some g) stepM fwd R zero = pure (out, s) ∧ out.toList.Nodup ∧
      ∀ x, x ∈ out.toList ↔ ClosMem E (idGraphNodes T) zero x ∧ Restr fwd R x = true := by
  obtain ⟨edges, sources, nodes, total, he, hsn, hnodes, hreach, hsrc⟩ :=
    closureEdges_spec st g T hst E hEN stepM hstep fwd R hR zero
  generalize hd : (R.isNone || fwd) = d at hreach
  have hEl : (if d then edges else IdPath.swap edges).toList = if d then edges.toList else swapL edges.toList := by
    cases d
    · simp only [Bool.false_eq_true, if_false]; exact swap_toList edges
    · rfl
  have hlen : (if d then edges else IdPath.swap edges).toList.length + 2 ≤ edges.size + 2 := by
    cases d <;> simp [IdPath.swap]
  -- the worklist of each start node
  have hrp : ∀ a, ∃ r, reachPlus (adjOf (if d then edges else IdPath.swap edges)) a (edges.size + 2) = some r ∧
      r.toList.Nodup ∧ ∀ c, c ∈ r.toList ↔ Reach1 (if d then edges.toList else swapL edges.toList) a c := by
    intro a
    obtain ⟨l, hl⟩ := IdPath.reachModel_some _ a _ hlen
    have he2 := IdPath.reachPlus_eq (if d then edges else IdPath.swap edges) a (edges.size + 2)
    rw [hl] at he2
    cases hrp : reachPlus (adjOf (if d then edges else IdPath.swap edges)) a (edges.size + 2) with
    | none => rw [hrp] at he2; cases he2
    | some r =>
      rw [hrp] at he2
      have hrl : r.toList = l := Option.some.inj he2
      obtain ⟨hnd, hm⟩ := IdPath.reachModel_mem _ a _ l hl
      refine ⟨r, rfl, hrl ▸ hnd, fun c => ?_⟩
      rw [hrl, hm, hEl]
  obtain ⟨out, hout, ht⟩ := emit_all (adjOf (if d then edges else IdPath.swap edges))
    (nodes.foldl (fun h x => h.insert x) {}) zero d (edges.size + 2) sources
    (fun a _ => by obtain ⟨r, hr, _⟩ := hrp a; rw [hr]; rfl)
  refine ⟨out, total, ?_, ?_, ?_⟩
  · unfold closureM
    simp only []
    rw [he]
    simp only [pure_bind]
    rw [hd, hout]
    rfl
  · rw [ht]
    apply flatMap_emit_nodup d _ hsn
    intro a _
    obtain ⟨r, hr, hnd, _⟩ := hrp a
    rw [hr]; exact hnd
  · have hself : ∀ a, (zero && (nodes.foldl (fun h x => h.insert x) ({} : Std.HashSet UInt64)).contains a) = true ↔
        zero = true ∧ a ∈ idGraphNodes T ∧ a ∈ sources.toList := by
      intro a
      rw [Bool.and_eq_true, contains_foldl_insert, hnodes]
      simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_or]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h.1, h⟩
    have hL : ∀ x, x ∈ out.toList ↔ keyOf d x ∈ sources.toList ∧
        ((zero = true ∧ keyOf d x ∈ idGraphNodes T ∧ keyOf d x ∈ sources.toList) ∧ otherOf d x = keyOf d x ∨
          Reach1 (if d then E else swapL E) (keyOf d x) (otherOf d x)) := by
      intro x
      rw [ht, mem_flatMap_emit]
      constructor
      · rintro ⟨hk, h | h⟩
        · exact ⟨hk, .inl ⟨(hself _).mp h.1, h.2⟩⟩
        · obtain ⟨r, hr, _, hm⟩ := hrp (keyOf d x)
          rw [hr] at h
          exact ⟨hk, .inr ((hreach _ hk _).mp ((hm _).mp h))⟩
      · rintro ⟨hk, h | h⟩
        · exact ⟨hk, .inl ⟨(hself _).mpr h.1, h.2⟩⟩
        · obtain ⟨r, hr, _, hm⟩ := hrp (keyOf d x)
          refine ⟨hk, .inr ?_⟩
          rw [hr]
          exact (hm _).mpr ((hreach _ hk _).mpr h)
    intro x
    rw [hL]
    cases R with
    | none =>
      have hd' : d = true := by rw [← hd]; rfl
      subst hd'
      simp only [if_true]
      show (x.1 ∈ sources.toList ∧ ((zero = true ∧ x.1 ∈ idGraphNodes T ∧ x.1 ∈ sources.toList) ∧ x.2 = x.1 ∨
        Reach1 E x.1 x.2)) ↔ _
      rw [closMem_fwd E _ hEN zero x.1 x.2]
      have hsx : ClosMem E (idGraphNodes T) zero (x.1, x.2) → x.1 ∈ sources.toList := by
        intro hc
        rw [hsrc]
        unfold SrcSpec ClosMem at *
        cases zero with
        | true => exact hc.1
        | false => obtain ⟨b, hb, _⟩ := hc; exact ⟨b, hb⟩
      constructor
      · rintro ⟨hc, _⟩; exact ⟨hc, rfl⟩
      · rintro ⟨hc, _⟩; exact ⟨hc, hsx hc⟩
    | some rs =>
      have hsr : ∀ a, a ∈ sources.toList ↔ a ∈ rs.toList := hsrc
      cases fwd with
      | true =>
        have hd' : d = true := by rw [← hd]; rfl
        subst hd'
        simp only [if_true]
        show (x.1 ∈ sources.toList ∧ ((zero = true ∧ x.1 ∈ idGraphNodes T ∧ x.1 ∈ sources.toList) ∧ x.2 = x.1 ∨
          Reach1 E x.1 x.2)) ↔ _
        rw [closMem_fwd E _ hEN zero x.1 x.2, hsr, restr_some, contains_iff]
        rfl
      | false =>
        have hd' : d = false := by rw [← hd]; rfl
        subst hd'
        simp only [Bool.false_eq_true, if_false]
        show (x.2 ∈ sources.toList ∧ ((zero = true ∧ x.2 ∈ idGraphNodes T ∧ x.2 ∈ sources.toList) ∧ x.1 = x.2 ∨
          Reach1 (swapL E) x.2 x.1)) ↔ _
        rw [show Reach1 (swapL E) x.2 x.1 ↔ Reach1 E x.1 x.2 from reach1_swap E x.2 x.1]
        rw [closMem_bwd E _ hEN zero x.1 x.2, hsr, restr_some, contains_iff]
        rfl

end

end L4Factoidal.Storage.Sbm11.IdPathClosureExec

#print axioms L4Factoidal.Storage.Sbm11.IdPathClosureExec.closureM_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPathClosureExec.closureEdges_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPathClosureExec.rounds_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPathClosureExec.emit_all
