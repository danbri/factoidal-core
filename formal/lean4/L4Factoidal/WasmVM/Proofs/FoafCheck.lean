/-
L4Factoidal.WasmVM.Proofs.FoafCheck: the FOAF overlap-check kernel
(labs/demos/foafnaut/wasm/foaf-check.wat, as assembled) under the WebAssembly SPEC
semantics computes `FoafCheckSpec.flagsK` and `certifyK`, which are the Lean certificate
`LayoutPolicy.checkFootprints` / `certify` (record:
docs/designissues/2026-11-09-verified-foaf-layout.md).

The body below is what WasmVM's decoder and `KI.parseBody` make of the assembled bytes;
`FoafCheckBinary.lean` checks that, by kernel evaluation, on the bytes themselves.
-/
import L4Factoidal.WasmVM.Proofs.SpecWPSubset
import L4Factoidal.WasmVM.Proofs.FoafCheckSpec

namespace L4Factoidal.WasmVM.Proofs.FoafCheck
open L4Factoidal.WasmVM Proofs.SpecWP Proofs.Refine L4Factoidal.UI.Geometry

/-! ### The kernel, as decoded -/

/-- The overlap of box `i` with box `j` (`j ≠ i`), added to the sum. -/
noncomputable def ifBody : KIs := ks [
  .localGet 2, .localGet 5, .i32const 16, .i32mul, .i32add, .localSet 7,
  .localGet 11, .localGet 7, .load32 8, .i64extu, .localTee 15, .localGet 11, .localGet 15, .i64lts, .select,
  .localGet 9, .localGet 7, .load32 0, .i64extu, .localTee 16, .localGet 9, .localGet 16, .i64gts, .select,
  .i64sub, .localTee 15, .i64const 0, .localGet 15, .i64const 0, .i64gts, .select, .localSet 15,
  .localGet 12, .localGet 7, .load32 12, .i64extu, .localTee 16, .localGet 12, .localGet 16, .i64lts, .select,
  .localGet 10, .localGet 7, .load32 4, .i64extu, .localTee 16, .localGet 10, .localGet 16, .i64gts, .select,
  .i64sub, .localTee 16, .i64const 0, .localGet 16, .i64const 0, .i64gts, .select,
  .localGet 15, .i64mul, .localGet 14, .i64add, .localSet 14]

/-- One step of the inner loop, over `j`. -/
noncomputable def innerBody : KIs := ks [
  .localGet 5, .localGet 0, .i32geu, .brIf 1,
  .localGet 5, .localGet 4, .i32ne, .ifThen ifBody,
  .localGet 5, .i32const 1, .i32add, .localSet 5, .br 0]

/-- Box `i`, its area, and a zero sum. -/
def outerHead : List KI := [
  .localGet 4, .localGet 0, .i32geu, .brIf 1,
  .localGet 2, .localGet 4, .i32const 16, .i32mul, .i32add, .localSet 7,
  .localGet 7, .load32 0, .i64extu, .localSet 9,
  .localGet 7, .load32 4, .i64extu, .localSet 10,
  .localGet 7, .load32 8, .i64extu, .localSet 11,
  .localGet 7, .load32 12, .i64extu, .localSet 12,
  .localGet 11, .localGet 9, .i64sub, .localTee 15, .i64const 0, .localGet 15, .i64const 0, .i64gts, .select,
  .localGet 12, .localGet 10, .i64sub, .localTee 16, .i64const 0, .localGet 16, .i64const 0, .i64gts, .select,
  .i64mul, .localSet 13, .i64const 0, .localSet 14, .i32const 0, .localSet 5]

/-- The flag of box `i`, its store, and the running result. -/
def outerTail : List KI := [
  .localGet 14, .i64const 10000, .i64mul, .localGet 1, .i64extu, .localGet 13, .i64mul, .i64les,
  .i32const 0, .localGet 13, .i64const 0, .i64gts, .select, .localSet 8,
  .localGet 3, .localGet 4, .i32const 4, .i32mul, .i32add, .localGet 8, .store32 0,
  .localGet 6, .i32const 0, .localGet 8, .select, .localSet 6,
  .localGet 4, .i32const 1, .i32add, .localSet 4, .br 0]

noncomputable def outerBody : KIs := ks (outerHead ++ [.block (ks [.loop innerBody])] ++ outerTail)

/-- The function body of `check`. -/
noncomputable def checkBody : KIs := ks [.i32const 1, .localSet 6, .block (ks [.loop outerBody]), .localGet 6]

/-! ### Locals

Parameters 0 `n`, 1 `bps`, 2 `boxes`, 3 `out`; i32 locals 4 `i`, 5 `j`, 6 `all`, 7 `p`,
8 `ok`; i64 locals 9 `l`, 10 `t`, 11 `r`, 12 `b`, 13 `area`, 14 `sum`, 15 `u`, 16 `v`. -/
noncomputable def locs (n bps boxes out i j all p ok : Nat) (l t r b area sum u v : Int) :
    List (Option Spec.val) :=
  [some (i32v n), some (i32v bps), some (i32v boxes), some (i32v out), some (i32v i), some (i32v j),
   some (i32v all), some (i32v p), some (i32v ok), some (i64v l), some (i64v t), some (i64v r),
   some (i64v b), some (i64v area), some (i64v sum), some (i64v u), some (i64v v)]

noncomputable abbrev st (S : Spec.store) (M : Spec.moduleinst) (L : List (Option Spec.val)) : Spec.state :=
  .mk_state S ⟨L, M⟩

/-- The bytes of box coordinates as the page writes them: four little-endian i32. -/
def BoxesAt (B : List Spec.byte) (boxes : Nat) (bx : List Box) : Prop :=
  ∀ j < bx.length,
    List.take 4 (List.drop (boxes + 16 * j + 0) B) = Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN bx[j]!.left.toNat)) ∧
    List.take 4 (List.drop (boxes + 16 * j + 4) B) = Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN bx[j]!.top.toNat)) ∧
    List.take 4 (List.drop (boxes + 16 * j + 8) B) = Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN bx[j]!.right.toNat)) ∧
    List.take 4 (List.drop (boxes + 16 * j + 12) B) = Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN bx[j]!.bottom.toNat))

/-- Coordinates in `[0, 2^15)`. -/
def Coord (x : Int) : Prop := 0 ≤ x ∧ x < 2^15

def BoxOk (b : Box) : Prop := Coord b.left ∧ Coord b.top ∧ Coord b.right ∧ Coord b.bottom

macro "wnorm" : tactic => `(tactic| simp only [with_local_mk, List.set_cons_succ, List.set_cons_zero,
  ite01_mod, ite_not, ite_i64v, ite_i32v, ite_lt_min, ite_gt_max, Int.natCast_zero, Int.cast_ofNat_Int])

theorem semR_load32' {z stk a off rest Q} {B : BrPost} {Bs : List Spec.byte} {E k : Nat}
    (hB : (Spec.fun_mem z (.mk_uN 0)).BYTES = Bs)
    (hb : List.take 4 (List.drop E Bs) = Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN k)))
    (he : a % 2^32 + off = E) (hk : k < 2^32)
    (h : SemR z (i32v k :: stk) rest Q B) :
    SemR z (i32v a :: stk) (.LOAD .I32 none (.mk_uN 0) (ma4 off) :: rest) Q B :=
  semR_load32 hk (by rw [hB, he]; exact hb) h

/-- `i32.load` of a coordinate, then `i64.extend_i32_u`: the coordinate as an i64. -/
macro "wload" hm:term:max hb:term:max : tactic => `(tactic| (
  refine semR_load32' (by rw [fun_mem_mk]; exact $hm) $hb (by omega) (by omega) ?_
  refine semR_i64extu (by omega) ?_
  simp (disch := omega) only [Int.toNat_of_nonneg]))

macro "wstep" : tactic => `(tactic| first
  | refine semR_localGet rfl ?_
  | (refine semR_localSet ?_; wnorm)
  | (refine semR_localTee ?_; wnorm)
  | refine semR_i32const (by decide) ?_
  | (refine semR_i64const (by decide) ?_; try wnorm)
  | refine semR_i64extu (by omega) ?_
  | refine semR_i64add ?_
  | refine semR_i64sub ?_
  | refine semR_i64mul ?_
  | refine semR_i32add ?_
  | refine semR_i32mul ?_
  | refine semR_i64gts (by omega) (by omega) (by omega) (by omega) ?_
  | refine semR_i64lts (by omega) (by omega) (by omega) (by omega) ?_
  | refine semR_i64les (by omega) (by omega) (by omega) (by omega) ?_
  | (refine semR_select ?_; wnorm))

/-! ### The inner `if`: one overlap added -/

theorem if_body (S : Spec.store) (M : Spec.moduleinst) (bx : List Box) (B : List Spec.byte)
    (n bps boxes out i j all p ok : Nat) (l t r b area sum u v : Int) (rest : List Spec.instr) (Q : Post) (Bk B' : BrPost)
    (hmem : (S.MEMS[M.MEMS[0]!]!).BYTES = B) (hbx : BoxesAt B boxes bx) (hok : ∀ c ∈ bx, BoxOk c)
    (hj : j < bx.length) (haddr : boxes + 16 * j < 2^32)
    (hl : Coord l) (ht : Coord t) (hr : Coord r) (hb : Coord b)
    (k : ∀ p' u' v', Sem (st S M (locs n bps boxes out i j all p' ok l t r b area
        (sum + pos (min r bx[j]!.right - max l bx[j]!.left) * pos (min b bx[j]!.bottom - max t bx[j]!.top)) u' v'))
        [] rest Q Bk) :
    SemR (st S M (locs n bps boxes out i j all p ok l t r b area sum u v)) [] (KI.toSpecs ifBody)
      (fun z' vs' => Sem z' vs' rest Q Bk) B' := by
  simp only [ifBody, toSpecs_ks, List.map, KI.toSpec, locs]
  obtain ⟨b0, b4, b8, b12⟩ := hbx j hj
  have hc : BoxOk bx[j]! := hok _ (by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj])
  obtain ⟨⟨hc1, hc2⟩, ⟨hc3, hc4⟩, ⟨hc5, hc6⟩, ⟨hc7, hc8⟩⟩ := hc
  obtain ⟨hl1, hl2⟩ := hl; obtain ⟨ht1, ht2⟩ := ht; obtain ⟨hr1, hr2⟩ := hr; obtain ⟨hb1, hb2⟩ := hb
  repeat wstep
  wload hmem b8
  repeat wstep
  wload hmem b0
  repeat wstep
  wload hmem b12
  repeat wstep
  wload hmem b4
  repeat wstep
  refine semR_nil ?_
  have e : max (min b bx[j]!.bottom - max t bx[j]!.top) 0 * max (min r bx[j]!.right - max l bx[j]!.left) 0 + sum =
      sum + pos (min r bx[j]!.right - max l bx[j]!.left) * pos (min b bx[j]!.bottom - max t bx[j]!.top) := by
    simp only [pos]; rw [Int.mul_comm, Int.add_comm]
  rw [e]
  exact k _ _ _

theorem bx_ok {bx : List Box} {j : Nat} (hok : ∀ c ∈ bx, BoxOk c) (hj : j < bx.length) : BoxOk bx[j]! :=
  hok _ (by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hj])

/-! ### The inner loop: the overlap sum of box `i` -/

theorem inner_loop (S : Spec.store) (M : Spec.moduleinst) (bx : List Box) (B : List Spec.byte)
    (n bps boxes out i all ok : Nat) (area : Int)
    (hmem : (S.MEMS[M.MEMS[0]!]!).BYTES = B) (hbx : BoxesAt B boxes bx) (hok : ∀ c ∈ bx, BoxOk c)
    (hn : n = bx.length) (hn32 : n < 2^16) (haddr : boxes + 16 * n < 2^32) (hi : i < n) :
    ∀ m j p sum u v, n - j = m → j ≤ n → sum = sumTo bx i j →
    SemR (st S M (locs n bps boxes out i j all p ok bx[i]!.left bx[i]!.top bx[i]!.right bx[i]!.bottom area sum u v)) []
      [.LOOP (._RESULT none) (KI.toSpecs innerBody)]
      (fun _ _ => False)
      (fun k z' _ => k = 0 ∧ ∃ p' u' v', z' = st S M (locs n bps boxes out i n all p' ok
        bx[i]!.left bx[i]!.top bx[i]!.right bx[i]!.bottom area (sumTo bx i n) u' v')) := by
  have hci := bx_ok hok (show i < bx.length by omega)
  intro m
  induction m with
  | zero =>
    intro j p sum u v hm hj hs
    have hjn : j = n := by omega
    subst hjn
    refine semR_loop ?_
    simp only [innerBody, toSpecs_ks, List.map, KI.toSpec, locs]
    refine semR_localGet rfl ?_
    refine semR_localGet rfl ?_
    refine semR_i32geu (by omega) (by omega) ?_
    refine semR_brIf ?_
    rw [if_neg (by simp)]
    exact ⟨rfl, p, u, v, by rw [hs]⟩
  | succ m ih =>
    intro j p sum u v hm hj hs
    have hjn : j < n := by omega
    refine semR_loop ?_
    simp only [innerBody, toSpecs_ks, List.map, KI.toSpec, locs]
    refine semR_localGet rfl ?_
    refine semR_localGet rfl ?_
    refine semR_i32geu (by omega) (by omega) ?_
    refine semR_brIf ?_
    rw [if_pos ((ite01_mod _).mpr (by omega))]
    refine semR_localGet rfl ?_
    refine semR_localGet rfl ?_
    refine semR_i32ne ?_
    -- the code after the `if`: j + 1, then a branch back to the loop
    have hrest : ∀ p' u' v' sum', sum' = sumTo bx i (j + 1) →
        Sem (st S M (locs n bps boxes out i j all p' ok bx[i]!.left bx[i]!.top bx[i]!.right bx[i]!.bottom area sum' u' v')) []
          [.LOCAL_GET (.mk_uN 5), .CONST .I32 (.mk_num__0 .I32 (.mk_uN 1)), .BINOP .I32 (.mk_binop__0 .I32 .ADD),
           .LOCAL_SET (.mk_uN 5), .BR (.mk_uN 0)]
          (fun z' vs' => Sem z' vs' [] (fun _ _ => False)
            (fun k z' _ => k = 0 ∧ ∃ p' u' v', z' = st S M (locs n bps boxes out i n all p' ok
              bx[i]!.left bx[i]!.top bx[i]!.right bx[i]!.bottom area (sumTo bx i n) u' v')))
          (labelBr [] (fun z' => Sem z' [] [.LOOP (._RESULT none) (KI.toSpecs innerBody)] (fun _ _ => False)
            (fun k z' _ => k = 0 ∧ ∃ p' u' v', z' = st S M (locs n bps boxes out i n all p' ok
              bx[i]!.left bx[i]!.top bx[i]!.right bx[i]!.bottom area (sumTo bx i n) u' v')))
            (fun k z' _ => k = 0 ∧ ∃ p' u' v', z' = st S M (locs n bps boxes out i n all p' ok
              bx[i]!.left bx[i]!.top bx[i]!.right bx[i]!.bottom area (sumTo bx i n) u' v'))) := by
      intro p' u' v' sum' hs'
      show SemR _ [] _ _ _
      simp only [locs]
      refine semR_localGet rfl ?_
      refine semR_i32const (by decide) ?_
      refine semR_i32add ?_
      refine semR_localSet ?_
      wnorm
      refine semR_br ?_
      exact ih (j + 1) p' sum' u' v' (by omega) (by omega) hs'
    refine semR_if ?_
    by_cases hji : j = i
    · rw [if_pos ((ite01_mod _).mpr (by rw [hji]; simp))]
      exact hrest p u v sum (by rw [hs, sumTo, if_pos hji]; omega)
    · have hne : j % 2^32 ≠ i % 2^32 := by
        rw [Nat.mod_eq_of_lt (by omega : j < 2^32), Nat.mod_eq_of_lt (by omega : i < 2^32)]; exact hji
      rw [if_neg (fun h => (ite01_mod _).mp h hne)]
      have hc := hci
      obtain ⟨hl, ht, hr, hb⟩ := hc
      exact if_body S M bx B n bps boxes out i j all p ok _ _ _ _ area sum u v _ _ _ _ hmem hbx hok
        (by omega) (by omega) hl ht hr hb
        (fun p' u' v' => hrest p' u' v' _ (by rw [hs, sumTo, if_neg hji]; rfl))

/-! ### Memory: the flags the kernel writes, and the boxes they leave alone -/

/-- The four bytes of an i32 flag. -/
noncomputable def flagBytes (f : Bool) : List Spec.byte :=
  Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN (if f then 1 else 0)))

/-- Memory after the flags of nodes `0 .. i-1` are written at `out`, in order. -/
noncomputable def flagWrite (B : List Spec.byte) (out : Nat) (fl : List Bool) : Nat → List Spec.byte
  | 0 => B
  | i + 1 => Spec.list_slice_update (flagWrite B out fl i) (out + 4 * i) 4 (flagBytes fl[i]!)

theorem flagBytes_length (f : Bool) : (flagBytes f).length = 4 := by
  rw [flagBytes, nbytes_i32 _ (by split <;> decide)]; rfl

theorem flagWrite_length (B : List Spec.byte) (out : Nat) (fl : List Bool) (i : Nat)
    (h : out + 4 * i ≤ B.length) : (flagWrite B out fl i).length = B.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have ih := ih (by omega)
    rw [flagWrite, slice_length _ _ _ (flagBytes_length _) (by omega), ih]

/-- A slice update elsewhere leaves four bytes at `x` as they were. -/
theorem take4_slice_other (l bs : List Spec.byte) (e x : Nat) (hb : bs.length = 4) (hl : e + 4 ≤ l.length)
    (hd : x + 4 ≤ e ∨ e + 4 ≤ x) :
    List.take 4 (List.drop x (Spec.list_slice_update l e 4 bs)) = List.take 4 (List.drop x l) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop, List.getElem?_drop, slice_get _ _ _ _ hb hl]
  split
  · by_cases h1 : x + k < e
    · rw [if_pos h1]
    · rw [if_neg h1, if_neg (by omega)]
  · rfl

theorem boxesAt_flagWrite (B : List Spec.byte) (boxes out : Nat) (bx : List Box) (fl : List Bool) (i : Nat)
    (hbx : BoxesAt B boxes bx) (hin : out + 4 * i ≤ B.length)
    (hd : ∀ k < i, out + 4 * k + 4 ≤ boxes ∨ boxes + 16 * bx.length ≤ out + 4 * k) :
    BoxesAt (flagWrite B out fl i) boxes bx := by
  induction i with
  | zero => exact hbx
  | succ i ih =>
    have ih := ih (by omega) (fun k hk => hd k (by omega))
    intro j hj
    obtain ⟨h0, h4, h8, h12⟩ := ih j hj
    have hl := flagWrite_length B out fl i (by omega)
    have hdi := hd i (by omega)
    simp only [flagWrite]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [take4_slice_other _ _ _ _ (flagBytes_length _) (by omega) (by omega)]; assumption)

/-- The flag slices: each holds its flag after all are written, if the slices are apart. -/
theorem flagWrite_get (B : List Spec.byte) (out : Nat) (fl : List Bool) (i k : Nat) (hk : k < i)
    (hin : out + 4 * i ≤ B.length) :
    List.take 4 (List.drop (out + 4 * k) (flagWrite B out fl i)) = flagBytes fl[k]! := by
  induction i with
  | zero => omega
  | succ i ih =>
    have hl := flagWrite_length B out fl i (by omega)
    simp only [flagWrite]
    by_cases hki : k = i
    · subst hki
      apply List.ext_getElem?
      intro m
      rw [List.getElem?_take, List.getElem?_drop, slice_get _ _ _ _ (flagBytes_length _) (by omega)]
      by_cases hm : m < 4
      · rw [if_pos hm, if_neg (by omega), if_pos (by omega)]
        congr 1; omega
      · rw [if_neg hm, List.getElem?_eq_none (by rw [flagBytes_length]; omega)]
    · rw [take4_slice_other _ _ _ _ (flagBytes_length _) (by omega) (by omega)]
      exact ih (by omega) (by omega)

/-! ### Bounds -/

theorem pos_le (x : Int) (c : Int) (h : x ≤ c) (hc : 0 ≤ c) : pos x ≤ c := by simp only [pos]; omega

theorem mul_le_2_30 (a b : Int) (ha0 : 0 ≤ a) (ha : a ≤ 2^15) (hb0 : 0 ≤ b) (hb : b ≤ 2^15) :
    0 ≤ a * b ∧ a * b ≤ 2^30 := by
  refine ⟨Int.mul_nonneg ha0 hb0, ?_⟩
  have := Int.mul_le_mul ha hb hb0 (by decide)
  simpa using this

theorem areaK_bounds (b : Box) (h : BoxOk b) : 0 ≤ areaK b ∧ areaK b ≤ 2^30 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩ := h
  exact mul_le_2_30 _ _ (pos_nonneg _) (pos_le _ _ (by omega) (by decide)) (pos_nonneg _) (pos_le _ _ (by omega) (by decide))

theorem interK_bounds (a c : Box) (ha : BoxOk a) (hc : BoxOk c) : 0 ≤ interK a c ∧ interK a c ≤ 2^30 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩ := ha
  obtain ⟨⟨g1, g2⟩, ⟨g3, g4⟩, ⟨g5, g6⟩, ⟨g7, g8⟩⟩ := hc
  exact mul_le_2_30 _ _ (pos_nonneg _) (pos_le _ _ (by omega) (by decide)) (pos_nonneg _) (pos_le _ _ (by omega) (by decide))

theorem sumTo_le (bx : List Box) (i : Nat) (hok : ∀ c ∈ bx, BoxOk c) (hi : i < bx.length) :
    ∀ m, m ≤ bx.length → sumTo bx i m ≤ m * 2^30 := by
  intro m
  induction m with
  | zero => intro _; simp [sumTo]
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    simp only [sumTo]
    split
    · push_cast; omega
    · have := interK_bounds bx[i]! bx[m]! (bx_ok hok hi) (bx_ok hok (by omega))
      push_cast; omega

theorem modify_get! {α} [Inhabited α] (l : List α) (i : Nat) (f : α → α) (h : i < l.length) :
    (l.modify i f)[i]! = f l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_modify, List.getElem?_eq_getElem h]

/-! ### The outer loop: one flag per box -/

/-- The running result after `i` nodes. -/
noncomputable def allBit (bx : List Box) (bps : Int) (i : Nat) : Nat :=
  if (List.range i).all (okK bx bps) then 1 else 0

/-- What the outer loop leaves when it is done (it leaves by a branch to its block). -/
def OuterPost (M : Spec.moduleinst) (bx : List Box) (B : List Spec.byte) (n bps boxes out : Nat) : BrPost :=
  fun k z' _ => k = 0 ∧ ∃ (S'' : Spec.store) (j p ok : Nat) (l t r b area sum u v : Int),
    z' = st S'' M (locs n bps boxes out n j (allBit bx bps n) p ok l t r b area sum u v) ∧
    M.MEMS[0]! < S''.MEMS.length ∧ (S''.MEMS[M.MEMS[0]!]!).BYTES = flagWrite B out (flagsK bx bps) n

theorem allBit_succ (bx : List Box) (bps : Int) (i : Nat) :
    allBit bx bps (i + 1) = if okK bx bps i then allBit bx bps i else 0 := by
  simp only [allBit, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  by_cases h1 : (List.range i).all (okK bx bps) = true <;> by_cases h2 : okK bx bps i = true <;> simp [h1, h2]

theorem flagsK_get (bx : List Box) (bps : Int) (i : Nat) (hi : i < bx.length) :
    (flagsK bx bps)[i]! = okK bx bps i := by
  simp [flagsK, List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem outer_loop (M : Spec.moduleinst) (bx : List Box) (B : List Spec.byte) (n bps boxes out : Nat)
    (hbx : BoxesAt B boxes bx) (hok : ∀ c ∈ bx, BoxOk c)
    (hn : n = bx.length) (hn16 : n < 2^16) (hbps : bps < 2^32) (haddr : boxes + 16 * n < 2^32)
    (hout : out + 4 * n < 2^32) (hlen : out + 4 * n ≤ B.length)
    (hd : out + 4 * n ≤ boxes ∨ boxes + 16 * n ≤ out) :
    ∀ m i (S' : Spec.store) (j p ok : Nat) (l t r b area sum u v : Int), n - i = m → i ≤ n →
    M.MEMS[0]! < S'.MEMS.length → (S'.MEMS[M.MEMS[0]!]!).BYTES = flagWrite B out (flagsK bx bps) i →
    SemR (st S' M (locs n bps boxes out i j (allBit bx bps i) p ok l t r b area sum u v)) []
      [.LOOP (._RESULT none) (KI.toSpecs outerBody)] (fun _ _ => False) (OuterPost M bx B n bps boxes out) := by
  intro m
  induction m with
  | zero =>
    intro i S' j p ok l t r b area sum u v hm hi hma hB
    have hin : i = n := by omega
    subst hin
    refine semR_loop ?_
    simp only [outerBody, outerHead, outerTail, List.cons_append, List.nil_append, toSpecs_ks, List.map,
      KI.toSpec, locs]
    refine semR_localGet rfl ?_
    refine semR_localGet rfl ?_
    refine semR_i32geu (by omega) (by omega) ?_
    refine semR_brIf ?_
    rw [if_neg (by simp)]
    exact ⟨rfl, S', j, p, ok, l, t, r, b, area, sum, u, v, rfl, hma, hB⟩
  | succ m ih =>
    intro i S' j p ok l t r b area sum u v hm hi hma hB
    have hin : i < n := by omega
    have hci := bx_ok hok (show i < bx.length by omega)
    have hbx' := boxesAt_flagWrite B boxes out bx (flagsK bx bps) i hbx (by omega) (fun k hk => by omega)
    obtain ⟨b0, b4, b8, b12⟩ := hbx' i (by omega)
    have hci' := hci
    obtain ⟨⟨hc1, hc2⟩, ⟨hc3, hc4⟩, ⟨hc5, hc6⟩, ⟨hc7, hc8⟩⟩ := hci'
    refine semR_loop ?_
    simp only [outerBody, outerHead, outerTail, List.cons_append, List.nil_append, toSpecs_ks, List.map,
      KI.toSpec, locs]
    refine semR_localGet rfl ?_
    refine semR_localGet rfl ?_
    refine semR_i32geu (by omega) (by omega) ?_
    refine semR_brIf ?_
    rw [if_pos ((ite01_mod _).mpr (by omega))]
    repeat wstep
    wload hB b0
    repeat wstep
    wload hB b4
    repeat wstep
    wload hB b8
    repeat wstep
    wload hB b12
    repeat wstep
    -- the inner loop
    refine semR_block ?_
    have hinner := inner_loop S' M bx _ n bps boxes out i (allBit bx bps i) ok
      (max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0) hB
      (boxesAt_flagWrite B boxes out bx (flagsK bx bps) i hbx (by omega) (fun k hk => by omega)) hok
      hn hn16 haddr hin (n - 0) 0 (boxes + i * 16) 0 (bx[i]!.right - bx[i]!.left) (bx[i]!.bottom - bx[i]!.top)
      rfl (by omega) (by simp [sumTo])
    refine semR_mono hinner (fun _ _ h => h.elim) ?_
    rintro k z' _ ⟨rfl, p', u', v', rfl⟩
    show SemR _ [] _ _ _
    simp only [locs]
    -- the flag of node i
    have hA := areaK_bounds _ hci
    simp only [areaK, pos] at hA
    have hS0 := sumTo_nonneg bx i n
    have hS1 := sumTo_le bx i hok (by omega) n (by omega)
    have hP : 0 ≤ (bps : Int) * (max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0) ∧
        (bps : Int) * (max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0) ≤ 2^62 := by
      refine ⟨Int.mul_nonneg (by omega) hA.1, ?_⟩
      have := Int.mul_le_mul (show (bps : Int) ≤ 2^32 by omega) hA.2 hA.1 (by decide)
      simpa using this
    have hnn : (n : Int) * 2^30 ≤ 2^46 := by omega
    repeat wstep
    have hokv : (if max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0 > 0 then
          (if sumTo bx i n * 10000 ≤ ↑bps * (max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0)
            then 1 else 0) else 0) = (if okK bx bps i = true then 1 else 0) := by
      simp only [okK, areaK, pos, ← hn, decide_eq_true_eq]
      by_cases h1 : max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0 > 0
      · by_cases h2 : sumTo bx i n * 10000 ≤ ↑bps * (max (bx[i]!.right - bx[i]!.left) 0 * max (bx[i]!.bottom - bx[i]!.top) 0)
        · rw [if_pos h1, if_pos h2, if_pos ⟨h1, by omega⟩]
        · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (by omega))]
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]
    rw [hokv]
    refine semR_store32 ?_
    simp only [with_mem_mk]
    repeat wstep
    rw [← allBit_succ]
    refine semR_br ?_
    have hea : (out + i * 4) % 2^32 + 0 = out + 4 * i := by omega
    have hfl : (flagsK bx bps)[i]! = okK bx bps i := flagsK_get bx bps i (by omega)
    refine ih (i + 1) _ n p' _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by rw [List.length_modify]; exact hma) ?_
    rw [modify_get! _ _ _ hma, hB, hea, flagWrite, hfl]
    simp only [flagBytes]
    congr 3
    split <;> rfl

/-! ### The function -/

/-- What the body leaves: the result `certifyK` as an i32, and memory with the flags. -/
def FinalPost (M : Spec.moduleinst) (bx : List Box) (B : List Spec.byte) (bps out : Nat) : Post :=
  fun z vs => vs = [i32v (allBit bx bps bx.length)] ∧ ∃ (S'' : Spec.store) (L : List (Option Spec.val)), z = .mk_state S'' ⟨L, M⟩ ∧
    M.MEMS[0]! < S''.MEMS.length ∧ (S''.MEMS[M.MEMS[0]!]!).BYTES = flagWrite B out (flagsK bx bps) bx.length

/-- The input conditions of `check`, as the page's glue sets them up. -/
structure Inputs (bx : List Box) (B : List Spec.byte) (n bps boxes out : Nat) : Prop where
  boxes_at : BoxesAt B boxes bx
  boxes_ok : ∀ c ∈ bx, BoxOk c
  count : n = bx.length
  count_lt : n < 2^16
  bps_lt : bps < 2^32
  boxes_fit : boxes + 16 * n < 2^32
  out_fit : out + 4 * n < 2^32
  out_in : out + 4 * n ≤ B.length
  apart : out + 4 * n ≤ boxes ∨ boxes + 16 * n ≤ out

theorem check_body (S : Spec.store) (M : Spec.moduleinst) (bx : List Box) (B : List Spec.byte)
    (n bps boxes out : Nat) (hin : Inputs bx B n bps boxes out)
    (hma : M.MEMS[0]! < S.MEMS.length) (hB : (S.MEMS[M.MEMS[0]!]!).BYTES = B) :
    SemR (st S M (locs n bps boxes out 0 0 0 0 0 0 0 0 0 0 0 0 0)) [] (KI.toSpecs checkBody)
      (FinalPost M bx B bps out) (fun _ _ _ => False) := by
  obtain ⟨hbx, hok, hn, hn16, hbps, haddr, hout, hlen, hd⟩ := hin
  simp only [checkBody, toSpecs_ks, List.map, KI.toSpec, locs]
  refine semR_i32const (by decide) ?_
  refine semR_localSet ?_
  wnorm
  refine semR_block ?_
  have hloop := outer_loop M bx B n bps boxes out hbx hok hn hn16 hbps haddr hout hlen hd (n - 0) 0 S 0 0 0
    0 0 0 0 0 0 0 0 rfl (by omega) hma hB
  refine semR_mono hloop (fun _ _ h => h.elim) ?_
  rintro k z' _ ⟨rfl, S'', j, p, ok, l, t, r, b, area, sum, u, v, rfl, hma', hB'⟩
  show SemR _ [] _ _ _
  simp only [locs]
  refine semR_localGet rfl ?_
  refine semR_nil ?_
  subst hn
  exact ⟨rfl, S'', _, rfl, hma', hB'⟩

/-- The local types of `check` after its parameters: five i32, eight i64. -/
def checkLocalTypes : List Spec.valtype := [.I32, .I32, .I32, .I32, .I32, .I64, .I64, .I64, .I64, .I64, .I64, .I64, .I64]

theorem init_locals (n bps boxes out : Nat) :
    ([i32v n, i32v bps, i32v boxes, i32v out].map some ++ checkLocalTypes.map Spec.default_) =
      locs n bps boxes out 0 0 0 0 0 0 0 0 0 0 0 0 0 := rfl

/-- **The kernel under the WebAssembly spec semantics.** Invoking the function at address
`a`, whose code is the decoded body of `check`, with the page's arguments, the generated
spec relation `Spec.Steps` reaches the result `certifyK` (as `allBit`, `1` or `0`) with the
memory holding the flags `flagsK` at `out` and every other byte as it was. -/
theorem check_spec (S : Spec.store) (f0 : Spec.frame) (a : Nat) (yy : Spec.typeuse) (fi : Spec.funcinst)
    (x : Spec.idx) (bx : List Box) (B : List Spec.byte) (n bps boxes out : Nat)
    (ha : a < S.FUNCS.length) (hfi : S.FUNCS[a]! = fi)
    (hty : Spec.Expand fi.TYPE (.FUNC (.mk_list [.I32, .I32, .I32, .I32]) (.mk_list [.I32])))
    (hcode : fi.CODE = .FUNC x (checkLocalTypes.map .LOCAL) (KI.toSpecs checkBody))
    (hma : fi.MODULE.MEMS[0]! < S.MEMS.length) (hB : (S.MEMS[fi.MODULE.MEMS[0]!]!).BYTES = B)
    (hin : Inputs bx B n bps boxes out) :
    ∃ S' : Spec.store,
      Spec.Steps (.mk_config (.mk_state S f0)
          (vals [i32v n, i32v bps, i32v boxes, i32v out] ++ [.REF_FUNC_ADDR a, .CALL_REF yy]))
        (.mk_config (.mk_state S' f0) (vals [i32v (allBit bx bps bx.length)])) ∧
      fi.MODULE.MEMS[0]! < S'.MEMS.length ∧
      (S'.MEMS[fi.MODULE.MEMS[0]!]!).BYTES = flagWrite B out (flagsK bx bps) bx.length := by
  let vf : Spec.frame := ⟨locs n bps boxes out 0 0 0 0 0 0 0 0 0 0 0 0 0, fi.MODULE⟩
  have hcall : Spec.Step (.mk_config (.mk_state S f0)
      (vals [i32v n, i32v bps, i32v boxes, i32v out] ++ [.REF_FUNC_ADDR a, .CALL_REF yy]))
      (.mk_config (.mk_state S f0) [.FRAME_ 0 vf [.LABEL_ 0 [] (KI.toSpecs checkBody)]]) := by
    refine Spec.Step.call_ref_func _ [i32v n, i32v bps, i32v boxes, i32v out] 0 a yy 0 vf (KI.toSpecs checkBody) fi
      _ _ x checkLocalTypes ha (by rw [show Spec.s (.mk_state S f0) = S from rfl, hfi]; exact BEq.rfl) hty
      (by rw [hcode]; exact BEq.rfl) (by rw [init_locals]; exact BEq.rfl)
  have hbody := check_body S fi.MODULE bx B n bps boxes out hin hma hB
  rcases hbody [] with ⟨z', vs', ⟨hvs, S'', L, rfl, hma', hB'⟩, hsteps⟩ | ⟨_, _, _, _, hf, _⟩
  · subst hvs
    refine ⟨S'', ?_, hma', hB'⟩
    simp only [List.reverse_nil, vals, List.map_nil, List.nil_append, List.append_nil] at hsteps
    have h1 := steps_frame 0 f0 (steps_label 0 [] hsteps)
    have h2 : Spec.Steps (.mk_config (.mk_state S'' f0) [.FRAME_ 0 ⟨L, fi.MODULE⟩ [.LABEL_ 0 [] (vals [i32v (allBit bx bps bx.length)])]])
        (.mk_config (.mk_state S'' f0) (vals [i32v (allBit bx bps bx.length)])) := by
      have s1 := steps_frame 0 f0 (S := S'') (f := ⟨L, fi.MODULE⟩)
        (steps_one (Spec.Step.pure _ _ _ (Spec.Step_pure.label_vals 0 [] [i32v (allBit bx bps bx.length)])))
      exact steps_trans s1 (steps_one (Spec.Step.pure _ _ _ (Spec.Step_pure.frame_vals 0 _ [i32v (allBit bx bps bx.length)])))
    exact steps_trans (steps_one hcall) (steps_trans h1 h2)
  · exact hf.elim

/-- **Transfer to the Lean certificate.** For any layout configuration `cfg`, the kernel run
with `bps = cfg.overlapBps` returns `1` exactly when `LayoutPolicy.certify cfg` accepts the
boxes; then every node meets the overlap budget (`LayoutPolicy.certify_sound`). The flag
written for node `i` is the `accepted` field of the certificate's report for node `i`. -/
theorem check_certifies (S : Spec.store) (f0 : Spec.frame) (a : Nat) (yy : Spec.typeuse) (fi : Spec.funcinst)
    (x : Spec.idx) (bx : List Box) (B : List Spec.byte) (cfg : UI.LayoutPolicy.Config) (boxes out : Nat)
    (ha : a < S.FUNCS.length) (hfi : S.FUNCS[a]! = fi)
    (hty : Spec.Expand fi.TYPE (.FUNC (.mk_list [.I32, .I32, .I32, .I32]) (.mk_list [.I32])))
    (hcode : fi.CODE = .FUNC x (checkLocalTypes.map .LOCAL) (KI.toSpecs checkBody))
    (hma : fi.MODULE.MEMS[0]! < S.MEMS.length) (hB : (S.MEMS[fi.MODULE.MEMS[0]!]!).BYTES = B)
    (hin : Inputs bx B bx.length cfg.overlapBps boxes out) :
    ∃ (S' : Spec.store) (r : Nat),
      Spec.Steps (.mk_config (.mk_state S f0)
          (vals [i32v bx.length, i32v cfg.overlapBps, i32v boxes, i32v out] ++ [.REF_FUNC_ADDR a, .CALL_REF yy]))
        (.mk_config (.mk_state S' f0) (vals [i32v r])) ∧
      (r = 1 ↔ UI.LayoutPolicy.certify cfg (bx.map some) = true) ∧
      (r = 1 → UI.LayoutPolicy.LayoutAccepted cfg (bx.map some)) ∧
      ∀ i < bx.length,
        List.take 4 (List.drop (out + 4 * i) (S'.MEMS[fi.MODULE.MEMS[0]!]!).BYTES) =
          flagBytes ((UI.LayoutPolicy.checkFootprints cfg (bx.map some)).map (·.accepted))[i]! := by
  obtain ⟨S', hs, hma', hB'⟩ := check_spec S f0 a yy fi x bx B bx.length cfg.overlapBps boxes out ha hfi hty hcode hma hB hin
  have hcert : allBit bx cfg.overlapBps bx.length = 1 ↔ UI.LayoutPolicy.certify cfg (bx.map some) = true := by
    rw [← certifyK_eq, certifyK, flagsK, allBit, List.all_map]
    by_cases h : (List.range bx.length).all (okK bx ↑cfg.overlapBps) = true
    · simp only [h, if_true]; simp only [Function.comp_def, id] at h ⊢; simp [h]
    · simp only [h, if_false]; simp only [Function.comp_def, id] at h ⊢; simp [h]
  refine ⟨S', _, hs, hcert, fun h => (UI.LayoutPolicy.certify_iff cfg _).mp (hcert.mp h), ?_⟩
  intro i hi
  rw [hB', flagWrite_get B out _ bx.length i hi hin.out_in, flagsK_eq cfg bx]

end L4Factoidal.WasmVM.Proofs.FoafCheck
