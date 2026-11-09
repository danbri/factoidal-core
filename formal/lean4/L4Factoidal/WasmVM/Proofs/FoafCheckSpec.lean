/-
L4Factoidal.WasmVM.Proofs.FoafCheckSpec: the FOAF overlap check as the WebAssembly
kernel computes it, over integer boxes, proved equal to the Lean certificate
`L4Factoidal.UI.LayoutPolicy.checkFootprints` / `certify` (record:
docs/designissues/2026-11-09-verified-foaf-layout.md).

The kernel's arithmetic is on `Int` with `max x 0` for the clamped extents
(`Box.area` and `Box.intersection` use `Int.toNat`), and the sum over the other nodes
runs in index order skipping the node itself, as `checkFootprints` builds `others`.
-/
import L4Factoidal.UI.LayoutPolicy

namespace L4Factoidal.WasmVM.Proofs.FoafCheck
open L4Factoidal.UI.Geometry L4Factoidal.UI.LayoutPolicy

instance : Inhabited Box := ⟨⟨0, 0, 0, 0⟩⟩

/-- A clamped extent. -/
def pos (x : Int) : Int := max x 0

def areaK (b : Box) : Int := pos (b.right - b.left) * pos (b.bottom - b.top)

def interK (a c : Box) : Int :=
  pos (min a.right c.right - max a.left c.left) * pos (min a.bottom c.bottom - max a.top c.top)

/-- The overlap sum of node `i` over the nodes `j < m`, `j ≠ i`, in index order. -/
noncomputable def sumTo (bx : List Box) (i : Nat) : Nat → Int
  | 0 => 0
  | j + 1 => sumTo bx i j + (if j = i then 0 else interK bx[i]! bx[j]!)

noncomputable def okK (bx : List Box) (bps : Int) (i : Nat) : Bool :=
  decide (0 < areaK bx[i]! ∧ 10000 * sumTo bx i bx.length ≤ bps * areaK bx[i]!)

/-- The flags the kernel writes, in node order. -/
noncomputable def flagsK (bx : List Box) (bps : Int) : List Bool := (List.range bx.length).map (okK bx bps)

/-- The kernel's result: every node passes. -/
noncomputable def certifyK (bx : List Box) (bps : Int) : Bool := (flagsK bx bps).all id

theorem pos_nonneg (x : Int) : 0 ≤ pos x := by simp only [pos]; omega

theorem sumTo_nonneg (bx : List Box) (i m : Nat) : 0 ≤ sumTo bx i m := by
  induction m with
  | zero => simp [sumTo]
  | succ m ih =>
    simp only [sumTo]
    split
    · omega
    · have := Int.mul_nonneg (pos_nonneg (min bx[i]!.right bx[m]!.right - max bx[i]!.left bx[m]!.left))
        (pos_nonneg (min bx[i]!.bottom bx[m]!.bottom - max bx[i]!.top bx[m]!.top))
      simp only [interK]; omega

/-! ### Agreement with `LayoutPolicy` -/

theorem pos_cast (x : Int) : pos x = ((x.toNat : Nat) : Int) := by
  simp only [pos]; omega

theorem areaK_eq (b : Box) : areaK b = ((b.area : Nat) : Int) := by
  simp only [areaK, Box.area, pos_cast, Int.natCast_mul]

theorem interK_eq (a c : Box) : interK a c = (((a.intersection c).area : Nat) : Int) := by
  simp only [interK, Box.area, Box.intersection, pos_cast, Int.natCast_mul]

theorem areaK_nonneg (b : Box) : 0 ≤ areaK b := by rw [areaK_eq]; omega

theorem interK_nonneg (a c : Box) : 0 ≤ interK a c := by rw [interK_eq]; omega

/-- `others` of `checkFootprints` for all-present boxes, as a list. -/
noncomputable def othersOf (bx : List Box) (i : Nat) : List Box :=
  ((List.range bx.length).filter (· ≠ i)).map (fun j => bx[j]!)

theorem filterMap_zipIdx (bx : List Box) (i : Nat) :
    (bx.map some).zipIdx.filterMap (fun (other, j) => if i == j then none else other) =
      ((List.range bx.length).filter (· ≠ i)).map (fun j => bx[j]!) := by
  suffices h : ∀ (k : Nat) (bx : List Box),
      ((bx.map some).zipIdx k).filterMap (fun (other, j) => if i == j then none else other) =
        (((List.range bx.length).map (· + k)).filter (· ≠ i)).map (fun j => bx[j - k]!) by
    simpa using h 0 bx
  intro k bx
  induction bx generalizing k with
  | nil => simp
  | cons b rest ih =>
    rw [List.map_cons, List.zipIdx_cons, List.filterMap_cons, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    have e : ((fun x => x + k) ∘ Nat.succ) = (fun x => x + (k + 1)) := by funext x; simp; omega
    rw [e]
    have ih' := ih (k + 1)
    have e2 : ∀ j ∈ (List.map (· + (k + 1)) (List.range rest.length)).filter (· ≠ i),
        (b :: rest)[j - k]! = rest[j - (k + 1)]! := by
      intro j hj
      simp only [List.mem_filter, List.mem_map, List.mem_range] at hj
      obtain ⟨⟨x, _, rfl⟩, _⟩ := hj
      have : x + (k + 1) - k = x + 1 := by omega
      rw [this]; simp
    by_cases hik : i = k
    · subst hik
      simp only [beq_self_eq_true, if_true, Nat.zero_add, List.filter_cons, ne_eq, not_true_eq_false,
        decide_false]
      rw [ih', List.map_congr_left (fun j hj => (e2 j hj).symm)]; rfl
    · have hb : (i == k) = false := by simp [hik]
      simp only [hb, Bool.false_eq_true, if_false, Nat.zero_add, List.filter_cons, ne_eq,
        Ne.symm hik, not_false_eq_true, decide_true, if_true, List.map_cons, Nat.sub_self]
      rw [ih', List.map_congr_left (fun j hj => (e2 j hj).symm)]
      simp

theorem sumTo_eq (bx : List Box) (i : Nat) (m : Nat) :
    sumTo bx i m = ((((List.range m).filter (· ≠ i)).map (fun j => bx[j]!)).map (fun o => interK bx[i]! o)).sum := by
  induction m with
  | zero => simp [sumTo]
  | succ m ih =>
    rw [sumTo, ih, List.range_succ, List.filter_append]
    by_cases h : m = i
    · subst h; simp
    · simp [h]

theorem overlapSum_cast (b : Box) (os : List Box) :
    ((overlapSum b os : Nat) : Int) = (os.map (fun o => interK b o)).sum := by
  induction os with
  | nil => simp [overlapSum]
  | cons o os ih =>
    simp only [overlapSum, List.map_cons, List.sum_cons, Int.natCast_add] at ih ⊢
    rw [ih, interK_eq]

theorem sumTo_cast (bx : List Box) (i : Nat) :
    sumTo bx i bx.length = ((overlapSum bx[i]! (othersOf bx i) : Nat) : Int) := by
  rw [overlapSum_cast, sumTo_eq, othersOf]

/-- Each report of `checkFootprints` on all-present boxes is the kernel's computation. -/
theorem checkFootprints_eq (cfg : Config) (bx : List Box) :
    checkFootprints cfg (bx.map some) =
      (List.range bx.length).map (fun i =>
        ⟨i, some bx[i]!, bx[i]!.area, overlapSum bx[i]! (othersOf bx i),
          okK bx cfg.overlapBps i⟩) := by
  unfold checkFootprints
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Option.map_some, Option.getD_some]
    simp only [List.length_map, List.length_zipIdx] at h1
    have hk : (bx.map some)[k]'(by simpa using h1) = some bx[k]! := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    have hb : bx[k]! = bx[k] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    have hf : List.filterMap (fun x => if (0 + k == x.snd) = true then none else x.fst) (bx.map some).zipIdx =
        othersOf bx k := by
      have := filterMap_zipIdx bx k
      simp only [Nat.zero_add]
      exact this
    rw [hf, hb, Nat.zero_add]
    congr 1
    simp only [withinBudget, okK]
    have ha := areaK_eq bx[k]!
    have hs := sumTo_cast bx k
    rw [hb] at ha hs
    rw [hb, ha, hs]
    simp only [Budget, decide_eq_decide]
    generalize bx[k].area = A
    generalize overlapSum bx[k] (othersOf bx k) = O
    generalize cfg.overlapBps = P
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      have : ((10000 * O : Nat) : Int) ≤ ((P * A : Nat) : Int) := Int.ofNat_le.mpr h2
      simpa [Int.natCast_mul] using this
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      have : ((10000 * O : Nat) : Int) ≤ ((P * A : Nat) : Int) := by simpa [Int.natCast_mul] using h2
      exact Int.ofNat_le.mp this

/-- The kernel's flags are the `accepted` field of the certificate's reports. -/
theorem flagsK_eq (cfg : Config) (bx : List Box) :
    (checkFootprints cfg (bx.map some)).map (·.accepted) = flagsK bx cfg.overlapBps := by
  rw [checkFootprints_eq, flagsK, List.map_map]; rfl

/-- The kernel's result is `certify`. -/
theorem certifyK_eq (cfg : Config) (bx : List Box) :
    certifyK bx cfg.overlapBps = certify cfg (bx.map some) := by
  rw [certify, certifyK, ← flagsK_eq, List.all_map]; rfl

end L4Factoidal.WasmVM.Proofs.FoafCheck
