/-! Layout units: the arithmetic of layout that theorems are proved about.

Layout geometry in `Rendering/Layout.lean` is `Float` px, and nothing can be proved about
`Float`. The algorithms that divide space (flexible lengths, flexible tracks, alignment)
therefore run on `Int` in units of 1/64 px, as other engines' layout units do, and are
converted at their edges (`ofPx`, `toPx`). This module has no import from the engine. -/
namespace L4Factoidal.Rendering.LU

/-- Units in one CSS px. -/
def perPx : Nat := 64

/-- A length in px as layout units: the nearest unit. NaN is 0; a length beyond the range
of 64 bits is the largest unit count of that sign. -/
def ofPx (x : Float) : Int :=
  if x.isNaN then 0
  else if x < 0 then -Int.ofNat ((-x * 64).round.toUInt64.toNat)
  else Int.ofNat ((x * 64).round.toUInt64.toNat)

/-- Layout units as px. -/
def toPx (u : Int) : Float := Float.ofInt u / 64

/-- A size within its limits; a minimum wins over a maximum (CSS 2.1 §10.4). `none`: no
maximum. -/
def clamp (lo : Int) (hi : Option Int) (v : Int) : Int :=
  match hi with
  | some h => max lo (min h v)
  | none => max lo v

/-- Lemma. Says: a clamped size is never below its minimum. Does not say: that the
minimum itself is sensible (non-negative). -/
theorem le_clamp (lo : Int) (hi : Option Int) (v : Int) : lo ≤ clamp lo hi v := by
  unfold clamp; cases hi <;> simp only <;> omega

/-- Lemma. Says: a clamped size is never above its maximum, unless the minimum is (then
it is the minimum). Does not say: anything when there is no maximum. -/
theorem clamp_le (lo h v : Int) : clamp lo (some h) v ≤ max lo h := by
  unfold clamp; simp only; omega

/-- Lemma. Says: a size already within its limits is not changed by `clamp`. -/
theorem clamp_of_within (lo : Int) (hi : Option Int) (v : Int) (h₁ : lo ≤ v)
    (h₂ : ∀ h, hi = some h → v ≤ h) : clamp lo hi v = v := by
  unfold clamp
  cases hi with
  | none => simp only; omega
  | some h => have := h₂ h rfl; simp only; omega

/-- Lemma. Says: clamping twice is clamping once. -/
theorem clamp_idem (lo : Int) (hi : Option Int) (v : Int) :
    clamp lo hi (clamp lo hi v) = clamp lo hi v := by
  unfold clamp; cases hi <;> simp only <;> omega

/-- The share of `space` for weight `w` when the weights still to be served sum to `total`. -/
def share (space w total : Nat) : Nat := if total = 0 then 0 else space * w / total

theorem share_le (space w total : Nat) (h : w ≤ total) : share space w total ≤ space := by
  unfold share
  split
  · omega
  · rename_i ht
    apply Nat.div_le_of_le_mul
    rw [Nat.mul_comm total space]
    exact Nat.mul_le_mul_left space h

theorem share_all (space w : Nat) (h : 0 < w) : share space w w = space := by
  unfold share
  rw [if_neg (by omega)]
  exact Nat.mul_div_cancel space h

theorem share_zero (space total : Nat) : share space 0 total = 0 := by
  unfold share; split <;> simp

/-- The loop of `distribute`: `space` is what is left to hand out, `total` the sum of the
weights not yet served, `acc` the shares so far. A loop, not a recursion on the stack. -/
def distributeLoop (space total : Nat) (acc : Array Nat) : List Nat → Array Nat
  | [] => acc
  | w :: rest =>
    let q := share space w total
    distributeLoop (space - q) (total - w) (acc.push q) rest

/-- `space` divided among `weights` in proportion, in whole units, by running remainder:
each weight in turn takes its proportion of what is left, so the last weight that is not
zero takes all that remains and nothing is lost to rounding. A share differs from the
exact proportion by less than one unit per earlier item. -/
def distribute (space : Nat) (weights : List Nat) : List Nat :=
  (distributeLoop space weights.sum #[] weights).toList

/-- `distribute` as a plain recursion: what the loop computes (`distribute_eq_spec`). Used
in proofs only; not compiled. -/
noncomputable def distributeSpec (space total : Nat) : List Nat → List Nat
  | [] => []
  | w :: rest => share space w total :: distributeSpec (space - share space w total) (total - w) rest

theorem distributeLoop_eq (ws : List Nat) : ∀ (space total : Nat) (acc : Array Nat),
    (distributeLoop space total acc ws).toList = acc.toList ++ distributeSpec space total ws := by
  induction ws with
  | nil => intro space total acc; simp [distributeLoop, distributeSpec]
  | cons w rest ih =>
    intro space total acc
    simp [distributeLoop, distributeSpec, ih]

/-- Refinement. Says: the loop computes the plain recursion. -/
theorem distribute_eq_spec (space : Nat) (ws : List Nat) :
    distribute space ws = distributeSpec space ws.sum ws := by
  simp [distribute, distributeLoop_eq]

private theorem distributeSpec_zero (ws : List Nat) : ∀ (space total : Nat),
    ∀ p ∈ ws.zip (distributeSpec space total ws), p.1 = 0 → p.2 = 0 := by
  induction ws with
  | nil => intro space total p hp; simp [distributeSpec] at hp
  | cons w rest ih =>
    intro space total p hp h0
    simp only [distributeSpec, List.zip_cons_cons, List.mem_cons] at hp
    cases hp with
    | inl h => subst h; simp only at h0 ⊢; rw [h0]; exact share_zero _ _
    | inr h => exact ih _ _ p h h0

/-- Lemma. Says: a weight of zero gets a share of zero (each weight is paired with its
share by position). -/
theorem distribute_zero (space : Nat) (ws : List Nat) :
    ∀ p ∈ ws.zip (distribute space ws), p.1 = 0 → p.2 = 0 := by
  rw [distribute_eq_spec]; exact distributeSpec_zero ws space ws.sum

theorem distributeLoop_toList_length (ws : List Nat) : ∀ (space total : Nat) (acc : Array Nat),
    (distributeLoop space total acc ws).toList.length = acc.toList.length + ws.length := by
  induction ws with
  | nil => intro space total acc; simp [distributeLoop]
  | cons w rest ih =>
    intro space total acc
    simp only [distributeLoop, ih, Array.toList_push, List.length_append, List.length_cons, List.length_nil]
    omega

/-- Lemma. Says: one share for each weight. -/
theorem distribute_length (space : Nat) (ws : List Nat) : (distribute space ws).length = ws.length := by
  unfold distribute; rw [distributeLoop_toList_length]; simp

private theorem distributeLoop_sum_zero (ws : List Nat) : ∀ (space : Nat) (acc : Array Nat),
    (distributeLoop space 0 acc ws).toList.sum = acc.toList.sum := by
  induction ws with
  | nil => intro space acc; simp [distributeLoop]
  | cons w rest ih =>
    intro space acc
    simp only [distributeLoop, share, if_true, Nat.zero_sub, ih, Array.toList_push, List.sum_append,
      List.sum_cons, List.sum_nil]
    omega

private theorem distributeLoop_sum (ws : List Nat) : ∀ (space : Nat) (acc : Array Nat), 0 < ws.sum →
    (distributeLoop space ws.sum acc ws).toList.sum = acc.toList.sum + space := by
  induction ws with
  | nil => intro space acc h; simp at h
  | cons w rest ih =>
    intro space acc h
    simp only [distributeLoop, List.sum_cons, Nat.add_sub_cancel_left]
    have hq : share space w (w + rest.sum) ≤ space := share_le _ _ _ (by omega)
    by_cases hr : 0 < rest.sum
    · rw [ih _ _ hr]
      simp only [Array.toList_push, List.sum_append, List.sum_cons, List.sum_nil]
      omega
    · have hr0 : rest.sum = 0 := by omega
      have hw : 0 < w := by simp only [List.sum_cons] at h; omega
      rw [hr0, distributeLoop_sum_zero]
      simp only [Nat.add_zero, share_all space w hw, Array.toList_push, List.sum_append, List.sum_cons, List.sum_nil]

/-- Conservation. Says: when some weight is not zero, the shares sum to exactly `space`:
no unit is lost or made by rounding. Does not say: how close each share is to its exact
proportion (within one unit per earlier item, not proved here). -/
theorem distribute_sum (space : Nat) (ws : List Nat) (h : 0 < ws.sum) :
    (distribute space ws).sum = space := by
  simp [distribute, distributeLoop_sum ws space #[] h]

/-- Lemma. Says: when every weight is zero, nothing is handed out. -/
theorem distribute_sum_zero (space : Nat) (ws : List Nat) (h : ws.sum = 0) :
    (distribute space ws).sum = 0 := by
  unfold distribute; rw [h, distributeLoop_sum_zero]; simp

#guard distribute 100 [1, 1, 1] == [33, 33, 34]
#guard distribute 100 [1, 0, 3] == [25, 0, 75]
#guard distribute 7 [0, 0] == [0, 0]
#guard distribute 10 [] == []
#guard distribute 640 [2, 1, 1, 0] == [320, 160, 160, 0]
#guard ofPx 1.5 == 96 && ofPx (-0.25) == -16 && ofPx 0 == 0
#guard toPx 96 == 1.5
#guard clamp 10 (some 5) 7 == 10 && clamp 0 (some 5) 7 == 5 && clamp 0 none 7 == 7

end L4Factoidal.Rendering.LU
