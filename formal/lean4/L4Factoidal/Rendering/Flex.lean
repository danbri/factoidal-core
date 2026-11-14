import L4Factoidal.Rendering.LayoutUnit

/-! The flex layout algorithm (CSS Flexible Box Layout 1 §9) as pure geometry on layout
units (`LU`, 1/64 px), with its theorems. Nothing here knows about the DOM, styles, text
or paint: `Rendering/FlexLayout.lean` collects the items of a container, asks this
module for sizes and positions, and lays the items out.

Proved here (each theorem's comment says what it says and does not say):
- `resolve_frozen`: resolving flexible lengths (§9.7) ends within one round per item;
- `resolve_bounds`: no item is smaller than its minimum or larger than its maximum;
- `resolve_exact`: when the last round flexed with no violation, the items' outer main
  sizes sum to exactly the room they were given;
- `resolve_items`: the result has the items it was given, in order;
- `place_pairwise`: items placed along a line do not overlap;
- `justify_between_nonneg`, `justify_fits`: content distribution never pulls items
  together, and with room to spare keeps them inside the line;
- `breakLines_sum`, `breakLines_pos`: every item is on exactly one line, no line is empty;
- `alignOffset_within`: an item no larger than its line lies inside it. -/
namespace L4Factoidal.Rendering.Flex
open LU

/-- Flex factor 1: `flex-grow` and `flex-shrink` are counted in millionths. -/
def one : Nat := 1000000

/-- One flex item on the main axis. Sizes are content-box sizes in layout units. -/
structure Item where
  /-- Flex base size (§9.2 step 3). -/
  base : Int
  /-- Used minimum main size (not negative). -/
  lo : Int := 0
  /-- Used maximum main size; `none`: no maximum. -/
  hi : Option Int := none
  /-- `flex-grow` in millionths. -/
  grow : Nat := 0
  /-- `flex-shrink` in millionths. -/
  shrink : Nat := one
  /-- Margins, borders and padding along the main axis: outer size less inner size. -/
  edges : Int := 0
  deriving Repr, BEq

/-- Hypothetical main size (§9.2 step 3E): the base size within the item's limits. -/
def Item.hyp (i : Item) : Int := clamp i.lo i.hi i.base

/-- An item while flexible lengths are resolved. -/
structure St where
  item : Item
  frozen : Bool
  /-- Target main size; read only when `frozen`. -/
  target : Int
  deriving Repr, BEq

/-- The size an item counts for in the free space: its target when frozen, else its base. -/
def St.cur (s : St) : Int := if s.frozen then s.target else s.item.base
/-- The same with its margins, borders and padding. -/
def St.outer (s : St) : Int := s.cur + s.item.edges
/-- The sum of the outer sizes: the room in use. -/
def used (l : List St) : Int := (l.map St.outer).sum

/-- §9.7 step 2: an item is frozen at its hypothetical size from the start when its
factor is zero, or when flexing could only move it away from that size. -/
def init (growing : Bool) (i : Item) : St :=
  let factor := if growing then i.grow else i.shrink
  {item := i, target := i.hyp,
   frozen := factor == 0 || (if growing then decide (i.hyp < i.base) else decide (i.base < i.hyp))}

/-- What stays the same over the rounds. -/
structure Ctx where
  /-- The container's inner main size less the gaps between items. -/
  room : Int
  /-- The used flex factor is `flex-grow` (else `flex-shrink`): §9.7 step 1. -/
  growing : Bool
  /-- Magnitude of the initial free space (§9.7 step 3). -/
  initial : Nat

/-- The weight an item takes of the space handed out in a round: its `flex-grow`, or its
scaled flex shrink factor (`flex-shrink` times its base size); zero when frozen. -/
def weight (growing : Bool) (s : St) : Nat :=
  if s.frozen then 0 else if growing then s.item.grow else s.item.shrink * s.item.base.toNat

/-- The flex factor of an unfrozen item. -/
def factor (growing : Bool) (s : St) : Nat :=
  if s.frozen then 0 else if growing then s.item.grow else s.item.shrink

/-- §9.7 step 4b: how much space this round hands out (growing) or takes back
(shrinking). Free space of the wrong sign hands out nothing. When the factors of the
unfrozen items sum to less than 1, at most that fraction of the initial free space. -/
def amount (c : Ctx) (l : List St) : Nat :=
  let free := c.room - used l
  let mag := if c.growing then free.toNat else (-free).toNat
  let fsum := total (l.map (factor c.growing))
  if fsum < one then min mag (c.initial * fsum / one) else mag

/-- An item with the signed space it was handed this round. -/
abbrev Cand := St × Int

def unclamped (p : Cand) : Int := p.1.item.base + p.2
def clamped (p : Cand) : Int := clamp p.1.item.lo p.1.item.hi (unclamped p)
/-- §9.7 step 4d: how far the limits moved the item's size; zero when frozen. -/
def violation (p : Cand) : Int := if p.1.frozen then 0 else clamped p - unclamped p

/-- §9.7 step 4e: an unfrozen item is frozen this round when the total violation `tv` is
zero, or positive and the item has a minimum violation, or negative and it has a maximum
violation. -/
def freezes (tv : Int) (p : Cand) : Bool :=
  decide (tv = 0) || (decide (0 < tv) && decide (unclamped p < clamped p)) ||
    (decide (tv < 0) && decide (clamped p < unclamped p))

/-- The item after the round: frozen at its clamped size, or as it was. -/
def step (tv : Int) (p : Cand) : St :=
  if p.1.frozen || !freezes tv p then p.1 else {item := p.1.item, frozen := true, target := clamped p}

/-- The signed shares of one round. -/
def shares (c : Ctx) (l : List St) : List Int :=
  (distribute (amount c l) (l.map (weight c.growing))).map fun (q : Nat) => if c.growing then (q : Int) else -(q : Int)

def cands (c : Ctx) (l : List St) : List Cand := l.zip (shares c l)

def totalViolation (c : Ctx) (l : List St) : Int := ((cands c l).map violation).sum

/-- A round flexed exactly: some weight was not zero, all of the free space was handed
out, and the limits moved nothing in total. -/
def exactRound (c : Ctx) (l : List St) : Bool :=
  decide (0 < total (l.map (weight c.growing))) &&
  decide ((if c.growing then (amount c l : Int) else -(amount c l : Int)) = c.room - used l) &&
  decide (totalViolation c l = 0)

/-- One round of §9.7 step 4. -/
def round (c : Ctx) (l : List St) : List St :=
  (cands c l).map (step (totalViolation c l))

/-- The loop of §9.7 step 4: rounds until every item is frozen. `fuel` bounds the rounds;
one per item is enough (`resolve_frozen`). The flag says that the last round was exact. -/
def loop (c : Ctx) : Nat → List St → Bool → List St × Bool
  | 0, l, e => (l, e)
  | n + 1, l, e => if l.all (·.frozen) then (l, e) else loop c n (round c l) (exactRound c l)

/-- The result of resolving the flexible lengths of one line. -/
structure Resolved where
  items : List St
  /-- The last round flexed exactly (`resolve_exact`). -/
  exact : Bool

/-- The context of a line of `items` in `room`. -/
def ctxOf (room : Int) (items : List Item) : Ctx :=
  let growing := decide ((items.map fun i => i.hyp + i.edges).sum < room)
  let free := room - used (items.map (init growing))
  {room, growing, initial := if growing then free.toNat else (-free).toNat}

/-- §9.7: the used main sizes of the items of one line. `room` is the container's inner
main size less the gaps between the items. -/
def resolve (room : Int) (items : List Item) : Resolved :=
  let c := ctxOf room items
  let r := loop c items.length (items.map (init c.growing)) false
  ⟨r.1, r.2⟩

/-- The used main sizes (content box), in item order. -/
def Resolved.sizes (r : Resolved) : List Int := r.items.map St.cur

/-! ### Theorems on resolving flexible lengths -/

theorem length_shares (c : Ctx) (l : List St) : (shares c l).length = l.length := by
  simp [shares, distribute_length]

theorem cands_fst (c : Ctx) (l : List St) : (cands c l).map Prod.fst = l := by
  unfold cands; exact List.map_fst_zip (by rw [length_shares]; exact Nat.le_refl _)

theorem cands_snd (c : Ctx) (l : List St) : (cands c l).map Prod.snd = shares c l := by
  unfold cands; exact List.map_snd_zip (by rw [length_shares]; exact Nat.le_refl _)

theorem step_item (tv : Int) (p : Cand) : (step tv p).item = p.1.item := by
  unfold step; split <;> rfl

theorem step_frozen_of_frozen (tv : Int) (p : Cand) (h : p.1.frozen = true) : (step tv p).frozen = true := by
  unfold step; simp [h]

theorem round_items (c : Ctx) (l : List St) : (round c l).map (·.item) = l.map (·.item) := by
  unfold round
  rw [List.map_map]
  have : ((fun (s : St) => s.item) ∘ step (totalViolation c l)) = (fun (s : St) => s.item) ∘ Prod.fst := by
    funext p; simp [step_item]
  rw [this, ← List.map_map, cands_fst]

/-- An invariant of the rounds carries through the loop. -/
theorem loop_inv (c : Ctx) (P : List St → Bool → Prop)
    (hround : ∀ l e, P l e → ¬ (l.all (·.frozen) = true) → P (round c l) (exactRound c l)) :
    ∀ (n : Nat) (l : List St) (e : Bool), P l e → P (loop c n l e).1 (loop c n l e).2 := by
  intro n
  induction n with
  | zero => intro l e h; simpa [loop] using h
  | succ n ih =>
    intro l e h
    unfold loop
    split
    · exact h
    · rename_i hf; exact ih _ _ (hround l e h hf)

/-- Preservation. Says: the result of `resolve` holds the items it was given, in the
same order, so a size can be read back by position. -/
theorem resolve_items (room : Int) (items : List Item) :
    (resolve room items).items.map (·.item) = items := by
  unfold resolve
  have h := loop_inv (ctxOf room items) (fun l _ => l.map (·.item) = items)
    (fun l e hl _ => by rw [round_items]; exact hl) items.length
    (items.map (init (ctxOf room items).growing)) false
    (by rw [List.map_map]; simp [Function.comp_def, init])
  exact h

/-- What holds of a frozen item: its target is within the item's limits. -/
def Within (s : St) : Prop :=
  s.frozen = true → s.item.lo ≤ s.target ∧ ∀ h, s.item.hi = some h → s.target ≤ max s.item.lo h

theorem within_step (tv : Int) (p : Cand) (h : Within p.1) : Within (step tv p) := by
  unfold step
  split
  · exact h
  · intro _
    refine ⟨le_clamp _ _ _, ?_⟩
    intro hi hhi
    simp only at hhi ⊢
    unfold clamped; rw [hhi]; exact clamp_le _ _ _

theorem within_init (g : Bool) (i : Item) : Within (init g i) := by
  intro _
  refine ⟨le_clamp _ _ _, ?_⟩
  intro hi hhi
  simp only [init] at hhi ⊢
  unfold Item.hyp; rw [hhi]; exact clamp_le _ _ _

theorem resolve_within (room : Int) (items : List Item) : ∀ s ∈ (resolve room items).items, Within s := by
  unfold resolve
  have h := loop_inv (ctxOf room items) (fun l _ => ∀ s ∈ l, Within s)
    (fun l e hl _ => by
      intro s hs
      unfold round at hs
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
      apply within_step
      apply hl
      rw [← cands_fst (ctxOf room items) l]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    items.length (items.map (init (ctxOf room items).growing)) false
    (by intro s hs; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs; exact within_init _ _)
  exact h

/-- The number of items not yet frozen. -/
def unfrozen (l : List St) : Nat := l.countP (fun s => !s.frozen)

theorem all_frozen_of_unfrozen_zero (l : List St) (h : unfrozen l = 0) : l.all (·.frozen) = true := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    unfold unfrozen at h ih
    rw [List.countP_cons] at h
    cases hs : s.frozen with
    | true => simp only [hs, Bool.not_true] at h; simp [hs]; simpa using ih (by simpa using h)
    | false => simp [hs] at h

theorem countP_lt_of_flip {α : Type} (L : List α) (f g : α → Bool) (hle : ∀ x, f x = true → g x = true)
    (hex : ∃ x ∈ L, g x = true ∧ f x = false) : L.countP f < L.countP g := by
  induction L with
  | nil => obtain ⟨x, hx, _⟩ := hex; simp at hx
  | cons a rest ih =>
    have hmono : rest.countP f ≤ rest.countP g := List.countP_mono_left (fun x _ => hle x)
    rw [List.countP_cons, List.countP_cons]
    obtain ⟨x, hx, hg, hf⟩ := hex
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hg, hf]; omega
    · have := ih ⟨x, hx', hg, hf⟩
      cases hfa : f a with
      | true => simp [hle a hfa]; omega
      | false => cases hga : g a <;> simp <;> omega

theorem exists_pos_of_sum_pos {α : Type} (L : List α) (f : α → Int) (h : 0 < (L.map f).sum) :
    ∃ x ∈ L, 0 < f x := by
  induction L with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases ha : 0 < f a
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨x, hx, hpos⟩ := ih (by omega)
      exact ⟨x, List.mem_cons_of_mem a hx, hpos⟩

theorem exists_neg_of_sum_neg {α : Type} (L : List α) (f : α → Int) (h : (L.map f).sum < 0) :
    ∃ x ∈ L, f x < 0 := by
  induction L with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases ha : f a < 0
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨x, hx, hneg⟩ := ih (by omega)
      exact ⟨x, List.mem_cons_of_mem a hx, hneg⟩

theorem step_frozen_of_freezes (tv : Int) (p : Cand) (h : freezes tv p = true) : (step tv p).frozen = true := by
  unfold step
  cases hf : p.1.frozen <;> simp [hf, h]

/-- Progress. Says: a round that starts with an unfrozen item ends with fewer unfrozen
items. -/
theorem round_decreases (c : Ctx) (l : List St) (h : ¬ (l.all (·.frozen) = true)) :
    unfrozen (round c l) < unfrozen l := by
  have hfst := congrArg unfrozen (cands_fst c l)
  rw [← hfst]
  unfold round unfrozen
  rw [List.countP_map, List.countP_map]
  apply countP_lt_of_flip
  · intro p hp
    simp only [Function.comp_apply, Bool.not_eq_eq_eq_not, Bool.not_true] at hp ⊢
    cases hf : p.1.frozen with
    | false => rfl
    | true => rw [step_frozen_of_frozen _ _ hf] at hp; exact absurd hp (by simp)
  · -- some unfrozen item is frozen by the round
    have hwit : ∃ p ∈ cands c l, p.1.frozen = false ∧ freezes (totalViolation c l) p = true := by
      by_cases h0 : totalViolation c l = 0
      · have : ∃ s ∈ l, s.frozen = false := by
          simpa using h
        obtain ⟨s, hs, hsf⟩ := this
        rw [← cands_fst c l] at hs
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
        exact ⟨p, hp, hsf, by simp [freezes, h0]⟩
      · by_cases hpos : 0 < totalViolation c l
        · obtain ⟨p, hp, hv⟩ := exists_pos_of_sum_pos (cands c l) violation hpos
          unfold violation at hv
          cases hf : p.1.frozen with
          | true => simp [hf] at hv
          | false =>
            simp only [hf, Bool.false_eq_true, if_false] at hv
            exact ⟨p, hp, hf, by simp [freezes, hpos]; omega⟩
        · have hneg : totalViolation c l < 0 := by omega
          obtain ⟨p, hp, hv⟩ := exists_neg_of_sum_neg (cands c l) violation hneg
          unfold violation at hv
          cases hf : p.1.frozen with
          | true => simp [hf] at hv
          | false =>
            simp only [hf, Bool.false_eq_true, if_false] at hv
            exact ⟨p, hp, hf, by simp [freezes, hneg]; omega⟩
    obtain ⟨p, hp, hf, hfr⟩ := hwit
    exact ⟨p, hp, by simp [hf], by simp [step_frozen_of_freezes _ _ hfr]⟩

theorem loop_frozen (c : Ctx) : ∀ (n : Nat) (l : List St) (e : Bool), unfrozen l ≤ n →
    (loop c n l e).1.all (·.frozen) = true := by
  intro n
  induction n with
  | zero => intro l e h; simpa [loop] using all_frozen_of_unfrozen_zero l (by omega)
  | succ n ih =>
    intro l e h
    unfold loop
    split
    · rename_i hf; exact hf
    · rename_i hf
      exact ih _ _ (by have := round_decreases c l hf; omega)

/-- Termination. Says: resolving the flexible lengths of n items is complete after at
most n rounds: every item of the result is frozen, so its size is final. Does not say:
how many rounds a given line takes (often one or two). -/
theorem resolve_frozen (room : Int) (items : List Item) :
    (resolve room items).items.all (·.frozen) = true := by
  unfold resolve
  apply loop_frozen
  unfold unfrozen
  have := List.countP_le_length (p := fun (s : St) => !s.frozen) (l := items.map (init (ctxOf room items).growing))
  simpa using this

/-- Bounds. Says: every used main size is at least the item's minimum, and at most its
maximum unless the minimum is larger (then it is the minimum): CSS 2.1 §10.4's rule that
a minimum wins. Does not say: that the size is the one a given browser computes. -/
theorem resolve_bounds (room : Int) (items : List Item) : ∀ s ∈ (resolve room items).items,
    s.item.lo ≤ s.cur ∧ ∀ h, s.item.hi = some h → s.cur ≤ max s.item.lo h := by
  intro s hs
  have hf : s.frozen = true := by
    have := resolve_frozen room items
    rw [List.all_eq_true] at this
    exact this s hs
  have := resolve_within room items s hs hf
  simpa [St.cur, hf] using this

theorem sum_map_add3 {α : Type} (L : List α) (F A B C : α → Int) (h : ∀ x ∈ L, F x = A x + B x + C x) :
    (L.map F).sum = (L.map A).sum + (L.map B).sum + (L.map C).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    have ha := h a List.mem_cons_self
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_map_natCast (l : List Nat) : (l.map fun (q : Nat) => (q : Int)).sum = (l.sum : Int) := by
  induction l with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_map_neg_natCast (l : List Nat) : (l.map fun (q : Nat) => -(q : Int)).sum = -(l.sum : Int) := by
  induction l with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- The signed shares of a round sum to the signed amount when some weight is not zero. -/
theorem shares_sum (c : Ctx) (l : List St) (h : 0 < (l.map (weight c.growing)).sum) :
    (shares c l).sum = if c.growing then (amount c l : Int) else -(amount c l : Int) := by
  unfold shares
  cases hg : c.growing with
  | true => simp only [if_true]; rw [sum_map_natCast, distribute_sum _ _ (by simpa [hg] using h)]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [sum_map_neg_natCast, distribute_sum _ _ (by simpa [hg] using h)]

/-- A frozen item is handed nothing. -/
theorem cands_frozen_zero (c : Ctx) (l : List St) : ∀ p ∈ cands c l, p.1.frozen = true → p.2 = 0 := by
  intro p hp hf
  unfold cands shares at hp
  rw [List.zip_map_right] at hp
  obtain ⟨⟨s, q⟩, hsq, rfl⟩ := List.mem_map.mp hp
  have hw : (weight c.growing s, q) ∈ (l.map (weight c.growing)).zip
      (distribute (amount c l) (l.map (weight c.growing))) := by
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨(s, q), hsq, rfl⟩
  have hq : q = 0 := distribute_zero _ _ _ hw (by
    simp only [Prod.map_fst, id_eq] at hf
    simp [weight, hf])
  simp [hq]

/-- Exactness of one round. Says: when a round is exact (`exactRound`), every item is
frozen after it and the outer sizes sum to exactly the room. -/
theorem round_exact (c : Ctx) (l : List St) (h : exactRound c l = true) :
    (round c l).all (·.frozen) = true ∧ used (round c l) = c.room := by
  unfold exactRound at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, total_eq_sum] at h
  obtain ⟨⟨hw, hamt⟩, htv⟩ := h
  constructor
  · unfold round
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hs
    cases hf : p.1.frozen with
    | true => exact step_frozen_of_frozen _ _ hf
    | false => exact step_frozen_of_freezes _ _ (by simp [freezes, htv])
  · unfold used round
    rw [List.map_map]
    rw [sum_map_add3 (cands c l) (St.outer ∘ step (totalViolation c l)) (fun p => p.1.outer) (fun p => p.2) violation]
    · have h1 : ((cands c l).map fun p => p.1.outer).sum = used l := by
        have := congrArg (fun x => (x.map St.outer).sum) (cands_fst c l)
        simpa [List.map_map, Function.comp_def, used] using this
      have h2 : ((cands c l).map fun p => p.2).sum = (shares c l).sum := by
        have := congrArg List.sum (cands_snd c l)
        simpa using this
      have h3 : ((cands c l).map violation).sum = 0 := htv
      rw [h1, h2, h3, shares_sum c l hw, hamt]
      omega
    · intro p hp
      simp only [Function.comp_apply]
      unfold step violation
      cases hf : p.1.frozen with
      | true => simp [cands_frozen_zero c l p hp hf]
      | false =>
        simp only [Bool.false_or, htv, freezes, decide_true, Bool.true_or, Bool.not_true,
          Bool.false_eq_true, if_false]
        simp only [St.outer, St.cur, hf, Bool.false_eq_true, if_false, if_true, unclamped]
        omega

/-- Exact sum. Says: when `resolve` reports `exact` (its last round handed out all of
the free space to items with a non-zero weight and the limits moved nothing in total),
the outer main sizes of the items sum to exactly `room`: with the gaps, the container's
inner main size, with no unit lost or made by rounding. Does not say: anything when
`exact` is false (every flexible item hit a limit, the factors sum to less than 1, or
no item can flex): then the line may underflow or overflow, as the specification has it. -/
theorem resolve_exact (room : Int) (items : List Item) (h : (resolve room items).exact = true) :
    used (resolve room items).items = room := by
  unfold resolve at h ⊢
  have hinv := loop_inv (ctxOf room items) (fun l e => e = true → used l = room)
    (fun l e _ _ he => (round_exact (ctxOf room items) l he).2) items.length
    (items.map (init (ctxOf room items).growing)) false (by simp)
  exact hinv h

theorem used_eq (l : List St) : used l = (l.map St.cur).sum + (l.map fun s => s.item.edges).sum := by
  unfold used
  induction l with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, St.outer] at ih ⊢; omega

/-- The same as a sum of sizes: the used main sizes and the items' edges sum to `room`. -/
theorem resolve_exact_sizes (room : Int) (items : List Item) (h : (resolve room items).exact = true) :
    (resolve room items).sizes.sum + (items.map (·.edges)).sum = room := by
  have hu := resolve_exact room items h
  have hi := congrArg (fun l => (l.map Item.edges).sum) (resolve_items room items)
  simp only [List.map_map, Function.comp_def] at hi
  rw [used_eq, hi] at hu
  exact hu

#guard (resolve 6400 [{base := 0, grow := one}, {base := 0, grow := one}, {base := 0, grow := one}]).sizes == [2133, 2133, 2134]
#guard (resolve 6400 [{base := 0, grow := one}, {base := 0, grow := one}, {base := 0, grow := one}]).exact
-- a maximum takes an item out; the others share the rest
#guard (resolve 600 [{base := 0, grow := one, hi := some 100}, {base := 0, grow := one}, {base := 100}]).sizes == [100, 400, 100]
-- shrinking in proportion to shrink factor times base size (CSS Flexbox 1 §9.7, example 6 sizes ×1)
#guard (resolve 300 [{base := 200}, {base := 400}]).sizes == [100, 200]
#guard (resolve 300 [{base := 200, lo := 150}, {base := 400}]).sizes == [150, 150]
-- factors that sum to less than 1 hand out that fraction of the free space
#guard (resolve 1000 [{base := 0, grow := 250000}, {base := 0, grow := 250000}]).sizes == [250, 250]
#guard !(resolve 1000 [{base := 0, grow := 250000}, {base := 0, grow := 250000}]).exact
-- nothing can flex
#guard (resolve 1000 [{base := 100, shrink := 0}, {base := 200}]).sizes == [100, 200]
#guard (resolve 100 []).sizes == []

/-! ### Main-axis placement (§9.5) -/

/-- `justify-content` (and `align-content`) as distribution along an axis whose start is
the side items are placed from. The glue maps `flex-start`, `flex-end`, `start`, `end`,
`left` and `right` to `start` or `end_` for the axis direction. -/
inductive Justify where
  | start | end_ | center | spaceBetween | spaceAround | spaceEvenly
  deriving Repr, BEq, DecidableEq

/-- CSS Box Alignment 3 §4.5 for `n` items and `free` space left on the line: the offset
of the first item from the line's start, and the space added between adjacent items. The
`space-*` values with no free space or (for `space-between`) one item fall back to `start`
(`space-between`) or to safe centring, which is `start` when the items overflow. -/
def justify (j : Justify) (free : Int) (n : Nat) : Int × Int :=
  if n = 0 then (0, 0) else
  match j with
  | .start => (0, 0)
  | .end_ => (free, 0)
  | .center => (free / 2, 0)
  | .spaceBetween => if free ≤ 0 ∨ n = 1 then (0, 0) else (0, free / ((n : Int) - 1))
  | .spaceAround => if free ≤ 0 then (0, 0) else (free / (n : Int) / 2, free / (n : Int))
  | .spaceEvenly => if free ≤ 0 then (0, 0) else (free / ((n : Int) + 1), free / ((n : Int) + 1))

/-- Lemma. Says: content distribution never moves adjacent items towards each other. -/
theorem justify_between_nonneg (j : Justify) (free : Int) (n : Nat) : 0 ≤ (justify j free n).2 := by
  unfold justify
  split
  · simp
  · rename_i hn
    cases j <;> simp only
    all_goals try omega
    · split
      · simp
      · rename_i h; exact Int.ediv_nonneg (by omega) (by omega)
    · split
      · simp
      · rename_i h; exact Int.ediv_nonneg (by omega) (by omega)
    · split
      · simp
      · rename_i h; exact Int.ediv_nonneg (by omega) (by omega)

/-- Containment. Says: with free space that is not negative, the first item does not
start before the line's start, and the offset plus the spaces between `n` items is no
more than the free space: the last item ends inside the line. Does not say: anything
for negative free space (then `end_` and `center` overflow the start, as specified). -/
theorem justify_fits (j : Justify) (free : Int) (n : Nat) (h : 0 ≤ free) :
    0 ≤ (justify j free n).1 ∧ (justify j free n).1 + (justify j free n).2 * ((n : Int) - 1) ≤ free := by
  unfold justify
  split
  · simp; exact h
  · rename_i hn
    have hn1 : (1 : Int) ≤ n := by omega
    cases j <;> simp only
    · omega
    · omega
    · have := Int.ediv_nonneg h (by omega : (0 : Int) ≤ 2)
      have := Int.ediv_le_self 2 h
      omega
    · split
      · omega
      · rename_i hc
        have hd : (0 : Int) < (n : Int) - 1 := by omega
        have := Int.ediv_mul_le free (Int.ne_of_gt hd)
        dsimp only
        omega
    · split
      · omega
      · have hb := Int.ediv_nonneg h (by omega : (0 : Int) ≤ (n : Int))
        have hm := Int.ediv_mul_le free (by omega : (n : Int) ≠ 0)
        have h2 := Int.ediv_le_self 2 hb
        have h3 := Int.ediv_nonneg hb (by omega : (0 : Int) ≤ 2)
        have he : free / (n : Int) * ((n : Int) - 1) = free / (n : Int) * (n : Int) - free / (n : Int) := by
          rw [Int.mul_sub, Int.mul_one]
        rw [he]
        omega
    · split
      · omega
      · have hb := Int.ediv_nonneg h (by omega : (0 : Int) ≤ (n : Int) + 1)
        have hm := Int.ediv_mul_le free (by omega : (n : Int) + 1 ≠ 0)
        have he : free / ((n : Int) + 1) * ((n : Int) - 1) = free / ((n : Int) + 1) * ((n : Int) + 1) - 2 * (free / ((n : Int) + 1)) := by
          rw [Int.mul_sub, Int.mul_add, Int.mul_one]; omega
        rw [he]
        omega

/-- The loop of `place`. -/
def placeLoop (between : Int) (pos : Int) (acc : Array (Int × Int)) : List Int → Array (Int × Int)
  | [] => acc
  | w :: rest => placeLoop between (pos + w + between) (acc.push (pos, w)) rest

/-- Boxes of the sizes `outers` placed one after another from `start`, `between` apart:
each as `(position, size)`. -/
def place (start between : Int) (outers : List Int) : List (Int × Int) :=
  (placeLoop between start #[] outers).toList

theorem placeLoop_pairwise (between : Int) (hb : 0 ≤ between) (outers : List Int) :
    ∀ (pos : Int) (acc : Array (Int × Int)), (∀ w ∈ outers, 0 ≤ w) →
      acc.toList.Pairwise (fun a b => a.1 + a.2 ≤ b.1) → (∀ a ∈ acc.toList, a.1 + a.2 ≤ pos) →
      (placeLoop between pos acc outers).toList.Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  induction outers with
  | nil => intro pos acc _ hp _; simpa [placeLoop] using hp
  | cons w rest ih =>
    intro pos acc hw hp hle
    have hw0 : 0 ≤ w := hw w List.mem_cons_self
    unfold placeLoop
    apply ih
    · intro x hx; exact hw x (List.mem_cons_of_mem w hx)
    · rw [Array.toList_push, List.pairwise_append]
      refine ⟨hp, by simp, ?_⟩
      intro a ha b hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact hle a ha
    · intro a ha
      rw [Array.toList_push, List.mem_append] at ha
      rcases ha with ha | ha
      · have := hle a ha; omega
      · simp only [List.mem_singleton] at ha; subst ha; simp only; omega

/-- No overlap. Says: boxes with sizes that are not negative, placed with a space
between them that is not negative, do not overlap: each ends at or before the start of
every later one. Does not say: anything for boxes with negative outer sizes (negative
margins larger than the box), which may overlap by design. -/
theorem place_pairwise (start between : Int) (outers : List Int) (hb : 0 ≤ between)
    (hw : ∀ w ∈ outers, 0 ≤ w) :
    (place start between outers).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  unfold place
  exact placeLoop_pairwise between hb outers start #[] hw (by simp) (by simp)

theorem placeLoop_snd (between : Int) (outers : List Int) : ∀ (pos : Int) (acc : Array (Int × Int)),
    (placeLoop between pos acc outers).toList.map Prod.snd = acc.toList.map Prod.snd ++ outers := by
  induction outers with
  | nil => intro pos acc; simp [placeLoop]
  | cons w rest ih => intro pos acc; simp [placeLoop, ih]

/-- Lemma. Says: `place` keeps the sizes, in order: one position per box. -/
theorem place_snd (start between : Int) (outers : List Int) :
    (place start between outers).map Prod.snd = outers := by
  simp [place, placeLoop_snd]

/-! ### Distribution without lost remainders (§9.5, CSS Box Alignment 3 §4.5) -/

/-- CSS Box Alignment 3 §4.5: the space before item `k` (from 0) of `n` on a line with
`free` space left: the offset of the first item and the spaces between the items before
`k`, together. Each is a share of the whole free space, so no remainder of a division
adds up along the line: with `space-between` the last item ends exactly at the line's
end. The `space-*` values with no free space (or, for `space-between`, one item) fall
back as `justify` does. -/
def lead (j : Justify) (free : Int) (n k : Nat) : Int :=
  if n = 0 then 0 else
  match j with
  | .start => 0
  | .end_ => free
  | .center => free / 2
  | .spaceBetween => if free ≤ 0 ∨ n = 1 then 0 else free * (k : Int) / ((n : Int) - 1)
  | .spaceAround => if free ≤ 0 then 0 else free * (2 * (k : Int) + 1) / (2 * (n : Int))
  | .spaceEvenly => if free ≤ 0 then 0 else free * ((k : Int) + 1) / ((n : Int) + 1)

/-- Lemma. Says: with free space that is not negative, no item is pulled before the
line's start. -/
theorem lead_nonneg (j : Justify) (free : Int) (n k : Nat) (h : 0 ≤ free) : 0 ≤ lead j free n k := by
  unfold lead
  split
  · omega
  · rename_i hn
    cases j <;> simp only
    · omega
    · omega
    · exact Int.ediv_nonneg h (by omega)
    · split
      · omega
      · exact Int.ediv_nonneg (Int.mul_nonneg h (by omega)) (by omega)
    · split
      · omega
      · exact Int.ediv_nonneg (Int.mul_nonneg h (by omega)) (by omega)
    · split
      · omega
      · exact Int.ediv_nonneg (Int.mul_nonneg h (by omega)) (by omega)

/-- Order. Says: with free space that is not negative, the space before an item is no
less than the space before the item before it: distribution never moves adjacent items
towards each other. -/
theorem lead_mono (j : Justify) (free : Int) (n k : Nat) (h : 0 ≤ free) :
    lead j free n k ≤ lead j free n (k + 1) := by
  unfold lead
  split
  · omega
  · rename_i hn
    cases j <;> simp only
    · omega
    · omega
    · omega
    · split
      · omega
      · rename_i hc
        apply Int.ediv_le_ediv (by omega)
        have : free * (k : Int) ≤ free * (((k + 1 : Nat) : Int)) := Int.mul_le_mul_of_nonneg_left (by omega) h
        exact this
    · split
      · omega
      · apply Int.ediv_le_ediv (by omega)
        exact Int.mul_le_mul_of_nonneg_left (by omega) h
    · split
      · omega
      · apply Int.ediv_le_ediv (by omega)
        exact Int.mul_le_mul_of_nonneg_left (by omega) h

/-- Containment. Says: with free space that is not negative, the space before any of the
`n` items is no more than the free space: the last item ends inside the line. -/
theorem lead_le (j : Justify) (free : Int) (n k : Nat) (h : 0 ≤ free) (hk : k < n) :
    lead j free n k ≤ free := by
  unfold lead
  split
  · omega
  · rename_i hn
    cases j <;> simp only
    · omega
    · omega
    · have := Int.ediv_le_self 2 h; omega
    · split
      · omega
      · rename_i hc
        have hd : (0 : Int) < (n : Int) - 1 := by omega
        have hle : free * (k : Int) ≤ free * ((n : Int) - 1) := Int.mul_le_mul_of_nonneg_left (by omega) h
        calc free * (k : Int) / ((n : Int) - 1) ≤ free * ((n : Int) - 1) / ((n : Int) - 1) := Int.ediv_le_ediv hd hle
          _ = free := Int.mul_ediv_cancel free (by omega)
    · split
      · omega
      · have hd : (0 : Int) < 2 * (n : Int) := by omega
        have hle : free * (2 * (k : Int) + 1) ≤ free * (2 * (n : Int)) := Int.mul_le_mul_of_nonneg_left (by omega) h
        calc free * (2 * (k : Int) + 1) / (2 * (n : Int)) ≤ free * (2 * (n : Int)) / (2 * (n : Int)) := Int.ediv_le_ediv hd hle
          _ = free := Int.mul_ediv_cancel free (by omega)
    · split
      · omega
      · have hd : (0 : Int) < (n : Int) + 1 := by omega
        have hle : free * ((k : Int) + 1) ≤ free * ((n : Int) + 1) := Int.mul_le_mul_of_nonneg_left (by omega) h
        calc free * ((k : Int) + 1) / ((n : Int) + 1) ≤ free * ((n : Int) + 1) / ((n : Int) + 1) := Int.ediv_le_ediv hd hle
          _ = free := Int.mul_ediv_cancel free (by omega)

/-- Exactness. Says: with `space-between`, free space and at least two items, the space
before the last item is all the free space: the last item ends exactly at the line's end,
whatever the remainder of dividing the space between the items. -/
theorem lead_between_last (free : Int) (n : Nat) (h : 0 < free) (hn : 2 ≤ n) :
    lead .spaceBetween free n (n - 1) = free := by
  unfold lead
  have h1 : ¬ n = 0 := by omega
  have h2 : ¬ (free ≤ 0 ∨ n = 1) := by omega
  simp only [h1, h2, if_false]
  have hc : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
  rw [hc]
  exact Int.mul_ediv_cancel free (by omega)

/-- The loop of `spread`: item `k` is next, `used` is the size of the items and gaps before it. -/
def spreadLoop (j : Justify) (free gap : Int) (n : Nat) (k : Nat) (used : Int) (acc : Array (Int × Int)) :
    List Int → Array (Int × Int)
  | [] => acc
  | w :: rest => spreadLoop j free gap n (k + 1) (used + w + gap) (acc.push (lead j free n k + used, w)) rest

/-- Boxes of the sizes `outers` along a line with `free` space left, `gap` apart, with the
free space distributed by `j` (`lead`): each as `(position, size)`. -/
def spread (j : Justify) (free gap : Int) (outers : List Int) : List (Int × Int) :=
  (spreadLoop j free gap outers.length 0 0 #[] outers).toList

theorem spreadLoop_pairwise (j : Justify) (free gap : Int) (n : Nat) (hf : 0 ≤ free) (hg : 0 ≤ gap)
    (outers : List Int) :
    ∀ (k : Nat) (used : Int) (acc : Array (Int × Int)), (∀ w ∈ outers, 0 ≤ w) →
      acc.toList.Pairwise (fun a b => a.1 + a.2 ≤ b.1) → (∀ a ∈ acc.toList, a.1 + a.2 ≤ lead j free n k + used) →
      (spreadLoop j free gap n k used acc outers).toList.Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  induction outers with
  | nil => intro k used acc _ hp _; simpa [spreadLoop] using hp
  | cons w rest ih =>
    intro k used acc hw hp hle
    have hw0 : 0 ≤ w := hw w List.mem_cons_self
    have hm := lead_mono j free n k hf
    unfold spreadLoop
    apply ih
    · intro x hx; exact hw x (List.mem_cons_of_mem w hx)
    · rw [Array.toList_push, List.pairwise_append]
      refine ⟨hp, by simp, ?_⟩
      intro a ha b hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact hle a ha
    · intro a ha
      rw [Array.toList_push, List.mem_append] at ha
      rcases ha with ha | ha
      · have := hle a ha; omega
      · simp only [List.mem_singleton] at ha; subst ha; simp only; omega

/-- No overlap. Says: boxes with sizes that are not negative, on a line with free space
and a gap that are not negative, do not overlap whatever the distribution: each ends at
or before the start of every later one. Does not say: anything for negative free space
(the items overflow the line; `end_` and `center` then start before it). -/
theorem spread_pairwise (j : Justify) (free gap : Int) (outers : List Int) (hf : 0 ≤ free) (hg : 0 ≤ gap)
    (hw : ∀ w ∈ outers, 0 ≤ w) :
    (spread j free gap outers).Pairwise (fun a b => a.1 + a.2 ≤ b.1) := by
  unfold spread
  exact spreadLoop_pairwise j free gap outers.length hf hg outers 0 0 #[] hw (by simp) (by simp)

theorem spreadLoop_snd (j : Justify) (free gap : Int) (n : Nat) (outers : List Int) :
    ∀ (k : Nat) (used : Int) (acc : Array (Int × Int)),
      (spreadLoop j free gap n k used acc outers).toList.map Prod.snd = acc.toList.map Prod.snd ++ outers := by
  induction outers with
  | nil => intro k used acc; simp [spreadLoop]
  | cons w rest ih => intro k used acc; simp [spreadLoop, ih]

/-- Lemma. Says: `spread` keeps the sizes, in order: one position per box. -/
theorem spread_snd (j : Justify) (free gap : Int) (outers : List Int) :
    (spread j free gap outers).map Prod.snd = outers := by
  simp [spread, spreadLoop_snd]

-- Eight boxes of 5 px in 40.09375 px (2566 units, 6 left): the last ends at the end.
#guard (spread .spaceBetween 6 0 (List.replicate 8 320)).getLast? == some (2246, 320)
#guard spread .spaceBetween 164 0 [12, 6, 18] == [(0, 12), (94, 6), (182, 18)]
#guard spread .center 100 10 [20, 30] == [(50, 20), (80, 30)]
#guard spread .end_ 100 0 [20, 30] == [(100, 20), (120, 30)]
#guard spread .spaceAround 60 0 [10, 10, 10] == [(10, 10), (40, 10), (70, 10)]
#guard spread .spaceEvenly 40 0 [10, 10, 10] == [(10, 10), (30, 10), (50, 10)]
#guard spread .spaceBetween (-5) 0 [10, 10] == [(0, 10), (10, 10)]
#guard spread .start 7 3 [] == []

/-! ### Lines (§9.3 step 5) -/

/-- The loop of `breakLines`: `count` items of total size `width` are on the open line. -/
def breakLoop (room gap : Int) (count : Nat) (width : Int) (acc : Array Nat) : List Int → Array Nat
  | [] => if count = 0 then acc else acc.push count
  | w :: rest =>
    if count = 0 then breakLoop room gap 1 w acc rest
    else if width + gap + w ≤ room then breakLoop room gap (count + 1) (width + gap + w) acc rest
    else breakLoop room gap 1 w (acc.push count) rest

/-- The items of a multi-line container collected into lines: the number of items on
each line, in order. Items are taken one by one while the next one fits in `room` with
the `gap` before it; an item that does not fit alone still gets a line. `outers` are the
items' hypothetical outer main sizes. -/
def breakLines (room gap : Int) (outers : List Int) : List Nat :=
  (breakLoop room gap 0 0 #[] outers).toList

theorem breakLoop_sum (room gap : Int) (outers : List Int) : ∀ (count : Nat) (width : Int) (acc : Array Nat),
    (breakLoop room gap count width acc outers).toList.sum = acc.toList.sum + count + outers.length := by
  induction outers with
  | nil =>
    intro count width acc
    unfold breakLoop
    split
    · rename_i h; simp [h]
    · simp
  | cons w rest ih =>
    intro count width acc
    unfold breakLoop
    split
    · rename_i h; rw [ih]; simp [h]; omega
    · split
      · rw [ih]; simp; omega
      · rw [ih]; simp; omega

/-- Partition. Says: the line sizes sum to the number of items: every item is on exactly
one line (lines are consecutive runs, so with `breakLines_pos` they partition the items
in order). -/
theorem breakLines_sum (room gap : Int) (outers : List Int) :
    (breakLines room gap outers).sum = outers.length := by
  unfold breakLines; rw [breakLoop_sum]; simp

theorem breakLoop_pos (room gap : Int) (outers : List Int) : ∀ (count : Nat) (width : Int) (acc : Array Nat),
    (∀ c ∈ acc.toList, 0 < c) → ∀ c ∈ (breakLoop room gap count width acc outers).toList, 0 < c := by
  induction outers with
  | nil =>
    intro count width acc hacc c hc
    unfold breakLoop at hc
    split at hc
    · exact hacc c hc
    · rename_i h
      rw [Array.toList_push, List.mem_append] at hc
      rcases hc with hc | hc
      · exact hacc c hc
      · simp only [List.mem_singleton] at hc; omega
  | cons w rest ih =>
    intro count width acc hacc c hc
    unfold breakLoop at hc
    split at hc
    · exact ih _ _ _ hacc c hc
    · rename_i h
      split at hc
      · exact ih _ _ _ hacc c hc
      · refine ih _ _ _ ?_ c hc
        intro d hd
        rw [Array.toList_push, List.mem_append] at hd
        rcases hd with hd | hd
        · exact hacc d hd
        · simp only [List.mem_singleton] at hd; omega

/-- Lemma. Says: no line is empty. -/
theorem breakLines_pos (room gap : Int) (outers : List Int) : ∀ c ∈ breakLines room gap outers, 0 < c := by
  unfold breakLines
  exact breakLoop_pos room gap outers 0 0 #[] (by simp)

#guard breakLines 100 0 [40, 40, 40, 40, 40] == [2, 2, 1]
#guard breakLines 100 10 [45, 45, 45] == [2, 1]
#guard breakLines 100 0 [300, 20, 20] == [1, 2]
#guard breakLines 100 0 [] == []
#guard breakLines 100 0 [0, 0, 100, 0] == [4]

/-! ### Cross-axis alignment of an item in its line (§9.6) -/

/-- `align-self` values as the algorithm reads them. `baseline` is `start` in
`alignOffset`; a caller that knows the baselines places such an item with
`baselineOffset`. -/
inductive Align where
  | start | end_ | center | stretch | baseline
  deriving Repr, BEq, DecidableEq

/-- The offset of an item's margin box of cross size `outer` from the start of a line
of cross size `line`. -/
def alignOffset (a : Align) (line outer : Int) : Int :=
  match a with
  | .start | .stretch | .baseline => 0
  | .end_ => line - outer
  | .center => (line - outer) / 2

/-- Containment. Says: an item no larger than its line lies inside the line. -/
theorem alignOffset_within (a : Align) (line outer : Int) (h : outer ≤ line) :
    0 ≤ alignOffset a line outer ∧ alignOffset a line outer + outer ≤ line := by
  unfold alignOffset
  cases a <;> simp only
  all_goals first
    | omega
    | (have h1 := Int.ediv_nonneg (by omega : 0 ≤ line - outer) (by omega : (0 : Int) ≤ 2)
       have h2 := Int.ediv_le_self 2 (by omega : 0 ≤ line - outer)
       omega)

/-! ### Baseline alignment in a line (§9.4 step 8, §8.3)

The items of a line that align by their baselines share one baseline. Each has an ascent
(from its cross-start margin edge to its baseline) and an outer cross size; its descent
is the rest. The shared baseline is as far from the line's start as the largest ascent,
and the items need the largest ascent plus the largest descent of cross size. -/

/-- The largest ascent of the baseline-aligned items `(ascent, outer)` of a line, and the
cross size they need together. -/
def baselineExtent (items : List (Int × Int)) : Int × Int :=
  let ascent := items.foldl (fun m i => max m i.1) 0
  let descent := items.foldl (fun m i => max m (i.2 - i.1)) 0
  (ascent, ascent + descent)

/-- The offset of a baseline-aligned item from the start of its line. -/
def baselineOffset (lineAscent ascent : Int) : Int := lineAscent - ascent

private theorem le_foldl_max (f : Int × Int → Int) (items : List (Int × Int)) :
    ∀ (init : Int), init ≤ items.foldl (fun m i => max m (f i)) init ∧
      ∀ i ∈ items, f i ≤ items.foldl (fun m i => max m (f i)) init := by
  induction items with
  | nil => intro init; simp
  | cons j rest ih =>
    intro init
    simp only [List.foldl_cons]
    have h := ih (max init (f j))
    refine ⟨by omega, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi'
    · omega
    · exact h.2 i hi'

/-- Says: the baselines coincide: every baseline-aligned item has its baseline at the
line's largest ascent. -/
theorem baseline_shared (items : List (Int × Int)) (i : Int × Int) :
    baselineOffset (baselineExtent items).1 i.1 + i.1 = (baselineExtent items).1 := by
  unfold baselineOffset; omega

/-- Containment. Says: a baseline-aligned item lies inside the cross size that
`baselineExtent` gives the line: it starts at or after the line's start and ends at or
before that size. -/
theorem baseline_within (items : List (Int × Int)) (i : Int × Int) (h : i ∈ items) :
    0 ≤ baselineOffset (baselineExtent items).1 i.1 ∧
      baselineOffset (baselineExtent items).1 i.1 + i.2 ≤ (baselineExtent items).2 := by
  unfold baselineOffset baselineExtent
  have ha := (le_foldl_max (fun i => i.1) items 0).2 i h
  have hd := (le_foldl_max (fun i => i.2 - i.1) items 0).2 i h
  simp only at ha hd ⊢
  omega

/-- Says: the cross size for the baseline-aligned items is never negative, and no
smaller than the largest ascent. -/
theorem baselineExtent_ge (items : List (Int × Int)) :
    0 ≤ (baselineExtent items).1 ∧ (baselineExtent items).1 ≤ (baselineExtent items).2 := by
  unfold baselineExtent
  have ha := (le_foldl_max (fun i => i.1) items 0).1
  have hd := (le_foldl_max (fun i => i.2 - i.1) items 0).1
  simp only at ha hd ⊢
  omega

#guard baselineExtent [(10, 30), (25, 30), (5, 40)] == (25, 60)
#guard baselineOffset 25 10 == 15
#guard baselineExtent [] == (0, 0)
#guard justify .spaceBetween 90 4 == (0, 30)
#guard justify .spaceAround 80 4 == (10, 20)
#guard justify .spaceEvenly 100 4 == (20, 20)
#guard justify .center (-10) 2 == (-5, 0)
#guard justify .spaceAround (-10) 2 == (0, 0)
#guard place 5 10 [20, 30, 0] == [(5, 20), (35, 30), (75, 0)]
#guard alignOffset .center 100 40 == 30 && alignOffset .end_ 100 40 == 60

end L4Factoidal.Rendering.Flex
