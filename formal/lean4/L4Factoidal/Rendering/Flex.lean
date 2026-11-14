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
- `breakLines_sum`, `breakLines_pos`: every item is on exactly one line, no line is empty. -/
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
  let fsum := (l.map (factor c.growing)).sum
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
  decide (0 < (l.map (weight c.growing)).sum) &&
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
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
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
