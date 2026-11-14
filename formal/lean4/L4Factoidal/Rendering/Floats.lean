import L4Factoidal.Rendering.LayoutUnit

/-! Floats (CSS 2.1 §9.5) as pure geometry on layout units, with theorems. A float is its
margin box; a block formatting context keeps the floats placed so far. Lines and boxes
that must not overlap floats get the free band beside them (`band`); a new float goes to
the first place where it fits (`place`).

Proved: the band is inside the container and beside every float that overlaps its
vertical range (`leftEdge_ge`, `leftEdge_clears`, `rightEdge_le`, `rightEdge_clears`); a
float placed by `place` overlaps no earlier float (`place_disjoint`); clearance is below
every float of the cleared sides (`clearY_ge`, `clearY_clears`). -/
namespace L4Factoidal.Rendering.Floats

/-- The margin box of a placed float. -/
structure Box where
  /-- Floated to the left (else to the right). -/
  left : Bool
  x : Int
  y : Int
  width : Int
  height : Int
  deriving Repr, BEq

/-- The float's vertical range meets the range `h` high from `y`. -/
def Box.meets (f : Box) (y h : Int) : Bool := decide (f.y < y + h) && decide (y < f.y + f.height)

/-- Two boxes share no point: one is beside, above or below the other. -/
def disjoint (ax ay aw ah : Int) (f : Box) : Prop :=
  ax + aw ≤ f.x ∨ f.x + f.width ≤ ax ∨ ay + ah ≤ f.y ∨ f.y + f.height ≤ ay

/-- The left edge of the room beside the left floats that meet the range: not left of `x`. -/
def leftEdge (floats : List Box) (x y h : Int) : Int :=
  floats.foldl (fun e f => if f.left && f.meets y h then max e (f.x + f.width) else e) x

/-- The right edge of the room beside the right floats that meet the range: not right of `r`. -/
def rightEdge (floats : List Box) (r y h : Int) : Int :=
  floats.foldl (fun e f => if !f.left && f.meets y h then min e f.x else e) r

theorem foldl_leftEdge_ge (floats : List Box) (y h : Int) : ∀ e : Int,
    e ≤ floats.foldl (fun e f => if f.left && f.meets y h then max e (f.x + f.width) else e) e := by
  induction floats with
  | nil => intro e; simp
  | cons f rest ih =>
    intro e
    simp only [List.foldl_cons]
    split
    · exact Int.le_trans (by omega) (ih _)
    · exact ih e

/-- Lemma. Says: the room's left edge is not left of the container's. -/
theorem leftEdge_ge (floats : List Box) (x y h : Int) : x ≤ leftEdge floats x y h :=
  foldl_leftEdge_ge floats y h x

theorem foldl_leftEdge_clears (floats : List Box) (y h : Int) : ∀ e : Int, ∀ f ∈ floats,
    f.left = true → f.meets y h = true →
    f.x + f.width ≤ floats.foldl (fun e f => if f.left && f.meets y h then max e (f.x + f.width) else e) e := by
  induction floats with
  | nil => intro e f hf; simp at hf
  | cons g rest ih =>
    intro e f hf hl hm
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hf with rfl | hf'
    · simp only [hl, hm, Bool.and_self, if_true]
      exact Int.le_trans (by omega) (foldl_leftEdge_ge rest y h _)
    · exact ih _ f hf' hl hm

/-- Exclusion. Says: every left float that meets the vertical range ends at or before the
room's left edge: a line that starts at the edge does not overlap it. -/
theorem leftEdge_clears (floats : List Box) (x y h : Int) (f : Box) (hf : f ∈ floats)
    (hl : f.left = true) (hm : f.meets y h = true) : f.x + f.width ≤ leftEdge floats x y h :=
  foldl_leftEdge_clears floats y h x f hf hl hm

theorem foldl_rightEdge_le (floats : List Box) (y h : Int) : ∀ e : Int,
    floats.foldl (fun e f => if !f.left && f.meets y h then min e f.x else e) e ≤ e := by
  induction floats with
  | nil => intro e; simp
  | cons f rest ih =>
    intro e
    simp only [List.foldl_cons]
    split
    · exact Int.le_trans (ih _) (by omega)
    · exact ih e

/-- Lemma. Says: the room's right edge is not right of the container's. -/
theorem rightEdge_le (floats : List Box) (r y h : Int) : rightEdge floats r y h ≤ r :=
  foldl_rightEdge_le floats y h r

theorem foldl_rightEdge_clears (floats : List Box) (y h : Int) : ∀ e : Int, ∀ f ∈ floats,
    f.left = false → f.meets y h = true →
    floats.foldl (fun e f => if !f.left && f.meets y h then min e f.x else e) e ≤ f.x := by
  induction floats with
  | nil => intro e f hf; simp at hf
  | cons g rest ih =>
    intro e f hf hl hm
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hf with rfl | hf'
    · simp only [hl, hm, Bool.not_false, Bool.and_self, if_true]
      exact Int.le_trans (foldl_rightEdge_le rest y h _) (by omega)
    · exact ih _ f hf' hl hm

/-- Exclusion. Says: every right float that meets the vertical range starts at or after
the room's right edge. -/
theorem rightEdge_clears (floats : List Box) (r y h : Int) (f : Box) (hf : f ∈ floats)
    (hl : f.left = false) (hm : f.meets y h = true) : rightEdge floats r y h ≤ f.x :=
  foldl_rightEdge_clears floats y h r f hf hl hm

/-- The room beside the floats for a range `h` high from `y`, in a container from `x`,
`width` wide: its left edge and its width (0 when the floats leave none). -/
def band (floats : List Box) (x width y h : Int) : Int × Int :=
  let l := leftEdge floats x y h
  let r := rightEdge floats (x + width) y h
  (l, max 0 (r - l))

/-- The lowest bottom edge of the floats, and not above `y`. -/
def below (floats : List Box) (y : Int) : Int :=
  floats.foldl (fun m f => max m (f.y + f.height)) y

theorem foldl_below_ge (floats : List Box) : ∀ m : Int, m ≤ floats.foldl (fun m f => max m (f.y + f.height)) m := by
  induction floats with
  | nil => intro m; simp
  | cons f rest ih => intro m; simp only [List.foldl_cons]; exact Int.le_trans (by omega) (ih _)

theorem foldl_below_clears (floats : List Box) : ∀ m : Int, ∀ f ∈ floats,
    f.y + f.height ≤ floats.foldl (fun m f => max m (f.y + f.height)) m := by
  induction floats with
  | nil => intro m f hf; simp at hf
  | cons g rest ih =>
    intro m f hf
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact Int.le_trans (by omega) (foldl_below_ge rest _)
    · exact ih _ f hf'

/-- CSS 2.1 §9.5.2 `clear`: the top edge at or below `y` that is below every float of the
cleared sides (`left`, `right`). -/
def clearY (floats : List Box) (left right : Bool) (y : Int) : Int :=
  below (floats.filter fun f => if f.left then left else right) y

/-- Lemma. Says: clearance never moves a box up. -/
theorem clearY_ge (floats : List Box) (left right : Bool) (y : Int) : y ≤ clearY floats left right y :=
  foldl_below_ge _ y

/-- Clearance. Says: a cleared box starts below every float of the sides it clears. -/
theorem clearY_clears (floats : List Box) (left right : Bool) (y : Int) (f : Box) (hf : f ∈ floats)
    (hs : (if f.left then left else right) = true) : f.y + f.height ≤ clearY floats left right y :=
  foldl_below_clears _ y f (List.mem_filter.mpr ⟨hf, hs⟩)

/-- A box `fw` by `fh` fits beside the floats at `y`. -/
def fits (floats : List Box) (x width fw fh y : Int) : Bool :=
  decide (fw ≤ rightEdge floats (x + width) y fh - leftEdge floats x y fh)

/-- CSS 2.1 §9.5.1: where a new float `fw` by `fh` goes in a container from `x`, `width`
wide, when the flow has reached `y`: at the first of `y` and the bottom edges of the
floats below `y` where it fits beside the floats, against the left or right edge of the
room there; when it fits nowhere, below every float. The answer is its margin box's
corner. -/
def place (floats : List Box) (left : Bool) (x width fw fh y : Int) : Int × Int :=
  let candidates := y :: ((floats.map fun f => f.y + f.height).filter fun b => decide (y < b)).mergeSort
  match candidates.find? (fits floats x width fw fh) with
  | some at' => (if left then leftEdge floats x at' fh else rightEdge floats (x + width) at' fh - fw, at')
  | none => (if left then x else x + width - fw, below floats y)

/-- No overlap. Says: a float placed by `place` shares no point with
any float placed before it. Does not say: that it is inside the container (a float wider
than the container overflows it, below the other floats), nor that it is at the highest
possible place (candidates are `y` and the bottoms of floats only, which is where room
can open). -/
theorem place_disjoint (floats : List Box) (left : Bool) (x width fw fh y : Int)
    (f : Box) (hf : f ∈ floats) :
    disjoint (place floats left x width fw fh y).1 (place floats left x width fw fh y).2 fw fh f := by
  unfold place
  simp only
  split
  · rename_i at' hfound
    have hfit : fits floats x width fw fh at' = true := List.find?_some hfound
    unfold fits at hfit
    simp only [decide_eq_true_eq] at hfit
    unfold disjoint
    by_cases hm : f.meets at' fh = true
    · cases hl : f.left with
      | true =>
        have h1 := leftEdge_clears floats x at' fh f hf hl hm
        cases left with
        | true => simp only [if_true]; omega
        | false =>
          simp only [Bool.false_eq_true, if_false]
          omega
      | false =>
        have h1 := rightEdge_clears floats (x + width) at' fh f hf hl hm
        cases left with
        | true => simp only [if_true]; omega
        | false => simp only [Bool.false_eq_true, if_false]; omega
    · unfold Box.meets at hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Int.not_lt] at hm
      by_cases h1 : f.y < at' + fh
      · have := hm h1; omega
      · omega
  · have := foldl_below_clears floats y f hf
    unfold disjoint below
    omega

private def demo : List Box := [⟨true, 0, 0, 40, 30⟩, ⟨false, 160, 0, 40, 50⟩]
#guard band demo 0 200 0 10 == (40, 120)
#guard band demo 0 200 35 10 == (0, 160)
#guard band demo 0 200 50 10 == (0, 200)
#guard place demo true 0 200 100 20 0 == (40, 0)
#guard place demo true 0 200 130 20 0 == (0, 30)
#guard place demo false 0 200 170 20 0 == (30, 50)
#guard place demo true 0 200 500 20 0 == (0, 50)
#guard place [] false 0 200 50 20 7 == (150, 7)
#guard clearY demo true false 0 == 30
#guard clearY demo true true 10 == 50
#guard clearY demo false false 10 == 10

end L4Factoidal.Rendering.Floats
