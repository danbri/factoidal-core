/-! The boxes of inline elements on a line (CSS 2.1 §9.2.2, §9.4.2). This module has no
import from the engine. The functions are generic in the number, so that the layout uses
them on the same `Float`s as the text of the line (an inline box then ends exactly where
its last word does); what is proved is proved on whole numbers.

An inline box (a `span`, an `a`) has one box on each line that holds part of it. While a
line is laid out, the inline boxes open at a point form a stack, innermost first; each
has a frame, the horizontal extent of its border box on this line so far: from its left
border edge when it starts on this line, over everything placed inside it, to its right
border edge when it ends on this line. A frame that is closed is part of its parent with
its margins.

Proved: a frame never has a negative width (`opened_ok`, `cover_ok`, `close_ok`); what is
placed in a frame is inside it (`cover_holds`) and what was inside stays inside
(`cover_keeps`); a closed box reaches its right edge (`close_reaches`); placing touches
only the innermost frame and keeps the depth (`place_length`, `place_tail`); closing a box
leaves its parent covering its border box when its margins are not negative
(`merge_covers`). -/
namespace L4Factoidal.Rendering.InlineBox

/-- The extent of an inline box on a line: `lo` and `hi` are the left and right edges of
its border box so far. `start`: the box starts on this line, so its left border and
padding are here. -/
structure Frame (α : Type) where
  id : Nat
  lo : α
  hi : α
  start : Bool
  deriving Repr, BEq

variable {α : Type} [Min α] [Max α] [Add α] [Sub α] [OfNat α 0]

/-- A frame is well formed when it has no negative width. -/
def Frame.ok (f : Frame Int) : Prop := f.lo ≤ f.hi

/-- The frame of a box that opens at `x` (its left border edge): as wide as its left
border and padding `edge` when it starts here, empty when it continues from a line before. -/
def Frame.opened (id : Nat) (x edge : α) (start : Bool) : Frame α :=
  ⟨id, x, x + (if start then max 0 edge else 0), start⟩

/-- The frame with `[a, b]` inside it. -/
def Frame.cover (f : Frame α) (a b : α) : Frame α := {f with lo := min f.lo a, hi := max f.hi b}

/-- The frame of a box that ends at `x` (where its content ends) with the right padding
and border `edge`. -/
def Frame.close (f : Frame α) (x edge : α) : Frame α := f.cover x (x + max 0 edge)

theorem Frame.opened_ok (id : Nat) (x edge : Int) (start : Bool) : (Frame.opened id x edge start).ok := by
  unfold Frame.opened Frame.ok
  cases start <;> simp <;> omega

theorem Frame.cover_ok (f : Frame Int) (a b : Int) (h : f.ok) : (f.cover a b).ok := by
  unfold Frame.cover Frame.ok at *
  simp only
  omega

/-- Says: what is placed in a frame is inside it. -/
theorem Frame.cover_holds (f : Frame Int) (a b : Int) : (f.cover a b).lo ≤ a ∧ b ≤ (f.cover a b).hi := by
  unfold Frame.cover
  simp only
  omega

/-- Says: what was inside a frame stays inside it: a frame only grows. -/
theorem Frame.cover_keeps (f : Frame Int) (a b : Int) : (f.cover a b).lo ≤ f.lo ∧ f.hi ≤ (f.cover a b).hi := by
  unfold Frame.cover
  simp only
  omega

theorem Frame.close_ok (f : Frame Int) (x edge : Int) (h : f.ok) : (f.close x edge).ok :=
  Frame.cover_ok f _ _ h

/-- Says: a closed box reaches its right border edge, and begins no later than where its
content ended. -/
theorem Frame.close_reaches (f : Frame Int) (x edge : Int) (h : 0 ≤ edge) :
    (f.close x edge).lo ≤ x ∧ x + edge ≤ (f.close x edge).hi := by
  have := Frame.cover_holds f x (x + max 0 edge)
  unfold Frame.close
  omega

/-- Something placed from `a` to `b`: it is inside the innermost open box. (The boxes
around that one take it when the inner one closes: `merge`.) -/
def place {β : Type} (stack : List (Frame α × β)) (a b : α) : List (Frame α × β) :=
  match stack with
  | [] => []
  | (f, v) :: rest => (f.cover a b, v) :: rest

theorem place_length {β : Type} (stack : List (Frame Int × β)) (a b : Int) : (place stack a b).length = stack.length := by
  cases stack <;> rfl

theorem place_tail {β : Type} (stack : List (Frame Int × β)) (a b : Int) : (place stack a b).tail = stack.tail := by
  cases stack <;> rfl

/-- The stack `rest` (the boxes around a box that is done on this line) with that box's
frame `f` inside its parent: its border box and, on the sides that are on this line, its
margins `left` and `right`. -/
def merge {β : Type} (rest : List (Frame α × β)) (f : Frame α) (left right : α) (ended : Bool) : List (Frame α × β) :=
  place rest (f.lo - (if f.start then left else 0)) (f.hi + (if ended then right else 0))

/-- Says: with margins that are not negative, the parent of a box that is done covers
that box's border box. -/
theorem merge_covers {β : Type} (p : Frame Int) (v : β) (rest : List (Frame Int × β)) (f : Frame Int) (left right : Int)
    (ended : Bool) (hl : 0 ≤ left) (hr : 0 ≤ right) :
    ∃ q, merge ((p, v) :: rest) f left right ended = (q, v) :: rest ∧ q.lo ≤ f.lo ∧ f.hi ≤ q.hi := by
  refine ⟨p.cover (f.lo - (if f.start then left else 0)) (f.hi + (if ended then right else 0)), rfl, ?_⟩
  have h := Frame.cover_holds p (f.lo - (if f.start then left else 0)) (f.hi + (if ended then right else 0))
  constructor
  · have : f.lo - (if f.start then left else 0) ≤ f.lo := by split <;> omega
    omega
  · have : f.hi ≤ f.hi + (if ended then right else 0) := by split <;> omega
    omega

#guard (Frame.opened 7 (100 : Int) 12 true) == ⟨7, 100, 112, true⟩
#guard (Frame.opened 7 (0 : Int) 12 false) == ⟨7, 0, 0, false⟩
#guard ((Frame.opened 7 (100 : Int) 12 true).cover 112 300) == ⟨7, 100, 300, true⟩
#guard ((Frame.opened 7 (100 : Int) 12 true).cover 112 300 |>.close 300 8) == ⟨7, 100, 308, true⟩
#guard (place [((Frame.opened 2 (50 : Int) 0 true), ()), ((Frame.opened 1 (0 : Int) 0 true), ())] 50 90).map (·.1.hi) == [90, 0]
#guard (merge [((Frame.opened 1 (0 : Int) 0 true), ())] (⟨2, 50, 90, true⟩ : Frame Int) 5 5 true).map (fun p => (p.1.lo, p.1.hi)) == [(0, 95)]
-- the same functions on floating point: a box ends exactly where its content does
#guard ((Frame.opened 7 (18 : Float) 0 true).cover 18 31.714285714285715).hi == 31.714285714285715

end L4Factoidal.Rendering.InlineBox
