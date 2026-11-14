/-! Geometry of the observers of layout (Intersection Observer §2.2 and §3.2, Resize
Observer §3.4), on layout units (1/64 px). The rectangles come from the layout reads of a
page; this module decides what an `IntersectionObserver` reports about them. It has no
import from the engine. -/
namespace L4Factoidal.Rendering.Observe

/-- An axis-aligned rectangle in layout units. -/
structure Rect where
  x : Int
  y : Int
  width : Int
  height : Int
  deriving Repr, BEq, DecidableEq

def Rect.right (r : Rect) : Int := r.x + r.width
def Rect.bottom (r : Rect) : Int := r.y + r.height
def Rect.area (r : Rect) : Int := r.width * r.height

/-- Intersection Observer §3.2.7 "compute the intersection": the rectangle that two
rectangles share. Rectangles that only touch at an edge or a corner share a rectangle of
no area there (the target then counts as intersecting, §3.2.8 step 9); `none` when they
are apart. -/
def intersect (a b : Rect) : Option Rect :=
  let x0 := max a.x b.x
  let y0 := max a.y b.y
  let x1 := min a.right b.right
  let y1 := min a.bottom b.bottom
  if x0 ≤ x1 ∧ y0 ≤ y1 then some ⟨x0, y0, x1 - x0, y1 - y0⟩ else none

/-- `r` is inside `a`: none of it lies outside. -/
def Rect.within (r a : Rect) : Prop :=
  a.x ≤ r.x ∧ a.y ≤ r.y ∧ r.right ≤ a.right ∧ r.bottom ≤ a.bottom

/-- Containment. Says: what two rectangles share is inside each of them, and its width
and height are not negative. -/
theorem intersect_within (a b r : Rect) (h : intersect a b = some r) :
    r.within a ∧ r.within b ∧ 0 ≤ r.width ∧ 0 ≤ r.height := by
  unfold intersect at h
  simp only at h
  split at h
  · rename_i hc
    cases h
    simp only [Rect.within, Rect.right, Rect.bottom] at *
    omega
  · cases h

/-- Symmetry. Says: the intersection does not depend on which rectangle is the target. -/
theorem intersect_comm (a b : Rect) : intersect a b = intersect b a := by
  unfold intersect
  simp only [Int.max_comm a.x b.x, Int.max_comm a.y b.y, Int.min_comm a.right b.right, Int.min_comm a.bottom b.bottom]

/-- Says: a rectangle with sides that are not negative intersects itself in itself. -/
theorem intersect_self (a : Rect) (hw : 0 ≤ a.width) (hh : 0 ≤ a.height) : intersect a a = some a := by
  obtain ⟨x, y, w, h⟩ := a
  simp only at hw hh
  unfold intersect
  simp only [Rect.right, Rect.bottom, Int.max_self, Int.min_self]
  have hc : x ≤ x + w ∧ y ≤ y + h := by omega
  simp only [hc, and_self, if_true, Option.some.injEq, Rect.mk.injEq, true_and]
  omega

/-- Says: a target inside the root (with sides that are not negative) intersects in
itself: it is wholly visible. -/
theorem intersect_of_within (t root : Rect) (hw : 0 ≤ t.width) (hh : 0 ≤ t.height) (h : t.within root) :
    intersect t root = some t := by
  obtain ⟨x, y, w, ht⟩ := t
  obtain ⟨rx, ry, rw, rh⟩ := root
  simp only [Rect.within, Rect.right, Rect.bottom] at h hw hh
  unfold intersect
  simp only [Rect.right, Rect.bottom]
  have h1 : max x rx = x := by omega
  have h2 : max y ry = y := by omega
  have h3 : min (x + w) (rx + rw) = x + w := by omega
  have h4 : min (y + ht) (ry + rh) = y + ht := by omega
  have hc : x ≤ x + w ∧ y ≤ y + ht := by omega
  simp only [h1, h2, h3, h4, hc, and_self, if_true, Option.some.injEq, Rect.mk.injEq, true_and]
  omega

/-- Says: rectangles that are apart on an axis share nothing. -/
theorem intersect_apart (a b : Rect) (h : a.right < b.x ∨ b.right < a.x ∨ a.bottom < b.y ∨ b.bottom < a.y) :
    intersect a b = none := by
  unfold intersect
  simp only [Rect.right, Rect.bottom] at h ⊢
  have hc : ¬ (max a.x b.x ≤ min (a.x + a.width) (b.x + b.width) ∧ max a.y b.y ≤ min (a.y + a.height) (b.y + b.height)) := by omega
  simp only [hc, if_false]

/-- The root's rectangle grown by the root margins (§3.2.6): top, right, bottom, left. -/
def grow (r : Rect) (top right bottom left : Int) : Rect :=
  ⟨r.x - left, r.y - top, r.width + left + right, r.height + top + bottom⟩

/-- Says: a margin that is not negative only adds to the root: the root is inside it. -/
theorem within_grow (r : Rect) (top right bottom left : Int)
    (ht : 0 ≤ top) (hr : 0 ≤ right) (hb : 0 ≤ bottom) (hl : 0 ≤ left) : r.within (grow r top right bottom left) := by
  simp only [Rect.within, grow, Rect.right, Rect.bottom]
  omega


/-! ### Root margins (§2.2 "parse a root margin") -/

/-- One side of a root margin: a length in px, or a percentage of the root's size. -/
structure Side where
  value : Float
  percent : Bool
  deriving Repr

/-- A decimal number: an optional sign, digits, and an optional fraction. `none` for
anything else (an exponent, an empty string, a lone sign or point). -/
def decimal? (text : String) : Option Float :=
  let cs := text.toList
  let (negative, cs) := match cs with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, cs)
  let whole := cs.takeWhile Char.isDigit
  let rest := cs.dropWhile Char.isDigit
  let fraction := match rest with
    | '.' :: digits => if !digits.isEmpty && digits.all Char.isDigit then some digits else none
    | [] => some []
    | _ => none
  match fraction with
  | none => none
  | some digits =>
    if whole.isEmpty && digits.isEmpty then none
    else if whole.length + digits.length > 15 then none
    else
      let number := fun (ds : List Char) => ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
      let scale := digits.foldl (fun n _ => n * 10) 1
      -- one correctly rounded division of two exact integers: the nearest double
      let v := Float.ofNat (number (whole ++ digits)) / Float.ofNat scale
      some (if negative then -v else v)

/-- One token of a root margin: `<number>px` or `<number>%`. No other unit, and no
number without a unit (§2.2: "only px and percent"). -/
def side? (token : String) : Option Side :=
  let cs := token.toList
  if cs.length > 2 && cs.drop (cs.length - 2) == ['p', 'x'] then
    (decimal? (String.ofList (cs.take (cs.length - 2)))).map fun v => ⟨v, false⟩
  else if cs.length > 1 && cs.drop (cs.length - 1) == ['%'] then
    (decimal? (String.ofList (cs.take (cs.length - 1)))).map fun v => ⟨v, true⟩
  else none

/-- The four sides of a root margin in the order top, right, bottom, left: no token is
`0px` on every side, and one to four tokens are read as the `margin` shorthand is.
`none` for more than four tokens or a token that is not a px length or a percentage
(the constructor then throws a `SyntaxError`). -/
def margin? (text : String) : Option (List Side) :=
  let tokens := ((text.map fun c => if c == '\t' || c == '\n' || c == '\r' || c == '\x0c' then ' ' else c).splitOn " ").filter (· != "")
  let zero : Side := ⟨0, false⟩
  match tokens.map side? with
  | [] => some [zero, zero, zero, zero]
  | [some a] => some [a, a, a, a]
  | [some a, some b] => some [a, b, a, b]
  | [some a, some b, some c] => some [a, b, c, b]
  | [some a, some b, some c, some d] => some [a, b, c, d]
  | _ => none

/-- Says: a root margin that parses has four sides. -/
theorem margin?_length (text : String) (m : List Side) (h : margin? text = some m) : m.length = 4 := by
  unfold margin? at h
  simp only at h
  split at h <;> first | (cases h; rfl) | cases h

/-- A number as the page reads it back: a whole number has no fraction. -/
def numberText (v : Float) : String :=
  if v == v.round && v.abs < 1.0e15 then
    (if v < 0 then "-" else "") ++ toString v.abs.toUInt64
  else
    let s := toString v
    -- drop the zeros that `toString` pads the fraction with
    let trimmed := (s.toList.reverse.dropWhile (· == '0')).reverse
    String.ofList (if trimmed.getLast? == some '.' then trimmed.dropLast else trimmed)

def Side.text (s : Side) : String := numberText s.value ++ (if s.percent then "%" else "px")

/-- `IntersectionObserver.rootMargin` (§2.2): the four sides, separated by spaces. -/
def marginText (m : List Side) : String := " ".intercalate (m.map Side.text)

/-- A side as layout units against the root's width or height (`basis`, in units). -/
def Side.units (s : Side) (basis : Int) : Int :=
  if s.percent then
    let v := Float.ofInt basis * s.value / 100
    if v.isNaN then 0 else if v < 0 then -Int.ofNat ((-v).round.toUInt64.toNat) else Int.ofNat (v.round.toUInt64.toNat)
  else
    let v := s.value * 64
    if v.isNaN then 0 else if v < 0 then -Int.ofNat ((-v).round.toUInt64.toNat) else Int.ofNat (v.round.toUInt64.toNat)

/-- §3.2.6 the root intersection rectangle: the root's rectangle grown by the root
margin; a percentage is of the root's width for left and right, of its height for top
and bottom. -/
def rootBounds (root : Rect) (m : List Side) : Rect :=
  match m with
  | [t, r, b, l] => grow root (t.units root.height) (r.units root.width) (b.units root.height) (l.units root.width)
  | _ => root

/-! ### One observation (§3.2.8 "run the update intersection observations steps", steps 4 to 11) -/

/-- What an observer reports about a target: whether it intersects the root, the shared
rectangle, the root's bounds, the areas of the shared rectangle and of the target, and
the index of the first threshold above the ratio. -/
structure Entry where
  intersecting : Bool
  shared : Rect
  root : Rect
  sharedArea : Int
  targetArea : Int
  thresholdIndex : Nat
  deriving Repr

/-- The intersection ratio (step 10): the shared area over the target's; for a target
with no area, 1 when it intersects and 0 when not. -/
def ratio (intersecting : Bool) (sharedArea targetArea : Int) : Float :=
  if targetArea > 0 then Float.ofInt sharedArea / Float.ofInt targetArea
  else if intersecting then 1 else 0

/-- Step 11: the index of the first threshold greater than the ratio, or the number of
thresholds when none is (the thresholds are in ascending order). -/
def thresholdIndex (r : Float) (thresholds : List Float) : Nat :=
  (thresholds.takeWhile (· <= r)).length

/-- Says: the threshold index is at most the number of thresholds. -/
theorem thresholdIndex_le (r : Float) (thresholds : List Float) : thresholdIndex r thresholds ≤ thresholds.length := by
  unfold thresholdIndex
  exact (List.takeWhile_sublist _).length_le

/-- The observation of `target` (its bounding box; `none` when it has no box or is not in
the root's document) against `root` (already grown by the root margin). A target with no
box does not intersect and shares an empty rectangle at the origin. -/
def observe (target : Option Rect) (root : Rect) (thresholds : List Float) : Entry :=
  match target.bind fun t => (intersect t root).map fun r => (t, r) with
  | some (t, r) =>
    { intersecting := true, shared := r, root, sharedArea := r.area, targetArea := t.area,
      thresholdIndex := thresholdIndex (ratio true r.area t.area) thresholds }
  | none =>
    { intersecting := false, shared := ⟨0, 0, 0, 0⟩, root, sharedArea := 0, targetArea := (target.map Rect.area).getD 0,
      thresholdIndex := thresholdIndex (ratio false 0 ((target.map Rect.area).getD 0)) thresholds }

/-- Says: a target that intersects is reported with a rectangle inside the target and
inside the root's bounds; one that does not is reported as not intersecting. -/
theorem observe_shared (t root : Rect) (thresholds : List Float) :
    ((observe (some t) root thresholds).intersecting = true →
      (observe (some t) root thresholds).shared.within t ∧ (observe (some t) root thresholds).shared.within root) ∧
    ((observe (some t) root thresholds).intersecting = false → intersect t root = none) := by
  unfold observe
  simp only [Option.bind_some]
  cases h : intersect t root with
  | none => simp
  | some r =>
    simp only [Option.map_some, true_implies]
    have hw := intersect_within t root r h
    exact ⟨⟨hw.1, hw.2.1⟩, by simp⟩

/-- Says: a target with no box never intersects. -/
theorem observe_none (root : Rect) (thresholds : List Float) : (observe none root thresholds).intersecting = false := rfl

/-! ### The wire (web_api op 170) -/

private def ints (text : String) : Option (List Int) :=
  ((text.splitOn " ").filter (· != "")).mapM String.toInt?

private def rect? (text : String) : Option Rect :=
  match ints text with
  | some [x, y, w, h] => some ⟨x, y, w, h⟩
  | _ => none

/-- One observation from text: `target;root;margin;thresholds`, where `target` and `root`
are `x y width height` in layout units (`target` empty for no box), `margin` a root margin
and `thresholds` decimals in ascending order. The answer is `i sx sy sw sh rx ry rw rh
sharedArea targetArea index`, in units, `i` 1 when intersecting; `none` for text that is
not of this form. -/
def entryText (input : String) : Option String :=
  match input.splitOn ";" with
  | [target, root, margin, thresholds] =>
    match rect? root, margin? margin, ((thresholds.splitOn " ").filter (· != "")).mapM decimal? with
    | some r, some m, some ts =>
      let t := rect? target
      if target.trimAscii.toString != "" && t.isNone then none else
      let e := observe t (rootBounds r m) ts
      let rectText := fun (q : Rect) => s!"{q.x} {q.y} {q.width} {q.height}"
      some s!"{if e.intersecting then 1 else 0} {rectText e.shared} {rectText e.root} {e.sharedArea} {e.targetArea} {e.thresholdIndex}"
    | _, _, _ => none
  | _ => none

#guard intersect ⟨0, 0, 10, 10⟩ ⟨5, 5, 10, 10⟩ == some ⟨5, 5, 5, 5⟩
#guard intersect ⟨0, 0, 10, 10⟩ ⟨10, 0, 10, 10⟩ == some ⟨10, 0, 0, 10⟩
#guard intersect ⟨0, 0, 10, 10⟩ ⟨11, 0, 10, 10⟩ == none
#guard intersect ⟨2, 3, 4, 5⟩ ⟨0, 0, 100, 100⟩ == some ⟨2, 3, 4, 5⟩
#guard grow ⟨0, 0, 100, 50⟩ 10 20 30 40 == ⟨-40, -10, 160, 90⟩
-- WPT intersection-observer/observer-attributes.html and observer-exceptions.html.
#guard (margin? "").map marginText == some "0px 0px 0px 0px"
#guard (margin? " ").map marginText == some "0px 0px 0px 0px"
#guard (margin? "10% 20px").map marginText == some "10% 20px 10% 20px"
#guard (margin? "1px 2px 3px").map marginText == some "1px 2px 3px 2px"
#guard (margin? "-1.5px").map marginText == some "-1.5px -1.5px -1.5px -1.5px"
#guard (margin? "1").isNone
#guard (margin? "2em").isNone
#guard (margin? "auto").isNone
#guard (margin? "calc(1px + 2px)").isNone
#guard (margin? "1px !important").isNone
#guard (margin? "1px 1px 1px 1px 1px").isNone
#guard decimal? "0.25" == some 0.25
#guard decimal? "1e3" == none
#guard decimal? "." == none
-- A root of 100 by 50 px with "10% 20px": 5 px above and below, 20 px at the sides.
#guard (margin? "10% 20px").map (rootBounds ⟨0, 0, 6400, 3200⟩) == some ⟨-1280, -320, 8960, 3840⟩
-- Half of a 100 by 100 target is inside the root: ratio 0.5, the second of [0, 0.5, 1].
#guard (observe (some ⟨0, 50, 100, 100⟩) ⟨0, 0, 200, 100⟩ [0, 0.5, 1]).thresholdIndex == 2
#guard (observe (some ⟨0, 100, 100, 100⟩) ⟨0, 0, 200, 100⟩ [0]).intersecting
#guard (observe (some ⟨0, 100, 100, 100⟩) ⟨0, 0, 200, 100⟩ [0]).thresholdIndex == 1
#guard !(observe (some ⟨0, 101, 100, 100⟩) ⟨0, 0, 200, 100⟩ [0]).intersecting
-- apart: ratio 0, which no threshold of [0] is greater than (the index is their number);
-- the change is reported through `intersecting`
#guard (observe (some ⟨0, 101, 100, 100⟩) ⟨0, 0, 200, 100⟩ [0]).thresholdIndex == 1
#guard (observe (some ⟨0, 101, 100, 100⟩) ⟨0, 0, 200, 100⟩ [0.5]).thresholdIndex == 0
#guard (observe (some ⟨10, 10, 0, 0⟩) ⟨0, 0, 200, 100⟩ [0, 1]).thresholdIndex == 2
#guard entryText "0 50 100 100;0 0 200 100;;0 0.5 1" == some "1 0 50 100 50 0 0 200 100 5000 10000 2"
#guard entryText ";0 0 200 100;10px;0" == some "0 0 0 0 0 -640 -640 1480 1380 0 0 1"
#guard entryText "0 0 1 1;0 0 2 2;1;0" == none

end L4Factoidal.Rendering.Observe
