import Init

/- Renderer-independent integer screen-space boxes. Half-open containment and
clamped nonnegative area also apply to empty or reversed intersections. These
are bounding-box operations, not claims about rasterized pixels. -/
namespace L4Factoidal.UI.Geometry

structure Box where
  left : Int
  top : Int
  right : Int
  bottom : Int
  deriving Repr, BEq, DecidableEq

abbrev Box.Contains (b : Box) (x y : Int) : Prop :=
  b.left ≤ x ∧ x < b.right ∧ b.top ≤ y ∧ y < b.bottom

def Box.contains (b : Box) (x y : Int) : Bool := decide (b.Contains x y)
def Box.area (b : Box) : Nat := (b.right-b.left).toNat * (b.bottom-b.top).toNat

def Box.intersection (a b : Box) : Box :=
  ⟨max a.left b.left, max a.top b.top, min a.right b.right, min a.bottom b.bottom⟩
def Box.union (a b : Box) : Box :=
  ⟨min a.left b.left, min a.top b.top, max a.right b.right, max a.bottom b.bottom⟩

theorem Box.contains_iff (b : Box) (x y : Int) :
    b.contains x y = true ↔ b.Contains x y := by simp [contains]

theorem Box.intersection_contains (a b : Box) (x y : Int) :
    (a.intersection b).Contains x y ↔ a.Contains x y ∧ b.Contains x y := by
  simp only [Contains, intersection]
  omega

theorem Box.union_contains_left (a b : Box) (x y : Int) (h : a.Contains x y) :
    (a.union b).Contains x y := by
  simp only [Contains, union] at *
  omega

theorem Box.union_contains_right (a b : Box) (x y : Int) (h : b.Contains x y) :
    (a.union b).Contains x y := by
  simp only [Contains, union] at *
  omega

end L4Factoidal.UI.Geometry
