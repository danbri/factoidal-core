import Graphics
import L4Factoidal.UI.Geometry
import L4Factoidal.UI.LayoutPolicy

/- Lab geometry over the rendered Shape vocabulary. Integer point predicates
are mathematical predicates; Float/WGSL rounding equivalence is not proved.
Curve bounds enclose the control hull expanded by half the stroke; exact curve
hit is unsupported. Pairwise box intersection sums can double count overlap:
the checker does not compute the area of a union or actual painted pixels. -/
namespace NativeGeometry
open NativeGraphics

abbrev Box := L4Factoidal.UI.Geometry.Box
namespace Box
abbrev mk (left top right bottom : Int) : Box := ⟨left,top,right,bottom⟩
abbrev Contains (b : Box) (x y : Int) := L4Factoidal.UI.Geometry.Box.Contains b x y
abbrev contains (b : Box) (x y : Int) := L4Factoidal.UI.Geometry.Box.contains b x y
abbrev area (b : Box) := L4Factoidal.UI.Geometry.Box.area b
abbrev intersection (a b : Box) := L4Factoidal.UI.Geometry.Box.intersection a b
abbrev union (a b : Box) := L4Factoidal.UI.Geometry.Box.union a b
export L4Factoidal.UI.Geometry.Box
  (contains_iff intersection_contains union_contains_left union_contains_right)
end Box

private def pointBox (p : Point) : Box := ⟨p.x,p.y,(p.x:Int)+1,(p.y:Int)+1⟩
private def expand (b : Box) (r : Nat) : Box :=
  ⟨b.left-r,b.top-r,b.right+r,b.bottom+r⟩

-- These are conservative integer-point boxes, not tight painted-pixel bounds.
-- Rectangle drawing includes its far edge; glyph cells are half open.
def bounds : Shape → Box
  | .circle p r _ => expand (pointBox p) r
  | .rectangle p s _ => ⟨p.x,p.y,(p.x:Int)+s.x+1,(p.y:Int)+s.y+1⟩
  | .segment a b w _ => expand ((pointBox a).union (pointBox b)) ((w+1)/2)
  | .quadratic a b c w _ =>
    expand (((pointBox a).union (pointBox b)).union (pointBox c)) ((w+1)/2)
  | .cubic a b c d w _ =>
    expand ((((pointBox a).union (pointBox b)).union (pointBox c)).union (pointBox d)) ((w+1)/2)
  | .glyph p s _ _ => ⟨p.x,p.y,(p.x:Int)+5*s,(p.y:Int)+7*s⟩

def glyphRow (bits : GlyphRows) : Nat → Nat
  | 0 => bits.row0 | 1 => bits.row1 | 2 => bits.row2 | 3 => bits.row3
  | 4 => bits.row4 | 5 => bits.row5 | 6 => bits.row6 | _ => 0

def glyphBlank (bits : GlyphRows) : Bool :=
  (List.range 7).all fun i => glyphRow bits i % 32 == 0

def visibleBounds (s : Shape) : Option Box := match s with
  | .glyph _ scale bits _ => if scale == 0 || glyphBlank bits then none else some (bounds s)
  | _ => some (bounds s)

private def combine : Option Box → Option Box → Option Box
  | none, b => b | a, none => a | some a, some b => some (a.union b)

-- Recursive shape-list aggregation; no host-maintained node radius is used.
def footprint : List Shape → Option Box
  | [] => none
  | s :: ss => combine (visibleBounds s) (footprint ss)

theorem footprint_cons (s : Shape) (ss : List Shape) :
    footprint (s::ss) = combine (visibleBounds s) (footprint ss) := rfl

theorem footprint_visible (ss : List Shape) (s : Shape) (b : Box)
    (member : s ∈ ss) (visible : visibleBounds s = some b) :
    ∃ total, footprint ss = some total := by
  induction ss with
  | nil => simp at member
  | cons a rest ih =>
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst a
      cases vr : footprint rest <;> simp [footprint, visible, vr, combine]
    · obtain ⟨rb, hr⟩ := ih member
      cases va : visibleBounds a <;> simp [footprint, va, hr, combine]

theorem footprint_contains (ss : List Shape) (s : Shape) (b total : Box)
    (member : s ∈ ss) (visible : visibleBounds s = some b)
    (aggregate : footprint ss = some total) (x y : Int) (inside : b.Contains x y) :
    total.Contains x y := by
  induction ss generalizing total with
  | nil => simp at member
  | cons a rest ih =>
    simp only [List.mem_cons] at member
    simp only [footprint] at aggregate
    cases va : visibleBounds a with
    | none =>
      simp only [va, combine] at aggregate
      rcases member with same | member
      · subst a; simp [va] at visible
      · exact ih total member aggregate
    | some ab =>
      cases vr : footprint rest with
      | none =>
        simp only [va, vr, combine, Option.some.injEq] at aggregate
        subst total
        rcases member with same | member
        · subst a; simp only [va, Option.some.injEq] at visible; subst b; exact inside
        · obtain ⟨rb,hr⟩ := footprint_visible rest s b member visible
          simp [vr] at hr
      | some rb =>
        simp only [va, vr, combine, Option.some.injEq] at aggregate
        subst total
        rcases member with same | member
        · subst a; simp only [va, Option.some.injEq] at visible; subst b
          exact Box.union_contains_left _ _ _ _ inside
        · exact Box.union_contains_right _ _ _ _ (ih rb member vr)

private def distance2 (x y : Int) (p : Point) : Int :=
  (x-p.x)*(x-p.x)+(y-p.y)*(y-p.y)

-- Integer capsule predicate using cross multiplication; no division/rounding.
def capsuleHit (a b : Point) (stroke : Nat) (x y : Int) : Bool :=
  let dx := (b.x:Int)-a.x
  let dy := (b.y:Int)-a.y
  let qx := x-a.x
  let qy := y-a.y
  let length2 := dx*dx+dy*dy
  let projection := qx*dx+qy*dy
  let width2 := (stroke:Int)*stroke
  if length2 == 0 || projection ≤ 0 then decide (4*distance2 x y a ≤ width2)
  else if projection ≥ length2 then decide (4*distance2 x y b ≤ width2)
  else decide (4*(qx*dy-qy*dx)*(qx*dy-qy*dx) ≤ width2*length2)

def glyphHit (p : Point) (scale : Nat) (bits : GlyphRows) (x y : Int) : Bool :=
  if scale == 0 || x < p.x || y < p.y || x ≥ (p.x:Int)+5*scale || y ≥ (p.y:Int)+7*scale
  then false
  else
    let col := (x-p.x).toNat / scale
    let row := (y-p.y).toNat / scale
    (glyphRow bits row >>> (4-col)) &&& 1 == 1

-- none explicitly refuses exact curve hit. Circle/rectangle include boundaries.
def hit : Shape → Int → Int → Option Bool
  | .circle p r _, x, y => some (decide (distance2 x y p ≤ (r:Int)*r))
  | .rectangle p s _, x, y =>
    some (decide ((p.x:Int) ≤ x ∧ x ≤ (p.x:Int)+s.x ∧ (p.y:Int) ≤ y ∧ y ≤ (p.y:Int)+s.y))
  | .segment a b w _, x, y => some (capsuleHit a b w x y)
  | .glyph p s bits _, x, y => some (glyphHit p s bits x y)
  | .quadratic .., _, _ | .cubic .., _, _ => none

theorem rectangle_hit_in_bounds (p size : Point) (color : RGB) (x y : Int)
    (h : hit (.rectangle p size color) x y = some true) :
    (bounds (.rectangle p size color)).Contains x y := by
  simp only [hit, Option.some.injEq, decide_eq_true_eq] at h
  simp only [bounds, Box.Contains, L4Factoidal.UI.Geometry.Box.Contains]
  omega

def hitShapes : List Shape → Int → Int → Option Bool
  | [], _, _ => some false
  | s::ss, x, y => do
    let a ← hit s x y
    let b ← hitShapes ss x y
    pure (a || b)

-- Compatibility wrappers instantiate the shared experimental profile.
abbrev overlapSum := L4Factoidal.UI.LayoutPolicy.overlapSum
abbrev NodeCheck := L4Factoidal.UI.LayoutPolicy.NodeCheck
abbrev WithinBudget (area sum : Nat) : Prop :=
  L4Factoidal.UI.LayoutPolicy.Budget L4Factoidal.UI.LayoutPolicy.defaultConfig area sum

def withinBudget (area sum : Nat) : Bool :=
  L4Factoidal.UI.LayoutPolicy.withinBudget L4Factoidal.UI.LayoutPolicy.defaultConfig area sum

theorem withinBudget_iff (area sum : Nat) :
    withinBudget area sum = true ↔ 0 < area ∧ 20*sum ≤ area := by
  rw [withinBudget, L4Factoidal.UI.LayoutPolicy.withinBudget_iff]
  simp only [L4Factoidal.UI.LayoutPolicy.defaultConfig]
  omega

abbrev overlapSum_member_le := L4Factoidal.UI.LayoutPolicy.overlapSum_member_le

theorem budget_each_overlap (b other : Box) (others : List Box)
    (member : other ∈ others) (accepted : withinBudget b.area (overlapSum b others) = true) :
    20*(b.intersection other).area ≤ b.area := by
  have bound := overlapSum_member_le b other others member
  have budget := ((withinBudget_iff _ _).mp accepted).2
  simp only [Box.area, Box.intersection, overlapSum] at *
  omega

def checkFootprints (boxes : List (Option Box)) : List NodeCheck :=
  L4Factoidal.UI.LayoutPolicy.checkFootprints L4Factoidal.UI.LayoutPolicy.defaultConfig boxes

def checkLayout (nodes : List (List Shape)) : List NodeCheck :=
  checkFootprints (nodes.map footprint)

-- Clip the aggregate footprint, retaining zero-area reports for offscreen nodes.
-- This bounds visible integer geometry; it is not an exact painted-pixel count.
def checkLayoutIn (viewport : Box) (nodes : List (List Shape)) : List NodeCheck :=
  checkFootprints (nodes.map fun shapes => (footprint shapes).map (·.intersection viewport))

-- A report is a checker result, not a claim about pixel areas or GPU execution.
theorem checkFootprints_length (boxes : List (Option Box)) :
    (checkFootprints boxes).length = boxes.length := by simp [checkFootprints, L4Factoidal.UI.LayoutPolicy.checkFootprints_length]

theorem checkFootprints_accepted_iff (boxes : List (Option Box)) (report : NodeCheck)
    (member : report ∈ checkFootprints boxes) :
    report.accepted = true ↔ 0 < report.area ∧ 20*report.overlapSum ≤ report.area := by
  have accepted := L4Factoidal.UI.LayoutPolicy.checkFootprints_accepted_iff
    L4Factoidal.UI.LayoutPolicy.defaultConfig boxes report member
  simp only [L4Factoidal.UI.LayoutPolicy.defaultConfig] at accepted
  constructor
  · intro h
    have h' := accepted.mp h
    omega
  · intro h
    apply accepted.mpr
    omega

theorem checkLayout_length (nodes : List (List Shape)) :
    (checkLayout nodes).length = nodes.length := by
  simp [checkLayout, checkFootprints_length]

theorem checkLayout_accepted_iff (nodes : List (List Shape)) (report : NodeCheck)
    (member : report ∈ checkLayout nodes) :
    report.accepted = true ↔ 0 < report.area ∧ 20*report.overlapSum ≤ report.area :=
  checkFootprints_accepted_iff _ _ member

theorem checkLayoutIn_length (viewport : Box) (nodes : List (List Shape)) :
    (checkLayoutIn viewport nodes).length = nodes.length := by
  simp [checkLayoutIn, checkFootprints_length]

theorem checkLayoutIn_accepted_iff (viewport : Box) (nodes : List (List Shape)) (report : NodeCheck)
    (member : report ∈ checkLayoutIn viewport nodes) :
    report.accepted = true ↔ 0 < report.area ∧ 20*report.overlapSum ≤ report.area :=
  checkFootprints_accepted_iff _ _ member

end NativeGeometry
