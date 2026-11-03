import Geometry
import Font
import SceneSVG

/-!
# Solving: the retained scene boundary

This first slice is the semantic display list shared by producers and
backends. It deliberately uses the lab's existing Lean Shape vocabulary and
integer geometry. Hosts may lower `RenderItem` values to GPU, SVG, or another
backend; they do not decide shape geometry or hit targets.
-/
namespace Solving
open NativeGraphics

structure Rect where
  left : Int
  top : Int
  right : Int
  bottom : Int
  deriving Repr, DecidableEq

def Rect.contains (r : Rect) (x y : Int) : Bool :=
  r.left ≤ x && x < r.right && r.top ≤ y && y < r.bottom

structure Node where
  id : Nat
  shape : Shape
  translateX : Int := 0
  translateY : Int := 0
  clip : Option Rect := none
  deriving Repr

structure Scene where
  width : Nat
  height : Nat
  nodes : List Node
  deriving Repr

/-- Backend-facing item. List order is painter order (back to front). -/
structure RenderItem where
  id : Nat
  shape : Shape
  translateX : Int
  translateY : Int
  clip : Option Rect
  deriving Repr

def lowerNode (n : Node) : RenderItem :=
  ⟨n.id, n.shape, n.translateX, n.translateY, n.clip⟩

def lower (s : Scene) : List RenderItem := s.nodes.map lowerNode

theorem lower_preserves_order (s : Scene) :
    (lower s).map RenderItem.id = s.nodes.map Node.id := by
  simp [lower, lowerNode]

theorem lower_preserves_shapes (s : Scene) :
    (lower s).map RenderItem.shape = s.nodes.map Node.shape := by
  simp [lower, lowerNode]

def inClip (n : Node) (x y : Int) : Bool :=
  match n.clip with
  | none => true
  | some r => r.contains x y

/-- Geometry and interaction use the same `NativeGeometry.hit` predicate.
    Translation is inverted for the query; clips are tested in scene space. -/
def hitNode (n : Node) (x y : Int) : Bool :=
  inClip n x y &&
    (NativeGeometry.hit n.shape (x - n.translateX) (y - n.translateY)).getD false

def hitTest (s : Scene) (x y : Int) : Option Nat :=
  (s.nodes.reverse.find? (fun n => hitNode n x y)).map Node.id

def uniqueNodeIds (s : Scene) : Bool := decide ((s.nodes.map Node.id).Nodup)

def labelNodes (firstId x y scale : Nat) (label : String) (paint : RGB) : List Node :=
  (NativeFont.text ⟨x,y⟩ scale label paint).zipIdx.map fun (shape,index) =>
    ⟨firstId+index, shape, 0, 0, none⟩

private def clipMarkup (index : Nat) (r : Rect) : String :=
  s!"<clipPath id=\"solving-clip-{index}\" clipPathUnits=\"userSpaceOnUse\"><rect x=\"{r.left}\" y=\"{r.top}\" width=\"{r.right-r.left}\" height=\"{r.bottom-r.top}\"/></clipPath>"

private def nodeMarkup (n : Node) : Except String String := do
  let painted ← NativeSceneSVG.shapeElements n.shape
  let content := String.join painted
  let translated :=
    if n.translateX == 0 && n.translateY == 0 then content
    else s!"<g transform=\"translate({n.translateX} {n.translateY})\">{content}</g>"
  match n.clip with
  | none => return s!"<g id=\"solving-node-{n.id}\">{translated}</g>"
  | some r =>
    if r.right ≤ r.left || r.bottom ≤ r.top then
      throw s!"Solving node {n.id} has an empty or inverted clip"
    return s!"<g id=\"solving-node-{n.id}\" clip-path=\"url(#solving-clip-{n.id})\">{translated}</g>"

/-- Inspection/export backend for the retained scene. Browser code receives a
    complete SVG document; it does not reconstruct geometry or hit regions. -/
def serializeSVG (s : Scene) (background : RGB := ⟨18,24,39⟩) : Except String String := do
  if s.width == 0 || s.height == 0 || s.width > 4096 || s.height > 4096 then
    throw "Solving viewport must be between 1 and 4096 pixels"
  if !uniqueNodeIds s then throw "Solving node IDs must be unique"
  if background.r > 255 || background.g > 255 || background.b > 255 then
    throw "Solving background color component exceeds 255"
  let definitions := String.join (s.nodes.filterMap fun n =>
    n.clip.map fun r => clipMarkup n.id r)
  let body ← (s.nodes.mapM nodeMarkup)
  let bg := s!"<rect x=\"0\" y=\"0\" width=\"{s.width}\" height=\"{s.height}\" fill=\"rgb({background.r},{background.g},{background.b})\"/>"
  return s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"100vw\" height=\"100vh\" viewBox=\"0 0 {s.width} {s.height}\" style=\"background:rgb({background.r},{background.g},{background.b})\"><defs>{definitions}</defs>{bg}{String.join body}</svg>"

theorem hitNode_requires_clip (n : Node) (x y : Int) (r : Rect)
    (outside : r.contains x y = false) :
    hitNode {n with clip := some r} x y = false := by
  simp [hitNode, inClip, outside]

theorem hitTest_returns_scene_node (s : Scene) (x y id : Nat)
    (h : hitTest s x y = some id) : id ∈ s.nodes.map Node.id := by
  unfold hitTest at h
  cases hfind : s.nodes.reverse.find? (fun n => hitNode n x y) with
  | none => simp [hfind] at h
  | some n =>
    simp [hfind] at h
    subst id
    have hn : n ∈ s.nodes := by
      have hrev : n ∈ s.nodes.reverse := List.mem_of_find?_eq_some hfind
      simpa using hrev
    exact List.mem_map.mpr ⟨n, hn, rfl⟩

/-- Programmatic producer. It creates the same retained nodes that any
    admitted SVG or HTML producer must create before backend lowering. -/
def showcase : Scene :=
  { width := 720, height := 440, nodes :=
    [ ⟨1, .segment ⟨108,130⟩ ⟨260,105⟩ 3 ⟨58,103,147⟩, 0, 0, none⟩
    , ⟨2, .segment ⟨260,105⟩ ⟨420,178⟩ 3 ⟨58,103,147⟩, 0, 0, none⟩
    , ⟨3, .segment ⟨108,130⟩ ⟨198,280⟩ 3 ⟨58,103,147⟩, 0, 0, none⟩
    , ⟨4, .segment ⟨198,280⟩ ⟨420,178⟩ 3 ⟨58,103,147⟩, 0, 0, none⟩
    , ⟨10, .circle ⟨108,130⟩ 34 ⟨34,221,177⟩, 0, 0, none⟩
    , ⟨11, .circle ⟨260,105⟩ 27 ⟨115,149,255⟩, 0, 0, none⟩
    , ⟨12, .circle ⟨420,178⟩ 39 ⟨255,172,93⟩, 0, 0, none⟩
    , ⟨13, .circle ⟨198,280⟩ 31 ⟨235,115,192⟩, 0, 0, none⟩
    , ⟨20, .rectangle ⟨490,80⟩ ⟨150,250⟩ ⟨31,42,64⟩, 0, 0, some ⟨505,95,625,300⟩⟩ ] ++
    labelNodes 100 62 38 3 "SOLVING" ⟨215,229,244⟩ ++
    labelNodes 200 512 112 2 "RETAINED" ⟨74,235,198⟩ ++
    labelNodes 300 512 137 1 "SVG SCENE" ⟨137,158,191⟩ ++
    labelNodes 400 512 190 2 "4 PEOPLE" ⟨255,183,111⟩ ++
    labelNodes 500 512 230 1 "LEAN OWNS GEOMETRY" ⟨137,158,191⟩ ++
    labelNodes 600 512 248 1 "ORDER CLIP PICK" ⟨137,158,191⟩ }

end Solving
