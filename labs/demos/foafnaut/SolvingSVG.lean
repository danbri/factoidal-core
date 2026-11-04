import Solving
import SVG

/-!
# Solving's parsed SVG adapter

This adapter exposes the current typed SVG frontend scene to Solving clients
and wraps both SVG and programmatic nodes in one ordered retained-scene list.
It keeps NativeSVG's Float geometry, nested group boundaries and painter order
intact and does not serialize/reparse SVG to reach the picking API. The list is
still a tagged envelope, not a common geometry algebra or backend input.
-/
namespace Solving

abbrev SVGScene := NativeSVG.Scene

/-- A retained item keeps the producer's complete geometry record. The
    programmatic branch preserves quadratic/cubic curves and bitmap glyphs;
    the SVG branch preserves Float geometry, paint, affine transform, opacity,
    dash records plus nested SVG group structure and local transforms. No branch
    is flattened to the other producer's subset. -/
inductive RetainedPayload where
  | programmatic (node : Solving.Node)
  | svgNode (node : NativeSVG.DisplayNode)
  deriving Repr

structure RetainedItem where
  id : Option Nat
  payload : RetainedPayload
  deriving Repr

/-- One ordered scene envelope for current programmatic and parsed-SVG
    producers. SVG viewBox mapping stays at scene scope and its nested group
    nodes remain intact. This is not yet one geometry algebra or GPU input. -/
structure RetainedScene where
  width : Nat
  height : Nat
  svgMapping : Option NativeSVG.Mapping
  items : List RetainedItem
  deriving Repr

private def RetainedItem.ofProgrammaticNode (node : Solving.Node) : RetainedItem :=
  ⟨some node.id,.programmatic node⟩

def RetainedScene.fromProgrammatic (scene : Solving.Scene) : RetainedScene :=
  {width:=scene.width,height:=scene.height,svgMapping:=none,
   items:=scene.nodes.map RetainedItem.ofProgrammaticNode}

private def RetainedItem.ofSVGNode (node : NativeSVG.DisplayNode) : RetainedItem :=
  ⟨none,.svgNode node⟩

def RetainedScene.fromSVG (scene : NativeSVG.Scene) : RetainedScene :=
  {width:=scene.width,height:=scene.height,svgMapping:=some scene.mapping,
   items:=scene.tree.map RetainedItem.ofSVGNode}

private def RetainedItem.svgNode? (item : RetainedItem) : Option NativeSVG.DisplayNode :=
  match item.payload with
  | .programmatic _ => none
  | .svgNode node => some node

private def RetainedItem.programmaticNode? (item : RetainedItem) : Option Solving.Node :=
  match item.payload with
  | .programmatic node => some node
  | .svgNode _ => none

theorem mapM_none_of_refused_member {α β : Type} (f : α → Option β)
    (items : List α) (item : α) (member : item ∈ items) (refused : f item = none) :
    items.mapM f = none := by
  induction items with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.mem_cons] at member
    cases hHead : f head with
    | none => simp [List.mapM_cons, hHead]
    | some value =>
      rcases member with same | member
      · subst head
        simp [refused] at hHead
      · have hTail := ih member
        simp [List.mapM_cons, hHead, hTail]

private theorem svgItems_preserved (nodes : List NativeSVG.DisplayNode) :
    nodes.mapM (RetainedItem.svgNode? ∘ RetainedItem.ofSVGNode) =
      some nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    simp [RetainedItem.ofSVGNode, RetainedItem.svgNode?, ih]

theorem RetainedScene.fromProgrammatic_preserves_ids (scene : Solving.Scene) :
    (RetainedScene.fromProgrammatic scene).items.map RetainedItem.id =
      scene.nodes.map (some ∘ Solving.Node.id) := by
  simp [RetainedScene.fromProgrammatic, RetainedItem.ofProgrammaticNode]

theorem RetainedScene.fromProgrammatic_preserves_nodes (scene : Solving.Scene) :
    (RetainedScene.fromProgrammatic scene).items.map RetainedItem.payload =
      scene.nodes.map RetainedPayload.programmatic := by
  simp [RetainedScene.fromProgrammatic, RetainedItem.ofProgrammaticNode]

private theorem programmaticItems_preserved (nodes : List Solving.Node) :
    nodes.mapM (RetainedItem.programmaticNode? ∘ RetainedItem.ofProgrammaticNode) =
      some nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp [RetainedItem.ofProgrammaticNode,
      RetainedItem.programmaticNode?, ih]

/-- Lower only an all-programmatic list. Mixed lists are refused so an SVG
    backend cannot lose native nodes through a filtering conversion. -/
def RetainedScene.toProgrammatic? (scene : RetainedScene) : Option Solving.Scene :=
  match scene.svgMapping with
  | some _ => none
  | none => do
      let nodes ← scene.items.mapM RetainedItem.programmaticNode?
      pure {width:=scene.width,height:=scene.height,nodes}

theorem RetainedScene.toProgrammatic?_refuses_svg_item
    (scene : RetainedScene) (item : RetainedItem) (node : NativeSVG.DisplayNode)
    (member : item ∈ scene.items) (isSvg : item.payload = .svgNode node) :
    scene.toProgrammatic? = none := by
  cases hMapping : scene.svgMapping with
  | some mapping => simp [RetainedScene.toProgrammatic?, hMapping]
  | none =>
    have refused : RetainedItem.programmaticNode? item = none := by
      cases item with
      | mk id payload =>
        cases payload with
        | programmatic node => simp at isSvg
        | svgNode node => rfl
    have hItems := mapM_none_of_refused_member RetainedItem.programmaticNode?
      scene.items item member refused
    simp [RetainedScene.toProgrammatic?, hMapping, hItems]

theorem RetainedScene.fromProgrammatic_roundTrips (scene : Solving.Scene) :
    (RetainedScene.fromProgrammatic scene).toProgrammatic? = some scene := by
  simp only [RetainedScene.fromProgrammatic, RetainedScene.toProgrammatic?]
  rw [List.mapM_map]
  simp [programmaticItems_preserved]

theorem RetainedScene.fromSVG_preserves_tree_order (scene : NativeSVG.Scene) :
    (RetainedScene.fromSVG scene).items.map RetainedItem.payload =
      scene.tree.map RetainedPayload.svgNode := by
  simp [RetainedScene.fromSVG, RetainedItem.ofSVGNode]

theorem RetainedScene.fromSVG_preserves_painter_order (scene : NativeSVG.Scene) :
    List.flatten ((RetainedScene.fromSVG scene).items.map fun item =>
      match item.payload with
      | .programmatic _ => []
      | .svgNode node => NativeSVG.DisplayNode.lowerFromRoot node) =
      scene.primitives := by
  rw [scene.loweringCorrect]
  simpa [RetainedScene.fromSVG, RetainedItem.ofSVGNode, Function.comp_def,
    NativeSVG.Scene.primitives] using
    (NativeSVG.DisplayNode.lowerFromRootList_flatten scene.tree)

/-- Lower only a scene made entirely from SVG frontend items back to the
    existing typed SVG backend input. Mixed scenes are refused; filtering them
    would alter painter order and silently drop content. -/
def RetainedScene.toSVGScene (scene : RetainedScene) : Except String NativeSVG.Scene :=
  match scene.svgMapping with
  | none => .error "SVG backend mapping is absent"
  | some mapping =>
    match scene.items.mapM RetainedItem.svgNode? with
    | none => .error "mixed frontend scene cannot be compiled as SVG"
    | some tree => NativeSVG.Scene.make scene.width scene.height mapping tree

/-- Compatibility option view; callers needing the exact geometry/budget
    failure use the structured toSVGScene result above. -/
def RetainedScene.toSVGScene? (scene : RetainedScene) : Option NativeSVG.Scene :=
  scene.toSVGScene.toOption

theorem RetainedScene.toSVGScene?_refuses_programmatic_item
    (scene : RetainedScene) (item : RetainedItem) (node : Solving.Node)
    (member : item ∈ scene.items) (isProgrammatic : item.payload = .programmatic node) :
    scene.toSVGScene? = none := by
  cases hMapping : scene.svgMapping with
  | none => simp [RetainedScene.toSVGScene?, RetainedScene.toSVGScene, hMapping, Except.toOption]
  | some mapping =>
    have refused : RetainedItem.svgNode? item = none := by
      cases item with
      | mk id payload =>
        cases payload with
        | programmatic node => rfl
        | svgNode node => simp at isProgrammatic
    have hItems := mapM_none_of_refused_member RetainedItem.svgNode?
      scene.items item member refused
    simp [RetainedScene.toSVGScene?, RetainedScene.toSVGScene, hMapping, hItems, Except.toOption]

theorem RetainedScene.fromSVG_roundTrips_checked (scene : NativeSVG.Scene) :
    (RetainedScene.fromSVG scene).toSVGScene = .ok scene := by
  simp only [RetainedScene.fromSVG, RetainedScene.toSVGScene]
  rw [List.mapM_map,svgItems_preserved]
  exact NativeSVG.Scene.make_existing scene

theorem RetainedScene.fromSVG_roundTrips (scene : NativeSVG.Scene) :
    (RetainedScene.fromSVG scene).toSVGScene? = some scene := by
  simp [RetainedScene.toSVGScene?,RetainedScene.fromSVG_roundTrips_checked,Except.toOption]

#print axioms RetainedScene.fromSVG_roundTrips_checked

def parseSVG (source : String) (width height : Nat := 0) : Except String SVGScene :=
  NativeSVG.parse source width height

/-- Topmost geometric paint item at a viewport coordinate. `Fin` makes an
    invalid paint-list index unrepresentable. This is not yet an XML element
    identity or a browser DOM event target. -/
def pickSVG (scene : SVGScene) (x y : Float) : Option (Fin scene.primitives.length) :=
  scene.hitTestAt x y

/-- A hit in the current flattened backend list, with retained enclosing
    author groups. This makes paint identity and its scene-layer ancestry one
    result; it does not yet dispatch a browser event or isolate group surfaces. -/
structure SVGPickTarget (scene : SVGScene) where
  paintIndex : Fin scene.primitives.length
  groupPath : List (Option String)
  deriving Repr

def pickSVGTarget (scene : SVGScene) (x y : Float) : Option (SVGPickTarget scene) := do
  let paintIndex ← pickSVG scene x y
  let primitive := scene.primitives[paintIndex]
  pure ⟨paintIndex, primitive.groupPath⟩

theorem pickSVGTarget_retains_group_path (scene : SVGScene) (x y : Float)
    (target : SVGPickTarget scene) (isPicked : pickSVGTarget scene x y = some target) :
    target.groupPath = scene.primitives[target.paintIndex].groupPath := by
  cases h : scene.hitTestAt x y <;> simp [pickSVGTarget, pickSVG, h] at isPicked
  cases isPicked
  rfl

end Solving
