import Solving

/-!
# Solving layout policy adapter

This module binds the shared renderer-independent layout policy to actual
Solving nodes. Applications nominate semantic layout participants by stable
node ID; decorative paint such as connector lines does not have to count as a
layout object. Footprints are conservative integer boxes, not exact painted
pixels or overlap-union measurements.
-/
namespace Solving

open NativeGraphics
open L4Factoidal.UI.LayoutPolicy

private def viewportBox (width height : Nat) : NativeGeometry.Box :=
  ⟨0,0,Int.ofNat width,Int.ofNat height⟩

private def shifted (x y : Int) (box : NativeGeometry.Box) : NativeGeometry.Box :=
  ⟨box.left+x,box.top+y,box.right+x,box.bottom+y⟩

private def clipBox (clip : Rect) : NativeGeometry.Box :=
  ⟨clip.left,clip.top,clip.right,clip.bottom⟩

/-- Conservative visible scene-space footprint for a node. Empty glyphs remain
    absent; a node outside its clip or viewport gets a zero-area box and cannot
    pass the policy's positive-area check. -/
def Node.policyFootprint (width height : Nat) (node : Node) : Option NativeGeometry.Box := do
  let bounds ← NativeGeometry.visibleBounds node.shape
  let moved := shifted node.translateX node.translateY bounds
  let clipped := match node.clip with
    | none => moved
    | some clip => moved.intersection (clipBox clip)
  pure (clipped.intersection (viewportBox width height))

/-- One footprint per nominated semantic participant, in application order.
    Missing IDs produce `none`, which fails the positive-area policy check. -/
def Scene.policyFootprints (scene : Scene) (participantIds : List Nat) :
    List (Option NativeGeometry.Box) :=
  participantIds.map fun id =>
    (scene.nodes.find? fun node => node.id == id).bind
      (Node.policyFootprint scene.width scene.height)

def Scene.policyChecks (scene : Scene) (cfg : Config) (participantIds : List Nat) :
    List NodeCheck :=
  checkFootprints cfg (scene.policyFootprints participantIds)

def Scene.policyCertified (scene : Scene) (cfg : Config) (participantIds : List Nat) : Bool :=
  certify cfg (scene.policyFootprints participantIds)

def Scene.validPolicyParticipants (scene : Scene) (participantIds : List Nat) : Bool :=
  !participantIds.isEmpty && decide participantIds.Nodup && uniqueNodeIds scene &&
    participantIds.all (fun id => (scene.nodes.map Node.id).contains id)

/-- A backend can require this value before accepting a scene. The selected
    application's policy proof stays attached to the immutable source scene. -/
structure CertifiedScene (cfg : Config) where
  scene : Scene
  participants : List Nat
  participantsValid : scene.validPolicyParticipants participants = true
  accepted : scene.policyCertified cfg participants = true

def certifyScene (scene : Scene) (cfg : Config) (participantIds : List Nat) :
    Option (CertifiedScene cfg) :=
  if h : scene.validPolicyParticipants participantIds = true ∧
      scene.policyCertified cfg participantIds = true then
    some ⟨scene,participantIds,h.1,h.2⟩
  else none

theorem CertifiedScene.overlapBound {cfg : Config} (certified : CertifiedScene cfg)
    (report : NodeCheck)
    (member : report ∈ certified.scene.policyChecks cfg certified.participants) :
    0 < report.area ∧
      10000 * report.overlapSum ≤ cfg.overlapBps * report.area := by
  have hcert : certify cfg
      (certified.scene.policyFootprints certified.participants) = true := certified.accepted
  exact (certify_iff cfg _).mp hcert report member

/-- Application bounds may be stricter than the experimental profile, but the
    validated config prevents the application from widening its upper limit. -/
theorem CertifiedScene.applicationOverlapBound {cfg : Config}
    (certified : CertifiedScene cfg) (report : NodeCheck)
    (member : report ∈ certified.scene.policyChecks cfg certified.participants) :
    0 < report.area ∧
      10000 * report.overlapSum ≤ cfg.application.maxOverlapBps * report.area := by
  exact certify_application_bound cfg
    (certified.scene.policyFootprints certified.participants) certified.accepted report member

theorem CertifiedScene.frequencyInProfile {cfg : Config} (_certified : CertifiedScene cfg) :
    InProfile cfg.overlapBps cfg.checkHz := cfg.within_profile

/-- The SVG backend accepts the certified scene as its input. Other backends
    can use the same `CertifiedScene` value and policy theorem. -/
def CertifiedScene.serializeSVG {cfg : Config} (certified : CertifiedScene cfg)
    (background : RGB := ⟨18,24,39⟩) : Except String String :=
  Solving.serializeSVG certified.scene background

/-- Renderer adapters share the checked semantic scene as input while choosing
    their own output type. Each adapter still needs a separate refinement
    theorem connecting its output to scene semantics. -/
structure Backend (Output : Type) where
  name : String
  render : {cfg : Config} → CertifiedScene cfg → Except String Output

def svgBackend : Backend String :=
  ⟨"web-platform-svg", fun certified => certified.serializeSVG⟩

/-- The backend-facing lowering keeps the selected IDs and every field used by
    the footprint calculation. -/
def RenderItem.policyFootprint (width height : Nat) (item : RenderItem) :
    Option NativeGeometry.Box :=
  Node.policyFootprint width height
    ⟨item.id,item.shape,item.translateX,item.translateY,item.clip⟩

private def loweredFind (scene : Scene) (id : Nat) : Option RenderItem :=
  (lower scene).find? fun item => item.id == id

private theorem find_map_lowerNode (nodes : List Node) (id : Nat) :
    (nodes.map lowerNode).find? (fun item => item.id == id) =
      (nodes.find? fun node => node.id == id).map lowerNode := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
      by_cases h : node.id == id
      · simp [h, lowerNode]
      · simp [h, ih, lowerNode]

private theorem lower_find_preserves_node (scene : Scene) (id : Nat) :
    loweredFind scene id = (scene.nodes.find? fun node => node.id == id).map lowerNode := by
  unfold loweredFind lower
  exact find_map_lowerNode scene.nodes id

def loweredPolicyFootprints (scene : Scene) (participantIds : List Nat) :
    List (Option NativeGeometry.Box) :=
  participantIds.map fun id =>
    (loweredFind scene id).bind (RenderItem.policyFootprint scene.width scene.height)

theorem lower_preserves_policyFootprints (scene : Scene) (participantIds : List Nat) :
    loweredPolicyFootprints scene participantIds = scene.policyFootprints participantIds := by
  unfold loweredPolicyFootprints Scene.policyFootprints
  apply List.map_congr_left
  intro id _
  rw [lower_find_preserves_node]
  cases hfind : scene.nodes.find? (fun node => node.id == id) with
  | none => rfl
  | some node => simp [RenderItem.policyFootprint, Node.policyFootprint, lowerNode]

theorem lower_preserves_policyChecks (scene : Scene) (cfg : Config) (participantIds : List Nat) :
    checkFootprints cfg (loweredPolicyFootprints scene participantIds) =
      scene.policyChecks cfg participantIds := by
  simp [lower_preserves_policyFootprints, Scene.policyChecks]

theorem lower_preserves_policyCertificate (scene : Scene) (cfg : Config)
    (participantIds : List Nat) :
    certify cfg (loweredPolicyFootprints scene participantIds) =
      scene.policyCertified cfg participantIds := by
  simp [lower_preserves_policyFootprints, Scene.policyCertified]

end Solving
