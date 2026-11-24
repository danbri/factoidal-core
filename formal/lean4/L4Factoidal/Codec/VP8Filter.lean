import L4Factoidal.Codec.VP8Intra

/-!
The VP8 keyframe deblocking filter (RFC 6386 §15). The planes entering
this pass are unfiltered, so none of the predictor reads are affected.
-/
namespace L4Factoidal.Codec.VP8

private def signedClamp (low high value : Int) : Int :=
  max low (min high value)

private structure Strength where
  limit : Nat
  inside : Nat
  variance : Nat

private def strength (control : Control) (block : FilterBlock) : Strength :=
  let globalLevel := Int.ofNat control.filterLevel
  let base := match control.segmentation with
    | none => globalLevel
    | some s =>
      let delta := s.filter[block.segment]?.getD 0
      if s.absolute then delta else globalLevel+delta
  let adjustment := match control.modeDeltas with
    | none => 0
    | some d => (d.reference[0]?.getD 0) + if block.intra4 then d.mode[0]?.getD 0 else 0
  let level := (signedClamp 0 63 (base+adjustment)).toNat
  let inside :=
    if control.sharpness == 0 then level
    else min (9-control.sharpness) (level / (if control.sharpness > 4 then 4 else 2))
  let inside := max 1 inside
  ⟨if level == 0 then 0 else 2*level+inside, inside,
    if level ≥ 40 then 2 else if level ≥ 15 then 1 else 0⟩

private structure Edge where
  p3 : Int
  p2 : Int
  p1 : Int
  p0 : Int
  q0 : Int
  q1 : Int
  q2 : Int
  q3 : Int

private def across (edge : Edge) (limit : Nat) : Bool :=
  4*(edge.p0-edge.q0).natAbs + (edge.p1-edge.q1).natAbs ≤ 2*limit+1

/-- An edge whose two closest samples alone exceed the threshold is untouched,
regardless of all the more distant samples. -/
private theorem across_rejects_jump (edge : Edge) (limit : Nat)
    (tooLarge : 2*limit+1 < 4*(edge.p0-edge.q0).natAbs) : across edge limit = false := by
  have rejected : ¬ (4*(edge.p0-edge.q0).natAbs + (edge.p1-edge.q1).natAbs ≤ 2*limit+1) := by
    omega
  simp [across, rejected]

private def smooth (edge : Edge) (inside : Nat) : Bool :=
  (edge.p3-edge.p2).natAbs ≤ inside && (edge.p2-edge.p1).natAbs ≤ inside &&
  (edge.p1-edge.p0).natAbs ≤ inside && (edge.q3-edge.q2).natAbs ≤ inside &&
  (edge.q2-edge.q1).natAbs ≤ inside && (edge.q1-edge.q0).natAbs ≤ inside

private def highVariance (edge : Edge) (variance : Nat) : Bool :=
  (edge.p1-edge.p0).natAbs > variance || (edge.q1-edge.q0).natAbs > variance

private def twoSample (e : Edge) : Edge :=
  let impulse := 3*(e.q0-e.p0) + signedClamp (-128) 127 (e.p1-e.q1)
  let right := signedClamp (-16) 15 ((impulse+4)/8)
  let left := signedClamp (-16) 15 ((impulse+3)/8)
  {e with p0 := e.p0+left, q0 := e.q0-right}

private def fourSample (e : Edge) : Edge :=
  let impulse := 3*(e.q0-e.p0)
  let right := signedClamp (-16) 15 ((impulse+4)/8)
  let left := signedClamp (-16) 15 ((impulse+3)/8)
  let outer := (right+1)/2
  {e with p1 := e.p1+outer, p0 := e.p0+left, q0 := e.q0-right, q1 := e.q1-outer}

private def sixSample (e : Edge) : Edge :=
  let impulse := signedClamp (-128) 127 (3*(e.q0-e.p0) + signedClamp (-128) 127 (e.p1-e.q1))
  let near := (27*impulse+63)/128
  let middle := (18*impulse+63)/128
  let far := (9*impulse+63)/128
  {e with p2 := e.p2+far, p1 := e.p1+middle, p0 := e.p0+near,
          q0 := e.q0-near, q1 := e.q1-middle, q2 := e.q2-far}

private def atEdge (plane : ByteArray) (center step : Nat) (simple outer : Bool)
    (parameters : Strength) : ByteArray :=
  if center < 4*step || center+3*step ≥ plane.size then plane else
  let sampleAt := fun index => Int.ofNat ((plane[index]?.getD 0).toNat)
  let e : Edge := ⟨sampleAt (center-4*step),sampleAt (center-3*step),sampleAt (center-2*step),sampleAt (center-step),
    sampleAt center,sampleAt (center+step),sampleAt (center+2*step),sampleAt (center+3*step)⟩
  let limit := parameters.limit + if outer then 4 else 0
  if !across e limit || (!simple && !smooth e parameters.inside) then plane else
  let filtered :=
    if simple || highVariance e parameters.variance then twoSample e
    else if outer then sixSample e else fourSample e
  let plane := plane.set! (center-3*step) (clipSample filtered.p2)
  let plane := plane.set! (center-2*step) (clipSample filtered.p1)
  let plane := plane.set! (center-step) (clipSample filtered.p0)
  let plane := plane.set! center (clipSample filtered.q0)
  let plane := plane.set! (center+step) (clipSample filtered.q1)
  plane.set! (center+2*step) (clipSample filtered.q2)

private def rail (plane : ByteArray) (start step along length : Nat) (simple outer : Bool)
    (parameters : Strength) : ByteArray := Id.run do
  let mut plane := plane
  for i in [:length] do
    plane := atEdge plane (start+i*along) step simple outer parameters
  return plane

private def macroblockFilter (plane : ByteArray) (stride row col side : Nat)
    (simple inner : Bool) (parameters : Strength) : ByteArray := Id.run do
  let mut plane := plane
  let start := row*side*stride + col*side
  if col > 0 then
    plane := rail plane start 1 stride side simple true parameters
  if inner then
    for i in [1:side/4] do
      plane := rail plane (start+4*i) 1 stride side simple false parameters
  if row > 0 then
    plane := rail plane start stride 1 side simple true parameters
  if inner then
    for i in [1:side/4] do
      plane := rail plane (start+4*i*stride) stride 1 side simple false parameters
  return plane

/-- Filter macroblocks in raster order and vertical edges before horizontal
edges in each macroblock. The simple filter leaves U and V untouched. -/
def loopFilter (frame : Reconstructed) : Except String Reconstructed := do
  let ⟨columns,rows,y,u,v,control,blocks⟩ := frame
  let some c := control | return frame
  if c.filterLevel == 0 then return frame
  let mut y := y
  let mut u := u
  let mut v := v
  for row in [:rows] do
    for col in [:columns] do
      let some block := blocks[row*columns+col]? | throw "missing VP8 filter record"
      let parameters := strength c block
      if parameters.limit == 0 then continue
      y := macroblockFilter y (16*columns) row col 16 c.simpleFilter block.inner parameters
      if !c.simpleFilter then
        u := macroblockFilter u (8*columns) row col 8 false block.inner parameters
        v := macroblockFilter v (8*columns) row col 8 false block.inner parameters
  return ⟨columns,rows,y,u,v,control,blocks⟩

#print axioms across_rejects_jump

end L4Factoidal.Codec.VP8
