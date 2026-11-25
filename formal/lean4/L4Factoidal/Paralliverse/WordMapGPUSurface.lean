import L4Factoidal.Paralliverse.WordMapGPU
import L4Factoidal.Paralliverse.WGSL.Surface

/-! Exact bytes and single-invocation semantics for the two fixed word shaders. -/

namespace L4Factoidal.Paralliverse.WordMapGPU

open WGSL

private def address : Surface.Expr := .add (.literal 2) .gidX

def shaderModule (tag : KernelTag) : Surface.Module where
  first := ⟨0, 0, .read, .srcWords⟩
  second := ⟨0, 2, .readWrite, .dstWords⟩
  sizeX := 64
  sizeY := 1
  sizeZ := 1
  body := {
    left := .gidX
    right := .load .srcWords (.literal 0)
    destination := .dstWords
    address := address
    value := match tag with
      | .add => .add (.load .srcWords address) (.load .srcWords (.literal 1))
      | .multiply => .mul (.load .srcWords address) (.load .srcWords (.literal 1))
  }

set_option maxRecDepth 8192 in
/-- Kind: concrete syntax.
Says: parsing all exported UTF-8 bytes recovers each shader's actual bindings,
workgroup size, length guard, payload address and modular operation.
Does not say: that a device compiler accepts the same bytes. -/
theorem parse_shader (tag : KernelTag) :
    Surface.parseShader tag.shader.toUTF8 = some (shaderModule tag) := by
  cases tag <;> rfl

/-- Kind: source representation.
Says: the packet builder emits the length, chosen coefficient, original words
and arbitrary supplied tail in their declared order.
Does not say: that allocating a packet admits it to a GPU launch. -/
theorem packet_layout (k : UInt32) (xs tail : List UInt32) :
    (packet k xs tail).toList = UInt32.ofNat xs.length :: k :: (xs ++ tail) := by
  simp [packet]

/-- Kind: source denotation.
Says: the typed program represented by one pass maps the selected modular operation.
Does not say: that a shader executed that source program. -/
theorem eval_pass (pass : Pass) (xs : List UInt32) :
    Program.eval WordProgram.base (@WordProgram.reference) pass.program xs = xs.map pass.apply := by
  cases pass with | mk tag k => cases tag <;> rfl

/-- Expected destination and stores of one lane when its buffers meet the
capacity and layout premises of `run_module_lane`. -/
def laneEffect (pass : Pass) (xs : List UInt32) (prior : Array UInt32) (gid : UInt32) :
    Surface.Outcome :=
  if h : gid.toNat < xs.length then
    let value := pass.apply xs[gid.toNat]
    ⟨prior.setIfInBounds (2 + gid.toNat) value, [⟨0, 2, 2 + gid, value⟩]⟩
  else ⟨prior, []⟩

private def writeAt (prior : Array UInt32) (gid value : UInt32) : Option Surface.Outcome :=
  if h : (2 + gid : UInt32).toNat < prior.size then
    some ⟨prior.set (2 + gid : UInt32).toNat value h, [⟨0, 2, 2 + gid, value⟩]⟩
  else none

private theorem run_header (tag : KernelTag) (src prior : Array UInt32) (gid n : UInt32)
    (head : src[0]? = some n) :
    Surface.run (shaderModule tag) src prior gid =
      if gid < n then
        (Surface.eval (shaderModule tag) src gid (shaderModule tag).body.value).bind (writeAt prior gid)
      else some ⟨prior, []⟩ := by
  change (src[0]?).bind (fun n => if gid < n then
    (Surface.eval (shaderModule tag) src gid (shaderModule tag).body.value).bind (writeAt prior gid)
    else some ⟨prior, []⟩) = _
  rw [head] <;> rfl

private theorem eval_value (pass : Pass) (src : Array UInt32) (gid x : UInt32)
    (payload : src[(2 + gid : UInt32).toNat]? = some x) (coeff : src[1]? = some pass.coefficient) :
    Surface.eval (shaderModule pass.tag) src gid (shaderModule pass.tag).body.value =
      some (pass.apply x) := by
  have expr : Surface.eval (shaderModule pass.tag) src gid (shaderModule pass.tag).body.value =
      (src[(2 + gid : UInt32).toNat]?).bind (fun v => (src[1]?).bind
        (fun k => some ((⟨pass.tag, k⟩ : Pass).apply v))) := by
    cases pass with | mk tag k => cases tag <;> rfl
  rw [expr, payload, coeff] <;> rfl

/-- Kind: invocation semantics.
Says: from the actual packet prefix, the parsed module performs exactly one
logged modular write at its active lane's index and zero writes on a padded lane.
Does not say: that every lane has run or that native storage bindings are disjoint. -/
theorem run_module_lane (pass : Pass) (xs tail : List UInt32) (src prior : Array UInt32)
    (small : xs.length ≤ maxWords)
    (layout : src.toList = UInt32.ofNat xs.length :: pass.coefficient :: (xs ++ tail))
    (room : 2 + xs.length ≤ prior.size) (gid : UInt32) :
    Surface.run (shaderModule pass.tag) src prior gid = some (laneEffect pass xs prior gid) := by
  have head : src[0]? = some (UInt32.ofNat xs.length) := by
    rw [← Array.getElem?_toList, layout]; rfl
  have coeff : src[1]? = some pass.coefficient := by
    rw [← Array.getElem?_toList, layout]; rfl
  change xs.length ≤ 1024 at small
  have lengthWord : (UInt32.ofNat xs.length).toNat = xs.length := by
    apply UInt32.toNat_ofNat_of_lt'
    change xs.length < 4294967296
    omega
  have branch : gid < UInt32.ofNat xs.length ↔ gid.toNat < xs.length := by
    rw [UInt32.lt_iff_toNat_lt, lengthWord]
  rw [run_header pass.tag src prior gid _ head]
  by_cases active : gid.toNat < xs.length
  · have physical : (2 + gid : UInt32).toNat = 2 + gid.toNat := by
      rw [UInt32.toNat_add]
      change (2 + gid.toNat) % 4294967296 = _
      apply Nat.mod_eq_of_lt
      omega
    have payload : src[(2 + gid : UInt32).toNat]? = some xs[gid.toNat] := by
      rw [physical, ← Array.getElem?_toList, layout,
        show 2 + gid.toNat = (gid.toNat + 1) + 1 by omega]
      change (xs ++ tail)[gid.toNat]? = some xs[gid.toNat]
      rw [List.getElem?_append_left active, List.getElem?_eq_getElem active]
    have fits : 2 + gid.toNat < prior.size := by omega
    rw [if_pos (branch.mpr active), eval_value pass src gid _ payload coeff, laneEffect,
      dif_pos active]
    change writeAt prior gid (pass.apply xs[gid.toNat]) = _
    simp only [writeAt, physical, Array.setIfInBounds_def, dif_pos fits]
  · rw [if_neg (fun h => active (branch.mp h)), laneEffect, dif_neg active]

#print axioms parse_shader
#print axioms packet_layout
#print axioms eval_pass
#print axioms run_module_lane

end L4Factoidal.Paralliverse.WordMapGPU

