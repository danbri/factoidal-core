import L4Factoidal.PageGpu.Theorems
import L4Factoidal.PageGpu.Wire

/-! Build-time tests of the page GPU model. Each `#guard` runs while the module
elaborates; a wrong answer fails the build. -/
namespace L4Factoidal.PageGpu.Tests
open L4Factoidal.PageGpu

def ok {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

def errOf {α : Type} : Except String α → String
  | .ok _ => ""
  | .error e => e

/-- The demo's shader (labs/demos/foafnaut/pages/webgpu-triangle.html). -/
def triangle : String := "
struct U { angle: f32, aspect: f32, pulse: f32, pad: f32 }
@group(0) @binding(0) var<uniform> u: U;
struct VOut { @builtin(position) pos: vec4f, @location(0) color: vec3f }
@vertex fn vs(@location(0) p: vec2f, @location(1) c: vec3f) -> VOut {
  var o: VOut;
  let s = sin(u.angle);
  let k = cos(u.angle);
  o.pos = vec4f((p.x * k - p.y * s) * u.aspect, p.x * s + p.y * k, 0.0, 1.0);
  o.color = c * (0.75 + 0.25 * u.pulse);
  return o;
}
@fragment fn fs(@location(0) color: vec3f) -> @location(0) vec4f {
  return vec4f(color, 1.0);
}
"

/-- A shader that indexes a constant array by the vertex index (no vertex buffer). -/
def indexed : String := "
@vertex fn vs(@builtin(vertex_index) i: u32) -> @builtin(position) vec4f {
  var pts = array<vec2f, 3>(vec2f(0.0, 0.5), vec2f(-0.5, -0.5), vec2f(0.5, -0.5));
  return vec4f(pts[i], 0.0, 1.0);
}
@fragment fn fs() -> @location(0) vec4f {
  var c = vec3f(0.0);
  for (var j = 0; j < 4; j++) { c += vec3f(0.25); }
  return vec4f(c, 1.0);
}
"

#guard ok (Wgsl.compile triangle)
#guard ok (Wgsl.compile indexed)
#guard (Wgsl.compile triangle).toOption.map (·.uniformSize) == some (some 16)
-- The index is clamped in the printed text.
#guard ((Wgsl.compile indexed).toOption.map (·.print)).any (fun t => (t.splitOn "pts[min(u32(i), 2u)]").length == 2)
-- Outside the subset: loops, storage, user calls, unbounded for, assigning the counter.
#guard !ok (Wgsl.compile "@vertex fn vs() -> @builtin(position) vec4f { loop { } }")
#guard !ok (Wgsl.compile "@group(0) @binding(0) var<storage, read_write> b: array<f32>;")
#guard !ok (Wgsl.compile "fn f() -> f32 { return 1.0; }")
#guard !ok (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { var x = 0.0; for (var j = 0; j < 100000; j++) { x += 1.0; } return vec4f(x); }")
#guard !ok (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { for (var j = 0; j < 4; j++) { j = 0; } return vec4f(0.0); }")
#guard !ok (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { return textureSample(t, s, vec2f(0.0)); }")
-- An index into a value of unknown length is refused.
#guard !ok (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { let a = foo; return vec4f(a[1]); }")

-- A page: canvas, buffers, shader, pipeline, bind group, one pass.
def layout : VLayout := { stride := 20, attrs := [⟨.float32x2, 0, 0⟩, ⟨.float32x3, 8, 1⟩] }
def bytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

def page : List Command := [
  .configure 1 7 256 256,
  .createBuffer 2 60 (usageVertex ||| usageCopyDst),
  .writeBuffer 2 0 (bytes 60),
  .createBuffer 3 16 (usageUniform ||| usageCopyDst),
  .createShader 4 triangle,
  .createPipeline 5 4 "vs" "fs" [layout] .triangleList,
  .createBindGroup 6 5 3,
  .pass 1 (0, 0, 0, 255) [{ pipeline := 5, bind := some 6, vbufs := [2], count := 3, instances := 1, first := 0, firstInstance := 0 }]]

#guard (run (State.empty 1) page).1.objs.length == 6
#guard (run (State.empty 1) page).2.length == 10
-- A draw that reads past its vertex buffer, a write past the end, a mappable buffer,
-- a draw on a canvas that is not there: each is refused.
#guard !ok (step (run (State.empty 1) page).1 (.pass 1 (0,0,0,0) [{ pipeline := 5, bind := some 6, vbufs := [2], count := 4, instances := 1, first := 0, firstInstance := 0 }]))
#guard !ok (step (run (State.empty 1) page).1 (.writeBuffer 2 56 (bytes 8)))
#guard !ok (step (State.empty 1) (.createBuffer 9 64 (usageMapRead ||| usageCopyDst)))
#guard !ok (step (run (State.empty 1) page).1 (.pass 9 (0,0,0,0) []))
-- The wire form of the same commands.
#guard ok (Wire.decode 2 "2 60 40\n".toUTF8)
#guard ok (Wire.decode 7 "1 0 0 0 255 1 5 6 1 2 3 1 0 0".toUTF8)
#guard Wire.base64 "Man".toUTF8 == "TWFu" && Wire.base64 "Ma".toUTF8 == "TWE="

#print axioms compile_inSubset
#print axioms compile_cost
#print axioms compile_loops
#print axioms harden_clamped
#print axioms compile_clamped
#print axioms step_safe
#print axioms write_in_bounds
#print axioms draw_in_bounds
#print axioms buffer_usage
#print axioms canvas_usage
#print axioms pass_owned
#print axioms step_createBuffer_clears
#print axioms run_quota

end L4Factoidal.PageGpu.Tests
