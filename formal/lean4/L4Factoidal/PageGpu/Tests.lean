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

-- WebGL: one front end for GLSL ES 3.00 and 1.00.
def vs300 : String := "#version 300 es
layout(location = 0) in vec2 pos;
in vec3 color;
uniform float angle;
out vec3 vcolor;
void main() {
  float s = sin(angle);
  float c = cos(angle);
  vcolor = color;
  gl_Position = vec4(pos.x * c - pos.y * s, pos.x * s + pos.y * c, 0.0, 1.0);
}"
def fs300 : String := "#version 300 es
precision mediump float;
in vec3 vcolor;
out vec4 outColor;
void main() { outColor = vec4(vcolor, 1.0); }"
def vs100 : String := "attribute vec2 pos;
attribute vec3 color;
uniform float angle;
uniform vec2 scale;
varying vec3 vcolor;
void main() {
  vcolor = color;
  for (int i = 0; i < 3; i++) { vcolor.x += 0.0; }
  gl_Position = vec4(pos * scale * cos(angle), 0.0, 1.0);
}"
def fs100 : String := "#ifdef GL_ES
precision mediump float;
#endif
varying vec3 vcolor;
void main() { gl_FragColor = vec4(vcolor, 1.0); }"
#guard ok (Glsl.compileProgram vs300 fs300)
#guard ok (Glsl.compileProgram vs100 fs100)
#guard ((Glsl.compileProgram vs100 fs100).toOption.map (·.2.json)) ==
  some "{\"attributes\":{\"pos\":0,\"color\":1},\"uniforms\":{\"angle\":[0,\"float\"],\"scale\":[8,\"vec2\"]},\"uniformSize\":16}"
#guard !ok (Glsl.compileProgram "#define X 1\nvoid main() { gl_Position = vec4(0.0); }" fs100)
#guard !ok (Glsl.compileProgram "attribute vec2 p; void main() { while (true) { } }" fs100)
#guard !ok (Glsl.compileProgram vs100 "varying vec3 other; void main() { gl_FragColor = vec4(other, 1.0); }")
#guard ok (step (run (State.empty 1) page).1 (.createProgram 20 vs100 fs100))

def vsQuad0 : String := "#version 300 es\nin vec2 pos;\nvoid main() { gl_Position = vec4(pos, 0.0, 1.0); }"
-- Refusals say why (`Wgsl.whyNot`), for the page to show.
#guard errOf (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { var x = 0.0; for (var j = 0; j < 10000; j++) { x += 1.0; } return vec4f(x); }") ==
  "shader: the for loop over j runs 10000 times; the bound is 256"
#guard errOf (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { return wave(1.0) * vec4f(1.0); }") ==
  "shader: wave(...) is neither a builtin function of the subset nor a struct; functions of your own are not in the subset"
#guard errOf (Wgsl.compile "fn wave(x: f32) -> f32 { return x; }") ==
  "shader: only @vertex and @fragment functions: functions of your own are not in the subset (write their bodies inline)"
#guard errOf (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { var i = 0; while (i < 4) { i += 1; } return vec4f(0.0); }") ==
  "shader: 'while' is not in the subset: loops are for loops with integer literal bounds, at most 256 steps"
#guard errOf (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { var x = 0.0; for (var i = 0; i < 200; i++) { for (var j = 0; j < 200; j++) { for (var k = 0; k < 30; k++) { x += 1.0; } } } return vec4f(x); }") ==
  "shader: fs costs 6160807 operations for each pixel or vertex; the bound is 1000000"
#guard errOf (Glsl.compileProgram "attribute vec2 p; void main() { while (true) { } }" fs100) ==
  "shader: 'while' is not in the subset: loops are for loops with integer literal bounds, at most 256 steps"
#guard errOf (Glsl.compileProgram vs100 "float wave(float x) { return x; }\nvoid main() { gl_FragColor = vec4(1.0); }") ==
  "shader: the function wave is not in the subset: only main (write its body inline)"

-- A GLSL name that is a WGSL reserved word: refused by Lean with the word, not by the host's compiler.
#guard errOf (Glsl.compileProgram vsQuad0 "#version 300 es\nprecision highp float;\nout vec4 c;\nvoid main() { float target = 1.0; c = vec4(target); }") ==
  "shader: target is a reserved word of WGSL; give the variable another name"

-- GLSL builtins with other WGSL forms: mod, atan(y, x), inversesqrt.
def fsMod : String := "#version 300 es
precision highp float;
out vec4 c;
void main() { float a = mod(gl_FragCoord.x, 2.0); float b = atan(1.0, a); float d = atan(b); c = vec4(a, b, d, inversesqrt(4.0)); }"
def vsQuad : String := "#version 300 es
in vec2 pos;
void main() { gl_Position = vec4(pos, 0.0, 1.0); }"
#guard ok (Glsl.compileProgram vsQuad fsMod)
#guard ((Glsl.compileProgram vsQuad fsMod).toOption.map (·.1.print)).any fun t =>
  (t.splitOn "floor((gl_FragCoord.x / 2.0))").length == 2 && (t.splitOn "atan2(1.0, a)").length == 2 &&
  (t.splitOn "atan(b)").length == 2 && (t.splitOn "inverseSqrt(4.0)").length == 2
-- gl_FragCoord counts y from the bottom, as in GL: the drawing buffer's height comes as a uniform.
#guard ((Glsl.compileProgram vsQuad fsMod).toOption.map (·.1.print)).any fun t =>
  (t.splitOn "let gl_FragCoord = vec4<f32>(gl_FragPos.x, (gl_FragHeight - gl_FragPos.y), gl_FragPos.z, gl_FragPos.w);").length == 2
#guard ((Glsl.compileProgram vsQuad fsMod).toOption.map (·.2.json)) ==
  some "{\"attributes\":{\"pos\":0},\"uniforms\":{\"gl_FragHeight\":[0,\"float\"]},\"uniformSize\":16}"
-- A program that does not read gl_FragCoord is as before (no uniform added).
#guard ((Glsl.compileProgram vs300 fs300).toOption.map (·.2.uniformSize)) == some 16

-- The binary header (op 64 + k) gives the same command as the text header.
def passText : String := "1 0 0 0 255 1 5 6 1 2 3 1 0 0"
def passNums : List Nat := [1, 0, 0, 0, 255, 1, 5, 6, 1, 2, 3, 1, 0, 0]
#guard match Wire.decode 7 passText.toUTF8, Wire.decode (Wire.binaryOp + 7) (Wire.binaryHeader passNums) with
  | .ok (.pass c1 k1 d1), .ok (.pass c2 k2 d2) => c1 == c2 && k1 == k2 && d1 == d2
  | _, _ => false
#guard match Wire.decode (Wire.binaryOp + 3) (Wire.binaryHeader [2, 8] ++ bytes 12) with
  | .ok (.writeBuffer 2 8 d) => d.size == 12
  | _ => false
-- A count that does not fit, a missing separator: refused.
#guard !ok (Wire.decode (Wire.binaryOp + 7) (Wire.binaryHeader passNums |>.extract 0 20))
#guard !ok (Wire.decode (Wire.binaryOp + 8) (ByteArray.mk #[255, 255, 255, 255, 10]))

#print axioms program_inSubset
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
