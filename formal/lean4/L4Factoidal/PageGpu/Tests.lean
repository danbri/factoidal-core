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
-- A storage variable is in the subset only with a compute entry point's model (below);
-- a bad access mode, a second group, or a binding out of range are refused.
#guard !ok (Wgsl.compile "@group(0) @binding(0) var<storage, write> b: array<f32>;")
#guard !ok (Wgsl.compile "@group(1) @binding(0) var<storage, read_write> b: array<f32>;")
#guard !ok (Wgsl.compile "@group(0) @binding(4) var<storage, read_write> b: array<f32>;")
#guard !ok (Wgsl.compile "@group(0) @binding(0) var<storage> a: array<f32>; @group(0) @binding(0) var<storage> b: array<f32>;")
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
#guard ok (step (State.empty 1) (.createBuffer 9 64 (usageMapRead ||| usageCopyDst)))
#guard !ok (step (State.empty 1) (.createBuffer 9 64 (usageMapRead ||| usageStorage)))
#guard !ok (step (State.empty 1) (.createBuffer 9 64 (usageMapWrite ||| usageCopySrc)))
#guard !ok (step (State.empty 1) (.createBuffer 9 64 (usageIndex ||| usageCopyDst)))
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
  "shader: only @vertex, @fragment and @compute functions: functions of your own are not in the subset (write their bodies inline)"
#guard errOf (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { var i = 0; while (i < 4) { i += 1; } return vec4f(0.0); }") ==
  "shader: 'while' is not in the subset: loops are for loops with integer literal bounds, at most 256 steps"
#guard errOf (Wgsl.compile "@fragment fn fs() -> @location(0) vec4f { var x = 0.0; for (var i = 0; i < 200; i++) { for (var j = 0; j < 200; j++) { for (var k = 0; k < 30; k++) { x += 1.0; } } } return vec4f(x); }") ==
  "shader: fs costs 6160807 operations for each invocation; the bound is 1000000"
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

/-! ## Compute (record section 6a): the force-directed graph of
`labs/demos/foafnaut/pages/webgpu-force-graph.html` (the same shader texts). -/

def forceShader : String := "
struct Params { n: u32, e: u32, dt: f32, k: f32 }
@group(0) @binding(0) var<uniform> p: Params;
@group(0) @binding(1) var<storage, read> src: array<vec4f>;
@group(0) @binding(2) var<storage, read_write> dst: array<vec4f>;
@group(0) @binding(3) var<storage, read> edges: array<vec2u>;
@compute @workgroup_size(64)
fn tick(@builtin(global_invocation_id) id: vec3u) {
  let i = id.x;
  if (i < p.n) {
    let me = src[i];
    var f = vec2f(0.0, 0.0);
    for (var j = 0u; j < min(p.n, 1024u); j++) {
      let d = me.xy - src[j].xy;
      let r2 = dot(d, d) + 0.0001;
      f += d * (p.k * p.k / r2);
    }
    for (var q = 0u; q < min(p.e, 4096u); q++) {
      let ed = edges[q];
      if (ed.x == i) { let d = src[ed.y].xy - me.xy; f += d * (length(d) / p.k); }
      if (ed.y == i) { let d = src[ed.x].xy - me.xy; f += d * (length(d) / p.k); }
    }
    f -= me.xy * 0.02;
    var v = (me.zw + f * p.dt) * 0.85;
    let s = length(v);
    if (s > 0.02) { v = v * (0.02 / s); }
    dst[i] = vec4f(me.xy + v, v);
  }
}
"

#guard ok (Wgsl.compile forceShader)
-- Every index of a runtime-sized array is clamped by arrayLength; the capped loops print with min.
#guard ((Wgsl.compile forceShader).toOption.map (·.print)).any fun t =>
  (t.splitOn "src[min(u32(i), (arrayLength(&src) - 1u))]").length == 2 &&
  (t.splitOn "dst[min(u32(i), (arrayLength(&dst) - 1u))] = ").length == 2 &&
  (t.splitOn "for (var j: u32 = 0u; j < min(u32(p.n), 1024u); j++)").length == 2 &&
  (t.splitOn "@compute @workgroup_size(64, 1, 1) fn tick(").length == 2 &&
  (t.splitOn "@group(0) @binding(2) var<storage, read_write> dst: array<vec4<f32>>;").length == 2
#guard ((Wgsl.compile forceShader).toOption.bind (·.bindingNeeds)).map (·.map (fun n => (n.binding, n.minSize))) ==
  some [(0, 16), (1, 16), (2, 16), (3, 8)]
-- Outside the compute subset: a workgroup over 256 invocations, a cap over 65536, a loop
-- that assigns its counter, no @workgroup_size, `arrayLength` of something that is not a name.
#guard errOf (Wgsl.compile "@compute @workgroup_size(32, 16) fn c() { }") ==
  "shader: the workgroup of c has more than 256 invocations or a dimension out of range"
#guard !ok (Wgsl.compile "@group(0) @binding(0) var<uniform> n: u32; @compute @workgroup_size(1) fn c() { var x = 0u; for (var j = 0u; j < min(n, 100000u); j++) { x += 1u; } }")
#guard !ok (Wgsl.compile "@group(0) @binding(0) var<uniform> n: u32; @compute @workgroup_size(1) fn c() { for (var j = 0u; j < min(n, 8u); j++) { j = 0u; } }")
#guard !ok (Wgsl.compile "@compute fn c() { }")
#guard !ok (Wgsl.compile "@group(0) @binding(0) var<storage> a: array<f32>; @compute @workgroup_size(1) fn c() { let n = arrayLength(a); }")
-- A runtime-sized array only as a storage variable.
#guard !ok (Wgsl.compile "@compute @workgroup_size(1) fn c() { var a: array<f32>; }")

def kStorage : Nat := usageStorage ||| usageCopyDst ||| usageCopySrc ||| usageVertex
def graphN : Nat := 64
def graph : List Command := [
  .createBuffer 1 16 (usageUniform ||| usageCopyDst),
  .createBuffer 2 (16 * graphN) kStorage,
  .createBuffer 3 (16 * graphN) kStorage,
  .createBuffer 4 (8 * graphN) (usageStorage ||| usageCopyDst),
  .createShader 5 forceShader,
  .createComputePipeline 6 5 "tick",
  .createComputeBindGroup 7 6 [(0, 1), (1, 2), (2, 3), (3, 4)],
  .writeBuffer 2 0 (bytes (16 * graphN)),
  .computePass [{ pipeline := 6, bind := some 7, x := 1, y := 1, z := 1 }],
  .createBuffer 8 (16 * graphN) (usageMapRead ||| usageCopyDst),
  .copyBuffer 3 0 8 0 (16 * graphN),
  .mapRead 8 99]

def graphRun : State × List HostCmd := run (State.empty 1) graph
#guard graphRun.1.objs.length == 8
-- buffer+clear ×5, shader, pipeline, bind group, write, pass, copy, read
#guard graphRun.2.length == 17
#guard graphRun.1.pending == [(99, 8, 16 * graphN)]
-- the pass's work: 1 workgroup × 64 invocations × the entry point's cost
#guard graphRun.1.work == workOf graphRun.2 && 0 < graphRun.1.work && graphRun.1.work ≤ maxFrameWork
-- The host's answer: only for the waiting ticket, at the buffer's size.
#guard (((deliver graphRun.1 99 (bytes (16 * graphN))).bind (mappedOf · 8)).map (·.size)) == some (16 * graphN)
#guard (deliver graphRun.1 98 (bytes (16 * graphN))).isNone
#guard (deliver graphRun.1 99 (bytes 8)).isNone
-- While mapped (or being mapped): no second map, no copy into it; unmap frees it.
#guard !ok (step graphRun.1 (.mapRead 8 100))
#guard !ok (step graphRun.1 (.copyBuffer 3 0 8 0 16))
#guard ((deliver graphRun.1 99 (bytes (16 * graphN))).map fun s => ok (step ((step s (.unmap 8)).toOption.get!.1) (.copyBuffer 3 0 8 0 16))) == some true
-- Refused: a binding smaller than one element, a uniform buffer bound as storage, a bind
-- group missing a binding, too many workgroups, another pipeline's bind group, a frame's
-- work over the budget, a copy past the end, mapping a buffer without MAP_READ.
#guard !ok (step (run (State.empty 1) (graph.take 6 ++ [.createBuffer 10 4 usageStorage])).1 (.createComputeBindGroup 7 6 [(0, 1), (1, 2), (2, 3), (3, 10)]))
#guard !ok (step (run (State.empty 1) (graph.take 6)).1 (.createComputeBindGroup 7 6 [(0, 1), (1, 1), (2, 3), (3, 4)]))
#guard !ok (step (run (State.empty 1) (graph.take 6)).1 (.createComputeBindGroup 7 6 [(0, 1), (1, 2), (2, 3)]))
#guard !ok (step graphRun.1 (.computePass [{ pipeline := 6, bind := some 7, x := 65536, y := 1, z := 1 }]))
#guard !ok (step graphRun.1 (.computePass [{ pipeline := 6, bind := none, x := 1, y := 1, z := 1 }]))
#guard !ok (step graphRun.1 (.computePass [{ pipeline := 6, bind := some 7, x := 65535, y := 65535, z := 1 }]))
#guard !ok (step graphRun.1 (.copyBuffer 2 16 3 0 (16 * graphN)))
#guard !ok (step graphRun.1 (.mapRead 2 7))
-- A destroyed buffer of a bind group: its dispatches are refused.
#guard !ok (step (step graphRun.1 (.destroy 3)).toOption.get!.1 (.computePass [{ pipeline := 6, bind := some 7, x := 1, y := 1, z := 1 }]))
-- A new frame starts a new budget.
#guard graphRun.1.newFrame.work == 0
-- A render pipeline on a module with storage is refused (render binds one uniform at 0).
#guard !ok (step graphRun.1 (.createPipeline 20 5 "" "" [] .triangleList))
-- The wire form of the compute commands.
#guard match Wire.decode 11 "7 6 2 0 1 1 2".toUTF8 with
  | .ok (.createComputeBindGroup 7 6 [(0, 1), (1, 2)]) => true
  | _ => false
#guard match Wire.decode 12 "1 6 7 4 1 1".toUTF8 with
  | .ok (.computePass [d]) => d == { pipeline := 6, bind := some 7, x := 4, y := 1, z := 1 }
  | _ => false
#guard match Wire.decode 10 "6 5\ntick".toUTF8 with
  | .ok (.createComputePipeline 6 5 "tick") => true
  | _ => false
#guard ok (Wire.decode 13 "3 0 8 0 1024".toUTF8) && ok (Wire.decode 14 "8 99".toUTF8) && ok (Wire.decode 15 "8".toUTF8)
#guard (graphRun.2.map Wire.HostCmd.json).any (· == "{\"k\":\"read\",\"g\":[1,8],\"size\":1024,\"ticket\":99}")
#guard (graphRun.2.map Wire.HostCmd.json).any (· == "{\"k\":\"cpipeline\",\"g\":[1,6],\"shader\":[1,5],\"entry\":\"tick\",\"layout\":[[0,\"uniform\"],[1,\"read-only-storage\"],[2,\"storage\"],[3,\"read-only-storage\"]]}")

#print axioms compile_capLoops
#print axioms compile_workgroup
#print axioms dispatch_bounds
#print axioms computePass_owned
#print axioms computeBind_owned
#print axioms copy_in_bounds
#print axioms readBuffer_owned
#print axioms run_frameWork
#print axioms deliver_spec
#print axioms run_mapInv
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
