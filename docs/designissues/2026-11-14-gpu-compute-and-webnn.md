# GPU compute on the validated page GPU path, and WebNN on it

Date: 2026-11-14. Extends `2026-11-08-page-gpu.md` (section 6a is the specification of the
compute slice, section 1 its threat model, section 4 the theorems that keep holding) and
`2026-11-14-webnn.md` (the CPU reference). Code: `formal/lean4/L4Factoidal/PageGpu/`,
`docs/web/hub/foafnaut/page-gpu.mjs`, `tools/wasmvm/quickjs/prelude.js` (WebGPU section),
`labs/demos/foafnaut/pages/webgpu-force-graph.html`.

The aim is one GPU backend, the one Lean validates, for the engine's own drawing, page
WebGPU, page WebGL and WebNN execution. Part 1 is built; part 2 is the design of WebNN on it.

## Part 1. The compute slice (built)

### 1.1 What a page may do

| WebGPU | In Lean (`PageGpu.Command`) | Checked |
|---|---|---|
| `createShaderModule` with `@compute @workgroup_size(x, y, z)` | `createShader` (`Wgsl.compile`) | x·y·z ≤ 256, z ≤ 64 (`wgOk`); body cost ≤ 1,000,000 |
| `var<storage, read>`, `var<storage, read_write>`, fixed types or `array<T>` | module bindings 0..3 of group 0 | names and types of the subset, bindings distinct (`bindingsOk`) |
| `arrayLength(&a)` | the call `arrayLength(a)`, printed with `&` | one name only |
| `for (var i = A; i < min(e, C); i++)` | `Stmt.forCap` | C − A ≤ 65,536, counter never assigned |
| `createComputePipeline(Async)` | `createComputePipeline id shader entry` | entry is a compute entry point; layout derived by Lean (`Module.bindingNeeds`) |
| `createBindGroup` of a compute layout | `createComputeBindGroup id pipeline entries` | one entry per binding; whole page buffers; usage `UNIFORM`/`STORAGE` as the binding needs; size ≥ the binding's least size (> 0); no buffer twice |
| `beginComputePass`, `dispatchWorkgroups`, `submit` | `computePass dispatches` | ≤ 64 dispatches; ≤ 65,535 workgroups a dimension; bind group of that pipeline, buffers still this page's and large enough; work counted |
| `copyBufferToBuffer` | `copyBuffer` | two different page buffers, `COPY_SRC`/`COPY_DST`, both ranges inside, neither mapped |
| `mapAsync(READ)`, `getMappedRange`, `unmap` | `mapRead id ticket`, op 16, `unmap` | buffer has `MAP_READ` (then exactly `MAP_READ \| COPY_DST`); not mapped or pending; ≤ 16 waiting; readback bytes ≤ 16 MiB |

Not in the slice: workgroup variables, barriers, atomics, `dispatchWorkgroupsIndirect`,
bind groups other than 0, buffer offsets in bindings, `MAP_WRITE`, timestamp queries.

Hardening: every index of a runtime-sized array `a` becomes `a[min(u32(i), arrayLength(&a) - 1u)]`
(`Wgsl.clampRt`), only through the variable's own name; every index of a fixed array, vector or
matrix keeps the slice-1 clamp. A runtime-sized binding holds at least one element (checked at
bind time and again at every dispatch), so the subtraction does not wrap.

Readback path: Lean emits `readBuffer g size ticket`; the host (`page-gpu.mjs`, after the
replay's commands) maps the buffer, copies the bytes, unmaps, and sends them back with action
`gpuRead` of `scriptSession` (Hub worker and native window alike). Lean takes an answer only for
a waiting ticket and only of the size asked (`PageGpu.deliver`), holds the bytes, and queues the
page's callback as a task; the prelude's callback takes the bytes (`getMappedRange`, op 16,
answered as bytes) and resolves the promise. So the bytes reach the page as a task of the event
loop at the frame clock, never synchronously.

Per-frame work: every dispatch counts workgroups × invocations × the entry point's static
cost; `step` refuses a command whose work would take the page's frame past `maxFrameWork`
(2^30 operations); the budget restarts when the host takes the turn's commands
(`State.newFrame` in `WebScripts.drained`). The refusal is a `GPUValidationError` saying to
dispatch again in the next frame.

The host's buffers also get `COPY_DST`: the zeroing clear Lean emits after every
`createBuffer` (T4 of the threat model) is a WebGPU `clearBuffer`, which needs it. Lean's
table keeps the page's own usage, and every later check reads that.

### 1.2 Theorems

All in `PageGpu/Theorems.lean`; axioms `propext`, `Quot.sound` and for some
`Classical.choice` (printed by `Tests.lean`); no `sorry`, `native_decide`, `bv_decide`.

Extended (statement widened, proof redone, nothing weakened):

- `validate_sound` / `InSubset`: two new fields, `workgroup` (every compute entry point
  passes `wgOk`) and `bindings` (`bindingsOk`).
- `harden_clamped`: `clampedE` accepts exactly two index forms, the literal clamp of slice 1
  and `a[min(u32(j), arrayLength(&a) - 1u)]` where `a` is a name whose type is a runtime-sized
  array in scope. `clampAt_spec` says what the hardening builds.
- `step_safe`, `step_inv`, `run_inv`, `run_quota`, `step_createBuffer_clears`: unchanged
  statements; proofs now go through `step_ok`. Storage and readback buffers count against the
  same byte and object quotas.
- `buffer_usage`: no `MAP_WRITE`, `INDEX`, `INDIRECT`, `QUERY_RESOLVE`; a `MAP_READ` buffer
  is `MAP_READ | COPY_DST` exactly. (Slice 1 refused `MAP_READ`, `COPY_SRC` and `STORAGE`
  too; section 6a of the page-gpu record allows them.)

New:

- `compile_capLoops`: a `min(e, C)` loop runs at most 65,536 times, counter not assigned.
- `compile_workgroup`: every compute entry point of a shader the host receives has
  0 < x, y, z and x·y·z ≤ 256.
- `dispatch_bounds`: a dispatch's pipeline is this page's compute pipeline with
  invocations ≤ 256 and cost ≤ 1,000,000; workgroups ≤ 65,535 a dimension; its counted work
  is workgroups × invocations × cost; every binding's least size is positive; it binds only
  this page's bind group of that pipeline, whose entries pass `entriesOk`.
- `computePass_owned`, `computeBind_owned`, `bindEntry_bounds`, `entries_bounds`: a compute
  pass or bind group names only this page's objects; every bound buffer is this page's, of
  the right usage, bound whole and at least its binding's size.
- `copy_in_bounds`: copies stay inside two different buffers of the page.
- `readBuffer_owned`: the only readback is of a page buffer with `MAP_READ`, of its size.
- `step_work`, `run_frameWork`: from a new frame, the compute work of everything a command
  sequence emits is at most `maxFrameWork`, whatever is refused on the way.
- `deliver_spec`: a host answer is taken only for a waiting ticket, of exactly the size
  asked; it changes no GPU object.
- `run_mapInv`, `deliver_mapInv`, `fail_mapInv`: readback bytes held or waited for stay
  within `maxMapped` (16 MiB) over any commands and answers.
- `Hosts.Dom.gpuCommand_within`: still holds with the new byte answer (op 16): the import
  writes VM memory only in its output buffer.

### 1.3 Bounds (local-lean-rules section 11)

| Input | Bound | Status |
|---|---|---|
| Work of one invocation | static cost ≤ 1,000,000 (loops ≤ 256 literal or ≤ 65,536 capped) | proved (`compile_cost`, `compile_loops`, `compile_capLoops`) |
| Work of one frame | Σ dispatches ≤ 2^30 operations | proved (`run_frameWork`) |
| Invocations of a dispatch | 65,535³ × 256 workgroups × invocations | proved per dispatch; the frame budget is the binding limit |
| GPU memory | 64 MiB and 1,024 objects a page | proved (`run_quota`) |
| Readback memory in Lean | 16 MiB, 16 waiting | proved (`run_mapInv`) |
| Commands waiting for the host | 65,536 (`Hosts.Dom.maxGpuOut`) | by construction |
| Wall time of GPU work | none from Lean | not provable: operations, not time (section 5 of page-gpu); the host's gate allows one frame in flight |

### 1.4 What is not proved (lean-risk-flags)

- Driver and shader compiler (Metal via wgpu in Deno, Dawn/Tint in Chrome): that the printed
  WGSL means what the AST means, and that the hardware honours the clamp. Mitigated by the
  host's robust buffer access, which stays on.
- `Module.print` is tested, not proved, to print the AST (`arrayLength(&a)` included).
- `minSize` of a runtime-sized array is one element's stride by Lean's reading of the storage
  layout (`storageLayoutOf`); that `arrayLength` is then ≥ 1 is WGSL's definition, assumed.
- `HostCmd.safe` is a final check that `step` runs, not a proof that `plan` emits only safe
  commands (as in slice 1).
- The replay (`page-gpu.mjs`) and the readback copy in the host are not proved; they decide
  nothing (every id, size, layout, ticket is Lean's) and a wrong answer is refused by `deliver`.
- Taint: no host command brings content of another origin into a page buffer (there is no
  texture or image input in the slice), so every readback is of the page's own data. The
  general label theorem comes with textures, as the page-gpu record says.
- Timing: a readback's round trip is visible to the page at frame granularity.

### 1.5 What runs, and measurements

- Lean (`PageGpu`, typechecked locally, module by module; every `#guard` of `Tests.lean` passes,
  among them the force-graph shader, its printed clamps, the demo's command sequence, the
  wire forms and twelve refusals).
- Host replay, measured on this Mac (M-series GPU, Deno's WebGPU over Metal) with the host
  commands Lean emits for the demo (a Lean program runs `PageGpu.run` over the page's command
  sequence and prints `Wire.HostCmd.json`; a Deno script replays them through `page-gpu.mjs`):
  1,000 nodes, 1,098 edges, a compute pass of two dispatches and a render pass of two draws a
  frame: 0.57–0.65 ms a frame (replay and GPU, frames submitted back to back), CPU side of the
  replay 0.27–0.48 ms a frame, setup 18 ms; no validation error; six readbacks of 16,000 bytes
  each came back and decoded (extent 1.41, mean speed 0.0006 after 560 frames). Waiting for
  each frame's work alone measures 15.7 ms, which is the host's completion polling, not the GPU.
  Counted work: 390,466,944 operations a frame of the 1,073,741,824 budget. Lean's side of a
  frame (decode, `step`, JSON) in the interpreter: about 0.2 ms.
- Not yet run: the engine end to end (no local engine build tonight); the native window and the
  Hub with the new prelude. The cloud branch check builds the Linux engine and runs WPT.
- A page that uses no GPU pays nothing: the new code runs only on `gpu_command` ops 10–16 and the
  `gpuRead` action; `newFrame` is one field write in a drain that already copies the DOM state.

## Part 2. WebNN on this path (design)

### 2.1 One definition of each operator

Today the CPU reference has two kinds of operator: data movement as index maps
(`Move.remap inShape outShape g` with `g` a function on multi-indices: `transposeIdx`,
`sliceIdx`, `expandIdx`, `tileIdx`, `reverseIdx`) and arithmetic kernels in `Compute.lean`
(`unaryF`, `binaryF` by name, `reduce`, `matmul`, `gemm`, `conv2dNchw`, pooling).

The GPU path must not be a second implementation. The plan is to make the operator table the
definition, and derive both backends from it:

1. **Index maps as data.** A small first-order language `WebNN.Idx` of index expressions over
   the output multi-index (`out d`, literals, `+`, `*`, `/` and `%` by literals, `min` by a
   literal, and per-dimension selection), with an evaluator `Idx.eval : Idx → List Nat → Nat`.
   Each operator's map is written once in `Idx` (transpose: permuted `out`; slice: `start + out·stride`;
   expand: `out d % inDim` for broadcast dimensions; tile; reverse: `dim − 1 − out`; pooling and
   conv windows: `out·stride + k·dilation − pad`, with a validity guard). Theorems: `Idx.eval` of
   each is the existing function (`transposeIdx`, `sliceIdx`, …), so `remap` and every theorem of
   `Move` and `Shape` (`ravel_lt`, `remap_lt`, `transposeIdx_permute`, `slice_in_bounds`) carry
   over unchanged, and the CPU reference can run on `Idx.eval` with a `csimp`-free equality.
2. **Scalar functions as data.** One table row per element-wise operator: its name (the same
   strings as `Eval.unaryNames` and `binaryF`), its CPU function (the existing `unaryF`/`binaryF`
   branch) and its WGSL expression as a `Wgsl.Expr` over the inputs. Only builtins of the subset
   appear (`exp`, `tanh`, `max`, `select`, …); functions without a WGSL builtin (`erf`, `gelu`)
   get a WGSL expression written from the same formula the CPU uses (the continued fraction of
   `erfcLarge` with the same 60 levels is too long; `erf` uses the same rational approximation on
   both sides or stays CPU-only until it does).
3. **Kernels from the table.** `WebNN/Gpu.lean` (new, owned by this work) generates, for each
   operator node, a `Wgsl.Module` value (the AST, not text): one invocation per output element,
   `global_invocation_id.x` as the flat output number, `unravel` by the literal output shape, the
   `Idx` maps printed as `u32` arithmetic with literal shape constants, the scalar row's
   expression, and for reductions, matmul, gemm, conv2d and pooling a `forCap` loop over the
   reduced extent (bound from a uniform, cap a literal ≤ 65,536). The module then goes through
   `Wgsl.finish` like any page shader, so `compile_inSubset`, `harden_clamped`, `compile_cost`
   and the dispatch theorems hold for WebNN kernels with no new proof of bounds or termination.
4. **Execution.** A built graph's GPU plan is a list of `PageGpu.Command`s on the page's own
   table (the page's GPU objects and its WebNN tensors share one quota and one ownership proof):
   a storage buffer per operand, `createComputePipeline` per distinct kernel, one compute pass
   per `dispatch` (chunked across frames when its counted work passes `maxFrameWork`), and
   `readTensor` as `copyBuffer` + `mapRead`, answered by `deliver` like a page readback.

### 2.2 What is proved and what can only be measured

Proved (planned theorems, each stated against the CPU reference's own definitions):

- `Idx.eval` of each operator's map equals the existing index function (so index maps and
  output shapes of GPU and CPU are the same mathematical function).
- For every generated kernel: the integer index arithmetic it prints, evaluated by a Lean
  evaluator of the subset's `u32` expressions (`Wgsl.evalU32`, new, no floats), equals
  `ravel inShape (Idx.eval m (unravel outShape k))` for every `k < size outShape`, given
  `size ≤ 2^32` (which the tensor quota implies); so every input read is in bounds without the
  clamp, and the clamp is a second line, not a correction.
- Output size: the kernel writes exactly `size outShape` elements, each once (one invocation
  per output, guarded by `k < size`).
- The work of a graph's dispatch is the sum of its kernels' counted work, and the plan never
  exceeds the per-frame budget (chunking proved against `run_frameWork`).

Measured only:

- Floating-point results. The GPU computes in `f32` with the device's `exp`, `tanh`, fused
  multiply-adds and summation order; the CPU reference computes in binary64 and rounds once. They
  differ. The check is a differential test per operator: the WPT conformance vectors and
  generated random tensors run on both, compared with the tolerance the WebNN conformance tests
  state for that operator (ULP or absolute, `webnn/resources/utils.js`), on a real GPU (this Mac
  under Deno's WebGPU, and the Hub in Chrome). A failing operator stays CPU-only.
- Speed: GPU and CPU per operator and per graph, before and after, on the same machine.

### 2.3 How `MLContext` chooses

- The CPU reference is the specification and stays the scored path: the Linux test runners have
  no GPU and no host replay.
- A context uses the GPU only when all hold, decided in Lean at `createContext` and recorded on
  the context: the host said it replays GPU commands (a host fact given at session start, as
  `network` is; absent on the WPT runners); the options ask for `"gpu"` (or the default when the
  host has a GPU); and at `build`, every operator of the graph has a generated kernel and its
  tensors fit the page's GPU quota. Otherwise the graph runs on the CPU reference.
- No silent fallback in the middle of a graph: the backend is chosen once per graph at `build`
  and reported (`MLGraph` keeps it; `about:foafnaut` and the console say which). Falling back
  from the GPU to the CPU reference is not a risk in the `lean-risk-flags` sense (the CPU path is
  the specification), but its numerics differ, so the choice is visible.
- `navigator.gpu.requestAdapter()` should resolve `null` on a host that does not replay GPU
  commands (today it resolves an adapter whose work is never run): that host fact is the same one.
  Open; it changes what WebGPU pages see on the WPT runners and is left for a separate check.

### 2.4 Quotas for tensor memory

GPU tensors are page buffers: they count against the page's 64 MiB and 1,024 objects
(`run_quota`), with page WebGPU objects. A graph whose operands do not fit runs on the CPU
reference (decided at `build`). Readback of an output counts against `maxMapped` (16 MiB); a
larger `readTensor` reads in parts. The CPU reference keeps its own limits (`2026-11-14-webnn.md`).

### 2.5 Order of work and coordination

First group: element-wise unary and binary (with broadcasting through `expand` maps), matmul and
gemm, conv2d, average and max pooling, reductions. `WebNN/Gpu.lean` and `WebNN/Idx.lean` are new
files; `Move.lean`, `Compute.lean`, `Shape.lean` and `Eval.lean` belong to the webnn agent, and a
change there (the `Idx` equalities, a hook in `Eval` to choose the backend) is agreed in the
coordination log first.

### 2.6 Built so far (first group)

- `WebNN/Idx.lean`: `Coord`, `Idx.eval`; the maps of transpose, slice, expand (broadcast), tile
  and reverse as data, each proved equal to `Move`'s function (`transposeMap_eval`,
  `sliceMap_eval`, `expandMap_eval`, `tileMap_eval`, `reverseMap_eval`; `remap_transposeMap`).
- `WebNN/Gpu.lean`: kernels as `Wgsl.Module` values through `Wgsl.finish`: element-wise binary
  with broadcasting (add, sub, mul, div, max, min, pow), unary (abs, ceil, cos, exp, floor,
  neg, reciprocal, relu, sigmoid, sin, softsign, tan), transpose. `emitC_eval`: the printed
  `u32` index arithmetic computes `Coord.eval` whenever its values fit in 32 bits (with
  `evalU`, a Lean reading of WGSL's `u32` `+ - * / %`). `#guard`s: every kernel passes the
  subset check, the printed broadcast index, refusals (`gelu`, `tanh`, outputs over one dispatch).
- Not yet: the `Fits` side condition discharged from the tensor quota for whole kernels; the
  output unravel (`k / stride % dim`) proved equal to `Shape.unravel`; matmul, gemm, conv2d,
  pooling and reductions (a `forCap` loop each); the backend choice in `Graph`/`Eval` (to be
  agreed with the webnn agent); running graphs through `PageGpu` commands.

Differential test, 2026-11-14, this Mac (Apple M-series, Metal through Deno's WebGPU): Lean
printed each kernel and the CPU reference's outputs (`Compute.unaryF`/`binaryF` in binary64,
rounded once to binary32, binary operators broadcast by `Move.broadcastMap`) for 1,024
deterministic inputs; the kernels ran on the GPU and the outputs were compared with the
tolerances of the WebNN conformance tests.

| Operator | Largest difference | WPT tolerance | |
|---|---|---|---|
| abs, ceil, floor, neg, relu, max, min, add, sub, mul, transpose | 0 ULP | 0 or 1 ULP | within |
| reciprocal | 1 ULP | 2 ULP | within |
| div | 2 ULP | 2 ULP | within |
| softsign | 2 ULP | 3 ULP | within |
| pow | 5 ULP | 32 ULP | within |
| sigmoid | 7 ULP | 34 ULP | within |
| exp | 13 ULP | 32 ULP | within |
| cos, sin | 6.4e-7 absolute | 2^-10 absolute | within |
| tan | 1.2e-6 absolute | 2^-10 absolute | within |
| sqrt | 2 ULP | 1 ULP | over: CPU reference |
| tanh | 44 ULP | 16 ULP | over: CPU reference |
| log | 75 ULP | 8 ULP | over: CPU reference |

One GPU, one input set: a different GPU can differ, so the table is per device and the plan is
to run the same test on the Hub's GPU before an operator is enabled there.

## Proved / tested only / open

- Proved: section 1.2; `WebNN.Idx` map equalities; `emitC_eval`.
- Tested only: the WGSL printer; the replay and readback on a real GPU (section 1.5); the
  prelude's compute API (by the cloud check's WPT, `page_gpu_test.ts` and the demo page, not by
  a theorem); WebNN kernels' floating-point results (section 2.6, one GPU).
- Open: the engine end to end in the native window and on the Hub with the demo; error scopes
  from the host's compiler for compute; `requestAdapter` on hosts without GPU replay; the rest
  of part 2 (section 2.6, "not yet").
