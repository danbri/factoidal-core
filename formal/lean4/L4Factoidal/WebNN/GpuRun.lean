/-
L4Factoidal.WebNN.GpuRun: running a WebNN graph on the page's validated GPU path
(record: docs/designissues/2026-11-14-gpu-compute-and-webnn.md, part 2).

A context runs on the GPU path when the page asked for `deviceType: "gpu"` and the embedder
replays the page's GPU commands (`PageGpu.State.replay`); otherwise, and for every graph
with an operator that has no kernel here, the CPU reference (`Graph.dispatch`) runs. The
choice is made once per graph, at `build` (`buildGpu`), and kept on the graph.

Everything the GPU path does is a `PageGpu.Command` given to `PageGpu.step` on the page's
own GPU state (lent by the host for the call): the kernels' WGSL is compiled from its text
like a page's shader, every buffer counts against the page's GPU quota, every dispatch
against its work budget, and a refusal anywhere makes the graph run on the CPU reference
(at `build`) or the dispatch fail with an `OperationError` (at `dispatch`). The theorems of
`PageGpu` (subset, clamped indices, dispatch bounds, quotas, readback) hold for all of it.

Operators on the GPU path (float32): the element-wise binary operators, the unary operators
of `Gpu.unaryExpr`, transpose, expand, slice, tile, reverse, reshape, identity, matmul, the
reductions of `Gpu.reduceForm`, conv2d (NCHW, OIHW) and maxPool2d (NCHW). `log`, `tanh`,
`sqrt`, `gemm` and `averagePool2d` stay on the CPU reference: measured outside the WebNN
tolerances on a GPU (section 2.6 of the record).
-/
import L4Factoidal.WebNN.Graph
import L4Factoidal.WebNN.Gpu
import L4Factoidal.PageGpu.Model

namespace L4Factoidal.WebNN.GpuRun
open L4Factoidal.WebNN
open L4Factoidal.PageGpu (Command)

/-- The most host commands one WebNN call may add for the host. -/
def maxOut : Nat := 4096

/-- One command on the page's GPU state: its host commands are kept for the host. -/
def emit (s : State) (c : Command) : Except String State := do
  if s.out.size ≥ min s.room maxOut then throw "webnn gpu: too many commands waiting for the host"
  let (g, out) ← L4Factoidal.PageGpu.step s.page c
  pure { s with page := g, out := s.out ++ out.toArray }

/-- A fresh id for a GPU object. -/
def fresh (s : State) : State × Nat := ({ s with nextId := s.nextId + 1 }, s.nextId)

def usage : Nat := L4Factoidal.PageGpu.usageStorage ||| L4Factoidal.PageGpu.usageCopyDst ||| L4Factoidal.PageGpu.usageCopySrc

/-- Bytes of a GPU buffer for a tensor of `bytes` bytes: a multiple of 4, never empty. -/
def bufBytes (bytes : Nat) : Nat := max 4 (L4Factoidal.PageGpu.Wgsl.roundUp 4 bytes)

/-- The operators the GPU path runs (`kernelFor`). -/
def gpuOps : List String :=
  ["add", "sub", "mul", "div", "max", "min", "pow",
   "abs", "ceil", "cos", "exp", "floor", "neg", "reciprocal", "relu", "sigmoid", "sin", "softsign", "tan",
   "transpose", "expand", "slice", "tile", "reverse", "reshape", "identity", "matmul",
   "reduceSum", "reduceMean", "reduceL1", "reduceSumSquare", "reduceProduct", "reduceMax", "reduceMin",
   "conv2d", "maxPool2d"]

/-- How a node runs on the GPU: a kernel with its input operands in binding order, or a copy
of one operand into the output. -/
inductive Run where
  | kernel (m : L4Factoidal.PageGpu.Wgsl.Module) (ins : List Nat)
  | copy (src : Nat)

/-- The GPU form of one node, or why there is none. -/
def kernelFor (n : Node) (descs : Array Desc) : Except String Run := do
  if !gpuOps.contains n.op then throw s!"{n.op} has no kernel on the GPU path"
  let c : Call := ⟨n.args, descs⟩
  let some out := n.outDescs.head? | throw "no output"
  if n.outs.length != 1 then throw "one output only"
  let ins := n.inputs
  if !(ins.all fun i => (descs[i]?.map (·.dtype)) == some .float32) || out.dtype != .float32 then
    throw "float32 only on the GPU path"
  let d := fun (k : String) => (c.d k).shape
  let one := fun (k : String) => match c.id? k with | some i => pure i | none => throw s!"no {k}"
  let o := out.shape
  match n.op with
  | "add" | "sub" | "mul" | "div" | "max" | "min" | "pow" =>
    pure (.kernel (← Gpu.binaryKernel n.op (d "a") (d "b") o) [← one "a", ← one "b"])
  | "reshape" | "identity" => pure (.copy (← one "input"))
  | "transpose" =>
    let s := d "input"
    pure (.kernel (← Gpu.moveKernel (transposeMap (c.nats "permutation" (List.range s.length).reverse)) s o) [← one "input"])
  | "expand" => pure (.kernel (← Gpu.moveKernel (expandMap (d "input") o.length) (d "input") o) [← one "input"])
  | "slice" =>
    let s := d "input"
    pure (.kernel (← Gpu.moveKernel (sliceMap (c.nats "starts" []) (c.nats "strides" (List.replicate s.length 1)) o.length) s o) [← one "input"])
  | "tile" => pure (.kernel (← Gpu.moveKernel (tileMap (d "input") o.length) (d "input") o) [← one "input"])
  | "reverse" =>
    let s := d "input"
    pure (.kernel (← Gpu.moveKernel (reverseMap s (c.nats "axes" (List.range s.length)) o.length) s o) [← one "input"])
  | "matmul" => pure (.kernel (← Gpu.matmulKernel (d "a") (d "b") o) [← one "a", ← one "b"])
  | "conv2d" =>
    if c.str "inputLayout" "nchw" != "nchw" || !["", "oihw"].contains (c.str "filterLayout" "") then
      throw "conv2d: NCHW input and OIHW filter only on the GPU path"
    let bias := c.id? "bias"
    let m ← Gpu.conv2dKernel (d "input") (d "filter") o (c.nats "strides" [1, 1]) (c.nats "dilations" [1, 1])
      (c.nats "padding" [0, 0, 0, 0]) (c.nat "groups" 1) bias.isSome
    pure (.kernel m ([← one "input", ← one "filter"] ++ bias.toList))
  | "maxPool2d" =>
    if c.str "layout" "nchw" != "nchw" then throw "maxPool2d: NCHW only on the GPU path"
    let s := d "input"
    let m ← Gpu.poolKernel n.op s o (c.nats "windowDimensions" [s.getD 2 1, s.getD 3 1]) (c.nats "strides" [1, 1])
      (c.nats "dilations" [1, 1]) (c.nats "padding" [0, 0, 0, 0])
    pure (.kernel m [← one "input"])
  | name =>
    if name.startsWith "reduce" then
      let s := d "input"
      pure (.kernel (← Gpu.reduceKernel name s (c.nats "axes" (List.range s.length))) [← one "input"])
    else
      pure (.kernel (← Gpu.unaryKernel name (d "input")) [← one "input"])

/-- Whether context `c` runs on the GPU path. -/
def ctxGpu (s : State) (c : Nat) : Bool := s.gpuCtx[c]?.getD false

/-- `ML.createContext`: a context, on the GPU path when `deviceType` is `"gpu"` and the
embedder replays the page's GPU commands. -/
def createContext (s : State) (deviceType : String) : M (State × Nat) := do
  let (s, i) ← L4Factoidal.WebNN.createContext s
  pure ({ s with gpuCtx := s.gpuCtx.push (deviceType == "gpu" && s.page.replay) }, i)

/-- Destroy GPU objects (refusals ignored: an object already gone). -/
def destroyAll (s : State) (ids : List Nat) : State :=
  ids.foldl (fun s i => (emit s (.destroy i)).toOption.getD s) s

/-- The plan of a built graph on the page's GPU: a buffer for every operand the needed
operators read or write (constants written once), and a kernel (pipeline and bind group)
or a copy for each needed operator, in order. -/
def plan (s : State) (b : Builder) : Except String (State × GpuPlan) := do
  let mut s := s
  let mut bufs : Array (Option Nat) := Array.replicate b.descs.size none
  let mut objs : List Nat := []
  let mut steps : Array GpuStep := #[]
  for idx in List.range b.nodes.size do
    if !(b.needed[idx]?.getD false) then continue
    let n := b.nodes[idx]!
    let r ← kernelFor n b.descs
    for i in n.inputs ++ n.outs do
      if (bufs[i]?.join).isNone then
        let (s1, id) := fresh s
        let d := b.descs[i]?.getD default
        let s2 ← emit s1 (.createBuffer id (bufBytes d.byteLength) usage)
        s := s2
        objs := id :: objs
        bufs := bufs.setIfInBounds i (some id)
        -- a constant's bytes, once
        let bytes? : Option ByteArray := match b.srcs[i]? with
          | some (.const data) => some data
          | some (.tensor t) => (s.tensors[t]?.map (·.data))
          | _ => none
        if let some bytes := bytes? then
          if bytes.size > 0 then
            let padded := bytes ++ ByteArray.mk (Array.replicate (L4Factoidal.PageGpu.Wgsl.roundUp 4 bytes.size - bytes.size) 0)
            s ← emit s (.writeBuffer id 0 padded)
    let outBuf := (bufs[n.outs.headD 0]?.join).getD 0
    match r with
    | .copy src =>
      steps := steps.push (.copy ((bufs[src]?.join).getD 0) outBuf (bufBytes ((b.descs[src]?.getD default).byteLength)))
    | .kernel m ins =>
      let (s1, sh) := fresh s
      let s2 ← emit s1 (.createShader sh m.print)
      let (s3, pipe) := fresh s2
      let s4 ← emit s3 (.createComputePipeline pipe sh "main")
      let (s5, bind) := fresh s4
      let entries := (ins ++ [n.outs.headD 0]).zip (List.range (ins.length + 1)) |>.map fun (op, k) => (k, (bufs[op]?.join).getD 0)
      let s6 ← emit s5 (.createComputeBindGroup bind pipe entries)
      s := s6
      objs := bind :: pipe :: sh :: objs
      let outs := (n.outDescs.headD default).shape
      steps := steps.push (.kernel pipe bind (Gpu.groups (Shape.size outs)))
  pure (s, { bufs, steps := steps.toList, objs })

/-- After `build`: on a GPU context, the graph's plan on the page's GPU, if every needed
operator has a kernel there and the page's GPU quota holds it; otherwise the objects made
are destroyed and the graph runs on the CPU reference. -/
def buildGpu (s : State) (bid : Nat) : State :=
  match s.builders[bid]? with
  | none => s
  | some b =>
    if !ctxGpu s b.ctx || !b.built then s else
    match plan s b with
    | .ok (s', p) => { s' with builders := s'.builders.setIfInBounds bid { b with gpu := some p } }
    -- a refusal leaves `s` as it was: the page's GPU state and the host commands of the
    -- attempt are dropped together, so the host never sees half a plan
    | .error _ => s

/-- The tensor's GPU buffer, made on first use. -/
def tensorBuf (s : State) (tid : Nat) : Except String (State × Nat) := do
  let some t := s.tensors[tid]? | throw "no tensor"
  match t.buf with
  | some id => pure (s, id)
  | none =>
    let (s, id) := fresh s
    let s ← emit s (.createBuffer id (bufBytes t.desc.byteLength) usage)
    pure ({ s with tensors := s.tensors.setIfInBounds tid { t with buf := some id } }, id)

/-- `MLContext.dispatch` on the GPU path: the inputs into the graph's operand buffers (a
copy from a tensor already on the GPU, else its bytes), one compute pass of the steps
(passes of at most `maxDispatches`, copies between them), and the outputs copied into the
output tensors' buffers. A refusal (the frame's GPU work, the quota) is an `OperationError`
and the output tensors keep their previous values. -/
def dispatch (s : State) (c bid : Nat) (ins outs : List (String × Nat)) : M State := do
  let (b, feed, res) ← checkDispatch s c bid ins outs
  let some p := b.gpu | L4Factoidal.WebNN.dispatch s c bid ins outs
  let r : Except String State := do
    let mut s := s
    for (i, tid) in feed do
      let t := s.tensors[tid]?.getD default
      let dst := (p.bufs[i]?.join).getD 0
      if t.onGpu then
        let (s1, src) ← tensorBuf s tid
        s ← emit s1 (.copyBuffer src 0 dst 0 (bufBytes t.desc.byteLength))
      else if t.data.size > 0 then
        s ← emit s (.writeBuffer dst 0 (t.data ++ ByteArray.mk (Array.replicate (L4Factoidal.PageGpu.Wgsl.roundUp 4 t.data.size - t.data.size) 0)))
    -- kernels in passes, copies between them, in the graph's order
    let mut pass : Array L4Factoidal.PageGpu.Dispatch := #[]
    for st in p.steps do
      match st with
      | .kernel pipe bind groups =>
        pass := pass.push { pipeline := pipe, bind := some bind, x := groups, y := 1, z := 1 }
        if pass.size == L4Factoidal.PageGpu.maxDispatches then
          s ← emit s (.computePass pass.toList); pass := #[]
      | .copy src dst bytes =>
        if pass.size > 0 then s ← emit s (.computePass pass.toList); pass := #[]
        s ← emit s (.copyBuffer src 0 dst 0 bytes)
    if pass.size > 0 then s ← emit s (.computePass pass.toList)
    for (i, tid) in res do
      let (s1, dst) ← tensorBuf s tid
      let t := s1.tensors[tid]?.getD default
      s ← emit s1 (.copyBuffer ((p.bufs[i]?.join).getD 0) 0 dst 0 (bufBytes t.desc.byteLength))
      s := { s with tensors := s.tensors.setIfInBounds tid { t with onGpu := true } }
    pure s
  match r with
  | .ok s => pure s
  | .error m => throw (.dom "OperationError" m)

/-- `MLContext.readTensor` of a tensor whose value is on the GPU: a staging buffer
(`MAP_READ | COPY_DST`), a copy into it, and its readback with the page's `ticket` (the
callback the host's answer queues). The answer is the staging buffer's id: the page takes
its bytes (`getMappedRange`, `PageGpu.mappedOf`) and destroys it. -/
def readGpu (s : State) (c tid ticket : Nat) : M (State × Nat) := do
  let some t := s.tensors[tid]? | throw (.type "not a tensor")
  if t.destroyed then throw (.dom "InvalidStateError" "the tensor is destroyed")
  if t.ctx != c then throw (.type "the tensor is of another context")
  if !t.readable then throw (.type "the tensor is not readable")
  let some src := t.buf | throw (.dom "OperationError" "the tensor has no GPU value")
  let r : Except String (State × Nat) := do
    let (s, st) := fresh s
    let size := bufBytes t.desc.byteLength
    let s ← emit s (.createBuffer st size (L4Factoidal.PageGpu.usageMapRead ||| L4Factoidal.PageGpu.usageCopyDst))
    let s ← emit s (.copyBuffer src 0 st 0 size)
    let s ← emit s (.mapRead st ticket)
    pure (s, st)
  match r with
  | .ok v => pure v
  | .error m => throw (.dom "OperationError" m)

/-- `MLTensor.destroy()`, with its GPU buffer. -/
def destroyTensor (s : State) (tid : Nat) : State :=
  let buf := (s.tensors[tid]?.bind (·.buf))
  let s := L4Factoidal.WebNN.destroyTensor s tid
  match buf with
  | some id => destroyAll s [id]
  | none => s

/-- `MLGraph.destroy()`, with its GPU plan. -/
def destroyGraph (s : State) (bid : Nat) : State :=
  let objs := ((s.builders[bid]?.bind (·.gpu)).map fun p => p.objs ++ p.bufs.toList.filterMap id).getD []
  let s := L4Factoidal.WebNN.destroyGraph s bid
  let s := { s with builders := s.builders.modify bid fun b => { b with gpu := none } }
  destroyAll s objs

end L4Factoidal.WebNN.GpuRun

