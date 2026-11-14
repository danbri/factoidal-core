/-
L4Factoidal.PageGpu.Model: the GPU commands a page may give, the host commands Lean
emits for them, the page's object table and quotas
(record: docs/designissues/2026-11-08-page-gpu.md, sections 2 to 4).

`step` turns one page command into a change of the page's object table and a list of
host commands. It is built in three parts so that each theorem has one place to look:

- `plan` reads the command against the table and decides the change and the commands;
- `HostCmd.safe` is the independent final check of every emitted command (ownership,
  usage flags, bounds, quotas): `step` refuses a command whose plan emits anything that
  fails it, so `step_safe` holds by construction and the lemmas in `Theorems` unpack it;
- `apply` makes the change through `add` and `remove` only, the two places that check
  quotas (`apply_inv`).

Compute (record section 6a; `docs/designissues/2026-11-14-gpu-compute-and-webnn.md`):
compute pipelines with an explicit layout Lean derives from the module's bindings,
bind groups of up to `Wgsl.maxBindings` whole page buffers, compute passes of at most
`maxDispatches` dispatches, copies between page buffers, and the readback of a
`MAP_READ` buffer, whose bytes the host gives back (`deliver`) and the page then takes
(`mappedOf`). `step` counts the operations of every emitted dispatch against the page's
budget for the frame (`State.work`, at most `maxFrameWork`; `newFrame` when the host has
taken the commands).
-/
import L4Factoidal.PageGpu.Wgsl
import L4Factoidal.PageGpu.Glsl

namespace L4Factoidal.PageGpu

/-- A host GPU object: the page (script session) and the page's own number. -/
structure Gid where
  page : Nat
  id : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Format where
  | float32 | float32x2 | float32x3 | float32x4
  deriving DecidableEq, Repr, Inhabited

def Format.bytes : Format → Nat
  | .float32 => 4 | .float32x2 => 8 | .float32x3 => 12 | .float32x4 => 16

def Format.ty : Format → Wgsl.Ty
  | .float32 => .scalar .f32 | .float32x2 => .vec 2 .f32
  | .float32x3 => .vec 3 .f32 | .float32x4 => .vec 4 .f32

def Format.name : Format → String
  | .float32 => "float32" | .float32x2 => "float32x2"
  | .float32x3 => "float32x3" | .float32x4 => "float32x4"

structure VAttr where
  format : Format
  offset : Nat
  location : Nat
  deriving DecidableEq, Repr, Inhabited

structure VLayout where
  stride : Nat
  attrs : List VAttr
  deriving DecidableEq, Repr, Inhabited

/-- The last byte (exclusive) an attribute of the layout reads within one vertex. -/
def VLayout.extent (l : VLayout) : Nat := l.attrs.foldl (fun m a => max m (a.offset + a.format.bytes)) 0

/-- The bytes of a vertex buffer that `count` vertices from `first` read. -/
def vertexNeed (l : VLayout) (first count : Nat) : Nat :=
  if count = 0 then 0 else (first + count - 1) * l.stride + l.extent

inductive Topology where
  | triangleList | triangleStrip | lineList | pointList
  deriving DecidableEq, Repr, Inhabited

def Topology.name : Topology → String
  | .triangleList => "triangle-list" | .triangleStrip => "triangle-strip"
  | .lineList => "line-list" | .pointList => "point-list"

structure Draw where
  pipeline : Nat
  bind : Option Nat
  vbufs : List Nat
  count : Nat
  instances : Nat
  first : Nat
  firstInstance : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The clear colour of a pass, each channel 0..255. -/
abbrev Rgba := Nat × Nat × Nat × Nat

/-- One `dispatchWorkgroups(x, y, z)` with a pipeline and its bind group (`bind` none for a
pipeline with no bindings). -/
structure Dispatch where
  pipeline : Nat
  bind : Option Nat
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr, Inhabited

/-- What a page script asks for (one import call each). Ids are the page's own. -/
inductive Command where
  /-- `canvas.getContext('webgpu')` + `configure`: page canvas `id` for DOM node `node`. -/
  | configure (id node w h : Nat)
  | createBuffer (id size usage : Nat)
  | writeBuffer (id offset : Nat) (data : ByteArray)
  | createShader (id : Nat) (code : String)
  /-- A WebGL program (`linkProgram`): GLSL ES vertex and fragment shaders, translated by
  `Glsl.compileProgram` into one WGSL module with entry points `vs` and `fs`. -/
  | createProgram (id : Nat) (vs fs : String)
  | createPipeline (id shader : Nat) (vs fs : String) (layouts : List VLayout) (topology : Topology)
  /-- Group 0, binding 0: a uniform buffer, for `pipeline`'s layout. -/
  | createBindGroup (id pipeline buffer : Nat)
  /-- A render pass on a page canvas (always `loadOp: clear`), submitted. -/
  | pass (canvas : Nat) (clear : Rgba) (draws : List Draw)
  | destroy (id : Nat)
  /-- A compute pipeline: the compute entry point `entry` ("" for the first) of `shader`. -/
  | createComputePipeline (id shader : Nat) (entry : String)
  /-- A bind group of `pipeline`'s layout: (binding, buffer) pairs, each buffer whole. -/
  | createComputeBindGroup (id pipeline : Nat) (entries : List (Nat × Nat))
  /-- A compute pass, submitted. -/
  | computePass (dispatches : List Dispatch)
  | copyBuffer (src srcOffset dst dstOffset size : Nat)
  /-- `mapAsync(GPUMapMode.READ)` of the whole buffer; `ticket` names the answer. -/
  | mapRead (id ticket : Nat)
  /-- `unmap()`: Lean drops the bytes it holds for the page. -/
  | unmap (id : Nat)
  deriving Inhabited

/-- The page's objects, as Lean knows them. -/
inductive Obj where
  | canvas (node w h : Nat)
  | buffer (size usage : Nat)
  /-- A hardened, validated module and the bytes of its printed text. -/
  | shader (m : Wgsl.Module) (bytes : Nat)
  /-- Vertex layouts, the uniform size the shader declares (if any). -/
  | pipeline (layouts : List VLayout) (uniform : Option Nat)
  | bindGroup (pipeline buffer size : Nat)
  /-- A compute pipeline: invocations of one workgroup, the entry point's static cost, and
  the bindings it needs. -/
  | computePipeline (invocations cost : Nat) (needs : List Wgsl.BindingNeed)
  /-- A compute bind group: its pipeline and (binding, buffer) entries. -/
  | computeBind (pipeline : Nat) (entries : List (Nat × Nat))
  deriving Inhabited

/-- The bytes an object holds against the page's quota. -/
def Obj.bytes : Obj → Nat
  | .canvas _ w h => w * h * 4
  | .buffer size _ => size
  | .shader _ b => b
  | _ => 0

structure HostDraw where
  pipeline : Gid
  bind : Option Gid
  vbufs : List Gid
  count : Nat
  instances : Nat
  first : Nat
  firstInstance : Nat
  deriving DecidableEq, Repr, Inhabited

structure HostDispatch where
  pipeline : Gid
  bind : Option Gid
  x : Nat
  y : Nat
  z : Nat
  /-- The dispatch's operations: workgroups × invocations × the entry point's cost, as Lean
  counts them (checked against the pipeline by `dispatchSafe`). -/
  work : Nat
  deriving DecidableEq, Repr, Inhabited

/-- What Lean asks the host's WebGPU device to do. Nothing copies out of a texture (a
page canvas has no `COPY_SRC`); the only kind that reads GPU memory back is `readBuffer`,
of a page's own `MAP_READ` buffer. -/
inductive HostCmd where
  /-- A texture `w`x`h`, `rgba8unorm`, usage `usage` (always `canvasUsage`). -/
  | createCanvas (g : Gid) (node w h usage : Nat)
  | createBuffer (g : Gid) (size usage : Nat)
  /-- `encoder.clearBuffer(g)`: zeros, before any read. -/
  | clearBuffer (g : Gid) (size : Nat)
  | writeBuffer (g : Gid) (offset : Nat) (data : ByteArray)
  /-- `createShaderModule` with Lean's printing of the hardened module. -/
  | createShader (g : Gid) (code : String)
  | createPipeline (g shader : Gid) (vs fs : String) (layouts : List VLayout) (topology : Topology)
  | createBindGroup (g pipeline buffer : Gid) (size : Nat)
  /-- One render pass on a page canvas with `loadOp: clear`, then submit. -/
  | pass (canvas : Gid) (clear : Rgba) (draws : List HostDraw)
  | destroy (g : Gid)
  /-- A compute pipeline with an explicit layout: group 0's (binding, space) pairs. -/
  | createComputePipeline (g shader : Gid) (entry : String) (layout : List (Nat × Wgsl.Space))
  /-- A bind group of the pipeline's layout: (binding, buffer, size) with size the whole buffer. -/
  | createComputeBind (g pipeline : Gid) (entries : List (Nat × Gid × Nat))
  /-- One compute pass with these dispatches, then submit. -/
  | computePass (dispatches : List HostDispatch)
  | copyBuffer (src : Gid) (srcOffset : Nat) (dst : Gid) (dstOffset size : Nat)
  /-- Map the buffer for reading, copy its `size` bytes out, unmap, and give them back to
  Lean with `ticket` (`deliver`). -/
  | readBuffer (g : Gid) (size ticket : Nat)
  deriving Inhabited

/-! ## Limits -/

def maxObjects : Nat := 1024
def maxBytes : Nat := 67108864
def maxBuffer : Nat := 16777216
def maxCanvas : Nat := 2048
def maxDraws : Nat := 64
def maxVertices : Nat := 1048576
def maxStride : Nat := 2048
def maxLayouts : Nat := 8
def maxAttrs : Nat := 16
/-- Dispatches of one compute pass, and workgroups per dimension of one dispatch
(WebGPU's `maxComputeWorkgroupsPerDimension`). -/
def maxDispatches : Nat := 64
def maxWorkgroups : Nat := 65535
/-- Operations of compute work a page may emit in one frame (the commands the host takes
at once): the sum over its dispatches of workgroups × invocations × static cost. -/
def maxFrameWork : Nat := 1073741824
/-- Bytes Lean holds for a page's readbacks: asked for and not yet answered, plus answered
and not yet unmapped. -/
def maxMapped : Nat := 16777216
/-- Readbacks of one page waiting for the host. -/
def maxPending : Nat := 16

/-- WebGPU buffer usage bits. -/
def usageMapRead : Nat := 1
def usageMapWrite : Nat := 2
def usageCopySrc : Nat := 4
def usageCopyDst : Nat := 8
def usageIndex : Nat := 16
def usageVertex : Nat := 32
def usageUniform : Nat := 64
def usageStorage : Nat := 128
/-- Every usage bit a page buffer may not have: map for writing, index, indirect, query
resolve. (`MAP_READ`, `COPY_SRC` and `STORAGE` are the compute slice's, record 6a.) -/
def forbiddenUsage : Nat := 2 ||| 16 ||| 256 ||| 512
/-- A page buffer's usage: no forbidden bit, below 1024, and a `MAP_READ` buffer is
`MAP_READ | COPY_DST` exactly (as WebGPU requires): it is never bound, drawn from or
copied out of on the GPU, only filled by a copy and read back. -/
def usageOk (usage : Nat) : Bool :=
  usage &&& forbiddenUsage == 0 && usage < 1024 &&
  (usage &&& usageMapRead == 0 || usage == (usageMapRead ||| usageCopyDst))
/-- WebGPU texture usage of a page canvas: `RENDER_ATTACHMENT | TEXTURE_BINDING`
(16 ||| 4); never `COPY_SRC` (1). -/
def canvasUsage : Nat := 20

/-! ## The page's table -/

structure State where
  page : Nat := 0
  objs : List (Nat × Obj) := []
  /-- Compute operations emitted since the host last took the page's commands. -/
  work : Nat := 0
  /-- Readbacks asked for and not yet answered: (ticket, buffer, size). -/
  pending : List (Nat × Nat × Nat) := []
  /-- Readbacks answered and not yet unmapped: (buffer, bytes). -/
  mapped : List (Nat × ByteArray) := []
  deriving Inhabited

def State.empty (page : Nat) : State := { page }

def State.get (s : State) (id : Nat) : Option Obj := s.objs.lookup id

def State.used (s : State) : Nat := (s.objs.map (·.2.bytes)).sum

/-- The quota invariant. -/
def Inv (s : State) : Prop := s.used ≤ maxBytes ∧ s.objs.length ≤ maxObjects

def State.gid (s : State) (id : Nat) : Gid := ⟨s.page, id⟩

def bufferOf (s : State) (id : Nat) : Option (Nat × Nat) :=
  match s.get id with | some (.buffer size usage) => some (size, usage) | _ => none

def pipelineOf (s : State) (id : Nat) : Option (List VLayout × Option Nat) :=
  match s.get id with | some (.pipeline ls u) => some (ls, u) | _ => none

def bindGroupOf (s : State) (id : Nat) : Option (Nat × Nat × Nat) :=
  match s.get id with | some (.bindGroup p b z) => some (p, b, z) | _ => none

def isCanvas (s : State) (id : Nat) : Bool :=
  match s.get id with | some (.canvas ..) => true | _ => false

def isShader (s : State) (id : Nat) : Bool :=
  match s.get id with | some (.shader ..) => true | _ => false

def computePipelineOf (s : State) (id : Nat) : Option (Nat × Nat × List Wgsl.BindingNeed) :=
  match s.get id with | some (.computePipeline i c ns) => some (i, c, ns) | _ => none

def computeBindOf (s : State) (id : Nat) : Option (Nat × List (Nat × Nat)) :=
  match s.get id with | some (.computeBind p es) => some (p, es) | _ => none

/-- Bytes Lean holds or has asked for, for the page's readbacks. -/
def State.mappedBytes (s : State) : Nat :=
  (s.pending.map (·.2.2)).sum + (s.mapped.map (·.2.size)).sum

/-- The usage a buffer bound in `space` must have. -/
def spaceUsage : Wgsl.Space → Nat
  | .uniform => usageUniform
  | _ => usageStorage

def owned (s : State) (g : Gid) : Bool := g.page == s.page && (s.get g.id).isSome
def fresh (s : State) (g : Gid) : Bool := g.page == s.page && (s.get g.id).isNone

/-- One draw is safe: its pipeline, bind group and vertex buffers are this page's, each
vertex buffer has `VERTEX` usage and holds every byte the draw reads, and the vertex
count is in the quota. -/
def drawSafe (s : State) (d : HostDraw) : Bool :=
  owned s d.pipeline && d.count * d.instances ≤ maxVertices &&
  match pipelineOf s d.pipeline.id with
  | none => false
  | some (layouts, uniform) =>
    layouts.length == d.vbufs.length &&
    (layouts.zip d.vbufs).all (fun (l, g) =>
      owned s g && match bufferOf s g.id with
        | some (size, usage) => usage &&& usageVertex != 0 && vertexNeed l d.first d.count ≤ size
        | none => false) &&
    match uniform, d.bind with
    | none, none => true
    | some need, some b => owned s b && match bindGroupOf s b.id with
      | some (p, _, size) => p == d.pipeline.id && need ≤ size
      | none => false
    | _, _ => false

/-- One bound buffer of a compute bind group is right for its binding: this page's buffer,
with the usage the binding's space needs, holding at least the binding's least size
(for a runtime-sized array, one element: `arrayLength` is at least 1), and bound whole. -/
def bindEntryOk (s : State) (needs : List Wgsl.BindingNeed) (e : Nat × Gid × Nat) : Bool :=
  owned s e.2.1 &&
  match needs.find? (·.binding == e.1), bufferOf s e.2.1.id with
  | some n, some (size, usage) => usage &&& spaceUsage n.space != 0 && n.minSize ≤ size && e.2.2 == size
  | _, _ => false

/-- A compute bind group's entries match the pipeline's bindings one to one, and no buffer
is bound twice. -/
def entriesOk (s : State) (needs : List Wgsl.BindingNeed) (es : List (Nat × Gid × Nat)) : Bool :=
  es.map (·.1) == needs.map (·.binding) && (es.map (·.2.1.id)).Nodup && es.all (bindEntryOk s needs)

/-- The entries of a page's bind group as host entries: buffer ids as this page's, each
with the buffer's present size. -/
def hostEntries (s : State) (es : List (Nat × Nat)) : List (Nat × Gid × Nat) :=
  es.map fun (b, id) => (b, s.gid id, ((bufferOf s id).map (·.1)).getD 0)

/-- One dispatch is safe: its pipeline is this page's compute pipeline, the workgroup
counts are within `maxWorkgroups`, its bind group is this page's, made for that pipeline,
and every buffer in it is still this page's, of the right usage and large enough; and its
work is what the pipeline's invocations and cost make it. -/
def dispatchSafe (s : State) (d : HostDispatch) : Bool :=
  owned s d.pipeline && d.x ≤ maxWorkgroups && d.y ≤ maxWorkgroups && d.z ≤ maxWorkgroups &&
  match computePipelineOf s d.pipeline.id with
  | none => false
  | some (inv, cost, needs) =>
    inv ≤ Wgsl.maxInvocations && cost ≤ Wgsl.maxCost && d.work == d.x * d.y * d.z * inv * cost &&
    needs.all (0 < ·.minSize) &&
    match needs, d.bind with
    | [], none => true
    | _, some b => owned s b && match computeBindOf s b.id with
      | some (p, es) => p == d.pipeline.id && entriesOk s needs (hostEntries s es)
      | none => false
    | _, none => false

/-- The operations a host command asks of the GPU's compute units (0 but for a compute pass). -/
def HostCmd.work : HostCmd → Nat
  | .computePass ds => (ds.map (·.work)).sum
  | _ => 0

/-- The compute operations of a list of host commands. -/
def workOf (out : List HostCmd) : Nat := (out.map HostCmd.work).sum

/-- The final check of one emitted command against the table before the command. -/
def HostCmd.safe (s : State) : HostCmd → Bool
  | .createCanvas g _ w h usage => fresh s g && usage == canvasUsage && 0 < w && w ≤ maxCanvas && 0 < h && h ≤ maxCanvas
  | .createBuffer g size usage => fresh s g && usageOk usage && size ≤ maxBuffer && size % 4 == 0
  | .clearBuffer g size => g.page == s.page && size ≤ maxBuffer
  | .writeBuffer g offset data => owned s g && offset % 4 == 0 && data.size % 4 == 0 &&
      match bufferOf s g.id with
      | some (size, usage) => usage &&& usageCopyDst != 0 && offset + data.size ≤ size
      | none => false
  | .createShader g code => fresh s g && code.utf8ByteSize ≤ 4 * Wgsl.maxCodeBytes
  | .createPipeline g sh _ _ layouts _ => fresh s g && owned s sh && isShader s sh.id &&
      layouts.length ≤ maxLayouts
  | .createBindGroup g p b size => fresh s g && owned s p && owned s b &&
      (pipelineOf s p.id).isSome &&
      match bufferOf s b.id with
      | some (bsize, usage) => usage &&& usageUniform != 0 && size ≤ bsize
      | none => false
  | .pass c _ draws => owned s c && isCanvas s c.id && draws.length ≤ maxDraws && draws.all (drawSafe s)
  | .destroy g => owned s g
  | .createComputePipeline g sh _ layout => fresh s g && owned s sh && isShader s sh.id &&
      layout.length ≤ Wgsl.maxBindings
  | .createComputeBind g p es => fresh s g && owned s p &&
      match computePipelineOf s p.id with
      | some (_, _, needs) => entriesOk s needs es
      | none => false
  | .computePass ds => ds.length ≤ maxDispatches && ds.all (dispatchSafe s)
  | .copyBuffer src so dst do_ size => owned s src && owned s dst && src.id != dst.id &&
      so % 4 == 0 && do_ % 4 == 0 && size % 4 == 0 &&
      match bufferOf s src.id, bufferOf s dst.id with
      | some (ss, su), some (ds, du) =>
        su &&& usageCopySrc != 0 && du &&& usageCopyDst != 0 && so + size ≤ ss && do_ + size ≤ ds
      | _, _ => false
  | .readBuffer g size _ => owned s g &&
      match bufferOf s g.id with
      | some (bsize, usage) => usage &&& usageMapRead != 0 && size == bsize
      | none => false

/-! ## Changes, with the quota checks -/

inductive Change where
  | none
  | add (id : Nat) (o : Obj)
  | remove (id : Nat)
  /-- A readback asked for: (ticket, buffer, size) waits for the host. -/
  | read (ticket id size : Nat)
  /-- `unmap`: the bytes held for the buffer are dropped. -/
  | unmap (id : Nat)

def add (s : State) (id : Nat) (o : Obj) : Except String State :=
  if (s.get id).isSome then .error "gpu: id in use"
  else if s.objs.length + 1 > maxObjects then .error "gpu: too many objects"
  else if s.used + o.bytes > maxBytes then .error "gpu: page GPU memory quota"
  else .ok { s with objs := (id, o) :: s.objs }

/-- Remove an object, and any readback of it, waiting or answered. -/
def remove (s : State) (id : Nat) : State :=
  { s with objs := s.objs.filter (·.1 != id), pending := s.pending.filter (·.2.1 != id),
           mapped := s.mapped.filter (·.1 != id) }

def apply (s : State) : Change → Except String State
  | .none => .ok s
  | .add id o => add s id o
  | .remove id => .ok (remove s id)
  | .read ticket id size =>
    if s.pending.length ≥ maxPending then .error "gpu: too many readbacks waiting"
    else if s.mappedBytes + size > maxMapped then .error "gpu: readback memory quota"
    else .ok { s with pending := (ticket, id, size) :: s.pending }
  | .unmap id => .ok { s with mapped := s.mapped.filter (·.1 != id) }

/-! ## Planning a command -/

def layoutOk (l : VLayout) : Bool :=
  l.stride ≤ maxStride && l.stride % 4 == 0 && l.attrs.length ≤ maxAttrs &&
  l.attrs.all (fun a => a.offset % 4 == 0 && a.offset + a.format.bytes ≤ l.stride && a.location < 16)

/-- Every `@location` input of the vertex entry has an attribute of its type. -/
def inputsMatch (m : Wgsl.Module) (vs : Wgsl.Fn) (layouts : List VLayout) : Bool :=
  (vs.locations m.structs).all fun (loc, ty) =>
    layouts.any fun l => l.attrs.any fun a => a.location == loc && a.format.ty == ty

def planDispatch (s : State) (d : Dispatch) : HostDispatch :=
  let work := match computePipelineOf s d.pipeline with
    | some (inv, cost, _) => d.x * d.y * d.z * inv * cost
    | none => 0
  { pipeline := s.gid d.pipeline, bind := d.bind.map s.gid, x := d.x, y := d.y, z := d.z, work }

def planDraw (s : State) (d : Draw) : HostDraw :=
  { pipeline := s.gid d.pipeline, bind := d.bind.map s.gid, vbufs := d.vbufs.map s.gid,
    count := d.count, instances := d.instances, first := d.first, firstInstance := d.firstInstance }

def plan (s : State) : Command → Except String (Change × List HostCmd)
  | .configure id node w h => do
    if w == 0 || h == 0 || w > maxCanvas || h > maxCanvas then throw "gpu: canvas size"
    return (.add id (.canvas node w h), [.createCanvas (s.gid id) node w h canvasUsage])
  | .createBuffer id size usage => do
    if size > maxBuffer then throw "gpu: buffer too large"
    let size := Wgsl.roundUp 4 size
    if !usageOk usage then throw "gpu: buffer usage not allowed for pages (no MAP_WRITE, INDEX, INDIRECT or QUERY_RESOLVE; MAP_READ only with COPY_DST)"
    -- The host's buffer also has COPY_DST, which its clear needs (WebGPU's clearBuffer);
    -- the page's own usage, kept in the table, is what every later check reads.
    return (.add id (.buffer size usage), [.createBuffer (s.gid id) size (usage ||| usageCopyDst), .clearBuffer (s.gid id) size])
  | .writeBuffer id offset data => do
    let some (size, _) := bufferOf s id | throw "gpu: writeBuffer: no such buffer"
    if offset % 4 != 0 || data.size % 4 != 0 then throw "gpu: writeBuffer: not a multiple of 4"
    if offset + data.size > size then throw "gpu: writeBuffer: out of range"
    return (.none, [.writeBuffer (s.gid id) offset data])
  | .createShader id code => do
    let m ← Wgsl.compile code
    let text := m.print
    return (.add id (.shader m text.utf8ByteSize), [.createShader (s.gid id) text])
  | .createProgram id vs fs => do
    let (m, _) ← Glsl.compileProgram vs fs
    let text := m.print
    return (.add id (.shader m text.utf8ByteSize), [.createShader (s.gid id) text])
  | .createPipeline id sh vs fs layouts topology => do
    let some (.shader m _) := s.get sh | throw "gpu: pipeline: no such shader module"
    if !m.storage.isEmpty || m.uniformBinding != 0 then
      throw "gpu: pipeline: a render pipeline binds one uniform at binding 0 and no storage"
    let some vf := m.entry? .vertex vs | throw "gpu: pipeline: no vertex entry point"
    let some ff := m.entry? .fragment fs | throw "gpu: pipeline: no fragment entry point"
    if layouts.length > maxLayouts || !layouts.all layoutOk then throw "gpu: pipeline: vertex layout"
    if !inputsMatch m vf layouts then throw "gpu: pipeline: vertex inputs do not match the layout"
    let uniform ← match m.uniform with
      | none => pure none
      | some _ => match m.uniformSize with
        | some z => pure (some z)
        | none => throw "gpu: pipeline: uniform layout"
    return (.add id (.pipeline layouts uniform),
      [.createPipeline (s.gid id) (s.gid sh) vf.name ff.name layouts topology])
  | .createBindGroup id p b => do
    let some (_, some need) := pipelineOf s p | throw "gpu: bind group: pipeline has no uniform"
    let some (size, _) := bufferOf s b | throw "gpu: bind group: no such buffer"
    if size < need then throw "gpu: bind group: buffer smaller than the uniform"
    return (.add id (.bindGroup p b need), [.createBindGroup (s.gid id) (s.gid p) (s.gid b) need])
  | .pass c clear draws => do
    if !isCanvas s c then throw "gpu: pass: no such canvas"
    if draws.length > maxDraws then throw "gpu: pass: too many draws"
    let clear := (min clear.1 255, min clear.2.1 255, min clear.2.2.1 255, min clear.2.2.2 255)
    return (.none, [.pass (s.gid c) clear (draws.map (planDraw s))])
  | .destroy id => do
    if (s.get id).isNone then throw "gpu: destroy: no such object"
    return (.remove id, [.destroy (s.gid id)])
  | .createComputePipeline id sh entry => do
    let some (.shader m _) := s.get sh | throw "gpu: compute pipeline: no such shader module"
    let some f := m.entry? .compute entry | throw "gpu: compute pipeline: no compute entry point"
    let some needs := m.bindingNeeds | throw "gpu: compute pipeline: a binding's layout"
    let (x, y, z) := f.workgroup
    return (.add id (.computePipeline (x * y * z) f.body.cost needs),
      [.createComputePipeline (s.gid id) (s.gid sh) f.name (needs.map fun n => (n.binding, n.space))])
  | .createComputeBindGroup id p es => do
    let some (_, _, needs) := computePipelineOf s p | throw "gpu: bind group: no such compute pipeline"
    if es.length > Wgsl.maxBindings then throw "gpu: bind group: too many entries"
    -- entries in the pipeline's order of bindings
    let es := needs.filterMap fun n => es.find? (·.1 == n.binding)
    if es.length != needs.length then throw "gpu: bind group: an entry for each binding of the pipeline"
    for (b, buf) in es do
      let some n := needs.find? (·.binding == b) | throw "gpu: bind group: no such binding"
      let some (size, usage) := bufferOf s buf | throw "gpu: bind group: no such buffer"
      if usage &&& spaceUsage n.space == 0 then throw "gpu: bind group: the buffer's usage does not allow this binding"
      if size < n.minSize then throw s!"gpu: bind group: binding {b} needs at least {n.minSize} bytes"
    return (.add id (.computeBind p es), [.createComputeBind (s.gid id) (s.gid p) (hostEntries s es)])
  | .computePass ds => do
    if ds.length > maxDispatches then throw "gpu: compute pass: too many dispatches"
    return (.none, [.computePass (ds.map (planDispatch s))])
  | .copyBuffer src so dst do_ size => do
    -- WebGPU: a buffer that is mapped or being mapped is not used in a submit
    if s.pending.any (fun r => r.2.1 == src || r.2.1 == dst) || s.mapped.any (fun r => r.1 == src || r.1 == dst) then
      throw "gpu: copyBufferToBuffer: a buffer is mapped or being mapped"
    return (.none, [.copyBuffer (s.gid src) so (s.gid dst) do_ size])
  | .mapRead id ticket => do
    let some (size, usage) := bufferOf s id | throw "gpu: mapAsync: no such buffer"
    if usage &&& usageMapRead == 0 then throw "gpu: mapAsync: the buffer has no MAP_READ usage"
    if s.pending.any (fun r => r.1 == ticket || r.2.1 == id) || s.mapped.any (·.1 == id) then
      throw "gpu: mapAsync: the buffer is mapped or being mapped"
    return (.read ticket id size, [.readBuffer (s.gid id) size ticket])
  | .unmap id => return (.unmap id, [])

/-- One page command: the new table and the host commands, or a refusal (the table is
then unchanged). -/
def step (s : State) (c : Command) : Except String (State × List HostCmd) := do
  let (ch, out) ← plan s c
  if !out.all (·.safe s) then throw "gpu: command refused by the final check"
  if s.work + workOf out > maxFrameWork then
    throw "gpu: compute pass: the page's GPU work for this frame is used up; dispatch again in the next frame"
  let s' ← apply s ch
  return ({ s' with work := s.work + workOf out }, out)

/-- The host has taken the page's commands: a new frame's work budget. -/
def State.newFrame (s : State) : State := { s with work := 0 }

/-- The host's answer to readback `ticket`: the buffer's bytes. Accepted only for a
readback that is waiting, with exactly the size asked for; the bytes are then held for
the page until it unmaps. `none` for anything else (the state is then unchanged). -/
def deliver (s : State) (ticket : Nat) (data : ByteArray) : Option State :=
  match s.pending.find? (·.1 == ticket) with
  | some (_, id, size) =>
    if data.size == size then
      some { s with pending := s.pending.filter (·.1 != ticket), mapped := (id, data) :: s.mapped }
    else none
  | none => none

/-- The host could not read back `ticket` (the device was lost, the map failed): the
readback is dropped. -/
def fail (s : State) (ticket : Nat) : State := { s with pending := s.pending.filter (·.1 != ticket) }

/-- The bytes held for a page's buffer, if it was read back and not unmapped. -/
def mappedOf (s : State) (id : Nat) : Option ByteArray := s.mapped.lookup id

/-- The buffer a waiting readback `ticket` is of. -/
def pendingOf (s : State) (ticket : Nat) : Option Nat := (s.pending.find? (·.1 == ticket)).map (·.2.1)

/-- One command of a sequence: a refused command changes nothing. -/
def stepOr (acc : State × List HostCmd) (c : Command) : State × List HostCmd :=
  match step acc.1 c with
  | .ok (s', out) => (s', acc.2 ++ out)
  | .error _ => acc

/-- A command sequence from `s`. -/
def run (s : State) (cs : List Command) : State × List HostCmd := cs.foldl stepOr (s, [])

end L4Factoidal.PageGpu
