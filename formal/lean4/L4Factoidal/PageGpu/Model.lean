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
-/
import L4Factoidal.PageGpu.Wgsl

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

/-- What a page script asks for (one import call each). Ids are the page's own. -/
inductive Command where
  /-- `canvas.getContext('webgpu')` + `configure`: page canvas `id` for DOM node `node`. -/
  | configure (id node w h : Nat)
  | createBuffer (id size usage : Nat)
  | writeBuffer (id offset : Nat) (data : ByteArray)
  | createShader (id : Nat) (code : String)
  | createPipeline (id shader : Nat) (vs fs : String) (layouts : List VLayout) (topology : Topology)
  /-- Group 0, binding 0: a uniform buffer, for `pipeline`'s layout. -/
  | createBindGroup (id pipeline buffer : Nat)
  /-- A render pass on a page canvas (always `loadOp: clear`), submitted. -/
  | pass (canvas : Nat) (clear : Rgba) (draws : List Draw)
  | destroy (id : Nat)
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

/-- What Lean asks the host's WebGPU device to do. There is no kind that copies out of a
texture or a buffer, or maps one: the host has nothing to read back with. -/
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

/-- WebGPU buffer usage bits. -/
def usageMapRead : Nat := 1
def usageMapWrite : Nat := 2
def usageCopySrc : Nat := 4
def usageCopyDst : Nat := 8
def usageIndex : Nat := 16
def usageVertex : Nat := 32
def usageUniform : Nat := 64
def usageStorage : Nat := 128
/-- Every usage bit a page buffer may not have: map, copy out, storage, index,
indirect, query resolve. -/
def forbiddenUsage : Nat := 1 ||| 2 ||| 4 ||| 16 ||| 128 ||| 256 ||| 512
/-- WebGPU texture usage of a page canvas: `RENDER_ATTACHMENT | TEXTURE_BINDING`
(16 ||| 4); never `COPY_SRC` (1). -/
def canvasUsage : Nat := 20

/-! ## The page's table -/

structure State where
  page : Nat := 0
  objs : List (Nat × Obj) := []
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

/-- The final check of one emitted command against the table before the command. -/
def HostCmd.safe (s : State) : HostCmd → Bool
  | .createCanvas g _ w h usage => fresh s g && usage == canvasUsage && 0 < w && w ≤ maxCanvas && 0 < h && h ≤ maxCanvas
  | .createBuffer g size usage => fresh s g && usage &&& forbiddenUsage == 0 && usage < 1024 &&
      size ≤ maxBuffer && size % 4 == 0
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

/-! ## Changes, with the quota checks -/

inductive Change where
  | none
  | add (id : Nat) (o : Obj)
  | remove (id : Nat)

def add (s : State) (id : Nat) (o : Obj) : Except String State :=
  if (s.get id).isSome then .error "gpu: id in use"
  else if s.objs.length + 1 > maxObjects then .error "gpu: too many objects"
  else if s.used + o.bytes > maxBytes then .error "gpu: page GPU memory quota"
  else .ok { s with objs := (id, o) :: s.objs }

def remove (s : State) (id : Nat) : State := { s with objs := s.objs.filter (·.1 != id) }

def apply (s : State) : Change → Except String State
  | .none => .ok s
  | .add id o => add s id o
  | .remove id => .ok (remove s id)

/-! ## Planning a command -/

def layoutOk (l : VLayout) : Bool :=
  l.stride ≤ maxStride && l.stride % 4 == 0 && l.attrs.length ≤ maxAttrs &&
  l.attrs.all (fun a => a.offset % 4 == 0 && a.offset + a.format.bytes ≤ l.stride && a.location < 16)

/-- Every `@location` input of the vertex entry has an attribute of its type. -/
def inputsMatch (m : Wgsl.Module) (vs : Wgsl.Fn) (layouts : List VLayout) : Bool :=
  (vs.locations m.structs).all fun (loc, ty) =>
    layouts.any fun l => l.attrs.any fun a => a.location == loc && a.format.ty == ty

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
    if usage &&& forbiddenUsage != 0 || usage ≥ 1024 then throw "gpu: buffer usage not allowed for pages"
    return (.add id (.buffer size usage), [.createBuffer (s.gid id) size usage, .clearBuffer (s.gid id) size])
  | .writeBuffer id offset data => do
    let some (size, _) := bufferOf s id | throw "gpu: writeBuffer: no such buffer"
    if offset % 4 != 0 || data.size % 4 != 0 then throw "gpu: writeBuffer: not a multiple of 4"
    if offset + data.size > size then throw "gpu: writeBuffer: out of range"
    return (.none, [.writeBuffer (s.gid id) offset data])
  | .createShader id code => do
    let m ← Wgsl.compile code
    let text := m.print
    return (.add id (.shader m text.utf8ByteSize), [.createShader (s.gid id) text])
  | .createPipeline id sh vs fs layouts topology => do
    let some (.shader m _) := s.get sh | throw "gpu: pipeline: no such shader module"
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

/-- One page command: the new table and the host commands, or a refusal (the table is
then unchanged). -/
def step (s : State) (c : Command) : Except String (State × List HostCmd) := do
  let (ch, out) ← plan s c
  if !out.all (·.safe s) then throw "gpu: command refused by the final check"
  let s' ← apply s ch
  return (s', out)

/-- One command of a sequence: a refused command changes nothing. -/
def stepOr (acc : State × List HostCmd) (c : Command) : State × List HostCmd :=
  match step acc.1 c with
  | .ok (s', out) => (s', acc.2 ++ out)
  | .error _ => acc

/-- A command sequence from `s`. -/
def run (s : State) (cs : List Command) : State × List HostCmd := cs.foldl stepOr (s, [])

end L4Factoidal.PageGpu
