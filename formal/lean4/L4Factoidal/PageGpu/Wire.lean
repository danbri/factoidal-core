/-
L4Factoidal.PageGpu.Wire: the bytes of the `foafnaut_dom.gpu_command` import, and the
JSON text of host commands (record: docs/designissues/2026-11-08-page-gpu.md).

An import call is `gpu_command(op, unused, ptr, len, out, cap)`. The bytes at `ptr` are
a header line of decimal numbers separated by spaces, then `\n`, then a payload:

| op | command | header | payload |
|---|---|---|---|
| 1 | configure | id node w h | |
| 2 | createBuffer | id size usage | |
| 3 | writeBuffer | id offset | the data |
| 4 | createShader | id | the WGSL text |
| 5 | createPipeline | id shader topology nLayouts (stride nAttrs (format offset location)*)* | vs `\n` fs |
| 6 | createBindGroup | id pipeline buffer | |
| 7 | pass | canvas r g b a nDraws (pipeline bind nVb vb* count instances first firstInstance)* | |
| 8 | destroy | id | |
| 9 | createProgram | id | the GLSL vertex shader, U+0000, the fragment shader |
| 10 | createComputePipeline | id shader | the entry point's name |
| 11 | createComputeBindGroup | id pipeline n (binding buffer)* | |
| 12 | computePass | n (pipeline bind x y z)* | |
| 13 | copyBuffer | src srcOffset dst dstOffset size | |
| 14 | mapRead | id ticket | |
| 15 | unmap | id | |
| 16 | mapped bytes (a query: the answer is the bytes, `Hosts.Dom.gpuCommand`) | id | |

`bind` 0 is none (page ids start at 1). Formats 1..4 are `float32`..`float32x4`;
topologies 0..3 are triangle-list, triangle-strip, line-list, point-list.

Op `64 + k` is op `k` with a binary header (`binaryOp`): a little-endian u32 count n,
then n little-endian u32 numbers, then `\n`, then the payload. The numbers are the same
as in the text form (`decode_binary_pass` checks one pass in both forms); the binary
form spares a page script the conversion of numbers to text, which costs a script
engine in WasmVM more than anything else in a frame (record, section 10).
-/
import L4Factoidal.PageGpu.Model

namespace L4Factoidal.PageGpu.Wire
open L4Factoidal.PageGpu

def maxHeader : Nat := 65536

/-- Split the bytes at the first `\n`. -/
def splitLine (b : ByteArray) : ByteArray × ByteArray := Id.run do
  let mut k := b.size
  for i in [0:b.size] do
    if b[i]! == 10 then k := i; break
  return (b.extract 0 k, b.extract (k + 1) b.size)

def nums (header : ByteArray) : Except String (List Nat) := do
  if header.size > maxHeader then throw "gpu: header too long"
  let some text := String.fromUTF8? header | throw "gpu: header is not UTF-8"
  let parts := (text.splitOn " ").filter (· != "")
  parts.mapM fun p => match p.toNat? with
    | some n => pure n
    | none => throw "gpu: header number"

/-- Ops at or above this carry a binary header. -/
def binaryOp : Nat := 64

/-- The little-endian u32 at byte `i` (0 past the end). -/
def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 256 + b[i+2]!.toNat * 65536 + b[i+3]!.toNat * 16777216

/-- A binary header: the numbers and the payload after its `\n`. -/
def binHeader (b : ByteArray) : Except String (List Nat × ByteArray) := do
  if b.size < 4 then throw "gpu: header too short"
  let n := u32At b 0
  if 4 * n > maxHeader then throw "gpu: header too long"
  let stop := 4 + 4 * n
  if b.size < stop + 1 || b[stop]! != 10 then throw "gpu: header too short"
  return ((List.range n).map (fun k => u32At b (4 + 4 * k)), b.extract (stop + 1) b.size)

/-- A reader over the header numbers. -/
abbrev R := StateT (List Nat) (Except String)

def next : R Nat := do
  match ← get with
  | n :: rest => set rest; return n
  | [] => throw "gpu: header too short"

def format : Nat → Except String Format
  | 1 => .ok .float32 | 2 => .ok .float32x2 | 3 => .ok .float32x3 | 4 => .ok .float32x4
  | _ => .error "gpu: vertex format"

def topology : Nat → Except String Topology
  | 0 => .ok .triangleList | 1 => .ok .triangleStrip | 2 => .ok .lineList | 3 => .ok .pointList
  | _ => .error "gpu: topology"

def layouts (n : Nat) : R (List VLayout) := do
  if n > maxLayouts then throw "gpu: too many vertex buffers"
  let mut out : Array VLayout := #[]
  for _ in [0:n] do
    let stride ← next
    let k ← next
    if k > maxAttrs then throw "gpu: too many attributes"
    let mut attrs : Array VAttr := #[]
    for _ in [0:k] do
      let f ← format (← next)
      let offset ← next
      let location ← next
      attrs := attrs.push { format := f, offset, location }
    out := out.push { stride, attrs := attrs.toList }
  return out.toList

def draws (n : Nat) : R (List Draw) := do
  if n > maxDraws then throw "gpu: too many draws"
  let mut out : Array Draw := #[]
  for _ in [0:n] do
    let pipeline ← next
    let b ← next
    let k ← next
    if k > maxLayouts then throw "gpu: too many vertex buffers"
    let mut vbufs : Array Nat := #[]
    for _ in [0:k] do vbufs := vbufs.push (← next)
    let count ← next
    let instances ← next
    let first ← next
    let firstInstance ← next
    out := out.push { pipeline, bind := if b == 0 then none else some b, vbufs := vbufs.toList,
                      count, instances, first, firstInstance }
  return out.toList

def entries (n : Nat) : R (List (Nat × Nat)) := do
  if n > Wgsl.maxBindings then throw "gpu: too many bind group entries"
  let mut out : Array (Nat × Nat) := #[]
  for _ in [0:n] do
    let b ← next
    let buf ← next
    out := out.push (b, buf)
  return out.toList

def dispatches (n : Nat) : R (List Dispatch) := do
  if n > maxDispatches then throw "gpu: too many dispatches"
  let mut out : Array Dispatch := #[]
  for _ in [0:n] do
    let pipeline ← next
    let b ← next
    let x ← next; let y ← next; let z ← next
    out := out.push { pipeline, bind := if b == 0 then none else some b, x, y, z }
  return out.toList

def text (b : ByteArray) : Except String String :=
  match String.fromUTF8? b with | some s => .ok s | none => .error "gpu: text is not UTF-8"

/-- The command of op `op` with header numbers `ns` and the payload. -/
def decodeWith (op : Nat) (ns : List Nat) (payload : ByteArray) : Except String Command := do
  let read := fun (r : R Command) => (r.run ns).map (·.1)
  match op with
  | 1 => read do return Command.configure (← next) (← next) (← next) (← next)
  | 2 => read do return Command.createBuffer (← next) (← next) (← next)
  | 3 => read do return Command.writeBuffer (← next) (← next) payload
  | 4 => do
    let code ← text payload
    read do return Command.createShader (← next) code
  | 5 => do
    let (vs, fs) := splitLine payload
    let vs ← text vs
    let fs ← text fs
    read do
      let id ← next
      let sh ← next
      let t ← topology (← next)
      let ls ← layouts (← next)
      return Command.createPipeline id sh vs fs ls t
  | 6 => read do return Command.createBindGroup (← next) (← next) (← next)
  | 7 => read do
    let c ← next
    let r ← next; let g ← next; let b ← next; let a ← next
    return Command.pass c (r, g, b, a) (← draws (← next))
  | 8 => read do return Command.destroy (← next)
  | 9 => do
    let some k := (List.range payload.size).find? (fun i => payload[i]! == 0) | throw "gpu: program needs two shaders"
    let vs ← text (payload.extract 0 k)
    let fs ← text (payload.extract (k + 1) payload.size)
    read do return Command.createProgram (← next) vs fs
  | 10 => do
    let entry ← text payload
    read do return Command.createComputePipeline (← next) (← next) entry
  | 11 => read do
    let id ← next
    let p ← next
    return Command.createComputeBindGroup id p (← entries (← next))
  | 12 => read do return Command.computePass (← dispatches (← next))
  | 13 => read do return Command.copyBuffer (← next) (← next) (← next) (← next) (← next)
  | 14 => read do return Command.mapRead (← next) (← next)
  | 15 => read do return Command.unmap (← next)
  | _ => throw "gpu: unknown command"

/-- Op 16 (or `binaryOp + 16`): the page asks for the bytes Lean holds for a buffer it read
back (`getMappedRange`); the answer is the bytes themselves, not text. -/
def mappedOp : Nat := 16

/-- Op 17: does the embedder replay this page's GPU commands (`State.replay`)? The answer
is "1" or "0" (`navigator.gpu.requestAdapter()` answers null on "0"). -/
def replayOp : Nat := 17

/-- The buffer id of a `mappedOp` call. -/
def mappedId (op : Nat) (bytes : ByteArray) : Option Nat :=
  let ns := if op ≥ binaryOp then (binHeader bytes).toOption.map (·.1) else (nums (splitLine bytes).1).toOption
  match ns with
  | some [id] => some id
  | _ => none

/-- The command of one import call: a text header (ops below `binaryOp`) or a binary one. -/
def decode (op : Nat) (bytes : ByteArray) : Except String Command :=
  if op ≥ binaryOp then do
    let (ns, payload) ← binHeader bytes
    decodeWith (op - binaryOp) ns payload
  else do
    let (header, payload) := splitLine bytes
    decodeWith op (← nums header) payload

/-- The binary header of `ns` (each below 2^32), as a page script writes it, with the `\n`. -/
def binaryHeader (ns : List Nat) : ByteArray :=
  let u32 := fun (n : Nat) => ByteArray.mk #[(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 16777216 % 256).toUInt8]
  ns.foldl (fun acc n => acc ++ u32 n) (u32 ns.length) ++ ByteArray.mk #[10]

/-! ## JSON of host commands -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList[n % 16]!

def jsonString (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c.toNat < 32 then "\\u00" ++ String.singleton (hexDigit (c.toNat / 16)) ++ String.singleton (hexDigit c.toNat)
    else String.singleton c) ++ "\""

def b64chars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

def base64 (b : ByteArray) : String := Id.run do
  let mut out : Array Char := #[]
  let n := b.size
  for k in [0:(n + 2) / 3] do
    let i := 3 * k
    let b0 := b[i]!.toNat
    let b1 := if i + 1 < n then b[i+1]!.toNat else 0
    let b2 := if i + 2 < n then b[i+2]!.toNat else 0
    let w := b0 * 65536 + b1 * 256 + b2
    out := out.push b64chars[w / 262144 % 64]! |>.push b64chars[w / 4096 % 64]!
    out := out.push (if i + 1 < n then b64chars[w / 64 % 64]! else '=')
    out := out.push (if i + 2 < n then b64chars[w % 64]! else '=')
  return String.ofList out.toList

def gid (g : Gid) : String := s!"[{g.page},{g.id}]"

def layoutJson (l : VLayout) : String :=
  s!"\{\"arrayStride\":{l.stride},\"attributes\":[" ++
  ",".intercalate (l.attrs.map fun a =>
    s!"\{\"format\":\"{a.format.name}\",\"offset\":{a.offset},\"shaderLocation\":{a.location}}") ++ "]}"

def drawJson (d : HostDraw) : String :=
  s!"\{\"pipeline\":{gid d.pipeline},\"bind\":{match d.bind with | some b => gid b | none => "null"}," ++
  s!"\"vbufs\":[{",".intercalate (d.vbufs.map gid)}],\"count\":{d.count},\"instances\":{d.instances}," ++
  s!"\"first\":{d.first},\"firstInstance\":{d.firstInstance}}"

/-- The WebGPU buffer binding type of a space. -/
def spaceName : Wgsl.Space → String
  | .uniform => "uniform" | .read => "read-only-storage" | .readWrite => "storage"

def dispatchJson (d : HostDispatch) : String :=
  s!"\{\"pipeline\":{gid d.pipeline},\"bind\":{match d.bind with | some b => gid b | none => "null"}," ++
  s!"\"x\":{d.x},\"y\":{d.y},\"z\":{d.z}}"

def HostCmd.json : HostCmd → String
  | .createCanvas g node w h usage =>
    s!"\{\"k\":\"canvas\",\"g\":{gid g},\"node\":{node},\"w\":{w},\"h\":{h},\"usage\":{usage}}"
  | .createBuffer g size usage => s!"\{\"k\":\"buffer\",\"g\":{gid g},\"size\":{size},\"usage\":{usage}}"
  | .clearBuffer g size => s!"\{\"k\":\"clear\",\"g\":{gid g},\"size\":{size}}"
  | .writeBuffer g offset data =>
    s!"\{\"k\":\"write\",\"g\":{gid g},\"offset\":{offset},\"data\":\"{base64 data}\"}"
  | .createShader g code => s!"\{\"k\":\"shader\",\"g\":{gid g},\"code\":{jsonString code}}"
  | .createPipeline g sh vs fs ls t =>
    s!"\{\"k\":\"pipeline\",\"g\":{gid g},\"shader\":{gid sh},\"vs\":{jsonString vs},\"fs\":{jsonString fs}," ++
    s!"\"topology\":\"{t.name}\",\"buffers\":[{",".intercalate (ls.map layoutJson)}]}"
  | .createBindGroup g p b size =>
    s!"\{\"k\":\"bind\",\"g\":{gid g},\"pipeline\":{gid p},\"buffer\":{gid b},\"size\":{size}}"
  | .pass c (r, g, b, a) ds =>
    s!"\{\"k\":\"pass\",\"canvas\":{gid c},\"clear\":[{r},{g},{b},{a}],\"draws\":[{",".intercalate (ds.map drawJson)}]}"
  | .destroy g => s!"\{\"k\":\"destroy\",\"g\":{gid g}}"
  | .createComputePipeline g sh entry layout =>
    s!"\{\"k\":\"cpipeline\",\"g\":{gid g},\"shader\":{gid sh},\"entry\":{jsonString entry},\"layout\":[" ++
    ",".intercalate (layout.map fun (b, sp) => s!"[{b},\"{spaceName sp}\"]") ++ "]}"
  | .createComputeBind g p es =>
    s!"\{\"k\":\"cbind\",\"g\":{gid g},\"pipeline\":{gid p},\"entries\":[" ++
    ",".intercalate (es.map fun (b, buf, size) => s!"[{b},{gid buf},{size}]") ++ "]}"
  | .computePass ds => "{\"k\":\"cpass\",\"dispatches\":[" ++ ",".intercalate (ds.map dispatchJson) ++ "]}"
  | .copyBuffer src so dst do_ size =>
    s!"\{\"k\":\"copy\",\"src\":{gid src},\"srcOffset\":{so},\"dst\":{gid dst},\"dstOffset\":{do_},\"size\":{size}}"
  | .readBuffer g size ticket => s!"\{\"k\":\"read\",\"g\":{gid g},\"size\":{size},\"ticket\":{ticket}}"

end L4Factoidal.PageGpu.Wire
