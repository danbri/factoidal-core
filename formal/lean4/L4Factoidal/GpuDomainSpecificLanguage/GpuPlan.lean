import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath
import L4Factoidal.GpuDomainSpecificLanguage.GraphJson

/-!
# PVGraph GPU plan: Lean owns lowering, the host only allocates and dispatches

The input is the *actual* admitted GDSL 0.2 document plus buffer shapes.
Only the direct parallel u32 fragment is emitted. Scan, reduction, unknown
operators and shape errors refuse. No JavaScript operator registry or graph
checker is involved. A kernel's numeric opcode is the one in GpuFastPath,
whose typed model is proved equivalent to the Lean primitive evaluator.

This plan does not assert that GPU shader compilers or physical devices
implement WGSL. Tests must execute the source below on a real WebGPU
adapter; missing GPU evidence must not be reported as a pass.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.GpuPlan

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.Graph
open L4Factoidal.GpuDomainSpecificLanguage.GraphJson
open L4Factoidal.GpuDomainSpecificLanguage.GraphWords
open L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath

def workgroupSize : Nat := 64
def maxWords : Nat := 262144

/-- Fixed, reviewable WGSL: one invocation writes exactly its own word,
    never reads an output buffer and performs UInt32 wrapping operations.
    GPU compiler/runtime refinement is an explicit external boundary. -/
def shader : String := String.intercalate "\n" [
  "@group(0) @binding(0) var<storage, read> a : array<u32>;",
  "@group(0) @binding(1) var<storage, read> b : array<u32>;",
  "@group(0) @binding(2) var<storage, read_write> outWords : array<u32>;",
  "@group(0) @binding(3) var<storage, read> config : array<u32>;",
  "@compute @workgroup_size(64,1,1)",
  "fn main(@builtin(global_invocation_id) gid : vec3<u32>) {",
  "  let i = gid.x;",
  "  let count = config[1];",
  "  if (i >= count) { return; }",
  "  let code = config[0];",
  "  let k = config[2];",
  "  if (code == 1u) { outWords[i] = a[i] + k; }",
  "  else if (code == 2u) { outWords[i] = a[i] * k; }",
  "  else if (code == 3u) { outWords[i] = a[i] ^ k; }",
  "  else if (code == 4u) { outWords[i] = a[i] + b[i]; }",
  "  else if (code == 5u) { outWords[i] = a[i] ^ b[i]; }",
  "  else if (code == 8u) { outWords[i] = a[0] + b[0]; }",
  "  else if (code == 9u) { outWords[i] = a[0]; }",
  "}"
]

private def fail {α : Type} (message : String) : Except String α :=
  .error ("PVGraph GPU: " ++ message)

private def strField (j : Json) (name : String) : Except String String := do
  (← j.getObjVal? name).getStr?

private def paramValue (j : Json) : Except String Nat := do
  let p ← j.getObjVal? "params"
  (← p.getObjVal? "value").getNat?

private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def txt (s : String) : Json := toJson s
private def num (n : Nat) : Json := toJson n

private structure Shape where
  kind : LinkKind
  words : Nat

private structure State where
  shapes : List (String × Shape) := []
  steps : List Json := []
  outputs : List Json := []
  inputs : List (String × Json) := []

private def shapeOf (st : State) (name : String) : Except String Shape := do
  match st.shapes.find? (fun p => p.1 == name) with
  | some (_, shape) => pure shape
  | none => fail ("missing or forward reference " ++ name)

private def sourceOf (doc : Document) (node port : String) : Except String String := do
  match doc.links.find? (fun e => e.target.node == node && e.target.port == port) with
  | some link => pure link.source.node
  | none => fail ("unbound input port " ++ node ++ "." ++ port)

private def sourceShape (st : State) (doc : Document) (node port : String) :
    Except String (String × Shape) := do
  let source ← sourceOf doc node port
  return (source, ← shapeOf st source)

private def record (st : State) (node : String) (shape : Shape)
    (step : Json) : State :=
  { st with shapes := (node,shape) :: st.shapes, steps := step :: st.steps }

/-- Generate an all-or-nothing GPU plan from the canonical admitted PVGraph
    and *only input sizes*. The actual values remain in typed host buffers. -/
def compile? (rawGraph inputSizes : Json) : Except String Json := do
  let certified ← GraphJson.decodeCertified? rawGraph
  let doc := certified.graph
  let rawNodes ← (← rawGraph.getObjVal? "nodes").getArr?
  let mut st : State := {}
  for (node, raw) in doc.nodes.zip rawNodes.toList do
    if node.op == "core.input" then
      let p ← raw.getObjVal? "params"
      let name ← strField p "name"
      let length ← (← inputSizes.getObjVal? name).getNat?
      let kind := (node.outputs.head!).dataType.kind
      if kind == .scalar && length != 1 then
        fail ("scalar input needs one word: " ++ name)
      if length > maxWords then fail ("input exceeds GPU bound: " ++ name)
      st := record st node.id ⟨kind,length⟩
        (obj [("kind",txt "input"),("node",txt node.id),
              ("name",txt name),("words",num length)])
      st := { st with inputs := (name,num length) :: st.inputs }
    else if node.op == "core.output" then
      let p ← raw.getObjVal? "params"
      let name ← strField p "name"
      let (source,shape) ← sourceShape st doc node.id "in"
      st := { st with outputs := obj [
        ("name",txt name),("source",txt source),
        ("kind",txt (if shape.kind == .scalar then "scalar" else "buffer")),
        ("words",num shape.words)] :: st.outputs }
    else if node.op == "u32.scalar.const" then
      let constant ← paramValue raw
      st := record st node.id ⟨.scalar,1⟩ (obj [
        ("kind",txt "const"),("node",txt node.id),("value",num constant),
        ("words",num 1)])
    else do
      let some op := Operator.fromName? node.op |
        fail ("unsupported GPU operator " ++ node.op)
      let some tag := KernelTag.ofOperator? op |
        fail ("operator requires Lean CPU fallback: " ++ node.op)
      let mut a := ""
      let mut b := ""
      let mut words := 0
      let mut outKind := LinkKind.buffer
      let mut constant := 0
      if op == .mapAdd || op == .mapMul || op == .mapXor then
        let (src,sh) ← sourceShape st doc node.id "x"
        a := src
        b := src
        words := sh.words
        constant ← paramValue raw
      else if op == .zipAdd || op == .zipXor then
        let (srcA,shA) ← sourceShape st doc node.id "a"
        let (srcB,shB) ← sourceShape st doc node.id "b"
        if shA.words != shB.words then fail ("unequal zip input lengths at " ++ node.id)
        a := srcA
        b := srcB
        words := shA.words
      else if op == .scalarAdd then
        let (srcA,_) ← sourceShape st doc node.id "a"
        let (srcB,_) ← sourceShape st doc node.id "b"
        a := srcA
        b := srcB
        words := 1
        outKind := .scalar
      else if op == .broadcast then
        let (srcA,_) ← sourceShape st doc node.id "value"
        let (srcB,shB) ← sourceShape st doc node.id "shape"
        a := srcA
        b := srcB
        words := shB.words
      else fail ("nonparallel operation " ++ node.op)
      let groups := max 1 ((words + workgroupSize - 1) / workgroupSize)
      if groups > 65535 || words > maxWords then fail "GPU dispatch limit"
      st := record st node.id ⟨outKind, words⟩ (obj [
        ("kind",txt "kernel"),("node",txt node.id),
        ("code",num tag.code.toNat),("a",txt a),("b",txt b),
        ("constant",num constant),("words",num words),
        ("workgroups",num groups)])
  if inputSizes.compress != (obj st.inputs).compress then
    fail "GPU input shapes must bind every and only declared input"
  pure (obj [
    ("version",txt "pvgraph-gpu/0.1"),
    ("shader",txt shader),
    ("steps",toJson st.steps.reverse),
    ("outputs",toJson st.outputs.reverse)])

#guard (shader.splitOn "@compute").length == 2

end L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
