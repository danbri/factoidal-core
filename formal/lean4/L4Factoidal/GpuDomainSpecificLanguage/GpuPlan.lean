import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath
import L4Factoidal.GpuDomainSpecificLanguage.GraphJson
import L4Factoidal.GpuDomainSpecificLanguage.MapZipPlan

/-!
# PVGraph GPU plan: Lean owns lowering, the host only allocates and dispatches

The input is the *actual* admitted GDSL 0.2 document plus buffer shapes.
Parallel u32 operators, hierarchical scans and indexed tuple searches are
emitted. Reduction, unknown operators and shape errors refuse. No JavaScript operator registry or graph
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
def maxWords : Nat := IndexedJoinOps.maxWords

def shader : String := String.intercalate "\n" [
  "@group(0) @binding(0) var<storage, read> a : array<u32>;",
  "@group(0) @binding(1) var<storage, read> b : array<u32>;",
  "@group(0) @binding(2) var<storage, read_write> outWords : array<u32>;",
  "@group(0) @binding(3) var<storage, read> config : array<u32>;",
  "fn compare_row(r:u32,l:u32,k:u32)->i32 {",
  "  for (var c=0u;c<k;c=c+1u) {",
  "    let rp=2u*(r*k+c); let lp=2u*(l*k+c);",
  "    if (b[rp+1u]<a[lp+1u]) { return -1; }",
  "    if (b[rp+1u]>a[lp+1u]) { return 1; }",
  "    if (b[rp]<a[lp]) { return -1; }",
  "    if (b[rp]>a[lp]) { return 1; }",
  "  }",
  "  return 0;",
  "}",
  "@compute @workgroup_size(64,1,1)",
  "fn main(@builtin(global_invocation_id) gid : vec3<u32>) {",
  "  let i=gid.x; let count=config[1]; let code=config[0]; let k=config[2];",
  "  if (code==15u) {",
  "    if (i>=k) { return; }",
  "    var lo=0u; var hi=config[3];",
  "    for (var fuel=0u;fuel<32u && lo<hi;fuel=fuel+1u) {",
  "      let mid=lo+(hi-lo)/2u;",
  "      if (a[mid]<=i) { lo=mid+1u; } else { hi=mid; }",
  "    }",
  "    if (lo>=config[3]) { return; }",
  "    var previous=0u;",
  "    if (lo>0u) { previous=a[lo-1u]; }",
  "    outWords[2u*i]=lo; outWords[2u*i+1u]=b[lo]+i-previous;",
  "    return;",
  "  }",
  "  if (i>=count) { return; }",
  "  if (code==1u) { outWords[i]=a[i]+k; }",
  "  else if (code==2u) { outWords[i]=a[i]*k; }",
  "  else if (code==3u) { outWords[i]=a[i]^k; }",
  "  else if (code==4u) { outWords[i]=a[i]+b[i]; }",
  "  else if (code==5u) { outWords[i]=a[i]^b[i]; }",
  "  else if (code==8u) { outWords[i]=a[0]+b[0]; }",
  "  else if (code==9u) { outWords[i]=a[0]; }",
  "  else if (code==10u || code==11u) {",
  "    var lo=0u; var hi=config[4]/(2u*k);",
  "    for (var fuel=0u;fuel<32u && lo<hi;fuel=fuel+1u) {",
  "      let mid=lo+(hi-lo)/2u; let relation=compare_row(mid,i,k);",
  "      if (relation<0 || (code==11u && relation==0)) { lo=mid+1u; }",
  "      else { hi=mid; }",
  "    }",
  "    outWords[i]=lo;",
  "  }",
  "  else if (code==12u) { outWords[i]=a[i]-b[i]; }",
  "  else if (code==13u) { outWords[i]=a[min((i+1u)*64u,config[3])-1u]; }",
  "  else if (code==14u) {",
  "    var carry=0u; if (i>=64u) { carry=b[i/64u-1u]; }",
  "    outWords[i]=a[i]+carry;",
  "  }",
  "}"
]

def scanShader : String := String.intercalate "\n" [
  "@group(0) @binding(0) var<storage, read> a : array<u32>;",
  "@group(0) @binding(1) var<storage, read> b : array<u32>;",
  "@group(0) @binding(2) var<storage, read_write> outWords : array<u32>;",
  "@group(0) @binding(3) var<storage, read> config : array<u32>;",
  "var<workgroup> values : array<u32,64>;",
  "@compute @workgroup_size(64,1,1)",
  "fn main(@builtin(global_invocation_id) gid:vec3<u32>,",
  "        @builtin(local_invocation_id) lid:vec3<u32>) {",
  "  let i=gid.x; let lane=lid.x; var value=0u;",
  "  if (i<config[1]) {",
  "    value=a[i];",
  "    if (config[2]!=0u) { value=value+b[i]; }",
  "  }",
  "  values[lane]=value; workgroupBarrier();",
  "  for (var offset=1u;offset<64u;offset=offset*2u) {",
  "    var addend=0u;",
  "    if (lane>=offset) { addend=values[lane-offset]; }",
  "    workgroupBarrier();",
  "    values[lane]=values[lane]+addend;",
  "    workgroupBarrier();",
  "  }",
  "  if (i<config[1]) { outWords[i]=values[lane]; }",
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

private def kernelStep (node a b : String) (code words constant aw bw : Nat)
    (shaderName : String := "") : Json :=
  let lanes := if code == 15 then constant else words
  let selectedShader := if shaderName != "" then shaderName
    else if 1 ≤ code && code ≤ 5 then "mapZip" else "word"
  obj [("kind",txt "kernel"),("node",txt node),
    ("shader",txt selectedShader),("code",num code),("a",txt a),("b",txt b),
    ("constant",num constant),("words",num words),
    ("config",toJson [code,words,constant,aw,bw]),
    ("workgroups",num (max 1 ((lanes + 63) / 64)))]

/-- Hierarchical scan: each 64-lane workgroup scans its block, then block
    totals are scanned recursively and added back. Temporary storage is
    linear; no invocation scans the whole input. Five levels suffice for
    the admitted buffer bound. -/
private def emitScan : Nat → State → String → Nat → String → Except String State
  | 0, _, _, _, _ => fail "parallel scan depth exceeded"
  | fuel+1, st, source, words, node => do
      let groups := (words + 63) / 64
      if groups ≤ 1 then
        pure (record st node ⟨.buffer,words⟩
          (kernelStep node source source 6 words 0 words words "scan"))
      else
        let stem := "__pvg.s" ++ toString st.steps.length
        let localNode := stem ++ ".local"
        let sumNode := stem ++ ".sums"
        let scanNode := stem ++ ".blocks"
        let st := record st localNode ⟨.buffer,words⟩
          (kernelStep localNode source source 6 words 0 words words "scan")
        let st := record st sumNode ⟨.buffer,groups⟩
          (kernelStep sumNode localNode localNode 13 groups 0 words words)
        let st ← emitScan fuel st sumNode groups scanNode
        pure (record st node ⟨.buffer,words⟩
          (kernelStep node localNode scanNode 14 words 0 words groups))

/-- Generate an all-or-nothing GPU plan from the canonical admitted PVGraph
    and *only input sizes*. The actual values remain in typed host buffers. -/
def compileCandidate? (rawGraph inputSizes : Json) : Except String Json := do
  let certified ← GraphJson.decodeCertified? rawGraph
  let doc := certified.graph
  let rawNodes ← (← rawGraph.getObjVal? "nodes").getArr?
  let mut st : State := {}
  for (node, raw) in doc.nodes.zip rawNodes.toList do
    if node.op == "core.input" then
      let p ← raw.getObjVal? "params"
      let name ← strField p "name"
      let length ← (← inputSizes.getObjVal? name).getNat?
      let kind ← match node.outputs with
        | [out] => pure out.dataType.kind
        | _ => fail "malformed input node signature"
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
    else if node.op == "u32.scan.sum" then
      let (source,shape) ← sourceShape st doc node.id "x"
      st ← emitScan 8 st source shape.words node.id
    else if node.op == "u64.tuple.lower" || node.op == "u64.tuple.upper" ||
        node.op == "u32.segment.expand" then
      let (srcA,shA) ← sourceShape st doc node.id "a"
      let (srcB,shB) ← sourceShape st doc node.id "b"
      let value ← paramValue raw
      let mut words := 0
      let mut code := 15
      if node.op == "u32.segment.expand" then
        if shA.words != shB.words then fail "segment inputs differ in length"
        if value > maxWords / 2 then fail "segment output capacity exceeded"
        words := 2 * value
      else
        if value == 0 || value > 16 then fail "tuple arity must be in 1..16"
        if shA.words % (2*value) != 0 || shB.words % (2*value) != 0 then
          fail "incomplete UInt64 tuple row"
        words := shA.words / (2*value)
        code := if node.op == "u64.tuple.lower" then 10 else 11
      st := record st node.id ⟨.buffer,words⟩
        (kernelStep node.id srcA srcB code words value shA.words shB.words)
    else if node.op == "u32.zip.sub" then
      let (srcA,shA) ← sourceShape st doc node.id "a"
      let (srcB,shB) ← sourceShape st doc node.id "b"
      if shA.words != shB.words then fail "unequal subtraction input lengths"
      st := record st node.id ⟨.buffer,shA.words⟩
        (kernelStep node.id srcA srcB 12 shA.words 0 shA.words shB.words)
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
      let shapeA ← shapeOf st a
      let shapeB ← shapeOf st b
      st := record st node.id ⟨outKind, words⟩
        (kernelStep node.id a b tag.code.toNat words constant
          shapeA.words shapeB.words)
  if inputSizes.compress != (obj st.inputs).compress then
    fail "GPU input shapes must bind every and only declared input"
  pure (obj [
    ("version",txt "pvgraph-gpu/0.2"),
    ("shader",txt shader),
    ("shaders",obj [("word",txt shader),("scan",txt scanShader),
      ("mapZip",txt MapZipShader.source)]),
    ("requiresInputValidation",toJson (doc.nodes.any
      (fun n => n.op == "u32.segment.expand"))),
    ("steps",toJson st.steps.reverse),
    ("outputs",toJson st.outputs.reverse)])

/-- The shipping compiler validates the candidate's actual JSON against the
    admitted source graph before exposing it to the host. The map/zip certificate
    is structural; source semantics are proved separately in MapZipRefinement. -/
def compile? (rawGraph inputSizes : Json) : Except String Json := do
  let candidate ← compileCandidate? rawGraph inputSizes
  let _ ← MapZipPlan.validate? rawGraph inputSizes candidate
  return candidate

/-- Kind: shipping producer boundary.
Says: every successful public GPU plan has structural evidence tied to its
actual decoded graph, original JSON fields and selected map/zip shader bytes.
Does not say: a host, GPU compiler or device respected that plan. -/
theorem compile_checked {rawGraph inputSizes plan : Json}
    (compiled : compile? rawGraph inputSizes = .ok plan) :
    Nonempty (MapZipPlan.Checked rawGraph inputSizes plan) := by
  unfold compile? at compiled
  cases hc : compileCandidate? rawGraph inputSizes with
  | error e => simp [hc,Bind.bind,Except.bind] at compiled
  | ok candidate =>
    cases hv : MapZipPlan.validate? rawGraph inputSizes candidate with
    | error e => simp [hc,hv,Bind.bind,Except.bind] at compiled
    | ok checked =>
      simp [hc,hv,Bind.bind,Except.bind,Pure.pure,Except.pure] at compiled
      subst plan
      exact ⟨checked⟩

#print axioms compile_checked

#guard (shader.splitOn "@compute").length == 2

end L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
