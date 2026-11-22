import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GraphAdmission
import L4Factoidal.GpuDomainSpecificLanguage.GraphWords

/-!
# GDSL 0.2: canonical PVGraph admission

`decode?` accepts only the exact versioned {version,nodes,links}
document. Lean reconstructs operator and port signatures from its
registry; client-provided signatures are never trusted. Unknown fields,
operators, invalid IDs, ill-typed links and malformed parameters are
refused. `decodeCertified?` checks the same document and returns
admission evidence for the actual serialized computation.

Domain extension operators require independently checked signatures;
this module currently admits the core u32 profile.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.GraphJson

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.Graph
open L4Factoidal.GpuDomainSpecificLanguage.GraphAdmission

private def fail {α : Type} (msg : String) : Except String α :=
  .error ("GDSL JSON: " ++ msg)

/-- Compare the entire object with precisely the named keys; do not
    silently ignore unexpected fields or typoed settings. -/
private def exactFields (j : Json) (keys : List String) : Except String Unit := do
  let entries ← keys.mapM fun key => do
    let value ← j.getObjVal? key
    return (key, value)
  if j.compress != (Json.mkObj entries).compress then
    fail "Unexpected, missing or duplicate object fields"
  else pure ()

private def fieldStr (j : Json) (name : String) : Except String String := do
  let v ← j.getObjVal? name
  v.getStr?

private def fieldNat (j : Json) (name : String) : Except String Nat :=
  j.getObjValAs? Nat name

private def fieldArr (j : Json) (name : String) : Except String (Array Json) := do
  let v ← j.getObjVal? name
  v.getArr?

private def idValid (s : String) : Bool :=
  let letters := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList
  let trailing := letters ++ "0123456789_.-".toList
  if s.length == 0 || s.length > 64 then false else
    match s.toList with
    | [] => false
    | c :: rest => letters.contains c && rest.all (fun x => trailing.contains x)

private def checkedId (s : String) : Except String String :=
  if idValid s then pure s else fail ("Invalid identifier: " ++ s)

private def dtype (t : String) : Except String LinkType :=
  match t with
  | "buffer<u32>" => pure ⟨.buffer, "u32"⟩
  | "scalar<u32>" => pure ⟨.scalar, "u32"⟩
  | _ => fail ("Unsupported type " ++ t)

private def linkType (kind atom : String) : Except String LinkType :=
  if kind == "buffer" && atom == "u32" then pure ⟨.buffer, "u32"⟩
  else if kind == "scalar" && atom == "u32" then pure ⟨.scalar, "u32"⟩
  else fail "Unsupported scalar/buffer link type"

private def portSig (name : String) (t : LinkType) : PortSig :=
  ⟨name, t⟩

private def b : LinkType := ⟨.buffer, "u32"⟩
private def s : LinkType := ⟨.scalar, "u32"⟩

private def parsePort (j : Json) : Except String Port := do
  exactFields j ["node", "port"]
  let node ← checkedId (← fieldStr j "node")
  let port ← checkedId (← fieldStr j "port")
  return ⟨node,port⟩

private def parseLink (j : Json) : Except String Link := do
  exactFields j ["from", "to", "kind", "type"]
  let source ← parsePort (← j.getObjVal? "from")
  let target ← parsePort (← j.getObjVal? "to")
  let dataType ← linkType (← fieldStr j "kind") (← fieldStr j "type")
  return ⟨source,target,dataType⟩

private def checkedU32Param (j : Json) : Except String Unit := do
  exactFields j ["value"]
  let n ← fieldNat j "value"
  if n > 4294967295 then fail "u32 parameter overflow" else pure ()

/-- Reconstruct exact common operator signatures. The serialized node is
    not permitted to supply its own input or output signature. -/
private def parseNode (j : Json) : Except String Node := do
  exactFields j ["id", "op", "params"]
  let id ← checkedId (← fieldStr j "id")
  let op ← fieldStr j "op"
  let params ← j.getObjVal? "params"
  let (inputs, outputs) ←
    if op == "core.input" then do
      exactFields params ["name", "type"]
      let _ ← checkedId (← fieldStr params "name")
      let t ← dtype (← fieldStr params "type")
      pure ([],[portSig "out" t])
    else if op == "core.output" then do
      exactFields params ["name", "type"]
      let _ ← checkedId (← fieldStr params "name")
      let t ← dtype (← fieldStr params "type")
      pure ([portSig "in" t],[portSig "out" t])
    else if op == "u32.map.add" || op == "u32.map.mul" ||
            op == "u32.map.xor" then do
      checkedU32Param params
      pure ([portSig "x" b],[portSig "out" b])
    else if op == "u32.scalar.const" then do
      checkedU32Param params
      pure ([],[portSig "out" s])
    else if op == "u32.scan.sum" then do
      exactFields params []
      pure ([portSig "x" b],[portSig "out" b])
    else if op == "u32.reduce.sum" then do
      exactFields params []
      pure ([portSig "x" b],[portSig "out" s])
    else if op == "u32.zip.add" || op == "u32.zip.xor" then do
      exactFields params []
      pure ([portSig "a" b,portSig "b" b],[portSig "out" b])
    else if op == "u32.scalar.add" then do
      exactFields params []
      pure ([portSig "a" s,portSig "b" s],[portSig "out" s])
    else if op == "u32.broadcast" then do
      exactFields params []
      pure ([portSig "value" s,portSig "shape" b],[portSig "out" b])
    else fail ("Unregistered core opcode: " ++ op)
  let node : Node := {id,op,inputs,outputs}
  if coreSignature node then pure node
  else fail ("Invalid operator signature " ++ op)

/-- Core-only, fully bounded and exact-keys JSON admission to the
    universal Lean typed-graph representation. -/
def decode? (j : Json) : Except String Document := do
  exactFields j ["version", "nodes", "links"]
  if (← fieldStr j "version") != "gdsl/0.2" then
    fail "Unsupported GDSL version"
  let jsonNodes ← fieldArr j "nodes"
  let jsonLinks ← fieldArr j "links"
  if jsonNodes.size < 2 || jsonNodes.size > 128 ||
     jsonLinks.size > 384 then
    fail "Node or link budget exceeded"
  let nodes ← jsonNodes.toList.mapM parseNode
  let links ← jsonLinks.toList.mapM parseLink
  -- These logical *endpoint names* are distinct from node identifiers.
  let mut inputs : List String := []
  let mut outputs : List String := []
  for node in jsonNodes do
    let op ← fieldStr node "op"
    if op == "core.input" || op == "core.output" then
      let params ← node.getObjVal? "params"
      let name ← fieldStr params "name"
      if op == "core.input" then
        if inputs.contains name then fail "Duplicate graph input binding name"
        inputs := name :: inputs
      else
        if outputs.contains name then fail "Duplicate graph output binding name"
        outputs := name :: outputs
  let d : Document := ⟨nodes,links⟩
  if Document.admitted d then pure d
  else fail "Common typed graph admission failed"

/-- The accepted document comes with the *actual proposition* that
    whole-graph admission succeeded. This is not a theorem about any JS
    parser, only an explicit Lean proof object returned with the graph. -/
structure AdmittedGraph where
  graph : Document
  admitted : Document.admitted graph = true

/-- An executable parser whose success result carries the admission proof.
    No proof field can be fabricated by untrusted serialized input. -/
def decodeCertified? (j : Json) : Except String AdmittedGraph := do
  let d ← decode? j
  if h : Document.admitted d = true then
    return ⟨d,h⟩
  else
    fail "Graph admission certificate not available"

/-- The certificate is a checked proposition about every returned graph. -/
theorem certified_sound (c : AdmittedGraph) :
    Document.admitted c.graph = true := c.admitted

#print axioms certified_sound

/-!
The certificate does not yet prove JS `fromSexpr/checkGraph` correctness,
nor a WebGPU backend's refinement. Cross-language differential evidence
is necessary but remains finite.
-/

end L4Factoidal.GpuDomainSpecificLanguage.GraphJson
