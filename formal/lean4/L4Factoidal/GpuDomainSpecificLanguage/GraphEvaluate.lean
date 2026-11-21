import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GraphJson
import L4Factoidal.GpuDomainSpecificLanguage.GraphWords

/-!
# GDSL 0.2: execute the actual canonical JSON dataflow graph in Lean

Unlike a standalone primitive fixture, `evaluate?` decodes and checks
the *real JSON graph document* and runs its op nodes in topological order.
It looks up each typed input port's incoming link, preserves scalar/buffer
distinctions and emits named results. This is a separate Lean reference
interpreter, not the JavaScript CPU implementation.

An external differential harness compares it with the JavaScript
`runCPU` interpreter. That test evidence does not prove the two parsers
or interpreters equivalent on all inputs. The WebGPU compiler and driver
remain outside this module's claim.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.GraphEvaluate

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.Graph
open L4Factoidal.GpuDomainSpecificLanguage.GraphJson
open L4Factoidal.GpuDomainSpecificLanguage.GraphWords

private def refuse {α : Type} (s : String) : Except String α :=
  .error ("GDSL Lean eval: " ++ s)

private def natU32 (j : Json) : Except String UInt32 := do
  let value ← j.getNat?
  if value > 4294967295 then
    refuse "u32 value exceeds the supported word range"
  else pure (UInt32.ofNat value)

private def inputValue (j : Json) (t : LinkType) : Except String Value := do
  if t.kind == .scalar && t.atom == "u32" then
    return .scalar (← natU32 j)
  else if t.kind == .buffer && t.atom == "u32" then
    let arr ← j.getArr?
    if arr.size > 4096 then refuse "Input buffer exceeds 4096 u32 words"
    else
      let vals ← arr.toList.mapM natU32
      return .buffer vals
  else refuse "Unsupported GDSL input atom or link kind"

private def valueJson : Value → Json
  | .scalar n => toJson n.toNat
  | .buffer xs => toJson (xs.map fun x => x.toNat)

private def portArgs (d : Document) (done : List (String × Value))
    (node : Node) : Except String (List Value) :=
  node.inputs.mapM fun port => do
    let some edge := d.links.find? (fun l =>
      l.target.node == node.id && l.target.port == port.name) |
      refuse ("Missing input edge at " ++ node.id ++ "." ++ port.name)
    let some entry := done.find? (fun e => e.1 == edge.source.node) |
      refuse ("Missing source value " ++ edge.source.node)
    return entry.2

private def constant? (n : Node) (raw : Json) : Except String (Option UInt32) := do
  if n.op == "u32.map.add" || n.op == "u32.map.mul" ||
     n.op == "u32.map.xor" || n.op == "u32.scalar.const" then
    let params ← raw.getObjVal? "params"
    return some (← natU32 (← params.getObjVal? "value"))
  else pure none

/-- Deterministic evaluation of the common accepted acyclic node/link graph,
    using the separately defined UInt32 primitive semantics. -/
def evaluate? (rawGraph rawBindings : Json) : Except String Json := do
  let certified ← GraphJson.decodeCertified? rawGraph
  let d := certified.graph
  let rawNodes ← (← rawGraph.getObjVal? "nodes").getArr?
  let mut inputs : List String := []
  for raw in rawNodes do
    let op ← (← raw.getObjVal? "op").getStr?
    if op == "core.input" then
      let params ← raw.getObjVal? "params"
      let name ← (← params.getObjVal? "name").getStr?
      inputs := name :: inputs
  let expected ← inputs.mapM fun name => do
    let v ← rawBindings.getObjVal? name
    return (name,v)
  if rawBindings.compress != (Json.mkObj expected).compress then
    refuse "Missing or additional named input binding"
  let mut values : List (String × Value) := []
  let mut outputs : List (String × Json) := []
  for (n,raw) in d.nodes.zip rawNodes.toList do
    let result ←
      if n.op == "core.input" then do
        let params ← raw.getObjVal? "params"
        let name ← (← params.getObjVal? "name").getStr?
        let source ← rawBindings.getObjVal? name
        match n.outputs with
        | [out] => inputValue source out.dataType
        | _ => refuse "Malformed common input signature"
      else if n.op == "core.output" then do
        match ← portArgs d values n with
        | [value] => pure value
        | _ => refuse "Malformed common output port"
      else do
        let some op := Operator.fromName? n.op |
          refuse ("Unregistered core primitive " ++ n.op)
        let args ← portArgs d values n
        let param ← constant? n raw
        GraphWords.execute op args param
    values := (n.id,result) :: values
    if n.op == "core.output" then
      let params ← raw.getObjVal? "params"
      let name ← (← params.getObjVal? "name").getStr?
      outputs := (name,valueJson result) :: outputs
  return Json.mkObj outputs

end L4Factoidal.GpuDomainSpecificLanguage.GraphEvaluate
