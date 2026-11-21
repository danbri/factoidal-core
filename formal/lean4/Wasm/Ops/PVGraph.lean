import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder

/-!
# PVGraph's Lean-owned Wasm-facing API

The JS/S-expression hosts may describe a sequence of calls but neither
construct the canonical document nor implement its operator semantics.
The only authoring path below invokes the same Lean PVGraph.Builder as native
Lean source; the resulting `gdsl/0.2` document goes through the same
proof-bearing Lean admission gate. No host-supplied certificate is accepted.

This is a pure JSON-string transport for the existing l4_call Wasm ABI,
not a claim that the Lean compiler, ABI glue or GPU backend is verified.
-/

namespace L4Wasm.Ops.PVGraphBridge

open Lean
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

inductive Source where
  | buffer : Wire .buffer → Source
  | scalar : Wire .scalar → Source

structure BuildState where
  inner : L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder.State := {}
  refs : List (String × Source) := []

private def fail {α : Type} (message : String) : Except String α :=
  .error ("PVGraph: " ++ message)

private def exactFields (j : Json) (keys : List String) : Except String Unit := do
  let fields ← keys.mapM fun k => do
    let v ← j.getObjVal? k
    pure (k, v)
  if j.compress != (Json.mkObj fields).compress then
    fail "unexpected or missing command fields"
  else pure ()

private def str (j : Json) (k : String) : Except String String := do
  (← j.getObjVal? k).getStr?

private def optionalId (j : Json) : Except String (Option String) := do
  match ← j.getObjVal? "id" with
  | .null => pure none
  | .str id => pure (some id)
  | _ => fail "id must be a string or null"

private def addRef (st : BuildState) (tag : String) (w : Source)
    (next : L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder.State) :
    Except String BuildState := do
  if tag.isEmpty || st.refs.any (fun r => r.1 == tag) then
    fail ("missing or duplicate wire reference " ++ tag)
  pure { inner := next, refs := (tag, w) :: st.refs }

private def getRef (st : BuildState) (tag : String) : Except String Source := do
  match st.refs.find? (fun r => r.1 == tag) with
  | some (_, source) => pure source
  | none => fail ("unbound, cyclic or forward wire reference " ++ tag)

private def argumentFor (st : BuildState) (j : Json) :
    Except String Argument := do
  exactFields j ["port", "source"]
  let port ← str j "port"
  let tag ← str j "source"
  match ← getRef st tag with
  | Source.buffer wire => pure (argument port wire)
  | Source.scalar wire => pure (argument port wire)

private def applyStep (st : BuildState) (j : Json) : Except String BuildState := do
  match ← str j "cmd" with
  | "input" =>
      exactFields j ["cmd", "ref", "name", "type", "id"]
      let tag ← str j "ref"
      let name ← str j "name"
      let id ← optionalId j
      match ← str j "type" with
      | "buffer<u32>" =>
          let (wire, next) := (input name .buffer id).run st.inner
          addRef st tag (Source.buffer wire) next
      | "scalar<u32>" =>
          let (wire, next) := (input name .scalar id).run st.inner
          addRef st tag (Source.scalar wire) next
      | _ => fail "input type must be buffer<u32> or scalar<u32>"
  | "op" =>
      exactFields j ["cmd", "ref", "op", "resultType", "args", "params", "id"]
      let tag ← str j "ref"
      let opcode ← str j "op"
      let kind ← str j "resultType"
      let id ← optionalId j
      let params ← j.getObjVal? "params"
      let args ← (← j.getObjVal? "args").getArr?
      let args ← args.toList.mapM (argumentFor st)
      match kind with
      | "buffer<u32>" =>
          let (wire, next) := (op opcode .buffer args params id).run st.inner
          addRef st tag (Source.buffer wire) next
      | "scalar<u32>" =>
          let (wire, next) := (op opcode .scalar args params id).run st.inner
          addRef st tag (Source.scalar wire) next
      | _ => fail "operator result type must be buffer<u32> or scalar<u32>"
  | "output" =>
      exactFields j ["cmd", "name", "source", "id"]
      let name ← str j "name"
      let tag ← str j "source"
      let id ← optionalId j
      match ← getRef st tag with
      | Source.buffer wire =>
          let (_, next) := (output name wire id).run st.inner
          pure { st with inner := next }
      | Source.scalar wire =>
          let (_, next) := (output name wire id).run st.inner
          pure { st with inner := next }
  | other => fail ("unknown builder command " ++ other)

/-- Build the actual GDSL 0.2 PVGraph document, with no JS semantic code. -/
def fromSteps? (source : Json) : Except String Json := do
  exactFields source ["steps"]
  let steps ← (← source.getObjVal? "steps").getArr?
  if steps.size > 128 then fail "at most 128 builder steps"
  let st ← steps.toList.foldlM applyStep ({} : BuildState)
  let doc := st.inner.document
  let _ ← PVGraph.admit? doc
  pure doc

private def envelope (name : String) (result : Except String Json) : String :=
  match result with
  | .ok value => (Json.mkObj [("ok", toJson true), (name, value)]).compress
  | .error msg => (Json.mkObj [("ok", toJson false), ("error", toJson msg)]).compress

private def parseBounded (s : String) : Except String Json := do
  if s.utf8ByteSize > 1048576 then fail "request exceeds 1 MiB"
  Json.parse s

/-- Lean builds and admits a program from host-supplied builder calls. -/
def build (stepsJson : String) : String :=
  envelope "pvgraph" do
    let steps ← parseBounded stepsJson
    fromSteps? steps

/-- Admission over external JSON is checked inside Lean, not by JS. -/
def admit (pvgraphJson : String) : String :=
  envelope "pvgraph" do
    let doc ← parseBounded pvgraphJson
    let _ ← PVGraph.admit? doc
    pure doc

/-- This reference evaluator uses the same Lean semantics as native authoring. -/
def evaluate (pvgraphJson bindingsJson : String) : String :=
  envelope "outputs" do
    let doc ← parseBounded pvgraphJson
    let inputs ← parseBounded bindingsJson
    PVGraph.evaluate? doc inputs

private def exampleSteps : Json := Json.mkObj [("steps", toJson ([
  Json.mkObj [("cmd", toJson "input"), ("ref", toJson "r1"),
    ("name", toJson "samples"), ("type", toJson "buffer<u32>"), ("id", Json.null)],
  Json.mkObj [("cmd", toJson "op"), ("ref", toJson "r2"), ("op", toJson "u32.map.mul"),
    ("resultType", toJson "buffer<u32>"),
    ("args", toJson ([Json.mkObj [("port", toJson "x"), ("source", toJson "r1")]] : List Json)),
    ("params", Json.mkObj [("value", toJson (3 : Nat))]), ("id", Json.null)],
  Json.mkObj [("cmd", toJson "output"), ("name", toJson "answer"),
    ("source", toJson "r2"), ("id", Json.null)]
] : List Json))]

#guard (match fromSteps? exampleSteps with | .ok _ => true | .error _ => false)
#guard (match fromSteps? (Json.mkObj [("steps", toJson ([
  Json.mkObj [("cmd", toJson "output"), ("name", toJson "answer"),
    ("source", toJson "missing"), ("id", Json.null)]
] : List Json))]) with | .ok _ => false | .error _ => true)

end L4Wasm.Ops.PVGraphBridge

namespace L4Wasm.Ops

def pvgraphBuild (steps : String) : String := PVGraphBridge.build steps
def pvgraphAdmit (source : String) : String := PVGraphBridge.admit source
def pvgraphEvaluate (source inputs : String) : String := PVGraphBridge.evaluate source inputs

end L4Wasm.Ops
