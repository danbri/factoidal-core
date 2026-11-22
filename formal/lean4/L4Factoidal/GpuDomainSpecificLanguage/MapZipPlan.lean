import L4Factoidal.GpuDomainSpecificLanguage.GraphJson
import L4Factoidal.GpuDomainSpecificLanguage.MapZipKind
import L4Factoidal.GpuDomainSpecificLanguage.MapZipShader

/-!
# Translation validation of actual PVGraph GPU plans

This module checks the candidate emitted by `GpuPlan`. It does not compute
output values. Checks bind each of the five covered source operators to the
actual step's source/destination names, coefficient, shader, config words,
allocation lengths and dispatch. Input and graph-output descriptions are also
checked against their original nodes. Other kernel semantics remain separate.
The shipping compiler calls this validator before returning its JSON.

Issue: https://github.com/danbri/factoidal-core/issues/802.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipPlan

open Lean Graph GraphJson MapZipKind

-- Keep equality decisions local: the Json readers return Except, whose core
-- type has no generic DecidableEq instance in the pinned toolchain.
private def exceptEq {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error _, .ok _ => isFalse (fun h => by cases h)
  | .ok _, .error _ => isFalse (fun h => by cases h)

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) :=
  exceptEq

def string? (j : Json) (key : String) : Except String String := do
  (← j.getObjVal? key).getStr?

def natural? (j : Json) (key : String) : Except String Nat := do
  (← j.getObjVal? key).getNat?

def array? (j : Json) (key : String) : Except String (Array Json) := do
  (← j.getObjVal? key).getArr?

def sourcePort? (doc : Document) (node port : String) : Option Port :=
  (doc.links.find? (fun e => e.target.node == node && e.target.port == port)).map
    (fun e => e.source)

def source? (doc : Document) (node port : String) : Option String :=
  (sourcePort? doc node port).map Port.node

def coefficient? (kind : Kind) (raw : Json) : Except String Nat := do
  if kind.isZip then return 0
  else natural? (← raw.getObjVal? "params") "value"

def groups (words : Nat) : Nat := max 1 ((words + 63) / 64)

/-- The fields consumed by the existing GPU host for one kernel dispatch. -/
structure Step where
  kind : String
  node : String
  shader : String
  code : Nat
  a : String
  b : String
  constant : Nat
  words : Nat
  config : List Nat
  workgroups : Nat
  deriving DecidableEq, Repr

/-- Read each consumed field with its actual JSON type. No JSON equality or
    hash is used to infer these field values. -/
def readStep? (j : Json) : Except String Step := do
  let kind ← string? j "kind"
  let node ← string? j "node"
  let shader ← string? j "shader"
  let code ← natural? j "code"
  let a ← string? j "a"
  let b ← string? j "b"
  let constant ← natural? j "constant"
  let words ← natural? j "words"
  let config ← (← array? j "config").toList.mapM Json.getNat?
  let workgroups ← natural? j "workgroups"
  return ⟨kind,node,shader,code,a,b,constant,words,config,workgroups⟩

def findStep? (steps : List Json) (node : String) : Option Nat :=
  ((steps.zipIdx).find? (fun p => string? p.1 "node" == .ok node)).map Prod.snd

/-- The declared length of the latest preceding allocation with this name. -/
def precedingWords? (steps : List Json) (node : String) : Option Nat :=
  steps.reverse.findSome? fun step =>
    if string? step "node" == .ok node then (natural? step "words").toOption else none

def bufferType : LinkType := ⟨.buffer,"u32"⟩

/-- Structural obligations only: none of these hypotheses states a result
    equality, a shader execution result, or a GraphWords answer. -/
def StepMatches (doc : Document) (node : Node) (raw : Json) (kind : Kind)
    (preceding : List Json) (step : Step) : Prop :=
  string? raw "id" = .ok node.id ∧ string? raw "op" = .ok node.op ∧
  step.kind = "kernel" ∧ step.node = node.id ∧ step.shader = "mapZip" ∧
  step.code = kind.code ∧
  node.inputs = kind.ports.map (fun p => (⟨p,bufferType⟩ : PortSig)) ∧
  node.outputs = [⟨"out",bufferType⟩] ∧
  sourcePort? doc node.id (if kind.isZip then "a" else "x") = some ⟨step.a,"out"⟩ ∧
  (if kind.isZip then sourcePort? doc node.id "b" = some ⟨step.b,"out"⟩ else step.b = step.a) ∧
  coefficient? kind raw = .ok step.constant ∧ step.constant < UInt32.size ∧
  step.words ≤ 4194240 ∧
  precedingWords? preceding step.a = some step.words ∧
  precedingWords? preceding step.b = some step.words ∧
  (preceding.all (fun old => string? old "node" != .ok step.node)) = true ∧
  step.config = [kind.code,step.words,step.constant,step.words,step.words] ∧
  step.workgroups = groups step.words ∧ step.workgroups ≤ 65535

instance (doc : Document) (node : Node) (raw : Json) (kind : Kind)
    (preceding : List Json) (step : Step) : Decidable (StepMatches doc node raw kind preceding step) := by
  unfold StepMatches
  infer_instance

def checkNode (doc : Document) (node : Node) (raw : Json) (kind : Kind)
    (steps : List Json) : Bool :=
  match findStep? steps node.id with
  | none => false
  | some index =>
    match steps[index]? with
    | none => false
    | some candidate =>
      match readStep? candidate with
      | .error _ => false
      | .ok step => decide (StepMatches doc node raw kind (steps.take index) step)

def inputMatches (node : Node) (raw inputSizes : Json) (steps : List Json) : Bool := Id.run do
  let some index := findStep? steps node.id | return false
  let some step := steps[index]? | return false
  let .ok params := raw.getObjVal? "params" | return false
  let .ok name := string? params "name" | return false
  let .ok words := natural? inputSizes name | return false
  return string? step "kind" == .ok "input" && string? step "name" == .ok name &&
    natural? step "words" == .ok words

def outputMatches (doc : Document) (node : Node) (raw : Json)
    (steps outputs : List Json) : Bool := Id.run do
  let .ok params := raw.getObjVal? "params" | return false
  let .ok name := string? params "name" | return false
  let some source := source? doc node.id "in" | return false
  let some words := precedingWords? steps source | return false
  let some output := outputs.find? (fun j => string? j "name" == .ok name) | return false
  let [port] := node.inputs | return false
  let kind := if port.dataType.kind == .scalar then "scalar" else "buffer"
  return string? output "source" == .ok source && natural? output "words" == .ok words &&
    string? output "kind" == .ok kind && sourcePort? doc node.id "in" == some ⟨source,"out"⟩

def marked (step : Json) : Bool :=
  string? step "shader" == .ok "mapZip" ||
    match natural? step "code" with
    | .ok code => 1 ≤ code && code ≤ 5
    | .error _ => false

/-- Every source map/zip must have a matching step, including unused outputs.
    Every marked target step must originate at such a source node. Unique step
    identifiers prevent a duplicate later allocation from changing that match. -/
def structural (doc : Document) (pairs : List (Node × Json)) (inputSizes : Json)
    (steps outputs : List Json) : Bool :=
  let sourceChecks := pairs.all fun (node,raw) =>
    match MapZipKind.ofName? node.op with
    | some kind => checkNode doc node raw kind steps
    | none => if node.op == "core.input" then inputMatches node raw inputSizes steps
      else if node.op == "core.output" then outputMatches doc node raw steps outputs
      else true
  let targetChecks := steps.all fun step =>
    !marked step || pairs.any (fun (node,_) =>
      string? step "node" == .ok node.id && (MapZipKind.ofName? node.op).isSome)
  let names := (steps.mapM (fun step => string? step "node")).toOption
  let outputNames := (outputs.mapM (fun output => string? output "name")).toOption
  sourceChecks && targetChecks &&
    (match names with | none => false | some ns => decide ns.Nodup) &&
    (match outputNames with | none => false | some ns => decide ns.Nodup) &&
    outputs.length == (pairs.filter (fun p => p.1.op == "core.output")).length

def shader? (plan : Json) : Except String String := do
  string? (← plan.getObjVal? "shaders") "mapZip"

/-- Evidence about the exact raw graph and candidate JSON. The proof fields are
    erased; the public compiler returns the original validated candidate. -/
structure Checked (rawGraph inputSizes plan : Json) where
  graph : AdmittedGraph
  decoded : GraphJson.decodeCertified? rawGraph = .ok graph
  rawNodes : Array Json
  nodesRead : array? rawGraph "nodes" = .ok rawNodes
  nodesLength : graph.graph.nodes.length = rawNodes.size
  steps : Array Json
  stepsRead : array? plan "steps" = .ok steps
  outputs : Array Json
  outputsRead : array? plan "outputs" = .ok outputs
  sourceRead : shader? plan = .ok MapZipShader.source
  valid : structural graph.graph (graph.graph.nodes.zip rawNodes.toList)
    inputSizes steps.toList outputs.toList = true

/-- Validate the real compiler result, refusing any failed structural obligation.
    This performs no reference evaluation and assumes no answer equality. -/
def validate? (rawGraph inputSizes plan : Json) : Except String (Checked rawGraph inputSizes plan) := do
  let graph : {g : AdmittedGraph // GraphJson.decodeCertified? rawGraph = .ok g} ←
    match h : GraphJson.decodeCertified? rawGraph with
    | .error e => .error e
    | .ok graph => pure ⟨graph,h⟩
  let rawNodes : {ns : Array Json // array? rawGraph "nodes" = .ok ns} ←
    match h : array? rawGraph "nodes" with
    | .error e => .error e
    | .ok nodes => pure ⟨nodes,h⟩
  let steps : {ss : Array Json // array? plan "steps" = .ok ss} ←
    match h : array? plan "steps" with
    | .error e => .error e
    | .ok steps => pure ⟨steps,h⟩
  let outputs : {os : Array Json // array? plan "outputs" = .ok os} ←
    match h : array? plan "outputs" with
    | .error e => .error e
    | .ok outputs => pure ⟨outputs,h⟩
  if nodesLength : graph.1.graph.nodes.length = rawNodes.1.size then
   if sourceRead : shader? plan = .ok MapZipShader.source then
    if valid : structural graph.1.graph (graph.1.graph.nodes.zip rawNodes.1.toList)
        inputSizes steps.1.toList outputs.1.toList = true then
      return ⟨graph.1,graph.2,rawNodes.1,rawNodes.2,nodesLength,steps.1,steps.2,
        outputs.1,outputs.2,sourceRead,valid⟩
    else .error "PVGraph GPU: map/zip plan structure differs from admitted graph"
   else .error "PVGraph GPU: map/zip shader source differs from checked source"
  else .error "PVGraph GPU: decoded/source node counts differ"

/-- Kind: translation-validation soundness.
Says: a checked source node has an actual indexed plan step, read with the host's
field types, satisfying the structural source/port/config/shape/dispatch relation.
Does not say: a platform uploaded those buffers or executed the shader. -/
theorem checkNode_sound (doc : Document) (node : Node) (raw : Json) (kind : Kind)
    (steps : List Json) (checked : checkNode doc node raw kind steps = true) :
    ∃ index candidate step,
      steps[index]? = some candidate ∧ readStep? candidate = .ok step ∧
      StepMatches doc node raw kind (steps.take index) step := by
  unfold checkNode at checked
  cases hi : findStep? steps node.id with
  | none => simp [hi] at checked
  | some index =>
    cases hj : steps[index]? with
    | none => simp [hi,hj] at checked
    | some candidate =>
      cases hs : readStep? candidate with
      | error e => simp [hi,hj,hs] at checked
      | ok step =>
        refine ⟨index,candidate,step,hj,hs,?_⟩
        simpa [hi,hj,hs] using checked

/-- Kind: actual admitted-graph coverage.
Says: every covered node of the exact successfully decoded document has a checked
step in the original candidate plan, even if no graph output uses that node.
Does not say: other operators or the complete host execution are refined. -/
theorem Checked.node_step {rawGraph inputSizes plan : Json}
    (checked : Checked rawGraph inputSizes plan) (node : Node) (raw : Json) (kind : Kind)
    (member : (node,raw) ∈ checked.graph.graph.nodes.zip checked.rawNodes.toList)
    (selected : MapZipKind.ofName? node.op = some kind) :
    ∃ index candidate step,
      checked.steps.toList[index]? = some candidate ∧ readStep? candidate = .ok step ∧
      StepMatches checked.graph.graph node raw kind (checked.steps.toList.take index) step := by
  have all := checked.valid
  simp only [structural, Bool.and_eq_true] at all
  have sourceChecks := all.1.1.1.1
  have row := List.all_eq_true.mp sourceChecks (node,raw) member
  simp only [selected] at row
  exact checkNode_sound _ _ _ _ _ row

#print axioms checkNode_sound
#print axioms Checked.node_step

end L4Factoidal.GpuDomainSpecificLanguage.MapZipPlan
