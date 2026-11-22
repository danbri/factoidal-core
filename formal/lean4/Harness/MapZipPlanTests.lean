import L4Factoidal.GpuDomainSpecificLanguage.MapZipCompileRefinement
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder

/-!
Executable controls for issue #802. Every refusal starts with an accepted
candidate from the shipping compiler and changes the real JSON/source bytes.
The array expectations below are independent fixed wrapping-u32 examples.
These are tests, not additional theorems or a substitute for device execution.
-/

open Lean
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.MapZipKind
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

private def kinds : List Kind := [.mapAdd,.mapMul,.mapXor,.zipAdd,.zipXor]

private def label : Kind → String
  | .mapAdd => "map.add" | .mapMul => "map.mul" | .mapXor => "map.xor"
  | .zipAdd => "zip.add" | .zipXor => "zip.xor"

private def constant : Kind → UInt32
  | .mapAdd => 4294967295 | .mapMul => 65537 | .mapXor => 2147483649 | _ => 0

private def program (kind : Kind) : M Unit := do
  let a ← input "left" .buffer (some "input-left")
  let b ← input "right" .buffer (some "input-right")
  let out ← match kind with
    | .mapAdd => mapAdd a (constant kind) (some "operation")
    | .mapMul => mapMul a (constant kind) (some "operation")
    | .mapXor => mapXor a (constant kind) (some "operation")
    | .zipAdd => zipAdd a b (some "operation")
    | .zipXor => zipXor a b (some "operation")
  output "answer" out (some "result")

private def sizes (left right : Nat) : Json :=
  Json.mkObj [("left",toJson left),("right",toJson right)]

private def field (j : Json) (name : String) (value : Json) : Json :=
  match j with
  | .obj fields => .obj (fields.insert name value)
  | _ => j

private def entries (j : Json) (name : String) : Array Json :=
  ((j.getObjValD name).getArr?).toOption.getD #[]

private def named (j : Json) (key name : String) : Bool :=
  (j.getObjValD key).getStr?.toOption == some name

private def changeNamed (j : Json) (arrayKey key name : String) (f : Json → Json) : Json :=
  field j arrayKey (.arr ((entries j arrayKey).map fun row => if named row key name then f row else row))

private def changeStep (plan : Json) (f : Json → Json) : Json :=
  changeNamed plan "steps" "node" "operation" f

private def step? (plan : Json) : Option Json :=
  (entries plan "steps").find? (fun row => named row "node" "operation")

private def changeShader (plan : Json) (before after : String) : Json :=
  field plan "shaders" (field (plan.getObjValD "shaders") "mapZip"
    (.str (MapZipShader.source.replace before after)))

private def config (kind : Kind) (code words coefficient aw bw : Nat) : Json :=
  let _ := kind
  toJson [code,words,coefficient,aw,bw]

private def mutations (kind : Kind) (plan : Json) : List (String × Json) :=
  let k := (constant kind).toNat
  let code := kind.code
  let sourceB := if kind.isZip then "input-left" else "input-right"
  let step := (step? plan).getD .null
  [
    ("source-arithmetic",changeShader plan "a[pv_gid.x] + config[2u]" "a[pv_gid.x] * config[2u]"),
    ("source-binding",changeShader plan "@binding(0)" "@binding(1)"),
    ("source-index",changeShader plan "a[pv_gid.x]" "a[0u]"),
    ("source-guard",changeShader plan "config[1u])" "config[2u])"),
    ("source-workgroup",changeShader plan "workgroup_size(64,1,1)" "workgroup_size(32,1,1)"),
    ("source-split-equality-token",changeShader plan " == " " = = "),
    ("source-trailing-bytes",field plan "shaders" (field (plan.getObjValD "shaders") "mapZip"
      (.str (MapZipShader.source ++ "\nignored")))),
    ("selected-shader",changeStep plan (fun s => field s "shader" (.str "word"))),
    ("step-kind",changeStep plan (fun s => field s "kind" (.str "input"))),
    ("step-opcode",changeStep plan (fun s => field s "code" (toJson (code+1)))),
    ("source-a",changeStep plan (fun s => field s "a" (.str "input-right"))),
    ("source-b",changeStep plan (fun s => field s "b" (.str sourceB))),
    ("coefficient-and-config",changeStep plan (fun s =>
      field (field s "constant" (toJson (k+1))) "config" (config kind code 65 (k+1) 65 65))),
    ("logical-output-length",changeStep plan (fun s => field s "words" (toJson (64 : Nat)))),
    ("config-opcode",changeStep plan (fun s => field s "config" (config kind (code+10) 65 k 65 65))),
    ("config-count",changeStep plan (fun s => field s "config" (config kind code 64 k 65 65))),
    ("config-coefficient",changeStep plan (fun s => field s "config" (config kind code 65 (k+1) 65 65))),
    ("config-a-length",changeStep plan (fun s => field s "config" (config kind code 65 k 64 65))),
    ("config-b-length",changeStep plan (fun s => field s "config" (config kind code 65 k 65 64))),
    ("config-short-packet",changeStep plan (fun s => field s "config" (toJson [code,65,k]))),
    ("dispatch-too-small",changeStep plan (fun s => field s "workgroups" (toJson (1 : Nat)))),
    ("dispatch-too-large",changeStep plan (fun s => field s "workgroups" (toJson (3 : Nat)))),
    ("destination-alias",changeStep plan (fun s => field s "node" (.str "input-left"))),
    ("missing-step",field plan "steps" (.arr ((entries plan "steps").filter fun s => !named s "node" "operation"))),
    ("duplicate-step",field plan "steps" (.arr ((entries plan "steps").push step))),
    ("extra-marked-step",field plan "steps" (.arr ((entries plan "steps").push (field step "node" (.str "extra"))))),
    ("input-allocation-length",changeNamed plan "steps" "node" "input-left"
      (fun s => field s "words" (toJson (64 : Nat)))),
    ("output-source",changeNamed plan "outputs" "name" "answer" (fun s => field s "source" (.str "input-left"))),
    ("output-length",changeNamed plan "outputs" "name" "answer" (fun s => field s "words" (toJson (64 : Nat)))),
    ("output-name",changeNamed plan "outputs" "name" "answer" (fun s => field s "name" (.str "other"))),
    ("output-kind",changeNamed plan "outputs" "name" "answer" (fun s => field s "kind" (.str "scalar")))
  ]

private def left : Array UInt32 := #[4294967295,2147483648,2147483647,0,1,4294967294]
private def right : Array UInt32 := #[1,2147483648,1,4294967295,2147483649,3]
private def sentinel : UInt32 := 3735928559

private def expected : Kind → List UInt32
  | .mapAdd => [4294967294,2147483647,2147483646,4294967295,0,4294967293]
  | .mapMul => [4294901759,2147483648,2147418111,0,65537,4294836222]
  | .mapXor => [2147483646,1,4294967294,2147483649,2147483648,2147483647]
  | .zipAdd => [0,0,2147483648,4294967295,2147483650,1]
  | .zipXor => [4294967294,0,2147483646,4294967295,2147483648,4294967293]

private def bound (a b : Array UInt32) : MapZipCompileRefinement.Buffers := fun name =>
  if name == "input-left" then some a
  else if name == "input-right" then some b else none

private def assertCase (name : String) (ok : Bool) : IO Unit := do
  IO.println (Json.mkObj [("case",toJson name),("pass",toJson ok)]).compress
  unless ok do throw (IO.userError ("map/zip control failed: " ++ name))

private def refused (raw inputSizes plan : Json) : Bool :=
  match MapZipPlan.validate? raw inputSizes plan with
  | .error message => message.startsWith "PVGraph GPU:"
  | .ok _ => false

def main : IO Unit := do
  let mut count := 0
  for kind in kinds do
    let raw := build (program kind)
    let .ok plan := GpuPlan.compile? raw (sizes 65 65) |
      throw (IO.userError ("baseline compile refused " ++ label kind))
    assertCase (label kind ++ "/public-compile")
      (match MapZipPlan.validate? raw (sizes 65 65) plan with | .ok _ => true | _ => false)
    count := count + 1
    let .ok candidate := GpuPlan.compileCandidate? raw (sizes 65 65) |
      throw (IO.userError "candidate compile refused")
    assertCase (label kind ++ "/candidate-retained") (candidate.compress == plan.compress)
    count := count + 1
    for (name,changed) in mutations kind plan do
      -- Guard against a misspelled mutation quietly becoming a positive case.
      unless changed.compress != plan.compress do
        throw (IO.userError ("mutation did not change candidate: " ++ name))
      assertCase (label kind ++ "/refuse-" ++ name) (refused raw (sizes 65 65) changed)
      count := count + 1
    assertCase (label kind ++ "/refuse-external-shape-drift") (refused raw (sizes 64 65) plan)
    count := count + 1
    let rewired := field raw "links" (.arr ((entries raw "links").map fun link =>
      if named (link.getObjValD "to") "node" "operation" &&
          named (link.getObjValD "to") "port" (if kind.isZip then "a" else "x") then
        field link "from" (field (link.getObjValD "from") "node" (.str "input-right"))
      else link))
    assertCase (label kind ++ "/refuse-source-graph-port-drift") (refused rewired (sizes 65 65) plan)
    count := count + 1
    if !kind.isZip then
      let changedRaw := changeNamed raw "nodes" "id" "operation" fun node =>
        field node "params" (field (node.getObjValD "params") "value"
          (toJson (((constant kind).toNat+1) % 4294967296)))
      assertCase (label kind ++ "/refuse-source-graph-constant-drift")
        (refused changedRaw (sizes 65 65) plan)
      count := count + 1
    let .ok smallPlan := GpuPlan.compile? raw (sizes 6 6) |
      throw (IO.userError "small compile refused")
    let some smallStep := step? smallPlan | throw (IO.userError "small step absent")
    let lanes := (List.range 64).map UInt32.ofNat
    for (name,order) in [("forward",lanes),("reverse",lanes.reverse)] do
      let observed := MapZipCompileRefinement.runJsonGrid? smallPlan smallStep
        (bound left right) (Array.replicate 7 sentinel) order
      assertCase (label kind ++ "/parsed-grid-" ++ name)
        (observed.map Array.toList == some (expected kind ++ [sentinel]))
      count := count + 1
    assertCase (label kind ++ "/refuse-short-output-allocation")
      (MapZipCompileRefinement.runJsonGrid? smallPlan smallStep
        (bound left right) (Array.replicate 5 sentinel) lanes).isNone
    count := count + 1
    assertCase (label kind ++ "/refuse-short-input-allocation")
      (MapZipCompileRefinement.runJsonGrid? smallPlan smallStep
        (bound (left.extract 0 5) right) (Array.replicate 6 sentinel) lanes).isNone
    count := count + 1
    let .ok emptyPlan := GpuPlan.compile? raw (sizes 0 0) |
      throw (IO.userError "empty compile refused")
    let some emptyStep := step? emptyPlan | throw (IO.userError "empty step absent")
    assertCase (label kind ++ "/empty-physical-input-output-dummies")
      ((MapZipCompileRefinement.runJsonGrid? emptyPlan emptyStep
        (bound #[sentinel] #[sentinel]) #[sentinel] lanes).map Array.toList == some [sentinel])
    count := count + 1
    assertCase (label kind ++ "/maximum-dispatch-admitted")
      (GpuPlan.compile? raw (sizes 4194240 4194240)).isOk
    count := count + 1
    assertCase (label kind ++ "/excess-dispatch-refused")
      (!(GpuPlan.compile? raw (sizes 4194241 4194241)).isOk)
    count := count + 1
    if kind.isZip then
      assertCase (label kind ++ "/unequal-zip-refused") (!(GpuPlan.compile? raw (sizes 1 2)).isOk)
      count := count + 1
  IO.println (Json.mkObj [("suite",toJson ("mapzip-emitted-plan" : String)),
    ("pass",toJson count),("fail",toJson (0 : Nat)),("total",toJson count)]).compress
