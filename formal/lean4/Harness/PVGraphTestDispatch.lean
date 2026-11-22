import Wasm.CoreDispatch
import Wasm.Ops.StageList
import Wasm.Ops.PipelineNodes
import Wasm.Ops.GraphNodes
import Wasm.Ops.PVGraph

/-!
Test-only core-plus-registry profile. Every operation delegates to its
shipping implementation. This smaller executable allows exact-source local
query, registry and npm-node tests without pretending to be the full engine.
Neither shipping dispatch table is changed. The full-engine CI remains the
shipping artifact gate.
-/
namespace L4Wasm.PVGraphTest

open L4Factoidal.JSON Ops

def additionalOps : List String :=
  ["stageList", "pipelineCheck", "pipelineCheckNodes", "graphCheckNodes",
   "pvgraphBuild", "pvgraphAdmit", "pvgraphEvaluate", "pvgraphGpuPlan"]

def reflection (io : Bool) : String :=
  (Json.object [
    ("ok", .bool true), ("abiVersion", .string "1"),
    ("engine", .string "core-plus-registry-test"),
    ("ops", .array ((Core.coreOpNames ++
      (if io then Core.coreIOOpNames else []) ++ additionalOps).map Json.string)),
    ("blobOps", .array []), ("blobIoOps", .array []),
    ("fullOnlyOps", .array ((Core.fullOnlyOpNames.filter (!additionalOps.contains ·)).map Json.string)),
    ("fullOnlyFormats", .array (jsonLdFormatTags.map Json.string))]).toString

def extra (op : String) (args : List String) : Option String :=
  match op with
  | "stageList" => some (match args with
      | [] => stageList
      | _ => errJson s!"{op} expects 0 arguments, got {args.length}")
  | "pipelineCheck" => some (Core.arity1 op pipelineCheck args)
  | "pipelineCheckNodes" => some (Core.arity1 op pipelineCheckNodes args)
  | "graphCheckNodes" => some (Core.arity1 op graphCheckNodes args)
  | "pvgraphBuild" => some (Core.arity1 op pvgraphBuild args)
  | "pvgraphAdmit" => some (Core.arity1 op pvgraphAdmit args)
  | "pvgraphEvaluate" => some (Core.arity2 op pvgraphEvaluate args)
  | "pvgraphGpuPlan" => some (Core.arity2 op pvgraphGpuPlan args)
  | _ => none

def call (op argsJson : String) : String :=
  match decodeArgs argsJson with
  | .error e => errJson e
  | .ok args =>
    if op == "ops" then reflection false
    else (extra op args).getD (Core.call op argsJson)

def callIO (op argsJson : String) : IO String := do
  match decodeArgs argsJson with
  | .error e => pure (errJson e)
  | .ok args =>
    if op == "ops" then pure (reflection true)
    else match extra op args with
      | some answer => pure answer
      | none => Core.callIO op argsJson

end L4Wasm.PVGraphTest
