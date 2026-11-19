import L4Factoidal.Paralliverse.StudioProgram
import L4Factoidal.JSON.Serialize

/-! Lean owns the Studio report, including the logical result, shader selection,
initial GPU buffers and the expected complete destination. -/
namespace L4Factoidal.Paralliverse.Studio

open WordMapGPU (KernelTag Pass Plan)
open L4Factoidal.JSON (Json)

private def primitiveTerm {a b : Shape Unit} : WordProgram.Op a b → String
  | .pack => ".pack"
  | .add k => "(.add " ++ toString k.toNat ++ ")"
  | .multiply k => "(.multiply " ++ toString k.toNat ++ ")"

/-- Print the actual syntax tree as a Lean term. All fragments come from
constructors and unsigned word values. -/
def sourceTerm {a b : Shape Unit} : Program WordProgram.Op a b → String
  | .identity => ".identity"
  | .prim op => "(.prim " ++ primitiveTerm op ++ ")"
  | .seq f g => "(.seq " ++ sourceTerm f ++ " " ++ sourceTerm g ++ ")"
  | .prod f g => "(.prod " ++ sourceTerm f ++ " " ++ sourceTerm g ++ ")"
  | .fanout f g => "(.fanout " ++ sourceTerm f ++ " " ++ sourceTerm g ++ ")"
  | .map f => "(.map " ++ sourceTerm f ++ ")"

def leanExample (term : String) : String :=
  "import L4Factoidal.Paralliverse.StudioProgram\n\nopen L4Factoidal.Paralliverse\n\n" ++
  "def studioExample : Studio.WordPipeline :=\n  " ++ term ++ "\n"

structure Evaluation where
  source : WordPipeline
  optimized : WordPipeline
  output : List UInt32
  selected : Option Plan

def evaluate (r : Request) : Evaluation :=
  let p := r.script.program
  let fused := Program.fuseMaps p
  ⟨p, fused, Program.runCPU WordProgram.base (@WordProgram.reference) 1 fused r.input,
    WordMapGPU.select? p⟩

/-- Kind: reported execution and selection.
Says: the Studio's CPU output is exactly the original program's meaning;
the device plan, when present, reconstructs the original typed source.
Does not say: that a browser or driver executed the selected plan. -/
theorem evaluate_correct (r : Request) (plan : Plan) :
    (evaluate r).output = Program.eval WordProgram.base (@WordProgram.reference) r.script.program r.input ∧
    ((evaluate r).selected = some plan ↔ r.script.program = plan.program) :=
  ⟨runCPU_eq_source 1 r.script.program r.input, WordMapGPU.select?_eq_some_iff r.script.program plan⟩

private def tagName : KernelTag → String
  | .add => "add"
  | .multiply => "multiply"

private def number (n : Nat) : Json := .number (toString n)
def wordsJson (xs : List UInt32) : Json := .array (xs.map fun w => number w.toNat)

def capabilities : Json :=
  .object [("schemaVersion", number 1), ("programLimit", number maxProgramBytes),
    ("studioLimit", number maxRequestBytes), ("wordLimit", number WordMapGPU.maxWords),
    ("commandLimit", number maxCommands)]

def capabilityBytes : ByteArray := (L4Factoidal.JSON.toStringCompact capabilities).toUTF8

private def stepFields (step : Pass) : List (String × Json) :=
  [("kernel", .string (tagName step.tag)), ("operand", number step.coefficient.toNat)]

/-- Source and intermediate header coefficients belong to their consuming pass.
The final header and each spare tail word make accidental overwrites observable. -/
private def tailWord (id : Nat) : UInt32 := 0xD00D0000 + UInt32.ofNat id
private def endCoefficient : UInt32 := 0xF00DF00D

def bufferJson (id : Nat) (coefficient : UInt32) (payload : List UInt32) : Json :=
  let initial := (WordMapGPU.packet coefficient payload [tailWord id]).toList
  .object [("id", number id), ("header", wordsJson (initial.take 2)),
    ("tail", wordsJson [tailWord id]), ("initialWords", wordsJson initial)]

def executionPlan (plan : Plan) (input output : List UInt32) : Json :=
  let passes := plan.passes
  let finalId := passes.length
  let scratch := List.replicate input.length (0xC0DECAFE : UInt32)
  let initial := passes.zipIdx.map fun (pass, id) =>
    bufferJson id pass.coefficient (if id == 0 then input else scratch)
  let buffers := initial ++ [bufferJson finalId endCoefficient scratch]
  let actions := passes.zipIdx.map fun (pass, id) =>
    Json.object (stepFields pass ++ [("shaderSelector", number pass.tag.shaderSelector.toNat),
      ("sourceBuffer", number id), ("destinationBuffer", number (id + 1))])
  let expected := UInt32.ofNat input.length :: endCoefficient :: (output ++ [tailWord finalId])
  .object [("wordCount", number input.length), ("workgroupSize", number 64),
    ("workgroups", number (WordMapGPU.workgroups input.length)), ("payloadWordOffset", number 2),
    ("readbackBuffer", number finalId), ("buffers", .array buffers), ("passes", .array actions),
    ("expectedWords", wordsJson expected)]

def report (r : Request) : Json :=
  let result := evaluate r
  let term := sourceTerm result.source
  let (refusal, target) : Json × Json := match result.selected with
    | some plan => (.null, executionPlan plan r.input result.output)
    | none => (.string "The WebGPU selector supports one or two source maps. The CPU ran the full pipeline.", .null)
  .object [("schemaVersion", number 1), ("sourceIR", .string term),
    ("optimizedIR", .string (sourceTerm result.optimized)), ("leanSource", .string (leanExample term)),
    ("steps", .array (r.script.steps.map fun step => .object (stepFields step))),
    ("input", wordsJson r.input), ("output", wordsJson result.output),
    ("gpuEligible", .bool result.selected.isSome), ("refusal", refusal), ("executionPlan", target)]

def call (bytes : ByteArray) : Except PackWire.Error ByteArray := do
  return (L4Factoidal.JSON.toStringCompact (report (← parseRequest bytes))).toUTF8

#print axioms evaluate_correct

end L4Factoidal.Paralliverse.Studio
