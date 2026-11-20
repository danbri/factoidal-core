import L4Factoidal.Paralliverse.Studio

/-! Field-level contracts for the JSON value provided by the Studio ABI. -/
namespace L4Factoidal.Paralliverse.Studio

open L4Factoidal.JSON (Json)
open WordMapGPU (Pass Plan)

namespace ReportContract

def unsigned (n : Nat) : Json := .number (toString n)

/-- The complete buffer record expected by a host. Both header words and the
spare tail belong to the observable initial frame. -/
def buffer (id : Nat) (coefficient : UInt32) (payload : List UInt32) : Json :=
  let header := [UInt32.ofNat payload.length, coefficient]
  let tail := [0xD00D0000 + UInt32.ofNat id]
  .object [("id", unsigned id), ("header", wordsJson header), ("tail", wordsJson tail),
    ("initialWords", wordsJson (header ++ payload ++ tail))]

def commandFields (p : Pass) : List (String × Json) :=
  let name := match p.tag with | .add => "add" | .multiply => "multiply"
  [("kernel", .string name), ("operand", unsigned p.coefficient.toNat)]

def pass (id : Nat) (p : Pass) : Json :=
  .object (commandFields p ++ [("shaderSelector", unsigned p.tag.shaderSelector.toNat),
    ("sourceBuffer", unsigned id), ("destinationBuffer", unsigned (id + 1))])

def buffers (plan : Plan) (xs : List UInt32) : List Json :=
  let scratch := List.replicate xs.length (0xC0DECAFE : UInt32)
  match plan with
  | .unary a => [buffer 0 a.coefficient xs, buffer 1 0xF00DF00D scratch]
  | .two a b => [buffer 0 a.coefficient xs, buffer 1 b.coefficient scratch,
      buffer 2 0xF00DF00D scratch]

def passes : Plan → List Json
  | .unary a => [pass 0 a]
  | .two a b => [pass 0 a, pass 1 b]

def readback : Plan → Nat
  | .unary _ => 1
  | .two _ _ => 2

def finalWords (plan : Plan) (count : Nat) (result : List UInt32) : List UInt32 :=
  UInt32.ofNat count :: 0xF00DF00D :: (result ++ [0xD00D0000 + UInt32.ofNat (readback plan)])

/-- The fields consulted by the device transport. The projected arrays describe
every JSON record, including the ordered source and destination buffer IDs. -/
def Describes (target : Json) (plan : Plan) (input output : List UInt32) : Prop :=
  target.field? "wordCount" = some (unsigned input.length) ∧
  target.field? "workgroupSize" = some (unsigned 64) ∧
  target.field? "workgroups" = some (unsigned (WordMapGPU.workgroups input.length)) ∧
  target.field? "payloadWordOffset" = some (unsigned 2) ∧
  target.field? "readbackBuffer" = some (unsigned (readback plan)) ∧
  target.getArray? "passes" = some (passes plan) ∧
  target.getArray? "buffers" = some (buffers plan input) ∧
  target.field? "expectedWords" = some (wordsJson (finalWords plan input.length output))

end ReportContract

private theorem buffer_fields (id : Nat) (k : UInt32) (payload : List UInt32) :
    bufferJson id k payload = ReportContract.buffer id k payload := by
  unfold bufferJson WordMapGPU.packet
  rfl

private theorem plan_fields (plan : Plan) (input output : List UInt32) :
    ReportContract.Describes (executionPlan plan input output) plan input output := by
  cases plan with
  | unary a =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    change some [bufferJson 0 a.coefficient input,
      bufferJson 1 0xF00DF00D (List.replicate input.length 0xC0DECAFE)] = _
    simp only [buffer_fields] <;> rfl
  | two a b =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    change some [bufferJson 0 a.coefficient input, bufferJson 1 b.coefficient (List.replicate input.length 0xC0DECAFE),
      bufferJson 2 0xF00DF00D (List.replicate input.length 0xC0DECAFE)] = _
    simp only [buffer_fields] <;> rfl

/-- Kind: actual report projections.
Says: the version, input, command list and CPU output describe the original
typed program. Both displayed terms, the copyable Lean example and GPU
eligibility come from that source or its actual fusion pass.
Does not say: that an external JSON parser or Lean compiler processed these strings. -/
theorem report_source_fields (r : Request) :
    (report r).field? "output" = some (wordsJson
      (Program.eval WordProgram.base (@WordProgram.reference) r.script.program r.input)) ∧
    (report r).getString? "sourceIR" = some (sourceTerm r.script.program) ∧
    (report r).getString? "optimizedIR" = some (sourceTerm (Program.fuseMaps r.script.program)) ∧
    (report r).getString? "leanSource" = some (leanExample (sourceTerm r.script.program)) ∧
    (report r).field? "schemaVersion" = some (ReportContract.unsigned 1) ∧
    (report r).field? "input" = some (wordsJson r.input) ∧
    (report r).getArray? "steps" = some (r.script.steps.map (fun p => .object (ReportContract.commandFields p))) ∧
    (report r).getBool? "gpuEligible" = some (WordMapGPU.select? r.script.program).isSome := by
  have oracle : (evaluate r).output =
      Program.eval WordProgram.base (@WordProgram.reference) r.script.program r.input :=
    runCPU_eq_source 1 r.script.program r.input
  rw [← oracle]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (report r).getBool? "gpuEligible" = some (evaluate r).selected.isSome
  cases h : (evaluate r).selected <;> simp only [report, h] <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Kind: selected plan report.
Says: every original source represented by a unary or two-pass plan reports that
plan's exact buffers, extracted coefficient, shader selector, ordered bindings,
dispatch geometry and full expected destination around the source CPU result.
Does not say: that the host transferred, submitted or observed these values. -/
theorem report_selected_plan (r : Request) (plan : Plan) (source : r.script.program = plan.program) :
    ∃ target, (report r).field? "executionPlan" = some target ∧
      (report r).field? "refusal" = some .null ∧ (report r).getBool? "gpuEligible" = some true ∧
      ReportContract.Describes target plan r.input
        (Program.eval WordProgram.base (@WordProgram.reference) r.script.program r.input) := by
  obtain ⟨oracle, selection⟩ := evaluate_correct r plan
  have chosen : (evaluate r).selected = some plan := selection.mpr source
  refine ⟨executionPlan plan r.input (evaluate r).output, ?_, ?_, ?_, ?_⟩
  · simp only [report, chosen] <;> rfl
  · simp only [report, chosen] <;> rfl
  · simp only [report, chosen] <;> rfl
  · rw [← oracle]
    exact plan_fields plan r.input (evaluate r).output

/-- Kind: reported capability refusal.
Says: when the real typed selector refuses a source, the actual JSON has a null
device plan, false eligibility, and a specific CPU-only explanation.
Does not say: a different backend cannot implement that program. -/
theorem report_refused_plan (r : Request) (h : WordMapGPU.select? r.script.program = none) :
    (report r).field? "executionPlan" = some .null ∧ (report r).getBool? "gpuEligible" = some false ∧
    (report r).getString? "refusal" =
      some "The WebGPU selector supports one or two source maps. The CPU ran the full pipeline." := by
  change (evaluate r).selected = none at h
  simp only [report, h] <;> exact ⟨rfl, rfl, rfl⟩

#print axioms report_source_fields
#print axioms report_selected_plan
#print axioms report_refused_plan

end L4Factoidal.Paralliverse.Studio
