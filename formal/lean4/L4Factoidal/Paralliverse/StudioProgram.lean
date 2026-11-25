import L4Factoidal.Paralliverse.WordMapGPU
import L4Factoidal.Paralliverse.PackWire

/-! Typed word-map pipelines and the bounded Studio command language. -/
namespace L4Factoidal.Paralliverse.Studio

open WordMapGPU (Pass Plan)

abbrev WordPipeline := Program WordProgram.Op WordProgram.words WordProgram.words

def add (k : UInt32) : Pass := ⟨.add, k⟩
def multiply (k : UInt32) : Pass := ⟨.multiply, k⟩

/-- Construct a nonempty typed pipeline, retaining the order of its source operations. -/
def pipeline : Pass → List Pass → WordPipeline
  | first, [] => first.program
  | first, next :: rest => .seq first.program (pipeline next rest)

def maxCommands : Nat := 16
def maxProgramBytes : Nat := 512
def maxInputBytes : Nat := PackWire.maxEditorBytes - 2
def maxRequestBytes : Nat := maxProgramBytes + 1 + maxInputBytes

structure Script where
  first : Pass
  rest : List Pass
  withinLimit : rest.length < maxCommands

def Script.steps (s : Script) : List Pass := s.first :: s.rest
def Script.program (s : Script) : WordPipeline := pipeline s.first s.rest

/-- Run the same fused task-based CPU interpreter used by other typed callers. -/
def runCPU (workers : Nat) (p : WordPipeline) (xs : List UInt32) : List UInt32 :=
  Program.runCPU WordProgram.base (@WordProgram.reference) workers (Program.fuseMaps p) xs

/-- Kind: library refinement.
Says: every Studio pipeline, for every worker count and word input, returns its
unfused source meaning under the modular word operations.
Does not say: how many host threads run or how long execution takes. -/
theorem runCPU_eq_source (workers : Nat) (p : WordPipeline) (xs : List UInt32) :
    runCPU workers p xs = Program.eval WordProgram.base (@WordProgram.reference) p xs :=
  congrFun (Program.runCPU_fuseMaps_eq_eval WordProgram.base (@WordProgram.reference)
    (@WordProgram.reference) (fun _ _ => rfl) workers p) xs

/-- Kind: concrete source correspondence.
Says: the ergonomic two-command pipeline builds the existing typed affine program.
Does not say: every extension of the source language has a device plan. -/
theorem pipeline_affine (a b : UInt32) :
    pipeline (multiply a) [add b] = WordProgram.affine a b := rfl

/-- Kind: capability boundary.
Says: every chain of at least three source maps receives an explicit refusal
from the actual bounded WGSL selector. The CPU interpreter accepts these chains.
Does not say: a larger future selector could not lower these programs. -/
theorem three_maps_refused (a b c : Pass) (rest : List Pass) :
    WordMapGPU.select? (pipeline a (b :: c :: rest)) = none := by
  cases a with
  | mk tag k => cases tag <;> rfl

/-- Kind: source admission.
Says: every admitted script contains one through sixteen operations.
Does not say: every text of the right length is a valid script. -/
theorem Script.command_count (s : Script) :
    0 < s.steps.length ∧ s.steps.length ≤ maxCommands := by
  have bound := s.withinLimit
  simp only [Script.steps, List.length_cons]
  omega

private def wordLiteral (token : String) (line : Nat) : Except PackWire.Error UInt32 := do
  if token.isEmpty || token.length > 10 || !(token.toList.all Char.isDigit) ||
      (token.startsWith "0" && token != "0") then
    throw (.invalid s!"Line {line} needs an unsigned decimal word from 0 through 4294967295.")
  let some n := token.toNat? | throw (.invalid s!"Line {line} has an invalid decimal word.")
  if n ≥ UInt32.size then throw (.invalid s!"The operand on line {line} exceeds 4294967295.")
  return UInt32.ofNat n

private def parseLine (line : Nat) (source : String) : Except PackWire.Error Pass := do
  match ((source.replace "\t" " ").splitOn " ").filter (· != "") with
  | ["map", "add", k] => return add (← wordLiteral k line)
  | ["map", "multiply", k] => return multiply (← wordLiteral k line)
  | _ => throw (.invalid s!"Line {line} must be 'map add N' or 'map multiply N'.")

private def parseCommands (bytes : ByteArray) : Except PackWire.Error Script := do
  if bytes.data.any (fun b => b >= 128) then throw (.invalid "Use ASCII program commands and decimal operands.")
  let some text := String.fromUTF8? bytes | throw (.invalid "Program text must be UTF-8.")
  let mut reversed : List Pass := []
  for (line, i) in (text.splitOn "\n").zipIdx do
    let source := line.trimAscii.toString
    unless source.isEmpty do
      if reversed.length ≥ maxCommands then throw (.limit "Use at most 16 map commands.")
      reversed := (← parseLine (i + 1) source) :: reversed
  match reversed.reverse with
  | [] => throw (.invalid "Enter at least one map command.")
  | first :: rest =>
    if h : rest.length < maxCommands then return ⟨first, rest, h⟩
    else throw (.limit "Use at most 16 map commands.")

def parseProgram (bytes : ByteArray) : Except PackWire.Error Script :=
  if bytes.size > maxProgramBytes then .error (.limit "Use at most 512 bytes of program text.")
  else parseCommands bytes

/-- Kind: byte admission.
Says: every oversized program receives the specific byte-limit refusal.
Does not say: a size-admitted source has valid syntax. -/
theorem parseProgram_over_limit (bytes : ByteArray) (h : bytes.size > maxProgramBytes) :
    parseProgram bytes = .error (.limit "Use at most 512 bytes of program text.") :=
  if_pos h

structure Request where
  script : Script
  input : List UInt32
  withinLimit : input.length ≤ WordMapGPU.maxWords

/-- Split at the first NUL within the bounded program prefix. Wrapping the input
in one outer array exposes the existing strict decimal word parser. -/
private def readRequest (bytes : ByteArray) : Except PackWire.Error Request := do
  let mut separator : Option Nat := none
  for i in [:min bytes.size (maxProgramBytes + 1)] do
    if bytes[i]! == 0 then
      separator := some i
      break
  let some i := separator | do
    if bytes.size > maxProgramBytes then throw (.limit "Use at most 512 bytes before the program separator.")
    else throw (.invalid "Separate the program and input with a NUL byte.")
  if bytes.size - (i + 1) > maxInputBytes then throw (.limit "The flat input exceeds 16382 bytes.")
  let script ← parseProgram (bytes.extract 0 i)
  let flat := bytes.extract (i + 1) bytes.size
  let rows ← PackWire.parseEditor ((ByteArray.empty.push 91 ++ flat).push 93)
  let [xs] := rows | throw (.invalid "Supply one flat JSON array of unsigned decimal words.")
  if h : xs.length ≤ WordMapGPU.maxWords then return ⟨script, xs, h⟩
  else throw (.limit "Use at most 1024 input words.")

def parseRequest (bytes : ByteArray) : Except PackWire.Error Request :=
  if bytes.size > maxRequestBytes then .error (.limit "The Studio request exceeds its byte limit.")
  else readRequest bytes

/-- Kind: byte admission.
Says: a request past the combined limit is refused before the parser scans or slices it.
Does not say: that a host enforces its own allocation limit. -/
theorem parseRequest_over_limit (bytes : ByteArray) (h : bytes.size > maxRequestBytes) :
    parseRequest bytes = .error (.limit "The Studio request exceeds its byte limit.") :=
  if_pos h

#print axioms runCPU_eq_source
#print axioms pipeline_affine
#print axioms three_maps_refused
#print axioms Script.command_count
#print axioms parseProgram_over_limit
#print axioms parseRequest_over_limit

end L4Factoidal.Paralliverse.Studio
