/-
Harness.LenientRun — the W3C syntax suites in lenient (recovery) mode,
`lake exe l4w3c --lenient <manifest…>`
(https://github.com/danbri/factoidal/issues/716).

This module only reads the test files and compares; the parsers are the
library's (`Syntax/NQuadsLenient.lean`, `Syntax/TurtleLenient.lean`). For each
Turtle, TriG, N-Triples and N-Quads test:

  * a positive syntax test and a positive evaluation test pass when the
    lenient parse reports NO diagnostic and returns the same graph or
    dataset as the strict parse (structural equality: the same triples in
    the same order, the same blank node labels);
  * a negative syntax test passes when the lenient parse reports AT LEAST
    ONE diagnostic;
  * a negative evaluation test passes when the lenient parse reports a
    diagnostic or returns no triple, the rule the strict runner applies;
  * in addition, for every Turtle, N-Triples and N-Quads test, the
    STREAMING lenient walk over 5-character chunks must report the same
    diagnostics (class, message, offset, line, column) and keep the same
    triples as the reference lenient walk. This is the differential check
    the design record names for the streaming executions; a disagreement is
    a failure of the test.

Every other test type is a `skip` ("not a syntax test").

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Run
import L4Factoidal.Syntax.NQuadsLenient
import L4Factoidal.Syntax.TurtleLenient

namespace Harness

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- Structural form of a dataset, for comparison (`Dataset` has no `BEq`). -/
def datasetShape (ds : Dataset) : Graph × List (Subject × Graph) :=
  (ds.default, ds.named.map fun ng => (ng.name, ng.graph))

/-- Characters in chunks of `n` (the last one shorter). -/
def chunksOf (n : Nat) (cs : List Char) : List (List Char) :=
  go (cs.length + 1) cs []
where
  go : Nat → List Char → List (List Char) → List (List Char)
    | 0, _, acc => acc.reverse
    | _, [], acc => acc.reverse
    | f + 1, cs, acc => go f (cs.drop n) (cs.take n :: acc)

/-- The streaming chunk size of the differential check. -/
def streamChunk : Nat := 5

def firstDiag (ds : List Diagnostic) : String :=
  match ds with
  | [] => "no diagnostic"
  | d :: _ => s!"{ds.length} diagnostic(s), first {d.line}:{d.column} {d.cls.tag}: {d.message}"

/-- The streaming N-Triples / N-Quads walk over `streamChunk`-character
chunks, with the reference accumulator. -/
def streamLines (reader : LineReader) (text : String) : Dataset × List Diagnostic :=
  let out := lenientStreamLines reader (fun ds t g => addQuad ds t g) pushDiag {}
    (chunksOf streamChunk text.toList) Dataset.empty []
  (out.acc, out.diags.reverse)

/-- The streaming Turtle walk over `streamChunk`-character chunks. -/
def streamTurtle (text base : String) (mode : Mode) : Graph × List Diagnostic :=
  let out := parseTurtleChunksLenient (freshBnodePrefix text) prependReverse pushDiag {} [] []
    ((chunksOf streamChunk text.toList).map String.ofList) (some base) mode
  (out.acc.reverse, out.diags.reverse)

/-- The streaming check: `none` when the streaming walk agrees. -/
def streamDisagrees {γ : Type} [BEq γ] (ref stream : γ × List Diagnostic) : Option String :=
  if ref.2 != stream.2 then
    some s!"streaming lenient walk disagrees on diagnostics (reference: {firstDiag ref.2}; streaming: {firstDiag stream.2})"
  else if !(ref.1 == stream.1) then
    some "streaming lenient walk disagrees on the triples kept"
  else none

/-- A positive test: no diagnostic, the strict result, and the streaming
walk agrees. -/
def positiveOutcome {γ : Type} [BEq γ] (strict : Except ParseError γ) (lenient : γ × List Diagnostic)
    (stream : Option (γ × List Diagnostic)) : Outcome :=
  match strict with
  | .error e => .fail s!"strict parser rejected input that should parse: {e.msg} (offset {e.pos})"
  | .ok v =>
      if !lenient.2.isEmpty then .fail s!"lenient parse reported {firstDiag lenient.2}"
      else if !(lenient.1 == v) then .fail "lenient parse returned a different result from the strict parse"
      else match stream.bind (streamDisagrees lenient) with
        | some why => .fail why
        | none => .pass

/-- A negative syntax test: at least one diagnostic, and the streaming walk
agrees. -/
def negativeOutcome {γ : Type} [BEq γ] (lenient : γ × List Diagnostic)
    (stream : Option (γ × List Diagnostic)) : Outcome :=
  if lenient.2.isEmpty then .fail "lenient parse reported no diagnostic for a negative syntax test"
  else match stream.bind (streamDisagrees lenient) with
    | some why => .fail why
    | none => .pass

/-- A negative evaluation test: a diagnostic, or no triple. -/
def negativeEvalOutcome {γ : Type} [BEq γ] (isEmpty : γ → Bool) (lenient : γ × List Diagnostic)
    (stream : Option (γ × List Diagnostic)) : Outcome :=
  if lenient.2.isEmpty && !isEmpty lenient.1 then
    .fail "lenient parse reported no diagnostic and kept triples for a negative evaluation test"
  else match stream.bind (streamDisagrees lenient) with
    | some why => .fail why
    | none => .pass

instance : BEq Dataset where
  beq a b := datasetShape a == datasetShape b

/-- Run one test case in lenient mode. -/
def runLenientTest (mode : Mode) (assumedBase : Option String) (manifestDir : String)
    (tc : TestCase) : IO RunResult := do
  let withAction (k : String → String → Outcome) : IO RunResult := do
    match tc.action with
    | none      => return .ofOutcome (.skip "mf:action is not a file IRI")
    | some path =>
      match ← readOpt path with
      | none      => return .ofOutcome (.skip s!"file missing: {path}")
      | some text => return .ofOutcome (k path text)
  let ntLenient (text : String) : Dataset × List Diagnostic :=
    let r := parseNTriplesLenient text mode
    ({ default := r.1, named := [] }, r.2)
  let ntStrict (text : String) : Except ParseError Dataset :=
    (parseNTriples text mode).map fun g => { default := g, named := [] }
  let ttlLenient (text base : String) : Graph × List Diagnostic :=
    parseTurtleLenient text (some base) mode
  let base (path : String) := fixtureBase assumedBase manifestDir path
  match tc.testType with
  | "TestNTriplesPositiveSyntax" =>
      withAction fun _ text =>
        positiveOutcome (ntStrict text) (ntLenient text) (some (streamLines (tripleReader mode) text))
  | "TestNTriplesNegativeSyntax" =>
      withAction fun _ text =>
        negativeOutcome (ntLenient text) (some (streamLines (tripleReader mode) text))
  | "TestNQuadsPositiveSyntax" =>
      withAction fun _ text =>
        positiveOutcome (parseNQuads text mode) (parseNQuadsLenient text mode)
          (some (streamLines (quadReader mode) text))
  | "TestNQuadsNegativeSyntax" =>
      withAction fun _ text =>
        negativeOutcome (parseNQuadsLenient text mode) (some (streamLines (quadReader mode) text))
  | "TestTurtlePositiveSyntax" | "TestTurtleEval" =>
      withAction fun path text =>
        positiveOutcome (parseTurtle text (some (base path)) mode) (ttlLenient text (base path))
          (some (streamTurtle text (base path) mode))
  | "TestTurtleNegativeSyntax" =>
      withAction fun path text =>
        negativeOutcome (ttlLenient text (base path)) (some (streamTurtle text (base path) mode))
  | "TestTurtleNegativeEval" =>
      withAction fun path text =>
        negativeEvalOutcome List.isEmpty (ttlLenient text (base path))
          (some (streamTurtle text (base path) mode))
  | "TestTrigPositiveSyntax" | "TestTrigEval" =>
      withAction fun path text =>
        positiveOutcome (parseTriG text (some (base path)) mode)
          (parseTriGLenient text (some (base path)) mode) none
  | "TestTrigNegativeSyntax" =>
      withAction fun path text =>
        negativeOutcome (parseTriGLenient text (some (base path)) mode) none
  | "TestTrigNegativeEval" =>
      withAction fun path text =>
        negativeEvalOutcome (fun ds => ds.default.isEmpty && ds.named.all (·.graph.isEmpty))
          (parseTriGLenient text (some (base path)) mode) none
  | t => return .ofOutcome (.skip s!"not a syntax test ({t}); --lenient runs the syntax suites only")

/-! ## Build-time checks -/

#guard chunksOf 2 "abcde".toList == ["ab".toList, "cd".toList, "e".toList]
#guard chunksOf 5 [] == []
#guard (chunksOf 3 "abcdefg".toList).flatten == "abcdefg".toList

end Harness
