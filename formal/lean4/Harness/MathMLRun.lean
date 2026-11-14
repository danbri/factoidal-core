/-
Harness/MathMLRun — the Content MathML evaluation corpus.

`third_party/testing/mathml/manifest.json` carries one entry per test:
the MathML source, an optional symbol environment, and the expected
value written as an exact rational (`157/50`), an integer, `true` /
`false`, or the literal `undef`.

`undef` is a REAL expected answer, not a skip. A division by zero, an
inexact root, a non-integer power and an unsupported operator all
denote nothing, and an evaluator that returned a number for any of
them would be wrong in the direction that is hardest to notice. Six of
the corpus's tests expect exactly that, so they are scored like any
other.

## Two manifests, one corpus

`manifest.json` holds the 56 chapter-4 arithmetic and relation cases.
`matrix-manifest.json` holds 25 more, all of them Content markup:
MathML 3.0 §4.4.10 (Linear Algebra) and the OpenMath `linalg1` /
`linalg2` Content Dictionaries. Both are read and scored together.
None of the 25 is a presentation-markup case; this module is a
Content MathML backend by design (decoding and exact evaluation), so
a presentation case would be out of scope rather than a gap, and
there are none here.

## Strict Content and OpenMath

`strict-manifest.json` gives a Content MathML input and the Strict Content MathML that MathML 3
section 4.6 (MathML 4 appendix F) says it becomes. A case passes when `toStrict` of the input is the
expression the expected markup reads as, the result is strict, the strict writer's output reads back
as the same expression, and `evalStrict` of the strict form gives the value `eval` gives the input.

`openmath-manifest.json` gives a Content MathML input and its OpenMath object in the XML encoding. A
case passes when `toOpenMath` of the input is that object, the object reads back as the strict form
of the input, and the object survives `writeOpenMath` then `parseOpenMath`. A case with no input is an
OpenMath object `Expr` has no counterpart for (a binder, an attribution, a float, a string): it passes
when it survives the XML round trip and `ofOpenMath` refuses it.

Each of the evaluation cases is also evaluated in its strict form (`evalStrict` of `toStrict`), which
tests on the corpus that the two evaluators agree.

## Where the corpus is found

A relative directory is tried first against the process working
directory (the repository root, as `lake -d formal/lean4 exe l4mathml`
runs it) and second against `../../` (the working directory when a
command runs inside `formal/lean4`), so both invocations work.

Usage: `lake exe l4mathml [tests-dir]`
       default corpus: `third_party/testing/mathml`
-/
import L4Factoidal.MathML.FromXml
import L4Factoidal.MathML.Core
import L4Factoidal.MathML.OpenMath
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.MathML

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

/-- Write a value the way the manifest writes it: an integer bare, a
    rational as `num/den`, a boolean as `true`/`false`, a vector as
    `[a,b,c]` and a matrix as `[[a,b],[c,d]]`. -/
def showValue : Option Value → String
  | none            => "undef"
  | some (.bool b)  => if b then "true" else "false"
  | some (.num r)   => showRat r
  | some (.vecv v)  => showVec v
  | some (.matv m)  => showMat m

/-- Resolve a corpus directory written relative to the repository root
    or relative to `formal/lean4`. -/
def resolveBase (d : String) : IO String := do
  if ← System.FilePath.pathExists (d ++ "/manifest.json") then return d
  let up := "../../" ++ d
  if ← System.FilePath.pathExists (up ++ "/manifest.json") then return up
  return d

/-- The environment an entry supplies, as the evaluator wants it. -/
def envOf (j : Json) : String → Option (Int × Int) :=
  let pairs : List (String × (Int × Int)) := match field? "env" j with
    | some (.object ms) =>
        ms.filterMap (fun (k, v) => match v with
          | .string s => (s.toInt?).map (fun i => (k, (i, (1 : Int))))
          | .number s => (s.toInt?).map (fun i => (k, (i, (1 : Int))))
          | _ => none)
    | _ => []
  fun s => (pairs.find? (fun (k, _) => k == s)).map (·.2)

/-- The cases of one manifest, or the empty list when it is absent. -/
def casesOf (path : String) : IO (List Json) := do
  if !(← System.FilePath.pathExists path) then
    IO.println s!"mathml runner: manifest not found: {path}"
    return []
  let text ← IO.FS.readFile path
  match parseJson? text with
  | none =>
      IO.println s!"mathml runner: manifest did not parse: {path}"
      return []
  | some j => return (match field? "tests" j with
      | some (.array ts) => ts
      | _                => [])

/-- One strict-transformation case: `none` when it passes, else what went wrong. -/
def strictCase (t : Json) : Option String :=
  match str? "input" t, str? "expectedStrict" t with
  | some src, some want =>
      match parseMathML src, parseMathML want with
      | some e, some w =>
          let s := toStrict e
          if !exprEq s w then some s!"strict form differs: got {toStrictContentMathML e}"
          else if !isStrict s then some "the result is not strict"
          else if !(match parseMathML (toStrictContentMathML e) with
                    | some r => exprEq r s
                    | none   => false) then some "the strict markup written does not read back"
          else if evalStrict (envOf t) s != eval (envOf t) e then
            some s!"value differs: strict {showValue (evalStrict (envOf t) s)}, input {showValue (eval (envOf t) e)}"
          else none
      | none, _ => some "the input did not read"
      | _, none => some "the expected strict markup did not read"
  | _, _ => some "case has no input or no expectedStrict"

/-- One OpenMath case: `none` when it passes, else what went wrong. -/
def openMathCase (t : Json) : Option String :=
  match str? "openmath" t with
  | none => some "case has no openmath"
  | some om =>
      match parseOpenMath om with
      | none => some "the OpenMath XML did not read"
      | some o =>
          if !(match parseOpenMath (writeOpenMath o) with
               | some o' => omEq o' o
               | none    => false) then some "the object does not survive write then parse"
          else match str? "input" t with
            | none =>
                if (ofOpenMath o).isSome then some "expected no Expr counterpart, but one was read"
                else none
            | some src =>
                match parseMathML src with
                | none => some "the input did not read"
                | some e =>
                    if !omEq (toOpenMath e) o then
                      some s!"object differs: got {writeOpenMath (toOpenMath e)}"
                    else if !(match ofOpenMath o with
                              | some r => exprEq r (toStrict e)
                              | none   => false) then some "the object does not read back as the strict form"
                    else none

/-- Score a list of cases with a checker; prints each failure. -/
def scoreCases (label : String) (check : Json → Option String) (cases : List Json) :
    IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for t in cases do
    match check t with
    | none => pass := pass + 1
    | some why =>
        fail := fail + 1
        IO.println s!"FAIL {label} {(str? "name" t).getD "?"}: {why}"
  return (pass, fail)

def main (args : List String) : IO UInt32 := do
  let dir ← resolveBase ((args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/mathml")
  let manifestPath := dir ++ "/manifest.json"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"mathml runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  do
      -- Both manifests are Content markup and are scored together.
      let arith ← casesOf manifestPath
      let linalg ← casesOf (dir ++ "/matrix-manifest.json")
      let tests := arith ++ linalg
      let mut pass := 0
      let mut fail := 0
      let mut unread := 0
      let mut spass := 0
      let mut sfail := 0
      for t in tests do
        let name := (str? "name" t).getD "?"
        match str? "input" t, str? "expectedValue" t with
        | some src, some want =>
            match parseMathML src with
            | none =>
                -- The markup did not READ. Distinct from an
                -- undefined VALUE: one is a gap in this module, the
                -- other is the answer.
                if want == "undef" then
                  fail := fail + 1
                  IO.println s!"FAIL {name}: markup did not read (expected the undefined VALUE, which is not the same thing)"
                else
                  unread := unread + 1
                  IO.println s!"UNREAD {name}: the markup did not parse into an expression"
            | some e =>
                let got := showValue (eval (envOf t) e)
                if got == want then pass := pass + 1
                else
                  fail := fail + 1
                  IO.println s!"FAIL {name}: got {got}, expected {want}"
                -- The same case through its strict form.
                let gotStrict := showValue (evalStrict (envOf t) (toStrict e))
                if gotStrict == want && isStrict (toStrict e) then spass := spass + 1
                else
                  sfail := sfail + 1
                  IO.println s!"FAIL strict-eval {name}: got {gotStrict}, expected {want}"
        | _, _ => pure ()
      IO.println ""
      IO.println s!"content-mathml evaluation: {pass} pass, {fail} fail, {unread} markup-not-read (out of {tests.length})"
      IO.println s!"  ({arith.length} chapter-4 arithmetic and relation cases + {linalg.length} section 4.4.10 linear-algebra cases)"
      IO.println "`undef` is an expected ANSWER here, not a skip: a division by zero,"
      IO.println "an inexact root, a non-integer power and an unsupported operator all"
      IO.println "denote nothing, and returning a number for any of them would be"
      IO.println "wrong in the direction hardest to notice."
      IO.println ""
      IO.println s!"evaluation cases through their strict form: {spass} pass, {sfail} fail (out of {spass + sfail})"
      let strictCases ← casesOf (dir ++ "/strict-manifest.json")
      let (sp, sf) ← scoreCases "strict" strictCase strictCases
      IO.println s!"strict content transformation: {sp} pass, {sf} fail (out of {strictCases.length})"
      let omCases ← casesOf (dir ++ "/openmath-manifest.json")
      let (op, of_) ← scoreCases "openmath" openMathCase omCases
      IO.println s!"openmath: {op} pass, {of_} fail (out of {omCases.length})"
      return 0
