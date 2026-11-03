/-
L4Factoidal.WebAnnotation.JsonTest — the W3C Web Annotation Data Model
(Recommendation, 2017-02-23) test semantics, in Lean.

The W3C test suite for the Data Model is `annotation-model/` of
web-platform-tests (vendored: `third_party/testing/web-annotation/`,
provenance in `third_party/testing/web-annotation-PROVENANCE.md`). Each
`.test` file lists assertion files. An assertion file is a JSON Schema
(draft-04) with four extra members:

* `assertionType`: `must`, `should` or `may` (default `must`; any other
  value is `must`);
* `expectedResult`: `valid` (default) or `invalid`;
* `onUnexpectedResult`: what the run does after an unexpected result —
  `failAndContinue` (default), `failAndSkip` (the rest of this level is not
  run) or `failAndAbort` (the rest of this level is not run, and the parent
  level is told to stop);
* `errorMessage`, `title`: text only.

A `.test` file can also give `skipFailures`, a list of assertion types
whose failures are not reported.

The suite's harness, `annotation-model/scripts/JSONtest.js` (`runTests`,
`determineResult`, `determineAction`), runs the list in order with ajv
4.0.4. This module is that procedure; the schemas are checked by
`L4Factoidal.JSONSchema` in its `draft04Ajv4` dialect. Two differences
from the JavaScript, both stated in the result:

* The JSON Schema validator is three-valued. An `unsupported` verdict is
  an UNDETERMINED subtest, never a pass. The run continues as after an
  expected result (`determineAction` is not reached for it).
* A comparison object (`compareWith`) or a nested list is not run: it is
  an undetermined subtest. No `.test` file of the vendored suite uses
  either (`tests/webannotation/run.sh` checks this).
-/
import L4Factoidal.JSONSchema.Validate
import L4Factoidal.JSON.Value

namespace L4Factoidal.WebAnnotation

open L4Factoidal.JSON
open L4Factoidal.JSONSchema

/-- The requirement level of an assertion (RFC 2119 keywords). -/
inductive Level where
  | must | should | may
  deriving Repr, DecidableEq, BEq, Inhabited

def Level.ofString (s : String) : Level :=
  match s.toLower with
  | "should" => .should
  | "may"    => .may
  | _        => .must

def Level.name : Level → String
  | .must => "must" | .should => "should" | .may => "may"

/-- The result of one subtest. -/
inductive Verdict where
  | pass | fail | undetermined
  deriving Repr, DecidableEq, BEq, Inhabited

/-- One reported subtest: `level:index title`, as JSONtest.js names it. -/
structure Subtest where
  name    : String
  /-- The assertion file (`""` for an inline assertion). -/
  file    : String := ""
  level   : Level
  verdict : Verdict
  deriving Repr, Inhabited

/-- The state that `determineAction` gives the next assertion. -/
inductive Action where
  | continue_ | skip | abort
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A loaded assertion file, keyed by the path the `.test` files use
    (`annotations/3.1-annotationTypeValidated.json`). -/
abbrev Cache := List (String × Json)

/-- The context of a run: the assertion cache, the schema registry for
    `$ref` (the `definitions/` files) and the base URI the assertions are
    read at. -/
structure Env where
  cache    : Cache
  registry : Registry
  base     : String
  skipFailures : List Level := []

def strField? (j : Json) (k : String) : Option String :=
  match j.field? k with
  | some (.string s) => some s
  | _ => none

def levelOf (a : Json) : Level := ((strField? a "assertionType").map Level.ofString).getD .must

/-- `expectedResult` is `invalid`. -/
def expectsInvalid (a : Json) : Bool := strField? a "expectedResult" == some "invalid"

/-- `determineResult`: did the validation give the expected result? -/
def determineResult (a : Json) (valid : Bool) : Bool :=
  if expectsInvalid a then !valid else valid

/-- `determineAction`: an expected result continues; otherwise the
    assertion's `onUnexpectedResult` decides. -/
def determineAction (a : Json) (expected : Bool) : Action :=
  if expected then .continue_
  else match strField? a "onUnexpectedResult" with
    | some "failAndSkip" | some "passAndSkip" => .skip
    | some "failAndAbort" | some "passAndAbort" => .abort
    | _ => .continue_

/-- The validation of `content` by one assertion schema. -/
def validateAssertion (env : Env) (a content : Json) : VResult :=
  validateIn env.registry a env.base 64 a content draft04Ajv4

/-- One step of `runTests` for an assertion that is a schema object:
    the subtests it reports and the next action. -/
def runSchema (env : Env) (lvl idx : Nat) (file : String) (a content : Json) :
    List Subtest × Action :=
  let name := s!"{lvl}:{idx} {(strField? a "title").getD ""}"
  let level := levelOf a
  match validateAssertion env a content with
  | .unsupported => ([{ name, file, level, verdict := .undetermined }], .continue_)
  | r =>
    let expected := determineResult a (r == .pass)
    let report := expected || !env.skipFailures.contains level
    ((if report then [{ name, file, level, verdict := if expected then .pass else .fail }] else []),
     determineAction a expected)

/-- `runTests` over one level of assertions. The loop is a tail call with
    an accumulator (the assertion lists are input data). -/
def runLevel (env : Env) (lvl : Nat) (content : Json) :
    List Json → Nat → Action → List Subtest → List Subtest × Action
  | [], _, act, acc => (acc.reverse, act)
  | a :: rest, idx, act, acc =>
    let idx' := idx + 1
    -- A string names an assertion file in the cache.
    let resolved : Option Json := match a with
      | .string f => (env.cache.find? (fun (k, _) => k == f)).map (·.2)
      | j => some j
    match resolved, a with
    | none, .string f =>
        runLevel env lvl content rest idx' act
          ({ name := s!"Processing {f}", level := .must, verdict := .fail } :: acc)
    | some (.object _), _ =>
        let obj := resolved.getD .null
        if (obj.field? "compareWith").isSome then
          runLevel env lvl content rest idx' act
            ({ name := s!"{lvl}:{idx'} comparison object (not run)", level := levelOf obj,
               verdict := .undetermined } :: acc)
        else if act != .continue_ then
          -- JSONtest.js runs no schema after a skip or an abort.
          runLevel env lvl content rest idx' act acc
        else
          let file := match a with
            | .string f => f
            | _ => ""
          let (subs, act') := runSchema env lvl idx' file obj content
          runLevel env lvl content rest idx' act' (subs.reverse ++ acc)
    | _, _ =>
        runLevel env lvl content rest idx' act
          ({ name := s!"{lvl}:{idx'} assertion that is not a schema object (not run)",
             level := .must, verdict := .undetermined } :: acc)

/-- The verdict of a `.test` file on one input: it fails when a reported
    subtest fails, is undetermined when none fails and one is
    undetermined, and passes otherwise. -/
def testVerdict (subs : List Subtest) : Verdict :=
  if subs.any (·.verdict == .fail) then .fail
  else if subs.any (·.verdict == .undetermined) then .undetermined
  else .pass

/-- A `.test` file. -/
structure TestFile where
  path         : String
  name         : String
  assertions   : List Json
  skipFailures : List Level

def TestFile.ofJson (path : String) (j : Json) : TestFile :=
  { path
    name := (strField? j "name").getD path
    assertions := match j.field? "assertions" with
      | some (.array xs) => xs
      | _ => []
    skipFailures := match j.field? "skipFailures" with
      | some (.array xs) => xs.filterMap (fun x => match x with
          | .string s => some (Level.ofString s)
          | _ => none)
      | _ => [] }

/-- Run a `.test` file on one input, as the suite's manual test page does
    when the input is pasted and "Check JSON" is pressed. -/
def runTestFile (env : Env) (t : TestFile) (content : Json) : List Subtest :=
  (runLevel { env with skipFailures := t.skipFailures } 1 content t.assertions 0 .continue_ []).1

/-! ## Which inputs a `.test` file is for

The `.test` descriptions say what to paste: a single Annotation
(`annotations/`), a single Annotation Collection (`collections/`), a single
Annotation Page (`collections/pages/`). The input's `type` decides. -/

/-- The kind of resource a Data Model §3, §5 or §5.1 document describes. -/
inductive Kind where
  | annotation | collection | page | other
  deriving Repr, DecidableEq, BEq

/-- The `type` values of a JSON-LD node (a string or an array of strings). -/
def typesOf (j : Json) : List String :=
  match j.field? "type" with
  | some (.string s) => [s]
  | some (.array xs) => xs.filterMap (fun x => match x with
      | .string s => some s
      | _ => none)
  | _ => []

/-- Data Model §3.1, §5.1, §5.2: the class names in the `anno.jsonld`
    context (`Annotation`, `AnnotationCollection`, `AnnotationPage`). -/
def kindOf (j : Json) : Kind :=
  let ts := typesOf j
  if ts.contains "Annotation" then .annotation
  else if ts.contains "AnnotationCollection" then .collection
  else if ts.contains "AnnotationPage" then .page
  else .other

/-- The kind of input a `.test` file is for, from its directory. -/
def kindForTestPath (p : String) : Kind :=
  if p.startsWith "annotations/" then .annotation
  else if p.startsWith "collections/pages/" then .page
  else if p.startsWith "collections/" then .collection
  else .other

end L4Factoidal.WebAnnotation
