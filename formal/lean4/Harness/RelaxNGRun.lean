/-
Harness/RelaxNGRun — the RELAX NG test suite of James Clark
(`third_party/testing/relaxng/spectest.xml`, for the RELAX NG Specification
of 3 December 2001 = ISO/IEC 19757-2:2008) against
`L4Factoidal.RelaxNG`.

The suite is one XML document. A `testCase` holds `resource` elements
(files a schema may name with `href`; `dir` elements give their
directories), then either `<incorrect>` with a schema that must be refused,
or `<correct>` with a schema that must be accepted, followed by `<valid>`
and `<invalid>` documents. Each of these is one counted case:

  * `N-incorrect`: the schema is refused;
  * `N-correct`: the schema is accepted;
  * `N-validK` / `N-invalidK`: the K-th valid (invalid) document of test
    case N is valid (invalid). When the schema was not accepted these
    cases fail too.

The schema and the documents are the element child of their wrapper,
taken from the parsed suite (so the suite's internal entity `&dii;` is
already expanded). Resources are written back to XML text and read by the
simplifier through its resolver, by their path from the test case
(`dir/name`).

Usage: `lake exe l4relaxng [spectest.xml] [--list] [--allow-fail]`. The
last line is `RELAX NG spectest: N pass, M fail (out of T)`. Exit 1 when a
case fails, unless `--allow-fail`.
-/
import L4Factoidal.RelaxNG.Validate
import L4Factoidal.RelaxNG.Theorems

open L4Factoidal.XML
open L4Factoidal.RelaxNG

namespace Harness.RelaxNGRun

/-- Character data escaped for element content. -/
def escText (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '&' => acc ++ "&amp;" | '<' => acc ++ "&lt;" | '>' => acc ++ "&gt;"
    | '\r' => acc ++ "&#13;" | c => acc.push c) ""

/-- Character data escaped for an attribute value (whitespace kept as
character references, so that attribute value normalization leaves it). -/
def escAttr (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '&' => acc ++ "&amp;" | '<' => acc ++ "&lt;" | '"' => acc ++ "&quot;"
    | '\t' => acc ++ "&#9;" | '\n' => acc ++ "&#10;" | '\r' => acc ++ "&#13;"
    | c => acc.push c) ""

/-- An element written back as XML text. -/
def ser (acc : String) : Node → String
  | .text s | .cdata s => acc ++ escText s
  | .element t as ks =>
    let open_ := as.foldl (fun a at_ => a ++ " " ++ at_.name ++ "=\"" ++ escAttr at_.value ++ "\"")
      (acc ++ "<" ++ t)
    ks.foldl (fun a k => ser a k) (open_ ++ ">") ++ "</" ++ t ++ ">"
  | _ => acc
termination_by n => n

/-- The local name of an element node. -/
def nameOf : Node → String
  | .element t _ _ => t
  | _ => ""

def kidsOf : Node → List Node
  | .element _ _ ks => ks
  | _ => []

def attrOf (n : Node) (k : String) : Option String :=
  match n with
  | .element _ as _ => (as.find? (fun a => a.name == k)).map (·.value)
  | _ => none

/-- The first element child. -/
def firstElem (n : Node) : Option Node :=
  (kidsOf n).find? (fun c => match c with | .element .. => true | _ => false)

/-- The resources of a test case, with their paths. `fuel` bounds the
`dir` nesting. -/
def resources : Nat → String → List Node → List (String × String)
  | 0, _, _ => []
  | f + 1, pfx, ns => ns.foldl (fun acc c =>
      match nameOf c with
      | "resource" =>
        let body := match firstElem c with
          | some e => ser "" e
          | none => (kidsOf c).foldl ser ""
        acc ++ [(pfx ++ (attrOf c "name").getD "", body)]
      | "dir" => acc ++ resources f (pfx ++ (attrOf c "name").getD "" ++ "/") (kidsOf c)
      | _ => acc) []

/-- One counted case: its id, whether it passed, and a message. -/
structure Outcome where
  id : String
  pass : Bool
  msg : String

/-- Run one test case. -/
def runCase (idx : Nat) (tc : Node) : List Outcome := Id.run do
  let kids := kidsOf tc
  let res := resources 8 "" kids
  let resolve (h : String) : Option String := res.lookup h
  let sections := (kids.filter (fun c => nameOf c == "section")).map
    (fun c => (kidsOf c).foldl ser "")
  let sec := String.intercalate "," sections
  let mut out : Array Outcome := #[]
  let mut grammar : Option Grammar := none
  let mut nv := 0
  let mut ni := 0
  for c in kids do
    match nameOf c with
    | "incorrect" =>
      let r := match firstElem c with
        | some s => simplifyNode resolve "" s
        | none => .error "no schema"
      out := out.push { id := s!"{idx}-incorrect", pass := !r.isOk,
                        msg := s!"[{sec}] schema accepted, expected incorrect" }
    | "correct" =>
      let r := match firstElem c with
        | some s => simplifyNode resolve "" s
        | none => .error "no schema"
      match r with
      | .ok g =>
        grammar := some g
        out := out.push { id := s!"{idx}-correct", pass := true, msg := "" }
      | .error m =>
        out := out.push { id := s!"{idx}-correct", pass := false,
                          msg := s!"[{sec}] schema refused: {m}" }
    | "valid" =>
      nv := nv + 1
      let ok := match grammar, firstElem c with
        | some g, some d => validNode g d
        | _, _ => false
      out := out.push { id := s!"{idx}-valid{nv}", pass := ok,
                        msg := s!"[{sec}] valid document judged invalid" }
    | "invalid" =>
      ni := ni + 1
      let ok := match grammar, firstElem c with
        | some g, some d => !validNode g d
        | _, _ => false
      out := out.push { id := s!"{idx}-invalid{ni}", pass := ok,
                        msg := s!"[{sec}] invalid document judged valid" }
    | _ => pure ()
  return out.toList

/-- The test cases of the suite, in document order. -/
def testCases : Nat → Node → List Node
  | 0, _ => []
  | f + 1, n => (kidsOf n).foldl (fun acc c =>
      match nameOf c with
      | "testCase" => acc ++ [c]
      | "testSuite" => acc ++ testCases f c
      | _ => acc) []

end Harness.RelaxNGRun

open Harness.RelaxNGRun in
def main (args : List String) : IO UInt32 := do
  let list := args.contains "--list"
  let allowFail := args.contains "--allow-fail"
  let path := (args.filter (fun a => !a.startsWith "--")).headD
    "../../third_party/testing/relaxng/spectest.xml"
  let txt ← IO.FS.readFile path
  match parseXML txt with
  | .error e =>
    IO.eprintln s!"{path}: not well-formed: {e.message}"
    return 2
  | .ok d =>
    let cases := testCases 16 d.root
    let mut pass := 0
    let mut fail := 0
    let mut idx := 0
    for tc in cases do
      idx := idx + 1
      for o in runCase idx tc do
        if o.pass then pass := pass + 1 else fail := fail + 1
        if list then IO.println s!"{o.id} {if o.pass then "PASS" else "FAIL"}"
        else if !o.pass then IO.println s!"FAIL {o.id} {o.msg}"
    IO.println s!"RELAX NG spectest: {pass} pass, {fail} fail (out of {pass + fail})"
    return (if fail > 0 && !allowFail then 1 else 0)
