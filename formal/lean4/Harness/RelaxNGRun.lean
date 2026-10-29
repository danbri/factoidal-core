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

The second suite is `third_party/testing/relaxng/compacttest.xml`, for the
RELAX NG Compact Syntax (OASIS Committee Specification 21 November 2002).
A `testCase` holds a `<compact>` part, with an `<incorrect>` or a
`<correct>` schema in the compact syntax, and for a correct one an `<xml>`
part with the same schema in the XML syntax. Each test case is one counted
case:

  * `N-incorrect`: `Compact.simplifyCompact` refuses the compact schema;
  * `N-correct`: the translation of the compact schema is strictly
    equivalent to the XML schema (§6.2; `Compact.strictForm`, which leaves
    out annotations), or both schemas simplify and their simplified grammars
    are loosely equivalent (§6.3; `Compact.looseEq`). The first test is
    needed because several schemas of the suite are not correct full RELAX
    NG schemas (for example a top-level `empty`, which §7.1 prohibits); the
    second because several XML schemas of the suite were written by Trang,
    which leaves out a `group` that §4.12 removes and the `text` of an
    `attribute`.

Resources of the `<compact>` part are compact schemas (their text is read
as it is); those of the `<xml>` part are XML.

Usage: `lake exe l4relaxng [spectest.xml [compacttest.xml]] [--list]
[--allow-fail]`. The last three lines are `RELAX NG spectest: N pass, M
fail (out of T)`, `RELAX NG compacttest: N pass, M fail (out of T)` and the
count of expected failures (`xfailCases`, each with its open issue). Exit 1
when a case fails or an expected failure passes (STALE), unless
`--allow-fail`.
-/
import L4Factoidal.RelaxNG.Validate
import L4Factoidal.RelaxNG.Theorems
import L4Factoidal.RelaxNG.Compact
import L4Factoidal.RelaxNG.CompactTheorems

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

/-- The text of an element's character data children, as it is. -/
def rawText (n : Node) : String :=
  (kidsOf n).foldl (fun acc c => match c with
    | .text s | .cdata s => acc ++ s
    | _ => acc) ""

/-- The `resource` children of a part, by name, with their raw text. -/
def compactResources (part : Node) : List (String × String) :=
  ((kidsOf part).filter (fun c => nameOf c == "resource")).map
    (fun c => ((attrOf c "name").getD "", rawText c))

/-- The first child element with this name. -/
def childNamed (n : Node) (nm : String) : Option Node :=
  (kidsOf n).find? (fun c => nameOf c == nm)

/-- Run one test case of `compacttest.xml`. -/
def runCompactCase (idx : Nat) (tc : Node) : Outcome :=
  match childNamed tc "compact" with
  | none => { id := s!"{idx}", pass := false, msg := "no compact part" }
  | some cp =>
    let cres := compactResources cp
    let cresolve (h : String) : Option String := cres.lookup h
    match childNamed cp "incorrect", childNamed cp "correct" with
    | some inc, _ =>
      let ok := !(Compact.simplifyCompact cresolve "" (rawText inc)).isOk
      { id := s!"{idx}-incorrect", pass := ok, msg := "compact schema accepted, expected incorrect" }
    | none, some cor =>
      let xpart := childNamed tc "xml"
      let xres := match xpart with | some xp => resources 8 "" (kidsOf xp) | none => []
      -- an `x.rng` that the XML part names but does not hold is the
      -- translation of the compact resource `x.rnc`
      let xresolve (h : String) : Option String :=
        match xres.lookup h with
        | some t => some t
        | none =>
          if h.endsWith ".rng" then
            (cres.lookup (String.ofList (h.toList.take (h.length - 4)) ++ ".rnc")).bind
              (fun t => (Compact.translateToXml t).toOption)
          else none
      let xroot : Option Node := xpart.bind (fun xp => (childNamed xp "correct").bind firstElem)
      match xroot with
      | none => { id := s!"{idx}-correct", pass := false, msg := "no xml schema" }
      | some xr =>
        -- §6.2: the translation is strictly equivalent to the XML schema
        let sc := Compact.strictFormCompact cresolve "" (rawText cor)
        let sx := Compact.strictForm xresolve "" xr
        -- §6.3: or both simplify, to loosely equivalent grammars
        let gc := Compact.simplifyCompact cresolve "" (rawText cor)
        let gx := simplifyNode xresolve "" xr
        let loose := match gc, gx with
          | .ok g, .ok h => Compact.looseEq g h
          | _, _ => false
        match sc, sx with
        | .ok a, .ok b =>
          { id := s!"{idx}-correct", pass := a == b || loose,
            msg := s!"neither strictly nor loosely equivalent to the XML schema:\n  {a}\n  {b}" }
        | .error m, _ => { id := s!"{idx}-correct", pass := false, msg := s!"compact schema refused: {m}" }
        | _, .error m => { id := s!"{idx}-correct", pass := false, msg := s!"xml schema refused: {m}" }
    | none, none => { id := s!"{idx}", pass := false, msg := "no schema" }

/-- Expected failures: cases that fail today, each with the open issue of
the shortfall. A case that passes is STALE and fails the run, so that it is
turned into an ordinary assertion and its issue closed. Each is (id,
issue, schema, document, whether the document is valid). -/
def xfailCases : List (String × String × String × String × Bool) :=
  [("dtdcompat-duplicate-id", "https://github.com/danbri/factoidal/issues/1199",
    "<element name=\"doc\" xmlns=\"http://relaxng.org/ns/structure/1.0\" " ++
      "datatypeLibrary=\"http://relaxng.org/ns/compatibility/datatypes/1.0\">" ++
      "<oneOrMore><element name=\"x\"><attribute name=\"id\"><data type=\"ID\"/>" ++
      "</attribute></element></oneOrMore></element>",
    "<doc><x id=\"a\"/><x id=\"a\"/></doc>", false)]

/-- Run one expected-failure case: does it pass? -/
def xfailPasses (schema doc : String) (valid : Bool) : Bool :=
  match simplifyText (fun _ => none) "" schema, parseXML doc with
  | .ok g, .ok d => validNode g d.root == valid
  | _, _ => false

end Harness.RelaxNGRun

open Harness.RelaxNGRun in
def main (args : List String) : IO UInt32 := do
  let list := args.contains "--list"
  let allowFail := args.contains "--allow-fail"
  let paths := args.filter (fun a => !a.startsWith "--")
  let path := paths.headD "../../third_party/testing/relaxng/spectest.xml"
  let cpath := (paths.drop 1).headD "../../third_party/testing/relaxng/compacttest.xml"
  let txt ← IO.FS.readFile path
  let ctxt ← IO.FS.readFile cpath
  match parseXML txt, parseXML ctxt with
  | .error e, _ =>
    IO.eprintln s!"{path}: not well-formed: {e.message}"
    return 2
  | _, .error e =>
    IO.eprintln s!"{cpath}: not well-formed: {e.message}"
    return 2
  | .ok d, .ok cd =>
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
    let mut cpass := 0
    let mut cfail := 0
    idx := 0
    for tc in testCases 16 cd.root do
      idx := idx + 1
      let o := runCompactCase idx tc
      if o.pass then cpass := cpass + 1 else cfail := cfail + 1
      if list then IO.println s!"compact {o.id} {if o.pass then "PASS" else "FAIL"}"
      else if !o.pass then IO.println s!"FAIL compact {o.id} {o.msg}"
    let mut stale := 0
    for (xid, issue, sch, doc, v) in xfailCases do
      if xfailPasses sch doc v then
        stale := stale + 1
        IO.println s!"STALE expected failure {xid} ({issue}): it passes now"
      else if list then IO.println s!"xfail {xid} XFAIL ({issue})"
    IO.println s!"RELAX NG spectest: {pass} pass, {fail} fail (out of {pass + fail})"
    IO.println s!"RELAX NG compacttest: {cpass} pass, {cfail} fail (out of {cpass + cfail})"
    IO.println s!"RELAX NG expected failures: {xfailCases.length - stale} (out of {xfailCases.length}), {stale} stale"
    return (if (fail > 0 || cfail > 0 || stale > 0) && !allowFail then 1 else 0)
