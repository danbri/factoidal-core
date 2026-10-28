/-
Harness/Xslt4Run — the xslt40-test (QT4 Community Group XSLT 4.0 test
suite, https://github.com/qt4cg/xslt40-test) runner for the XSLT 4.0
processor `L4Factoidal.XSLT4`.

    lake exe l4xslt4 [--root DIR] [--set NAME]... [--dir D]... [--list-fails] [--isolate SECS]

It reads `catalog.xml`, then every test set (or the ones named), and
scores every test case:

* **unsupported** — the test case or its test set has a dependency this
  processor does not satisfy: a spec that excludes XSLT 4.0, a feature
  it does not have (schema awareness, streaming, the namespace axis,
  XML 1.1, ...), an implementation-defined choice it does not make, or
  an environment with a schema, a collection or a package. An
  unsupported test is NEVER a pass;
* **pass** — every assertion holds; an `error` assertion holds only when
  the error raised has the expected code (or the code is `*`);
* **fail** — anything else, including a wrong error code.

Assertions are evaluated as in the catalog's own driver
(`runner/assert.xsl`): `assert` with the result (a document node, the
default delivery format) as context item and `$result` bound;
`assert-xml` by `fn:deep-equal` on the parsed fragments;
`serialization-matches` and `assert-serialization` on the result
serialized with the stylesheet's unnamed output definition;
`assert-message` and `assert-warning` hold (the driver cannot test them
either); `assert-result-document` applies its assertions to the
secondary result with that URI.

The test data is untrusted input: stylesheets run only in this
processor, with no I/O except the reading of files under the suite
root before the run.
-/
import L4Factoidal.XSLT4.Transform
import L4Factoidal.XSLT4.Theorems
import L4Factoidal.XSLT.Transform
import L4Factoidal.XML.Canonical
import Lean.Data.Json

open L4Factoidal.XPath4
open L4Factoidal.XSLT4
open L4Factoidal.XML

namespace Harness.Xslt4Run

def localTag (n : Node) : String :=
  match n.elementTag with
  | some t => (splitName t).2
  | none => ""

def kids (n : Node) : List Node := n.allChildElements
def kidsNamed (n : Node) (l : String) : List Node := (kids n).filter (fun c => localTag c == l)
def attr (n : Node) (a : String) : Option String := findAttr a n.elementAttrs
def attrD (n : Node) (a : String) (d : String := "") : String := (attr n a).getD d

def dirOf (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => "."
  | ps => String.intercalate "/" ps

/-- Read a file as text: UTF-8, or else decoded by its XML encoding
    declaration (XML 1.0 §4.3.3, `XML.decodeXmlBytes`). -/
def readFileSafe (p : String) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ =>
    try
      let bs ← IO.FS.readBinFile p
      match L4Factoidal.XML.decodeXmlBytes bs with
      | .ok t => pure (some t)
      | .error _ => pure none
    catch _ => pure none

/-- Normalise a file path (`a/./b/../c` to `a/c`). -/
def normPath (p : String) : String := Id.run do
  let abs := p.startsWith "/"
  let mut out : List String := []
  for seg in p.splitOn "/" do
    if seg == "." || seg == "" then continue
    if seg == ".." then
      match out with
      | _ :: r => out := r
      | [] => pure ()
    else out := seg :: out
  return (if abs then "/" else "") ++ String.intercalate "/" out.reverse

def fileUri (path : String) : String := "file://" ++ normPath path
def uriPath (u : String) : String := if u.startsWith "file://" then (u.drop 7).toString else u

/-! ## Dependencies -/

def specOk (v : String) : Bool :=
  (v.splitOn " ").any (fun t =>
    if t.startsWith "XSLT" then
      let rest := (t.drop 4).toString
      let plus := rest.endsWith "+"
      let num := (if plus then (rest.dropEnd 1).toString else rest).toNat?
      match num with
      | some k => k == 40 || (plus && k ≤ 40)
      | none => false
    else false)

/-- The features this processor has. -/
def featureSupported (f : String) : Bool :=
  ["higher_order_functions", "serialization", "backwards_compatibility", "dynamic_evaluation",
   "XPath_3.1", "XSD_1.1", "HTML5", "built_in_derived_types"].contains f

def depOk (d : Node) : Bool :=
  let ty := localTag d
  let v := attrD d "value"
  let sat := attrD d "satisfied" "true" != "false"
  match ty with
  | "spec" => specOk v
  | "feature" =>
      let fs := v.splitOn " "
      if sat then fs.all featureSupported else !(fs.all featureSupported)
  | "on-multiple-match" => if sat then v == "use-last" else v != "use-last"
  | "default_html_version" => if sat then v == "5" else v != "5"
  -- xsl:use-package picks the highest version that matches (§3.4.2)
  | "package_version_resolution" => if sat then v == "highest_version" else v != "highest_version"
  | _ => !sat

/-! ## Environments -/

structure EnvSpec where
  /-- (role, file path, uri, inline content) -/
  sources : List (String × String × String × Option String) := []
  stylesheets : List (String × String) := []    -- file, role
  /-- `<package>`: file, role, name (`uri`), version. -/
  packages : List (String × String × String × String) := []
  params : List (String × String × Bool) := []   -- name, select, static
  unsupported : Option String := none
  serialize : Bool := false
deriving Inhabited

def parseEnv (dir : String) (e : Node) : EnvSpec := Id.run do
  let mut s : EnvSpec := {}
  for c in kids e do
    match localTag c with
    | "source" =>
        if attrD c "validation" == "strict" || attrD c "validation" == "lax" then
          s := { s with unsupported := some "schema-validated source" }
        let content := match (kidsNamed c "content").head? with
          | some k => some k.textContent
          | none => none
        let file := match attr c "file" with
          | some f => normPath (dir ++ "/" ++ f)
          | none => ""
        s := { s with sources := s.sources ++ [(attrD c "role", file, attrD c "uri", content)] }
    | "stylesheet" => s := { s with stylesheets := s.stylesheets ++ [(normPath (dir ++ "/" ++ attrD c "file"), attrD c "role")] }
    | "param" =>
        let st := ["yes", "true", "1"].contains (attrD c "static")
        s := { s with params := s.params ++ [(attrD c "name", attrD c "select" "()", st)] }
    | "schema" => s := { s with unsupported := some "schema" }
    | "collection" => s := { s with unsupported := some "collection" }
    | "package" =>
        s := { s with packages := s.packages ++ [(normPath (dir ++ "/" ++ attrD c "file"), attrD c "role",
          (attrD c "uri").trimAscii.toString, (attrD c "package-version" "1").trimAscii.toString)] }
    | "output" => if attrD c "serialize" == "yes" then s := { s with serialize := true }
    | _ => pure ()
  pure s

/-! ## Outcomes -/

inductive Outcome where
  | pass
  | fail (why : String)
  | unsupported (why : String)
deriving Inhabited

def escText (s : String) : String :=
  String.join (s.toList.map (fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '\r' => "&#xD;" | c => String.ofList [c]))

def escAttr (s : String) : String :=
  String.join (s.toList.map (fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '"' => "&quot;" | '\n' => "&#xA;" | '\t' => "&#x9;" | '\r' => "&#xD;" | c => String.ofList [c]))

def cut (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
def sh (s : Seq) (n : Nat) : String := cut (showSeq s) n

def stringValueOf (env : Env) (s : Seq) : String :=
  String.intercalate " " (s.map (fun i => match i with
    | .atom a => a.str
    | .node n => env.nodeString n
    | _ => ""))

def normSp (s : String) : String :=
  String.intercalate " " ((String.ofList (s.toList.map (fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c))).splitOn " " |>.filter (· != ""))

def evalIn (env : Env) (src : String) : M Seq := do
  let e ← parseXPath src env.ns
  eval 20000 env e

/-- The XML of a result, for `assert-xml` (namespaces declared where
    they are used, so the expected and the actual trees compare by
    expanded names). -/
def serNode (env : Env) : Nat → NodeRef → String
  | 0, _ => ""
  | f + 1, n =>
    let r := env.nrec n
    match r.kind with
    | .document => String.join (r.children.toList.map (fun c => serNode env f (n.at (c))))
    | .text => escText r.value
    | .comment => "<!--" ++ r.value ++ "-->"
    | .pi => "<?" ++ r.name.loc ++ (if r.value == "" then "" else " " ++ r.value) ++ "?>"
    | .attribute => r.name.show ++ "=\"" ++ escAttr r.value ++ "\""
    | .namespace => ""
    | .element =>
      let nm := r.name.show
      let decl := " xmlns" ++ (if r.name.pfx == "" then "" else ":" ++ r.name.pfx) ++ "=\"" ++ escAttr r.name.uri ++ "\""
      let decl := if r.name.uri == "" && r.name.pfx != "" then "" else decl
      let ats := r.attrs.toList.map (fun a =>
        let ra := env.nrec (n.at (a))
        let d := if ra.name.uri != "" && ra.name.pfx != "" && ra.name.pfx != "xml" then
          " xmlns:" ++ ra.name.pfx ++ "=\"" ++ escAttr ra.name.uri ++ "\"" else ""
        d ++ " " ++ ra.name.show ++ "=\"" ++ escAttr ra.value ++ "\"")
      let body := String.join (r.children.toList.map (fun c => serNode env f (n.at (c))))
      "<" ++ nm ++ decl ++ String.join ats ++ (if body == "" then "/>" else ">" ++ body ++ "</" ++ nm ++ ">")

def serSeq (env : Env) (s : Seq) : String := Id.run do
  let mut out := ""
  let mut prevAtom := false
  for i in s do
    match i with
    | .atom a =>
        out := out ++ (if prevAtom then " " else "") ++ escText a.str
        prevAtom := true
    | .node n => out := out ++ serNode env 100000 n; prevAtom := false
    | _ => out := out ++ "?"; prevAtom := false
  pure out

def xmlEq1 (env : Env) (got : Seq) (expected : String) (trim : Bool := false) : Bool :=
  let gs := serSeq env got
  let gs := if trim then gs.trimAscii.toString else gs
  match Doc.ofString ("<w>" ++ gs ++ "</w>"), Doc.ofString ("<w>" ++ expected ++ "</w>") with
  | .ok d1, .ok d2 =>
    let e2 : Env := { docs := #[d1, d2] }
    let root1 := (d1.get 0).children.getD 0 0
    let root2 := (d2.get 0).children.getD 0 0
    e2.nodeDeepEq 100000 (NodeRef.mk' 0 root1) (NodeRef.mk' 1 root2)
  | _, _ => gs == expected

/-- `assert-xml`: also with the whitespace around the expected XML
    removed. -/
def xmlEq (env : Env) (got : Seq) (expected : String) : Bool :=
  xmlEq1 env got expected || xmlEq1 env got expected.trimAscii.toString ||
  -- whitespace around the top-level nodes of the result is not part of
  -- the fragment the assertion gives
  xmlEq1 env got expected.trimAscii.toString true

def codeMatches (expected got : String) : Bool :=
  expected == "*" || expected == got || ("err:" ++ got) == expected || expected.endsWith (":" ++ got) ||
  expected == "Q{http://www.w3.org/2005/xqt-errors}" ++ got || got.endsWith ("}" ++ expected)

/-- What an assertion sees: the delivered result, the raw result, the
    secondary results, and the serializer of the stylesheet. -/
structure RCtx where
  env : Env
  res : M Seq
  secondary : List (String × Seq × (Seq → M String))
  ser : Seq → M String

def checkAssert (rc : RCtx) : Nat → Node → Outcome
  | 0, _ => .fail "assertion nesting"
  | f + 1, a =>
    let env := rc.env
    let res := rc.res
    let txt := a.textContent
    let ok? (b : Bool) (why : String) : Outcome := if b then .pass else .fail why
    match localTag a with
    | "error" =>
        let code := attrD a "code"
        match res with
        | .error e => ok? (codeMatches code e.code) ("wrong error code " ++ e.code ++ " (expected " ++ code ++ "): " ++ cut e.msg 100)
        | .ok s => .fail ("expected error " ++ code ++ ", got " ++ (sh s 80))
    | "any-of" =>
        let rs := (kids a).map (fun c => checkAssert rc f c)
        if rs.any (fun r => match r with | .pass => true | _ => false) then .pass
        else .fail ("any-of: " ++ String.intercalate "; " (rs.map (fun r => match r with | .fail w => w | _ => "")))
    | "all-of" =>
        let rs := (kids a).map (fun c => checkAssert rc f c)
        match rs.find? (fun r => match r with | .pass => false | _ => true) with
        | some r => r
        | none => .pass
    | "not" =>
        match (kids a).head? with
        | some c => match checkAssert rc f c with
          | .pass => .fail "not: inner assertion held"
          | _ => .pass
        | none => .fail "empty not"
    | "assert-message" | "assert-warning" => .pass
    | "assert-serialization-error" =>
        let code := attrD a "code"
        match res with
        | .error e => ok? (codeMatches code e.code) ("wrong error code " ++ e.code ++ " (expected " ++ code ++ ")")
        | .ok s =>
          match rc.ser s with
          | .error e => ok? (codeMatches code e.code) ("wrong serialization error " ++ e.code ++ " (expected " ++ code ++ ")")
          | .ok out => .fail ("expected serialization error " ++ code ++ ", got " ++ cut out 80)
    | "assert-result-document" =>
        let u := attrD a "uri"
        match res with
        | .error e => .fail ("error " ++ e.code ++ ": " ++ cut e.msg 100)
        | .ok _ =>
          match rc.secondary.find? (fun (h, _) => h == u || h.endsWith ("/" ++ u)) with
          | none => .fail ("no result document " ++ u ++ " (have: " ++ String.intercalate ", " (rc.secondary.map (·.1)) ++ ")")
          | some (_, v, sr) =>
            let rc' := { rc with res := .ok v, ser := sr }
            let rs := (kids a).map (fun c => checkAssert rc' f c)
            match rs.find? (fun r => match r with | .pass => false | _ => true) with
            | some r => r
            | none => .pass
    | tag =>
      match res with
      | .error e => .fail ("error " ++ e.code ++ ": " ++ cut e.msg 120)
      | .ok s =>
      let envR := env.bind { uri := "", loc := "result" } s
      let envR := match s with
        | [_] => { envR with ctx := some s, pos := 1, size := 1 }
        | [] => envR
        | _ => envR
      match tag with
      | "assert-true" => ok? (match s with | [.atom ⟨_, .bool true⟩] => true | _ => false) ("got " ++ (sh s 80))
      | "assert-false" => ok? (match s with | [.atom ⟨_, .bool false⟩] => true | _ => false) ("got " ++ (sh s 80))
      | "assert-empty" => ok? (s.isEmpty || (match s with
          | [.node n] => (env.nrec n).kind == .document && (env.nrec n).children.isEmpty
          | _ => false)) ("got " ++ (sh s 80))
      | "assert-count" => ok? (s.length == (txt.trimAscii.toString.toNat?).getD 0) ("count " ++ toString s.length)
      | "assert-string-value" =>
          let got := stringValueOf env s
          -- the XSLT catalog's driver always normalizes space here
          -- (runner/assert.xsl)
          let ok := normSp got == normSp txt
          ok? ok ("string value '" ++ (cut got 80) ++ "'")
      | "assert-eq" =>
          match evalIn env txt with
          | .ok exp =>
            match s, exp with
            | [.atom x], [.atom y] =>
              let ok := match atomicCmp (if x.ty == .untyped then Atomic.ofStr x.str else x) y env.tz with
                | .ok (some .eq) => true | _ => false
              ok? ok ("got " ++ x.str ++ ", expected " ++ y.str)
            | _, _ => .fail ("got " ++ (sh s 80))
          | .error e => .fail ("could not evaluate expected value: " ++ e.code)
      | "assert-deep-eq" =>
          match evalIn env txt with
          | .ok exp => ok? (env.deepEq s exp) ("got " ++ (sh s 80) ++ ", expected " ++ (sh exp 80))
          | .error e => .fail ("could not evaluate expected value: " ++ e.code ++ " " ++ e.msg)
      | "assert" =>
          match evalIn envR txt with
          | .ok r =>
            match ebv r with
            | .ok true => .pass
            | _ => .fail ("assert {" ++ cut txt 80 ++ "} gave " ++ (sh r 60) ++ " for result " ++ cut (serSeq env s) 100)
          | .error e => .fail ("assert {" ++ cut txt 60 ++ "} raised " ++ e.code ++ " " ++ cut e.msg 80 ++ " for result " ++ cut (serSeq env s) 100)
      | "assert-type" =>
          match parseSeqType txt with
          | .ok t => ok? (env.seqMatches s t) ("type mismatch: got " ++ (sh s 60))
          | .error e => .fail ("bad type in assert-type: " ++ e.msg)
      | "serialization-matches" =>
          match rc.ser s with
          | .error e => .fail ("serialization raised " ++ e.code ++ " " ++ e.msg)
          | .ok out =>
            let q : QN := { uri := "", loc := "l4ser" }
            let pq : QN := { uri := "", loc := "l4pat" }
            let fq : QN := { uri := "", loc := "l4flags" }
            let envM := (((({} : Env).bind q (sStr out)).bind pq (sStr txt)).bind fq (sStr (attrD a "flags")))
            match evalIn envM "matches($l4ser, $l4pat, $l4flags)" with
            | .ok [.atom ⟨_, .bool true⟩] => .pass
            | .ok _ => .fail ("serialization '" ++ cut out 120 ++ "' does not match " ++ cut txt 60)
            | .error e => .fail ("serialization-matches raised " ++ e.code)
      | "assert-serialization" =>
          match rc.ser s with
          | .error e => .fail ("serialization raised " ++ e.code ++ " " ++ e.msg)
          | .ok out =>
            let ok := if attrD a "normalize-space" == "true" then normSp out == normSp txt
              else out == txt || xmlEq env s txt
            ok? ok ("serialization '" ++ cut out 120 ++ "'")
      | "assert-xml" =>
          ok? (xmlEq env s txt) ("xml " ++ (cut (serSeq env s) 600))
      | other => .fail ("assertion " ++ other ++ " is not evaluated")

/-- The assert-xml expected value is the element's inner markup. -/
def innerXml : Nat → Node → String
  | 0, _ => ""
  | f + 1, n =>
    match n with
    | .element _ _ cs => String.join (cs.map (fun c => match c with
        | .text t => escText t
        | .cdata t => t
        | .comment b => "<!--" ++ b ++ "-->"
        | .pi t d => "<?" ++ t ++ " " ++ d ++ "?>"
        | .element tag ats _ =>
            "<" ++ tag ++ String.join (ats.map (fun x => " " ++ x.name ++ "=\"" ++ escAttr x.value ++ "\""))
              ++ ">" ++ innerXml f c ++ "</" ++ tag ++ ">"))
    | _ => ""

def fixXml : Nat → Node → Node
  | 0, n => n
  | f + 1, n =>
    match n with
    | .element tag ats cs =>
        if (splitName tag).2 == "assert-xml" then .element tag ats [.text (innerXml 1000 n)]
        else .element tag ats (cs.map (fixXml f))
    | other => other

/-- Read the expected XML of each `assert-xml file="..."`. -/
def resolveXmlFiles (dir : String) : Nat → Node → IO Node
  | 0, n => pure n
  | f + 1, n =>
    match n with
    | .element tag ats cs => do
      if (splitName tag).2 == "assert-xml" || (splitName tag).2 == "assert-serialization" then
        match ats.find? (fun x => x.name == "file") with
        | some fa =>
          match ← readFileSafe (normPath (dir ++ "/" ++ fa.value)) with
          | none => pure n
          | some txt =>
            let txt := if (splitName tag).2 == "assert-xml" && txt.startsWith "<?xml" then
                match txt.splitOn "?>" with
                | _ :: rest => String.intercalate "?>" rest
                | [] => txt
              else txt
            pure (.element tag (ats.filter (fun x => x.name != "file")) [.text (txt.replace "\r" "")])
        | none => pure n
      else
        pure (.element tag ats (← cs.mapM (resolveXmlFiles dir f)))
    | other => pure other

/-! ## Running -/

/-! ## Defective test data

xslt40-test cases whose expected result contradicts the normative text
of XSLT 4.0 (defective test data, `skills/test-suites/SKILL.md`
§ Defective test data). They are reported apart as "excluded (defective
test data)", not in pass, fail or the total; a case on this list that
PASSES counts as a FAIL, so the exclusion cannot outlive a corrected
test. -/

/-- `(test-case name, issue URL)`. -/
def defective : List (String × String) :=
  let i1163 := "https://github.com/danbri/factoidal/issues/1163"
  -- default priorities of 4.0 patterns (§6.4.4, §6.4.6, §6.4.7); a
  -- function result type error; a non-public initial template in a
  -- package (§2.3.4); Saxon's code for a recursive item type (XTSE4035);
  -- a static error in xsl:evaluate (XTDE3160)
  [ "priority-124", "priority-141", "priority-160", "priority-162", "priority-163",
    "function-40-012", "accumulator-038", "type-alias-003", "type-alias-004",
    "evaluate-042" ].map (·, i1163)

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  unsup : Nat := 0
  /-- Defective test data (`defective`): not in the total. -/
  excl : Nat := 0
deriving Inhabited

def Tally.add (a b : Tally) : Tally := ⟨a.pass + b.pass, a.fail + b.fail, a.unsup + b.unsup, a.excl + b.excl⟩
def Tally.total (t : Tally) : Nat := t.pass + t.fail + t.unsup
def Tally.show (t : Tally) : String :=
  s!"{t.pass} pass, {t.fail} fail, {t.unsup} unsupported (out of {t.total})"
    ++ (if t.excl > 0 then s!"; {t.excl} excluded (defective test data)" else "")

structure Opts where
  root : String := "../../third_party/testing/xslt40-test"
  sets : List String := []
  dirs : List String := []
  listFails : Bool := false
  isolate : Option Nat := none
  progress : Option String := none
  childMode : Bool := false
  only : Option String := none
  /-- Skip the test cases up to and including this one. -/
  after : Option String := none
  /-- Compare with the XSLT 1.0 engine on the corpus in this directory
      (`manifest.json` of `third_party/testing/xslt` form). -/
  xslt10 : Option String := none

def parseArgs : List String → Opts → Opts
  | "--root" :: r :: rest, o => parseArgs rest { o with root := r }
  | "--set" :: s :: rest, o => parseArgs rest { o with sets := o.sets ++ [s] }
  | "--dir" :: s :: rest, o => parseArgs rest { o with dirs := o.dirs ++ [s] }
  | "--list-fails" :: rest, o => parseArgs rest { o with listFails := true }
  | "--isolate" :: n :: rest, o => parseArgs rest { o with isolate := n.toNat? }
  | "--progress" :: f :: rest, o => parseArgs rest { o with progress := some f, childMode := true }
  | "--test" :: t :: rest, o => parseArgs rest { o with only := some t }
  | "--after" :: t :: rest, o => parseArgs rest { o with after := some t }
  | "--xslt10" :: d :: rest, o => parseArgs rest { o with xslt10 := some d }
  | _ :: rest, o => parseArgs rest o
  | [], o => o

/-- Read a stylesheet and the modules it includes or imports. -/
def loadModules (principal : String) : IO (List (String × String)) := do
  let mut done : List (String × String) := []
  let mut todo : List String := [principal]
  for _ in [0:200] do
    match todo with
    | [] => break
    | u :: rest =>
      todo := rest
      if done.any (·.1 == u) then continue
      match ← readFileSafe (uriPath u) with
      | none => pure ()
      | some txt =>
        done := done ++ [(u, txt)]
        for r in moduleRefs u txt ++ packageRefs u txt do
          if !done.any (·.1 == r) then todo := todo ++ [r]
  return done

/-- The files that a text names by a relative reference (for `doc`,
    `document`, `unparsed-text`, `json-doc`), read in advance: every run
    of path characters that names a file under the suite root. -/
def scanResources (root dir src : String) : IO (List (String × String)) := do
  let isPathChar (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '/' || c == '-'
  let mut toks : List String := []
  let mut cur : String := ""
  for c in src.toList ++ [' '] do
    if isPathChar c then cur := cur.push c
    else
      if cur.length > 2 && cur.length < 200 && (cur.splitOn ".").length > 1 && !toks.contains cur then
        toks := cur :: toks
      cur := ""
  let absRoot := normPath root
  let mut out : List (String × String) := []
  for t in toks do
    let path := normPath (dir ++ "/" ++ t)
    if !path.startsWith absRoot then continue
    if path.endsWith ".xsl" then continue
    if ← System.FilePath.pathExists path then
      if (← System.FilePath.isDir path) then continue
      match ← readFileSafe path with
      | some txt => out := (t, txt) :: (fileUri path, txt) :: out
      | none => pure ()
  return out

/-- The data files (`.xml`, `.json`, `.txt`, `.csv`, `.dtd`) of a
    directory, read in advance, when it has at most 300 entries; files
    above 1 MB are left out. -/
def dirResources (dir : String) : IO (List (String × String)) := do
  let entries ← try System.FilePath.readDir dir catch _ => pure #[]
  if entries.size > 300 then return []
  let mut out : List (String × String) := []
  for e in entries do
    let p := e.path.toString
    let ext := (p.splitOn ".").getLast?.getD ""
    if !["xml", "json", "txt", "csv", "dtd", "ent"].contains ext then continue
    let md ← try some <$> e.path.metadata catch _ => pure none
    match md with
    | some m => if m.byteSize > 1000000 then continue
    | none => continue
    match ← readFileSafe p with
    | some t => out := (fileUri (normPath p), t) :: out
    | none => pure ()
  return out

/-- Parse a source document, as the processor would read it. -/
def loadDoc (txt uri : String) : Option Doc :=
  match Doc.ofString txt uri with
  | .ok d => some d
  | .error _ => none

def runCase (o : Opts) (dir : String) (localEnvs : List (String × EnvSpec)) (tc : Node) : IO Outcome := do
  let envSpec : Option EnvSpec :=
    match (kidsNamed tc "environment").head? with
    | none => some {}
    | some e =>
      match attr e "ref" with
      | some r => localEnvs.lookup r
      | none => some (parseEnv dir e)
  let some spec := envSpec | return .unsupported "unknown environment"
  if let some why := spec.unsupported then return .unsupported why
  let some testNode := (kidsNamed tc "test").head? | return .fail "no test element"
  let tspec := parseEnv dir testNode
  if let some why := tspec.unsupported then return .unsupported why
  let sheets := tspec.stylesheets ++ spec.stylesheets ++
    (tspec.packages ++ spec.packages).filterMap (fun (f, r, _, _) => if r == "principal" then some (f, r) else none)
  let some (principal, _) := sheets.find? (fun (_, r) => r != "secondary") | return .unsupported "no stylesheet"
  let pUri := fileUri principal
  let mut mods ← loadModules pUri
  -- the packages that xsl:use-package can name (§3.4.3)
  let lib : List PkgEntry := (tspec.packages ++ spec.packages).filterMap (fun (f, r, u, v) =>
    if r == "principal" then none else some { name := u, version := v, uri := fileUri f })
  for e in lib do
    mods := mods ++ (← loadModules e.uri).filter (fun (x, _) => !mods.any (·.1 == x))
  -- static parameters
  let mut statics : List (QN × Seq) := []
  for (nm, sel, st) in tspec.params ++ spec.params do
    if st then
      match evalIn {} sel with
      | .ok v => statics := statics ++ [({ uri := "", loc := nm }, v)]
      | .error _ => return .fail ("cannot evaluate static param " ++ nm)
  let r ← resolveXmlFiles dir 100 (fixXml 100000 ((kidsNamed tc "result").head?.getD (.element "result" [] [])))
  let some a := (kids r).head? | return .fail "no assertion"
  -- modules named only through static values (shadow attributes):
  -- read the one the compiler asks for, and compile again
  let mut sheet := compileStylesheet pUri mods statics lib
  for _ in [0:20] do
    match sheet with
    | .error e =>
      if e.code == "XTSE0165" && e.msg.startsWith "cannot read stylesheet module " then
        let u := (e.msg.drop "cannot read stylesheet module ".length).toString
        if mods.any (·.1 == u) then break
        match ← readFileSafe (uriPath u) with
        | some txt =>
          mods := mods ++ (← loadModules u).filter (fun (x, _) => !mods.any (·.1 == x))
          let _ := txt
          sheet := compileStylesheet pUri mods statics lib
        | none => break
      else break
    | .ok _ => break
  let (env, outcome) ← match sheet with
    | .error e => pure (({} : Env), (.error e : M (TResult × Sheet)))
    | .ok S => do
      -- the dynamic context: source documents and resources
      let mut env : Env := { baseUri := pUri }
      let mut globalCtx : Option Item := none
      for (role, file, uri, content) in spec.sources ++ tspec.sources do
        let txt ← match content with
          | some c => pure (some c)
          | none => readFileSafe file
        let some txt := txt | return .fail ("cannot read source " ++ file)
        let duri := if file != "" then fileUri file else if uri != "" then resolveUri pUri uri else ""
        let some d := loadDoc txt duri | return .fail ("source not well-formed: " ++ file)
        let idx := env.docs.size
        env := { env with docs := env.docs.push d }
        if duri != "" then env := { env with docUris := (duri, idx) :: env.docUris }
        if uri != "" then env := { env with docUris := (uri, idx) :: (resolveUri pUri uri, idx) :: env.docUris }
        if role == "." then globalCtx := some (.node (NodeRef.mk' idx 0))
      -- resources named in the stylesheets and the test
      let mut res : List (String × String) := mods.map (fun (u, t) => (u, t))
      for (u, t) in mods do
        res := res ++ (← scanResources o.root (dirOf (uriPath u)) t)
      res := res ++ (← scanResources o.root dir (testNode.textContent ++ String.join ((kids testNode).map (fun k =>
        String.join (k.elementAttrs.map (·.value ++ " "))))))
      -- the small data files of the test set's directory (for URIs that
      -- the stylesheet computes)
      res := res ++ (← dirResources dir).filter (fun (u, _) => !res.any (·.1 == u))
      env := { env with resources := res }
      -- stylesheet parameters
      let mut params : List (QN × Seq) := []
      for (nm, sel, st) in tspec.params ++ spec.params do
        if !st then
          match evalIn env sel with
          | .ok v => params := params ++ [({ uri := "", loc := nm }, v)]
          | .error e => return .fail ("cannot evaluate param " ++ nm ++ ": " ++ e.code)
      let nsOf (n : Node) (s : String) : QN :=
        match s.splitOn ":" with
        | [p, l] =>
          let u := (n.elementAttrs.find? (·.name == "xmlns:" ++ p)).map (·.value)
          let u := u.getD (if p == "xsl" then nsXSL else "")
          { uri := u, loc := l, pfx := p }
        | _ => if s.startsWith "Q{" then
            match (s.drop 2).toString.splitOn "}" with
            | [u, l] => { uri := u, loc := l }
            | _ => { uri := "", loc := s }
          else { uri := "", loc := s }
      let it := (kidsNamed testNode "initial-template").head?.map (fun n => nsOf n (attrD n "name"))
      let im := (kidsNamed testNode "initial-mode").head?
      let imName := im.bind (fun n => (attr n "name").map (fun s =>
        if s == "#default" || s == "#unnamed" then s else (nsOf n s).eqn))
      let imSel ← match im.bind (fun n => attr n "select") with
        | some sel => match evalIn { env with ctx := globalCtx.map (fun i => [i]), pos := 1, size := 1 } sel with
          | .ok v => pure (some v)
          | .error e => return .fail ("cannot evaluate initial-mode select: " ++ e.code)
        | none => pure none
      let ifn ← match (kidsNamed testNode "initial-function").head? with
        | some n => do
          let mut args : List Seq := []
          for p in kidsNamed n "param" do
            match evalIn env (attrD p "select" "()") with
            | .ok v => args := args ++ [v]
            | .error e => return .fail ("cannot evaluate function param: " ++ e.code)
          pure (some (nsOf n (attrD n "name"), args))
        | none => pure none
      -- the base output URI: the test's `<output file="..."/>` against
      -- the test set's directory (`#absent`: none); with no file, the
      -- `results/<test>.xml` of that directory, as the tests that name
      -- a file do
      let ofile := ((kidsNamed testNode "output").findSome? (fun n => attr n "file"))
      let ou := match ofile with
        | some "#absent" => ""
        | some "" => fileUri (dir ++ "/")
        | some f => fileUri (dir ++ "/" ++ f)
        | none => fileUri (dir ++ "/results/" ++ attrD tc "name" ++ ".xml")
      let topts : TOpts := { initialTemplate := it, initialMode := imName, initialSelect := imSel, initialFunction := ifn, globalCtx, params, env, outUri := ou }
      pure (env, (do let r ← transform S topts; pure (r, S) : M (TResult × Sheet)))
  -- delivery (the catalog driver's default format is a document node)
  -- delivery format raw: `output tree="no"` in the test, or an output
  -- definition with build-tree="no" or method json or adaptive (§26.1)
  let treeNo := (kidsNamed testNode "output").any (fun n => attrD n "tree" == "no")
  let rawMethod : Sheet → Bool := fun S =>
    let od := (S.outputs.lookup "").getD []
    treeNo || (match od.lookup "build-tree" with
      | some b => parseBool b == some false
      | none => match od.lookup "method" with
        | some m => m == "json" || m == "adaptive"
        | none => false)
  let initialFn := !(kidsNamed testNode "initial-function").isEmpty
  -- the principal result tree: sequence normalization with the
  -- item-separator of the unnamed output definition (§26.1)
  let deliver (S : Sheet) (raw : Seq) : M Seq :=
    if rawMethod S || initialFn then pure raw else
    let sep := ((S.outputs.lookup "").getD []).lookup "item-separator"
    match raw with
    | [.node n] => if (env.nrec n).kind == .document then pure raw else
        do pure [← materialize env (2 ^ 45) (.doc (← Out.normalizeTop sep (Out.ofSeq raw)) "")]
    | _ => do pure [← materialize env (2 ^ 45) (.doc (← Out.normalizeTop sep (Out.ofSeq raw)) "")]
  let res : M Seq := do
    let (r, S) ← outcome
    deliver S r.raw
  let serWith (fmt : String) (sp : List (String × String)) : Seq → M String := fun s => match outcome with
    | .ok (_, S) => do
        let props ← S.outputProps fmt sp
        serializeResult S env props s
    | .error e => throw e
  let secondary : List (String × Seq × (Seq → M String)) := match outcome with
    | .ok (r, S) => r.secondary.map (fun (h, v, f, sp) => (h, (if (sp.lookup "method").isSome || f != "" then pure v else deliver S v).toOption.getD v, serWith f sp))
    | .error _ => []
  let ser : Seq → M String := match outcome with
    | .ok (r, _) => serWith r.principalFormat.1 r.principalFormat.2
    | .error e => fun _ => throw e
  let env := match outcome with
    | .ok (r, _) => { env with docs := env.docs } |>.bind { uri := "", loc := "l4msgs" } (r.msgs.map (fun m => .atom (Atomic.ofStr m)))
    | .error _ => env
  pure (checkAssert { env, res, secondary, ser } 100 a)

def runSet (o : Opts) (file : String) : IO (String × Tally × List String) := do
  let some txt ← readFileSafe file | return (file, {}, ["cannot read " ++ file])
  let d ← match parseXML txt with
    | .ok d => pure d
    | .error _ => return (file, {}, ["cannot parse " ++ file])
  let ts := d.root
  let dir := dirOf file
  let setName := attrD ts "name"
  let setDeps := (kidsNamed ts "dependencies").flatMap kids
  let localEnvs := (kidsNamed ts "environment").filterMap (fun e =>
    match attr e "name" with | some n => some (n, parseEnv dir e) | none => none)
  let mut t : Tally := {}
  let mut fails : List String := []
  let mut skipping := o.after.isSome
  for tc in kidsNamed ts "test-case" do
    let name := attrD tc "name"
    if skipping then
      if some name == o.after then skipping := false
      continue
    if let some only := o.only then
      if name != only then continue
    if let some pf := o.progress then
      IO.FS.writeFile pf s!"{t.pass} {t.fail} {t.unsup} {name} {t.excl}\n"
    let deps := (kidsNamed tc "dependencies").flatMap kids
    let specGiven := deps.any (fun x => localTag x == "spec")
    let setOk := if specGiven then (setDeps.filter (fun x => localTag x != "spec")).all depOk else setDeps.all depOk
    if !(setOk && deps.all depOk) then
      t := { t with unsup := t.unsup + 1 }
      if o.listFails then
        let bad := (setDeps.filter (fun x => !depOk x && !(specGiven && localTag x == "spec"))) ++ deps.filter (fun x => !depOk x)
        let why := String.intercalate " " (bad.map (fun x => localTag x ++ "=" ++ attrD x "value" ++
          (if attrD x "satisfied" "true" == "false" then "(not)" else "")))
        fails := fails ++ [s!"UNSUP {setName}/{name}: dep {why}"]
      continue
    let outcome ← runCase o dir localEnvs tc
    if let some iss := defective.lookup name then
      match outcome with
      | .pass =>
        t := { t with fail := t.fail + 1 }
        fails := fails ++ [s!"FAIL {setName}/{name}: STALE exclusion: the test passes; remove it from `defective` in Harness/Xslt4Run.lean ({iss})"]
      | _ =>
        t := { t with excl := t.excl + 1 }
        if o.listFails then fails := fails ++ [s!"EXCLUDED {setName}/{name}: defective test data, {iss}"]
      continue
    match outcome with
    | .pass => t := { t with pass := t.pass + 1 }
    | .fail why =>
        t := { t with fail := t.fail + 1 }
        if o.listFails then fails := fails ++ [s!"FAIL {setName}/{name}: {why}"]
    | .unsupported why =>
        t := { t with unsup := t.unsup + 1 }
        if o.listFails then fails := fails ++ [s!"UNSUP {setName}/{name}: {why}"]
  if let some pf := o.progress then
    IO.FS.writeFile pf s!"{t.pass} {t.fail} {t.unsup} DONE {t.excl}\n"
  return (setName, t, fails)

/-- Run one test set in child processes, with a time limit per test case
    (an IO loop that ends on an outside event: the child exiting, or the
    clock). A test case that does not finish counts as FAIL, and a new
    child continues after it. -/
def runIsolated (o : Opts) (secs : Nat) (setName file : String) : IO (Tally × String) := do
  let pf := (← IO.getEnv "TMPDIR").getD "/tmp" ++ "/l4xslt4-progress-" ++ toString (← IO.Process.getPID) ++ "-" ++ setName
  let mut total : Tally := {}
  let mut after : Option String := none
  let mut notes : List String := []
  for _ in [0:100000] do
    IO.FS.writeFile pf ""
    let mut args : Array String := #["--root", o.root, "--set", setName, "--progress", pf]
    if o.listFails then args := args.push "--list-fails"
    if let some a := after then args := args ++ #["--after", a]
    let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, stdin := .null, stdout := .inherit, stderr := .null }
    let mut lastName := ""
    let mut since ← IO.monoMsNow
    let mut finished := false
    repeat
      match ← child.tryWait with
      | some _ => finished := true; break
      | none =>
        let line := ((← readFileSafe pf).getD "").trimAscii.toString
        let nm := (line.splitOn " ").getD 3 ""
        if nm != lastName then lastName := nm; since ← IO.monoMsNow
        if (← IO.monoMsNow) - since > secs * 1000 then break
        IO.sleep 50
    if !finished then
      child.kill
      let _ ← child.wait
    let line := ((← readFileSafe pf).getD "").trimAscii.toString
    let parts := line.splitOn " "
    let num (i : Nat) : Nat := ((parts.getD i "0").toNat?).getD 0
    let t : Tally := ⟨num 0, num 1, num 2, num 4⟩
    let last := parts.getD 3 ""
    total := total.add t
    if finished && last == "DONE" then break
    if last == "" || last == "DONE" then break
    -- the test case `last` did not finish: a failure; go on after it
    total := { total with fail := total.fail + 1 }
    notes := notes ++ [last]
    if o.listFails then IO.println s!"  FAIL {setName}/{last}: did not finish in {secs} s"
    after := some last
  try IO.FS.removeFile pf catch _ => pure ()
  -- test cases no child reported (a child that stopped early) are fails
  let count ← match ← readFileSafe file with
    | some txt => match parseXML txt with
      | .ok d => pure (kidsNamed d.root "test-case").length
      | .error _ => pure total.total
    | none => pure total.total
  let missing := count - total.total - total.excl
  let res := { total with fail := total.fail + missing }
  let ns := if missing > 0 then notes ++ [s!"{missing} not reported"] else notes
  return (res, if ns.isEmpty then "" else s!" [{ns.length} test(s) did not finish in {secs} s, counted as fail: {String.intercalate ", " ns}]")

/-! ## Agreement with the XSLT 1.0 engine

`--xslt10 DIR` runs each case of an XSLT 1.0 corpus (`manifest.json` with
`stylesheet`, `source`, `expected`) through both `L4Factoidal.XSLT` (the
XSLT 1.0 engine) and `L4Factoidal.XSLT4`, and compares the two results
with each other and with the expected output: the same comparison as
`l4xslt` (exact text, else Canonical XML 1.0 of the wrapped fragments,
else whitespace-collapsed text). -/

def normalizeEol (s : String) : String :=
  String.ofList (s.toList.foldr (fun c acc =>
    match c, acc with
    | '\r', '\n' :: r => '\n' :: r
    | '\r', r => '\n' :: r
    | _, r => c :: acc) [])

def stripDecl (s : String) : String :=
  let t := s.trimAscii.toString
  if t.startsWith "<?xml" then
    match (t.toList.drop 5).findIdx? (· == '>') with
    | some i => (String.ofList (t.toList.drop (5 + i + 1))).trimAscii.toString
    | none => t
  else t

def looseForm (s : String) : String :=
  let isW (c : Char) := c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let collapsed := s.toList.foldr (fun c acc =>
    if isW c then (match acc with | ' ' :: _ => acc | _ => ' ' :: acc) else c :: acc) []
  let dropped := collapsed.foldr (fun c acc =>
    match c, acc with
    | '>', ' ' :: '<' :: r => '>' :: '<' :: r
    | _, r => c :: r) []
  (String.ofList dropped).trimAscii.toString

/-- Do two serialized results agree (the `l4xslt` comparison)? -/
def sameResult (a b : String) : Bool :=
  let a := stripDecl (normalizeEol a)
  let b := stripDecl (normalizeEol b)
  if a == b then true else
  match L4Factoidal.XML.Canonical.canonicalFragment? a, L4Factoidal.XML.Canonical.canonicalFragment? b with
  | some x, some y => x == y || looseForm x == looseForm y
  | _, _ => looseForm a == looseForm b

/-- Run a stylesheet text on a source text with XSLT4, serialized. -/
def runXslt4 (styleUri : String) (mods : List (String × String)) (srcUri srcTxt : String)
    (res : List (String × String)) : M String := do
  let S ← compileStylesheet styleUri mods
  let some d := loadDoc srcTxt srcUri | throw { code := "FODC0002", msg := "source not well-formed" }
  let env : Env := { docs := #[d], docUris := [(srcUri, 0)], resources := res }
  let r ← transform S { globalCtx := some (.node (NodeRef.mk' 0 0)), env }
  let props ← S.outputProps r.principalFormat.1 r.principalFormat.2
  let raw := if r.raw.isEmpty then [] else r.raw
  -- the result tree of an XSLT 1.0 transform is a document node
  let v ← match raw with
    | [.node n] => if (env.nrec n).kind == .document then pure raw else
        do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq raw) "")]
    | _ => do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq raw) "")]
  serializeResult S env props v

def agree10 (dir : String) : IO UInt32 := do
  let some mtxt ← readFileSafe (dir ++ "/manifest.json") | IO.eprintln s!"cannot read {dir}/manifest.json"; return 2
  let .ok j := Lean.Json.parse mtxt | IO.eprintln "bad manifest"; return 2
  let .ok arr := j.getArr? | IO.eprintln "manifest is not an array"; return 2
  let mut n := 0
  let mut p10 := 0
  let mut p4 := 0
  let mut both := 0
  let mut agreeN := 0
  let mut only10 : List String := []
  for c in arr do
    let get (k : String) : String := ((c.getObjVal? k).bind Lean.Json.getStr?).toOption.getD ""
    let name := get "name"
    let sp := normPath (dir ++ "/" ++ get "stylesheet")
    let srcp := normPath (dir ++ "/" ++ get "source")
    let ep := normPath (dir ++ "/" ++ get "expected")
    let some st ← readFileSafe sp | continue
    let some src ← readFileSafe srcp | continue
    let some exp ← readFileSafe ep | continue
    n := n + 1
    -- XSLT 1.0 engine
    let r10 : Option String := match parseXML st, parseXML src with
      | .ok s1, .ok s2 => match L4Factoidal.XSLT.transform s1 s2 with
        | .produced t => some t
        | .refused _ => none
      | _, _ => none
    -- XSLT 4.0 engine
    let mods ← loadModules (fileUri sp)
    let res ← scanResources dir (dirOf sp) st
    let r4 : Option String := match runXslt4 (fileUri sp) mods (fileUri srcp) src res with
      | .ok t => some t
      | .error _ => none
    let ok10 := match r10 with | some t => sameResult t exp | none => false
    let ok4 := match r4 with | some t => sameResult t exp | none => false
    if ok10 then p10 := p10 + 1
    if ok4 then p4 := p4 + 1
    if ok10 && ok4 then both := both + 1
    if ok10 && !ok4 then only10 := only10 ++ [name]
    match r10, r4 with
    | some a, some b => if sameResult a b then agreeN := agreeN + 1
    | _, _ => pure ()
  IO.println s!"XSLT 1.0 corpus {dir}: {n} cases"
  IO.println s!"  XSLT 1.0 engine (L4Factoidal.XSLT): {p10} pass"
  IO.println s!"  XSLT 4.0 engine (L4Factoidal.XSLT4): {p4} pass"
  IO.println s!"  both pass: {both}; the two results agree: {agreeN}"
  IO.println s!"  pass with XSLT 1.0 only: {only10.length}"
  for x in only10 do IO.println s!"    {x}"
  return 0

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  if let some d := o.xslt10 then
    let cwd ← IO.currentDir
    return ← agree10 (normPath (if d.startsWith "/" then d else cwd.toString ++ "/" ++ d))
  let cwd ← IO.currentDir
  let o := { o with root := normPath (if o.root.startsWith "/" then o.root else cwd.toString ++ "/" ++ o.root) }
  let some ctxt ← readFileSafe (o.root ++ "/catalog.xml")
    | IO.eprintln s!"cannot read {o.root}/catalog.xml"; return 2
  let cat ← match parseXML ctxt with
    | .ok d => pure d.root
    | .error _ => IO.eprintln "cannot parse catalog.xml"; return 2
  let mut dirT : List (String × Tally) := []
  let mut total : Tally := {}
  for s in kidsNamed cat "test-set" do
    let file := attrD s "file"
    let nm := attrD s "name"
    let dir := (file.splitOn "/").getD 1 ""
    if !o.sets.isEmpty && !o.sets.contains nm then continue
    if !o.dirs.isEmpty && !o.dirs.contains dir then continue
    let path := o.root ++ "/" ++ file
    if !(← System.FilePath.pathExists path) then continue
    let (t, fails, note) ← match o.isolate with
      | some secs =>
        let (t, note) ← runIsolated o secs nm path
        pure (t, ([] : List String), note)
      | none =>
        let (_, t, fails) ← runSet o path
        pure (t, fails, "")
    if !o.childMode then IO.println s!"{dir}/{nm}: {t.show}{note}"
    for f in fails do IO.println ("  " ++ f)
    (← IO.getStdout).flush
    dirT := match dirT.find? (·.1 == dir) with
      | some _ => dirT.map (fun (d, x) => if d == dir then (d, x.add t) else (d, x))
      | none => dirT ++ [(dir, t)]
    total := total.add t
  if o.childMode then return 0
  IO.println "== directories =="
  for (d, t) in dirT do IO.println s!"{d}: {t.show}"
  IO.println s!"TOTAL: {total.show}"
  return 0

end Harness.Xslt4Run

def main (args : List String) : IO UInt32 := Harness.Xslt4Run.main args
