/-
Harness/Qt4Run — the qt4tests (QT4 Community Group XPath/XQuery/F&O
test suite) runner for the XPath 4.0 evaluator `L4Factoidal.XPath4`.

    lake exe l4qt4 [--root DIR] [--family F]... [--set NAME] [--list-fails]

It reads `catalog.xml`, then every test set of the selected families
(default `prod op fn map array math`), and scores every test case:

* **unsupported** — the test case or its test set has a dependency
  this processor does not satisfy: a spec that is not XPath 4.0
  (`XQ*` only, or an `XP` version range that excludes 4.0), a feature
  it does not have (schema import/validation, typed data, static
  typing, the namespace axis, `fn:transform`, ...), XML 1.1, a
  non-English default language, or an environment that needs a schema,
  a collection, a decimal format or a resource. An unsupported test is
  NEVER a pass;
* **pass** — every assertion holds; an `error` assertion holds only
  when the error raised has the expected code (or the code is `*`);
* **fail** — anything else, including a wrong error code.

The assertions are evaluated with the same XPath 4.0 evaluator
(`assert-eq` compares with `eq`, `assert-deep-eq` with `fn:deep-equal`,
`assert` evaluates the expression with `$result` bound). `assert-xml`
serialises the result nodes and compares them, with the expected XML,
by `fn:deep-equal` on the two parsed fragments (`assert-xml` with a
`file` attribute reads the expected XML from that file).
`serialization-matches`, `assert-serialization` and
`assert-serialization-error` serialize the result with
`XPath4.Serialize` (method `xml`, the map-form defaults).

The test data is untrusted input: it is parsed, never executed as
anything but XPath expressions in this evaluator.
-/
import L4Factoidal.XPath4.Eval
import L4Factoidal.XPath4.Theorems
import L4Factoidal.XPath4.SerializeTheorems
import L4Factoidal.EXPath.File.IOHost
import L4Factoidal.EXPath.File.Theorems
import L4Factoidal.EXPath.Binary.Theorems

open L4Factoidal.XPath4
open L4Factoidal.XML

/-! ## Defective test data

qt4tests cases whose expected result
contradicts the normative text of the specification they test
(defective test data, `skills/test-suites/SKILL.md` § Defective test
data). `l4qt4` reports them apart as "excluded (defective test data)",
not in pass, fail or the total; a case on this list that PASSES counts
as a FAIL, so the exclusion cannot outlive a corrected test.
-/
namespace Harness.Qt4Defective

/-- `(test-case name, issue URL)`. -/
def defective : List (String × String) :=
  let i1141 := "https://github.com/danbri/factoidal/issues/1141"
  -- EXPath Binary 4.0: a wrong $order is XPTY0004 (§ Octet order), an
  -- octet outside 0..255 is XPTY0004 (xs:unsignedByte arguments)
  [ "EXPath-binary-pack-double-001", "bin-pack-double15", "bin-pack-float15",
    "EXPath-binary-pack-integer-001", "bin-pack-integer14",
    "EXPath-binary-unpack-double-001", "bin-unpack-double18",
    "EXPath-binary-unpack-float-001", "bin-unpack-float18",
    "EXPath-binary-unpack-integer-001", "bin-unpack-integer16",
    "EXPath-binary-unpack-unsigned-integer-001", "bin-unpack-unsigned-integer20",
    "EXPath-binary-from-octets-003", "EXPath-binary-from-octets-004",
    "bin-from-octets4", "bin-from-octets5",
    "EXPath-binary-pad-left-003", "EXPath-binary-pad-left-004", "bin-pad-left5",
    "EXPath-binary-pad-right-003", "EXPath-binary-pad-right-004", "bin-pad-right5"
  ].map (fun n => (n, i1141))
  -- F&O 4.0: fn:collection and fn:uri-collection take $options, so two
  -- arguments are XPTY0004, not XPST0017
  ++ [ ("fn-collection-1", "https://github.com/danbri/factoidal/issues/1150"),
       ("fn-uri-collection-1", "https://github.com/danbri/factoidal/issues/1150") ]

end Harness.Qt4Defective

namespace Harness.Qt4Run

/-! ## XML helpers over the raw parse tree -/

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

def readFileSafe (p : String) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

def readBytesSafe (p : String) : IO (Option ByteArray) := do
  try pure (some (← IO.FS.readBinFile p)) catch _ => pure none

/-! ## Dependencies -/

def specOk (v : String) : Bool :=
  (v.splitOn " ").any (fun t =>
    if t.startsWith "XP" then
      let rest := (t.drop 2).toString
      let plus := rest.endsWith "+"
      let num := (if plus then (rest.dropEnd 1).toString else rest).toNat?
      match num with
      | some k => k == 40 || (plus && k ≤ 40)
      | none => false
    else false)

/-- The features this processor has. -/
def featureSupported (f : String) : Bool :=
  f == "higherOrderFunctions" || f == "serialization"
    -- UCA collations: unknown parameters are ignored with fallback=yes,
    -- and the parameters of `XPath4.Collation` are implemented
    || f == "simple-uca-fallback" || f == "advanced-uca-fallback"
  -- EXPath Binary 4.0 and File 4.0 (`L4Factoidal.EXPath`)
  || f == "binary" || f == "expath-file"
  -- IANA zone names (`XPath4.Tz`)
  || f == "olson-timezone"
  -- fn:invisible-xml (`XPath4.Ixml`)
  || f == "fn-invisible-xml"

def depOk (d : Node) : Bool :=
  let ty := attrD d "type"
  let v := attrD d "value"
  let sat := attrD d "satisfied" "true" != "false"
  match ty with
  | "spec" => specOk v
  | "feature" =>
      let fs := v.splitOn " "
      if sat then fs.all featureSupported else !(fs.all featureSupported)
  | "xml-version" =>
      let has := (v.splitOn " ").any (fun x => x == "1.0" || x == "1.0:4-" || x.startsWith "1.0")
      if sat then has else !has
  | "xsd-version" => if sat then v == "1.1" else v != "1.1"
  | "default-language" | "language" => if sat then v == "en" else v != "en"
  -- `XPath4.Unicode`: UAX #15 NFC, NFD, NFKC, NFKD (not FULLY-NORMALIZED)
  | "unicode-normalization-form" =>
      let has := v == "NFC" || v == "NFD" || v == "NFKC" || v == "NFKD"
      if sat then has else !has
  -- `XPath4.Format.fmtIntToken`: decimal digit families and the
  -- circled, parenthesised, full-stop and Greek sequences
  | "format-integer-sequence" =>
      let has := match v.toList with
        | [c] => isDigitU c || [0x2460, 0x2474, 0x2488, 0x3B1, 0x391].contains c.toNat
        | _ => false
      if sat then has else !has
  | _ => !sat

/-! ## Environments -/

structure EnvSpec where
  sources : List (String × String × String) := []   -- role, file (resolved), uri
  params : List (String × String) := []             -- name, select
  ns : List (String × String) := []
  ctxSelect : Option String := none
  unsupported : Option String := none
  baseUri : String := ""
  /-- A `collation` element with `default="true"`. -/
  defaultCollation : Option String := none
  /-- `resource` elements: (uri, file). -/
  resources : List (String × String) := []
  decimalFormats : List (String × List (String × String)) := []
  /-- EXPath File 4.0: the `sandpit` directory, copied for each test. -/
  sandpit : Option String := none
  /-- `collection` elements: the URI (`""` for the default collection),
      the sources (file resolved, uri) and the `query` texts. -/
  collections : List (String × List (String × String) × List String) := []
deriving Inhabited

def parseEnv (dir : String) (e : Node) : EnvSpec := Id.run do
  let mut s : EnvSpec := {}
  for c in kids e do
    match localTag c with
    | "source" =>
        if attrD c "validation" == "strict" || attrD c "validation" == "lax" then
          s := { s with unsupported := some "schema-validated source" }
        s := { s with sources := s.sources ++ [(attrD c "role", dir ++ "/" ++ attrD c "file", attrD c "uri")] }
    | "param" =>
        if attrD c "declared" != "true" then
          s := { s with params := s.params ++ [(attrD c "name", attrD c "select" "()")] }
    | "namespace" => s := { s with ns := s.ns ++ [(attrD c "prefix", attrD c "uri")] }
    | "context-item" => s := { s with ctxSelect := attr c "select" }
    | "schema" => s := { s with unsupported := some "schema" }
    | "collection" =>
        let srcs := (kidsNamed c "source").map (fun x => (dir ++ "/" ++ attrD x "file", attrD x "uri"))
        let qs := (kidsNamed c "query").map (fun x => x.textContent)
        s := { s with collections := s.collections ++ [(attrD c "uri", srcs, qs)] }
    | "resource" =>
        s := { s with resources := s.resources ++ [(attrD c "uri", dir ++ "/" ++ attrD c "file")] }
    | "decimal-format" =>
        let ats := c.elementAttrs
        let nsOf (p : String) : String :=
          match ats.find? (fun a => a.name == "xmlns:" ++ p) with
          | some a => a.value
          | none => (s.ns.lookup p).getD ""
        let key := match attr c "name" with
          | none => ""
          | some n => match n.splitOn ":" with
            | [p, l] => "Q{" ++ nsOf p ++ "}" ++ l
            | _ => "Q{}" ++ n
        let props := (ats.filter (fun a => a.name != "name" && !a.name.startsWith "xmlns")).map (fun a => (a.name, a.value))
        s := { s with decimalFormats := s.decimalFormats ++ [(key, props)] }
    | "collation" =>
        let u := attrD c "uri"
        match collationOf "" u with
        | .ok _ => if attrD c "default" == "true" then s := { s with defaultCollation := some u }
        | .error _ => s := { s with unsupported := some ("collation " ++ u) }
    | "static-base-uri" => s := { s with baseUri := attrD c "uri" }
    | "function-library" => s := { s with unsupported := some "function-library" }
    | "sandpit" => s := { s with sandpit := some (dir ++ "/" ++ attrD c "path") }
    | _ => pure ()
  pure s

/-! ## Outcomes -/

inductive Outcome where
  | pass
  | fail (why : String)
  | unsupported (why : String)
deriving Inhabited

/-! ## Serialisation of results (for assert-xml) -/

def escText (s : String) : String :=
  String.join (s.toList.map (fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '\r' => "&#xD;" | c => String.ofList [c]))

def escAttr (s : String) : String :=
  String.join (s.toList.map (fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '"' => "&quot;" | '\n' => "&#xA;" | '\t' => "&#x9;" | '\r' => "&#xD;" | c => String.ofList [c]))

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
      let decl := if r.name.uri == "" then (if r.name.pfx == "" then "" else "")
        else " xmlns" ++ (if r.name.pfx == "" then "" else ":" ++ r.name.pfx) ++ "=\"" ++ escAttr r.name.uri ++ "\""
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

/-! ## Assertions -/

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
  match env.fileSys with
  -- EXPath File 4.0: an assertion may also call a writing `file:` function
  | some fs => (·.1) <$> L4Factoidal.EXPath.File.evalMem env fs e
  | none => eval 20000 env e

def xmlEq1 (env : Env) (got : Seq) (expected : String) : Bool :=
  let gs := serSeq env got
  match Doc.ofString ("<w>" ++ gs ++ "</w>"), Doc.ofString ("<w>" ++ expected ++ "</w>") with
  | .ok d1, .ok d2 =>
    let e2 : Env := { docs := #[d1, d2] }
    let root1 := (d1.get 0).children.getD 0 0
    let root2 := (d2.get 0).children.getD 0 0
    e2.nodeDeepEq 100000 (NodeRef.mk' 0 root1) (NodeRef.mk' 1 root2)
  | _, _ => gs == expected

/-- `assert-xml`: also with the whitespace around the expected XML
    removed (the catalog's CDATA sections often end with a space or a
    newline that is not part of the expected result). -/
def xmlEq (env : Env) (got : Seq) (expected : String) : Bool :=
  xmlEq1 env got expected || xmlEq1 env got expected.trimAscii.toString

def checkAssert (env : Env) (res : M Seq) : Nat → Node → Outcome
  | 0, _ => .fail "assertion nesting"
  | f + 1, a =>
    let txt := a.textContent
    let ok? (b : Bool) (why : String) : Outcome := if b then .pass else .fail why
    match localTag a with
    | "error" =>
        let code := attrD a "code"
        match res with
        | .error e => ok? (code == "*" || code == e.code || ("err:" ++ e.code) == code || code.endsWith (":" ++ e.code)
              || code == "Q{http://www.w3.org/2005/xqt-errors}" ++ e.code) ("wrong error code " ++ e.code ++ " (expected " ++ code ++ ")")
        | .ok s => .fail ("expected error " ++ code ++ ", got " ++ (sh s 80))
    | "any-of" =>
        let rs := (kids a).map (fun c => checkAssert env res f c)
        if rs.any (fun r => match r with | .pass => true | _ => false) then .pass
        else .fail ("any-of: " ++ String.intercalate "; " (rs.map (fun r => match r with | .fail w => w | _ => "")))
    | "all-of" =>
        let rs := (kids a).map (fun c => checkAssert env res f c)
        match rs.find? (fun r => match r with | .pass => false | _ => true) with
        | some r => r
        | none => .pass
    | "not" =>
        match (kids a).head? with
        | some c => match checkAssert env res f c with
          | .pass => .fail "not: inner assertion held"
          | _ => .pass
        | none => .fail "empty not"
    | "assert-serialization-error" =>
        let code := attrD a "code"
        let codeOk (c : String) := code == "*" || code == c || ("err:" ++ c) == code || code.endsWith (":" ++ c)
        match res with
        | .error e => ok? (codeOk e.code) ("wrong error code " ++ e.code ++ " (expected " ++ code ++ ")")
        | .ok s =>
          match env.serializeWith {} s with
          | .error e => ok? (codeOk e.code) ("wrong serialization error " ++ e.code ++ " (expected " ++ code ++ ")")
          | .ok out => .fail ("expected serialization error " ++ code ++ ", got " ++ cut out 80)
    | tag =>
      match res with
      | .error e => .fail ("error " ++ e.code ++ ": " ++ e.msg)
      | .ok s =>
      let envR := env.bind { uri := "", loc := "result" } s
      -- QT3 test-suite assertions: the context item is the result when it is one item
      let envR := match s with | [_] => { envR with ctx := some s, pos := 1, size := 1 } | _ => envR
      match tag with
      | "assert-true" => ok? (match s with | [.atom ⟨_, .bool true⟩] => true | _ => false) ("got " ++ (sh s 80))
      | "assert-false" => ok? (match s with | [.atom ⟨_, .bool false⟩] => true | _ => false) ("got " ++ (sh s 80))
      | "assert-empty" => ok? s.isEmpty ("got " ++ (sh s 80))
      | "assert-count" => ok? (s.length == (txt.trimAscii.toString.toNat?).getD 0) ("count " ++ toString s.length)
      | "assert-string-value" =>
          let got := stringValueOf env s
          let ok := if attrD a "normalize-space" == "true" then normSp got == normSp txt else got == txt
          ok? ok ("string value '" ++ (cut got 80) ++ "'")
      | "assert-eq" =>
          match evalIn env txt with
          | .ok exp =>
            -- a single node (XNode or JNode) is compared by its typed value
            let s : Seq := match s with
              | [.node _] | [.jnode ..] => match env.atomize s with
                | .ok [x] => [Item.atom x]
                | _ => s
              | _ => s
            match s, exp with
            | [.atom x], [.atom y] =>
              let nan (z : Atomic) := (z.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false
              let ok := (nan x && nan y) || (match atomicCmp (if x.ty == .untyped then Atomic.ofStr x.str else x) y env.tz with
                | .ok (some .eq) => true | _ => false)
              ok? ok ("got " ++ x.str ++ " (xs:" ++ x.ty.name ++ "), expected " ++ y.str)
            | _, _ => .fail ("got " ++ (sh s 80))
          | .error e => .fail ("could not evaluate expected value: " ++ e.code)
      | "assert-deep-eq" =>
          match evalIn env txt with
          | .ok exp => ok? (env.deepEq s exp) ("got " ++ (sh s 80) ++ ", expected " ++ (sh exp 80))
          | .error e => .fail ("could not evaluate expected value: " ++ e.code ++ " " ++ e.msg)
      | "assert-permutation" =>
          match evalIn env txt with
          | .ok exp =>
            let ok := s.length == exp.length && s.all (fun i => exp.any (fun j => env.deepEq [i] [j]))
                      && exp.all (fun j => s.any (fun i => env.deepEq [i] [j]))
            ok? ok ("got " ++ (sh s 80))
          | .error e => .fail ("could not evaluate expected value: " ++ e.code)
      | "assert" =>
          match evalIn envR txt with
          | .ok [.atom ⟨_, .bool true⟩] => .pass
          | .ok r =>
            -- QT3 catalog: `assert` holds when the effective boolean value is true
            match ebv r with
            | .ok true => .pass
            | _ => .fail ("assert gave " ++ (sh r 60) ++ " for result " ++ (sh s 60))
          | .error e => .fail ("assert raised " ++ e.code ++ " " ++ e.msg)
      | "assert-type" =>
          match parseSeqType txt with
          | .ok t => ok? (env.seqMatches s t) ("type mismatch: got " ++ (sh s 60))
          | .error e => .fail ("bad type in assert-type: " ++ e.msg)
      | "serialization-matches" =>
          match env.serializeWith {} s with
          | .error e => .fail ("serialization raised " ++ e.code ++ " " ++ e.msg)
          | .ok out =>
            let q : QN := { uri := "", loc := "l4ser" }
            let pq : QN := { uri := "", loc := "l4pat" }
            let fq : QN := { uri := "", loc := "l4flags" }
            let envM := ((env.bind q (sStr out)).bind pq (sStr txt)).bind fq (sStr (attrD a "flags"))
            match evalIn envM "matches($l4ser, $l4pat, $l4flags)" with
            | .ok [.atom ⟨_, .bool true⟩] => .pass
            | .ok _ => .fail ("serialization '" ++ cut out 80 ++ "' does not match")
            | .error e => .fail ("serialization-matches raised " ++ e.code)
      | "assert-serialization" =>
          match env.serializeWith {} s with
          | .error e => .fail ("serialization raised " ++ e.code ++ " " ++ e.msg)
          | .ok out =>
            let ok := if attrD a "normalize-space" == "true" then normSp out == normSp txt else out == txt || xmlEq env s txt
            ok? ok ("serialization '" ++ cut out 80 ++ "'")
      | "assert-xml" =>
          match attr a "file" with
          | some _ => .fail "assert-xml file could not be read"
          | none =>
            let exp := match a with
              | .element _ _ cs => String.join (cs.map (fun c => match c with
                  | .text t => escText t
                  | .cdata t => escText t
                  | _ => ""))
              | _ => txt
            -- the expected fragment as written (child markup included)
            let exp := if (kids a).isEmpty then exp else exp
            ok? (xmlEq env s txt || xmlEq env s exp) ("xml " ++ (cut (serSeq env s) 80))
      | other => .fail ("assertion " ++ other ++ " is not evaluated")

/-- The assert-xml expected value is the element's inner markup; the
    raw parse tree has lost it, so it is re-serialised. -/
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

/-- Replace each assert-xml's text with its inner markup, so
    `checkAssert` sees the expected XML. -/
def fixXml : Nat → Node → Node
  | 0, n => n
  | f + 1, n =>
    match n with
    | .element tag ats cs =>
        if (splitName tag).2 == "assert-xml" then .element tag ats [.text (innerXml 1000 n)]
        else .element tag ats (cs.map (fixXml f))
    | other => other

/-- Normalise a relative file path (`a/./b/../c` to `a/c`); `none` when
    it climbs above its start. -/
def normPath (p : String) : Option String := Id.run do
  let mut out : List String := []
  for seg in p.splitOn "/" do
    if seg == "." || seg == "" then continue
    if seg == ".." then
      match out with
      | _ :: r => out := r
      | [] => return none
    else out := seg :: out
  return some (String.intercalate "/" out.reverse)

/-- Read the expected XML of each `assert-xml file="..."` (relative to
    the test set's directory, only under the suite root) into the
    element's text, without its XML declaration. -/
def resolveXmlFiles (root dir : String) : Nat → Node → IO Node
  | 0, n => pure n
  | f + 1, n =>
    match n with
    | .element tag ats cs => do
      if (splitName tag).2 == "assert-xml" then
        match ats.find? (fun x => x.name == "file") with
        | some fa =>
          let rel := if dir.startsWith (root ++ "/") then (dir.drop (root.length + 1)).toString else dir
          match normPath (rel ++ "/" ++ fa.value) with
          | none => pure n
          | some pth =>
            match ← readFileSafe (root ++ "/" ++ pth) with
            | none => pure n
            | some txt =>
              let txt := if txt.startsWith "<?xml" then
                  match txt.splitOn "?>" with
                  | _ :: rest => String.intercalate "?>" rest
                  | [] => txt
                else txt
              pure (.element tag (ats.filter (fun x => x.name != "file")) [.text txt])
        | none => pure n
      else
        pure (.element tag ats (← cs.mapM (resolveXmlFiles root dir f)))
    | other => pure other

/-! ## Running -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  unsup : Nat := 0
  /-- Defective test data (`Harness.Qt4Defective`): not in the total. -/
  excl : Nat := 0
deriving Inhabited

def Tally.add (a b : Tally) : Tally := ⟨a.pass + b.pass, a.fail + b.fail, a.unsup + b.unsup, a.excl + b.excl⟩
def Tally.total (t : Tally) : Nat := t.pass + t.fail + t.unsup
def Tally.show (t : Tally) : String :=
  s!"{t.pass} pass, {t.fail} fail, {t.unsup} unsupported (out of {t.total})"
    ++ (if t.excl > 0 then s!"; {t.excl} excluded (defective test data)" else "")

structure Opts where
  root : String := "../../third_party/testing/qt4tests"
  families : List String := []
  set : Option String := none
  listFails : Bool := false
  trace : Bool := false
  /-- Test cases not run because they do not finish in this
      implementation; each counts as a FAIL. -/
  hang : List String := []
  /-- Run each test set in a child process, killed after this many
      seconds; the tests it did not finish count as FAIL. -/
  isolate : Option Nat := none
  progress : Option String := none
  childMode : Bool := false
  /-- EXPath File 4.0 tests: `memory` (the in-memory file system) or
      `io` (a copy of the sandpit in a temporary directory). -/
  fileHost : String := "memory"

def parseArgs : List String → Opts → Opts
  | "--root" :: r :: rest, o => parseArgs rest { o with root := r }
  | "--family" :: f :: rest, o => parseArgs rest { o with families := o.families ++ [f] }
  | "--set" :: s :: rest, o => parseArgs rest { o with set := some s }
  | "--list-fails" :: rest, o => parseArgs rest { o with listFails := true }
  | "--trace" :: rest, o => parseArgs rest { o with trace := true }
  | "--isolate" :: n :: rest, o => parseArgs rest { o with isolate := n.toNat? }
  | "--progress" :: f :: rest, o => parseArgs rest { o with progress := some f, childMode := true }
  | "--hang" :: h :: rest, o => parseArgs rest { o with hang := o.hang ++ [h] }
  | "--file-host" :: h :: rest, o => parseArgs rest { o with fileHost := h }
  | _ :: rest, o => parseArgs rest o
  | [], o => o


/-- The files a test names by a relative reference in its text (for
    `fn:unparsed-text`, `fn:json-doc`, `fn:doc`, and external entities
    under `trust-external`): every run of path characters that names a
    file under the test suite root, resolved against the test set's
    directory. Read in advance, as text, because the evaluator does no
    I/O. Only files under the suite root are read. -/
def scanResources (root dir src : String) : IO (List (String × String) × List (String × ByteArray)) := do
  let isPathChar (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '/' || c == '-'
  let mut toks : List String := []
  let mut cur : String := ""
  for c in src.toList ++ [' '] do
    if isPathChar c then cur := cur.push c
    else
      if cur.length > 2 && cur.length < 200 && (cur.splitOn ".").length > 1 && !toks.contains cur then
        toks := cur :: toks
      cur := ""
  let rel := if dir.startsWith (root ++ "/") then (dir.drop (root.length + 1)).toString else dir
  let mut out : List (String × String) := []
  let mut bins : List (String × ByteArray) := []
  for t in toks do
    let t' := if t.startsWith "file:///" then none else some t
    let some t := t' | continue
    let some p := normPath (rel ++ "/" ++ t) | continue
    let path := root ++ "/" ++ p
    if ← System.FilePath.pathExists path then
      if (← System.FilePath.isDir path) then continue
      match ← readFileSafe path with
      | some txt => out := (t, txt) :: out
      | none => pure ()
      match ← readBytesSafe path with
      | some bs => bins := (t, bs) :: bins
      | none => pure ()
  return (out, bins)

/-- Build the dynamic context for an environment; `none` with a reason
    when it cannot be built. -/
def buildEnv (spec : EnvSpec) (cache : IO.Ref (List (String × Doc))) : IO (Except String Env) := do
  if let some why := spec.unsupported then return .error why
  let mut env : Env := { ns := spec.ns, baseUri := spec.baseUri }
  if let some c := spec.defaultCollation then env := { env with defaultCollation := c }
  for (role, file, uri) in spec.sources do
    let doc ← match (← cache.get).lookup file with
      | some d => pure (some d)
      | none =>
        match ← readFileSafe file with
        | none => pure none
        | some txt =>
          match Doc.ofString txt uri with
          | .ok d => cache.modify (fun c => (file, d) :: c); pure (some d)
          | .error _ => pure none
    match doc with
    | none => return .error ("source not loadable: " ++ file)
    | some d =>
      let idx := env.docs.size
      env := { env with docs := env.docs.push d,
                        docUris := if uri == "" then env.docUris else (uri, idx) :: env.docUris }
      if role == "." then env := { env with ctx := some [.node (NodeRef.mk' idx 0)], pos := 1, size := 1 }
      else if role.startsWith "$" then
        env := env.bind { uri := "", loc := (role.drop 1).toString } [.node (NodeRef.mk' idx 0)]
  -- collections (F&O 4.0 §1.7.2): documents are loaded like sources
  for (curi, srcs, qs) in spec.collections do
    let mut items : Seq := []
    let mut uris : List String := []
    for (file, uri) in srcs do
      let doc ← match (← cache.get).lookup file with
        | some d => pure (some d)
        | none =>
          match ← readFileSafe file with
          | none => pure none
          | some txt =>
            match Doc.ofString txt uri with
            | .ok d => cache.modify (fun c => (file, d) :: c); pure (some d)
            | .error _ => pure none
      match doc with
      | none => return .error ("collection source not loadable: " ++ file)
      | some d =>
        let idx := env.docs.size
        env := { env with docs := env.docs.push d,
                          docUris := if uri == "" then env.docUris else (uri, idx) :: env.docUris }
        items := items ++ [.node (NodeRef.mk' idx 0)]
        if uri != "" then uris := uris ++ [uri]
    for q in qs do
      match evalIn env q with
      | .ok v => items := items ++ v
      | .error e => return .error ("collection query: " ++ e.code)
    env := { env with collections := (curi, items) :: env.collections,
                      uriCollections := (curi, uris) :: env.uriCollections }
  env := { env with decimalFormats := spec.decimalFormats }
  for (uri, file) in spec.resources do
    match ← readBytesSafe file with
    | some bs =>
      env := { env with resourceBytes := (uri, bs) :: env.resourceBytes }
      if let some txt := String.fromUTF8? bs then
        env := { env with resources := (uri, txt) :: env.resources }
    | none => return .error ("resource not readable: " ++ file)
  for (name, sel) in spec.params do
    match evalIn env sel with
    | .ok v => env := env.bind { uri := "", loc := name } v
    | .error e => return .error ("param " ++ name ++ ": " ++ e.code)
  if let some sel := spec.ctxSelect then
    match evalIn env sel with
    | .ok [i] => env := { env with ctx := some [i], pos := 1, size := 1 }
    | _ => return .error "context-item select"
  return .ok env

def runSet (o : Opts) (catEnvs : List (String × EnvSpec)) (cache : IO.Ref (List (String × Doc)))
    (file : String) : IO (String × Tally × List String) := do
  let some txt ← readFileSafe file | return (file, {}, ["cannot read " ++ file])
  let d ← match parseXML txt with
    | .ok d => pure d
    | .error _ => return (file, {}, ["cannot parse " ++ file])
  let ts := fixXml 100000 d.root
  let dir := dirOf file
  let setName := attrD ts "name"
  let setDeps := kidsNamed ts "dependency"
  let setOk := setDeps.all depOk
  let localEnvs := (kidsNamed ts "environment").filterMap (fun e =>
    match attr e "name" with | some n => some (n, parseEnv dir e) | none => none)
  let mut t : Tally := {}
  let mut fails : List String := []
  for tc in kidsNamed ts "test-case" do
    let name := attrD tc "name"
    if let some pf := o.progress then
      IO.FS.writeFile pf s!"{t.pass} {t.fail} {t.unsup} {name} {t.excl}\n"
    let deps := kidsNamed tc "dependency"
    let specGiven := deps.any (fun x => attrD x "type" == "spec")
    -- a test case's spec dependency replaces the set's
    let setOk' := if specGiven then (setDeps.filter (fun x => attrD x "type" != "spec")).all depOk else setOk
    if !(setOk' && deps.all depOk) then
      t := { t with unsup := t.unsup + 1 }
      continue
    let envSpec : Option EnvSpec :=
      match (kidsNamed tc "environment").head? with
      | none => some {}
      | some e =>
        match attr e "ref" with
        | some r => (localEnvs.lookup r).orElse (fun _ => catEnvs.lookup r)
        | none => some (parseEnv dir e)
    let some spec := envSpec | do t := { t with unsup := t.unsup + 1 }; continue
    let some testNode := (kidsNamed tc "test").head? | do t := { t with fail := t.fail + 1 }; continue
    let src ← match attr testNode "file" with
      | some f => pure ((← readFileSafe (dir ++ "/" ++ f)).getD "")
      | none => pure testNode.textContent
    if o.trace then IO.eprintln s!"  test {name}"
    if o.hang.contains name then
      t := { t with fail := t.fail + 1 }
      if o.listFails then fails := fails ++ [s!"FAIL {setName}/{name}: not run (does not terminate in this implementation)"]
      continue
    match ← buildEnv spec cache with
    | .error why =>
        t := { t with unsup := t.unsup + 1 }
        if o.listFails then fails := fails ++ [s!"UNSUP {setName}/{name}: {why}"]
    | .ok env =>
      let (scanned, scannedBins) ← scanResources o.root dir src
      let env := { env with resources := env.resources ++ scanned,
                            resourceBytes := env.resourceBytes ++ scannedBins }
      let (res, env) ← match spec.sandpit with
        | some sp => L4Factoidal.EXPath.File.evalSandpit (o.fileHost == "io") sp env src
        | none => pure (evalIn env src, env)
      let some r := (kidsNamed tc "result").head? | do t := { t with fail := t.fail + 1 }; continue
      let r ← resolveXmlFiles o.root dir 100 r
      match (kids r).head? with
      | none => t := { t with fail := t.fail + 1 }
      | some a =>
        let bad := Harness.Qt4Defective.defective.lookup name
        match checkAssert env res 100 a, bad with
        | .pass, none => t := { t with pass := t.pass + 1 }
        | .pass, some iss =>
            t := { t with fail := t.fail + 1 }
            fails := fails ++ [s!"FAIL {setName}/{name}: STALE exclusion: the test passes; remove it from Harness.Qt4Defective in Harness/Qt4Run.lean ({iss})"]
        | .fail _, some iss =>
            t := { t with excl := t.excl + 1 }
            if o.listFails then fails := fails ++ [s!"EXCLUDED {setName}/{name}: defective test data, {iss}"]
        | .fail why, none =>
            t := { t with fail := t.fail + 1 }
            if o.listFails then fails := fails ++ [s!"FAIL {setName}/{name}: {why}"]
        | .unsupported _, _ => t := { t with unsup := t.unsup + 1 }
  if let some pf := o.progress then
    IO.FS.writeFile pf s!"{t.pass} {t.fail} {t.unsup} DONE {t.excl}\n"
  return (setName, t, fails)

/-- Run one test set in a child process with a time limit (an IO loop
    that ends on an outside event: the child exiting, or the clock). -/
def runIsolated (o : Opts) (secs : Nat) (fam setName file : String) : IO (Tally × String) := do
  let pf := (← IO.getEnv "TMPDIR").getD "/tmp" ++ "/l4qt4-progress-" ++ setName
  IO.FS.writeFile pf ""
  let mut args : Array String := #["--root", o.root, "--family", fam, "--set", setName, "--progress", pf]
  if o.listFails then args := args.push "--list-fails"
  for h in o.hang do args := args ++ #["--hang", h]
  args := args ++ #["--file-host", o.fileHost]
  let child ← IO.Process.spawn { cmd := (← IO.appPath).toString, args, stdin := .null, stdout := .inherit, stderr := .null }
  let start ← IO.monoMsNow
  let mut finished := false
  repeat
    match ← child.tryWait with
    | some _ => finished := true; break
    | none =>
      if (← IO.monoMsNow) - start > secs * 1000 then break
      IO.sleep 50
  if !finished then
    child.kill
    let _ ← child.wait
  let line := ((← readFileSafe pf).getD "").trimAscii.toString
  try IO.FS.removeFile pf catch _ => pure ()
  let parts := line.splitOn " "
  let num (i : Nat) : Nat := ((parts.getD i "0").toNat?).getD 0
  let t : Tally := ⟨num 0, num 1, num 2, num 4⟩
  let last := parts.getD 3 ""
  if finished && last == "DONE" then return (t, "")
  -- count the test cases of the set; those not reached are failures
  let total ← match ← readFileSafe file with
    | some txt => match parseXML txt with
      | .ok d => pure (kidsNamed d.root "test-case").length
      | .error _ => pure t.total
    | none => pure t.total
  let rest := total - t.total - t.excl
  return ({ t with fail := t.fail + rest },
    s!" [TIMEOUT or crash at test {last}: {rest} tests not finished, counted as fail]")

def main (args : List String) : IO UInt32 := do
  let o := parseArgs args {}
  let fams := if o.families.isEmpty then ["prod", "op", "fn", "map", "array", "math"] else o.families
  let some ctxt ← readFileSafe (o.root ++ "/catalog.xml")
    | IO.eprintln s!"cannot read {o.root}/catalog.xml"; return 2
  let cat ← match parseXML ctxt with
    | .ok d => pure d.root
    | .error _ => IO.eprintln "cannot parse catalog.xml"; return 2
  let catEnvs := (kidsNamed cat "environment").filterMap (fun e =>
    match attr e "name" with | some n => some (n, parseEnv o.root e) | none => none)
  let cache ← IO.mkRef ([] : List (String × Doc))
  let mut famT : List (String × Tally) := fams.map (fun f => (f, {}))
  let mut total : Tally := {}
  for s in kidsNamed cat "test-set" do
    let file := attrD s "file"
    let fam := ((file.splitOn "/").headD "")
    if !fams.contains fam then continue
    if let some want := o.set then
      if attrD s "name" != want then continue
    if o.listFails then IO.eprintln s!"running {file}"
    let (nm, t, fails, note) ← match o.isolate with
      | some secs =>
        let (t, note) ← runIsolated o secs fam (attrD s "name") (o.root ++ "/" ++ file)
        pure (attrD s "name", t, ([] : List String), note)
      | none =>
        let (nm, t, fails) ← runSet o catEnvs cache (o.root ++ "/" ++ file)
        pure (nm, t, fails, "")
    if !o.childMode then IO.println s!"{fam}/{nm}: {t.show}{note}"
    for f in fails do IO.println ("  " ++ f)
    (← IO.getStdout).flush
    famT := famT.map (fun (f, x) => if f == fam then (f, x.add t) else (f, x))
    total := total.add t
  if o.childMode then return 0
  IO.println "== families =="
  for (f, t) in famT do IO.println s!"{f}: {t.show}"
  IO.println s!"TOTAL: {total.show}"
  return 0

end Harness.Qt4Run

def main (args : List String) : IO UInt32 := Harness.Qt4Run.main args
