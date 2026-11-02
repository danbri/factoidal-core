/-
Harness/XIncludeRun — the XInclude processor (`XInclude.expandX`, with
the four XPointer schemes) over the W3C XInclude test suite
(`third_party/testing/xinclude/XIncl20060927`, provenance: its
PROVENANCE.md; 175 cases, `testdescr.xml`).

A `success` case passes when processing gives a document whose document
element, under Canonical XML 1.0 with comments, is the document element
of the case's expected output under the same canonicalization. An `error`
case passes when parsing or processing gives a fatal error, or a resource
error with no fallback.

Expected failures are listed in `tests/xinclude/expected-fail.tsv`
(case id, open issue URL). A listed case that passes is STALE and fails
the run, so that the list cannot outlive the gap.

Usage: `lake exe l4xinclude [suite-dir] [expected-fail.tsv]`. Exit 0 when
every case passes or is a listed expected failure, and none is stale.
-/
import L4Factoidal.XPath4.XInclude
import L4Factoidal.XML.XPointerXPath
import L4Factoidal.XML.Enc
import L4Factoidal.XML.C14n

open L4Factoidal.XML
open L4Factoidal.XPath4.XInclude
open L4Factoidal.XML.Enc (serNode)

namespace XIncludeRun

/-- `a/b/../c` gives `a/c`; `.` segments are dropped. -/
def normPath (p : String) : String :=
  let segs := (p.splitOn "/").foldl (fun (acc : List String) s =>
    if s == "." then acc
    else if s == ".." then (match acc with | _ :: r => r | [] => [])
    else s :: acc) []
  String.intercalate "/" segs.reverse

def dirOf (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => ""
  | ds => String.intercalate "/" ds

def joinRef (dir ref : String) : String :=
  if ref.startsWith "/" then ref else normPath (if dir == "" then ref else dir ++ "/" ++ ref)

/-- The files under `dir`, to depth `fuel`. -/
def walkFiles : Nat → System.FilePath → IO (List System.FilePath)
  | 0, _ => return []
  | f + 1, dir => do
    let mut out := []
    for e in ← dir.readDir do
      if ← e.path.isDir then out := out ++ (← walkFiles f e.path)
      else out := out ++ [e.path]
    return out

def attr (as : List Attribute) (n : String) : String :=
  ((as.find? (·.name == n)).map (·.value)).getD ""

structure Case where
  id : String
  path : String
  kind : String
  output : String
  features : String

/-- The test cases of `testdescr.xml`. -/
def cases (root : Node) : List Case :=
  match root with
  | .element _ _ groups => groups.flatMap (fun g => match g with
    | .element "testcases" gas tcs =>
      let base := attr gas "basedir"
      tcs.filterMap (fun t => match t with
        | .element "testcase" as kids =>
          let out := kids.findSome? (fun k => match k with
            | .element "output" _ [.text o] => some o.trimAscii.toString
            | _ => none)
          some { id := attr as "id", path := joinRef base (attr as "href"), kind := attr as "type",
                 output := (out.map (joinRef base)).getD "", features := attr as "features" }
        | _ => none)
    | _ => [])
  | _ => []

/-- A document element under Canonical XML 1.0 with comments. -/
def canonRoot (n : Node) : Except String String :=
  L4Factoidal.XML.C14n.canonString? L4Factoidal.XML.C14n.c10c (serNode "" n)

def main (args : List String) : IO UInt32 := do
  let suite := args.getD 0 "../../third_party/testing/xinclude/XIncl20060927"
  let xfPath := args.getD 1 "../../tests/xinclude/expected-fail.tsv"
  let paths ← walkFiles 16 suite
  let mut files : Std.HashMap String ByteArray := {}
  for p in paths do
    let rel := normPath ((p.toString.drop (suite.length + 1)).toString)
    files := files.insert rel (← IO.FS.readBinFile p)
  let resolverAt (rel : String) : Resolver := fun sys =>
    (files.get? (joinRef (dirOf rel) sys)).bind (fun bs => (decodeXmlBytes bs).toOption)
  let parseAt (rel : String) (bs : ByteArray) : Except String Document :=
    (parseXMLBytesWith (resolverAt rel) bs).mapError (·.message)
  let cfg : Cfg := {
    fetch := fun u => files.get? (normPath u)
    parseDoc := fun u bs => parseAt (normPath u) bs
    pointer := some L4Factoidal.XML.XPointerXPath.resolveAll }
  let some descr := files.get? "testdescr.xml" | do IO.eprintln "no testdescr.xml"; return 2
  let .ok dd := parseAt "testdescr.xml" descr | do IO.eprintln "testdescr.xml does not parse"; return 2
  let xfLines := (← (IO.FS.readFile xfPath).toBaseIO).toOption.getD ""
  let xfail : List String := (xfLines.splitOn "\n").filterMap (fun l =>
    if l.startsWith "#" || l.trimAscii.isEmpty then none else some ((l.splitOn "\t").headD ""))
  let mut pass := 0
  let mut fail := 0
  let mut xf := 0
  let mut stale := 0
  let all := cases dd.root
  for c in all do
    let got : Except String Document := match files.get? c.path with
      | none => .error ("missing " ++ c.path)
      | some bs => match parseAt c.path bs with
        | .error m => .error ("parse: " ++ m)
        | .ok d => (processDocument cfg 64 c.path d).mapError (·.msg)
    let (ok, why) : Bool × String :=
      if c.kind == "error" then
        match got with
        | .error _ => (true, "")
        | .ok d => (false, "no error; got " ++ serNode "" d.root)
      else match got with
        | .error m => (false, "error: " ++ m)
        | .ok d =>
          match files.get? c.output with
          | none => (false, "no output file " ++ c.output)
          | some obs => match parseAt c.output obs with
            | .error m => (false, "expected output does not parse: " ++ m)
            | .ok ed =>
              match canonRoot d.root, canonRoot ed.root with
              | .ok a, .ok b => if a == b then (true, "") else (false, "differs\n    got:      " ++ a ++ "\n    expected: " ++ b)
              | .error m, _ => (false, "canonicalization of the result: " ++ m)
              | _, .error m => (false, "canonicalization of the expected output: " ++ m)
    let listed := xfail.contains c.id
    if ok && listed then
      stale := stale + 1
      IO.println s!"STALE {c.id}: passes but is listed in {xfPath}"
    else if ok then pass := pass + 1
    else if listed then xf := xf + 1
    else
      fail := fail + 1
      IO.println s!"FAIL {c.id} ({c.kind}{if c.features == "" then "" else ", " ++ c.features}): {why}"
  IO.println s!"l4xinclude: {pass} pass, {fail} fail, {xf} expected failures, {stale} stale (out of {all.length})"
  return if fail == 0 && stale == 0 then 0 else 1

end XIncludeRun

def main (args : List String) : IO UInt32 := XIncludeRun.main args
