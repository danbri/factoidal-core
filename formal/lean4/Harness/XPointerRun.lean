/-
Harness/XPointerRun — XPointer (Framework, element(), xmlns(),
xpointer()) over the pointers of the W3C XInclude test suite
(`third_party/testing/xinclude/`, provenance: its PROVENANCE.md).

Every `xi:include` element of a test document that has an `xpointer`
attribute gives one case: the pointer is resolved against the resource
that `href` names (the including document when `href` is empty; a
fragment identifier in `href` is dropped), parsed with its DTD. The
outcome is written as one line: the nodes identified (each serialized),
`no-subresource`, or `syntax-error`. The expected lines are
`tests/xpointer/expected.tsv`; each was checked by hand against the
target document and, where the suite has one, the expected output of the
including test case. Two lines are `no-subresource` on the source
infoset and identify an element only on the acquired infoset, after the
target's own inclusions (XInclude 1.1 §4.2): `EdUni/test/extract.xml`
(`chap1`) and `Harold/test/tobintop.xml` (`element(/1/1/2)`). They are
checked as XInclude cases when XInclude calls this module.

Usage: `lake exe l4xpointer [suite-dir] [expected.tsv]`; with `--write`
as a third argument the lines are written instead of compared. Exit 0
when every case gives its expected line.
-/
import L4Factoidal.XML.XPointerXPath
import L4Factoidal.XML.Enc

open L4Factoidal.XML
open L4Factoidal.XML.XPointer
open L4Factoidal.XML.XPointerXPath
open L4Factoidal.XML.Enc (serNode)

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

/-- The files under `dir`, to depth `fuel` (the suite is four levels deep). -/
def walkFiles : Nat → System.FilePath → IO (List System.FilePath)
  | 0, _ => return []
  | f + 1, dir => do
    let mut out := []
    for e in ← dir.readDir do
      if ← e.path.isDir then out := out ++ (← walkFiles f e.path)
      else out := out ++ [e.path]
    return out

/-- The `(href, xpointer)` of every include element with a pointer, in
document order. -/
def includes : Nat → Node → List (String × String)
  | 0, _ => []
  | f + 1, .element tag attrs kids =>
    let local_ := (tag.splitOn ":").getLast!
    let here := if local_ == "include" then
        match attrs.find? (·.name == "xpointer") with
        | some xp => [((attrs.find? (·.name == "href")).map (·.value) |>.getD "", xp.value)]
        | none => []
      else []
    here ++ kids.flatMap (includes f)
  | _, _ => []

def showHit : Hit → String
  | .node n _ => serNode "" n
  | .attr a => "@" ++ a.name ++ "=\"" ++ a.value ++ "\""
  | .nsNode p u => "namespace " ++ p ++ "=" ++ u

def flat (s : String) : String :=
  String.ofList (s.toList.map (fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c))

def showOutcome : Outcome → String
  | .hits hs => "hits " ++ toString hs.length ++ ": " ++ flat (String.intercalate " | " (hs.map showHit))
  | .noSubresource => "no-subresource"
  | .syntaxError _ => "syntax-error"

def main (args : List String) : IO UInt32 := do
  let suite := args.getD 0 "../../third_party/testing/xinclude/XIncl20060927"
  let expPath := args.getD 1 "../../tests/xpointer/expected.tsv"
  let write := args.getD 2 "" == "--write"
  let paths ← walkFiles 16 suite
  -- the parser's resolver is pure, so every file of the suite is read first
  let mut files : Std.HashMap String String := {}
  for p in paths do
    let rel := normPath ((p.toString.drop (suite.length + 1)).toString)
    match ← (IO.FS.readFile p).toBaseIO with
    | .ok t => files := files.insert rel t
    | .error _ => pure ()
  let parseAt (rel : String) : Option Document :=
    match files.get? rel with
    | none => none
    | some src =>
      let resolve : Resolver := fun sys => files.get? (joinRef (dirOf rel) sys)
      (parseXMLWith resolve src).toOption
  let rels := (files.toList.map (·.1)).filter (·.endsWith ".xml") |>.toArray.qsort (· < ·)
  let mut lines : Array String := #[]
  for rel in rels do
    match parseAt rel with
    | none => pure ()
    | some d =>
      for (href, xp) in includes 100000 d.root do
        let h := (href.splitOn "#").head!
        let target := if h == "" then rel else joinRef (dirOf rel) h
        let out := match parseAt target with
          | none => "target-unreadable"
          | some td => showOutcome (resolveAll td xp)
        lines := lines.push (rel ++ "\t" ++ xp ++ "\t" ++ out)
  if write then
    IO.FS.writeFile expPath (String.intercalate "\n" lines.toList ++ "\n")
    IO.println s!"wrote {lines.size} lines to {expPath}"
    return 0
  let expected := ((← IO.FS.readFile expPath).splitOn "\n").filter (· != "") |>.toArray
  let mut pass := 0
  let mut fail := 0
  for i in [0:max lines.size expected.size] do
    let got := lines.getD i "(missing)"
    let exp := expected.getD i "(missing)"
    if got == exp then pass := pass + 1
    else
      fail := fail + 1
      IO.println s!"FAIL\n  expected: {exp}\n  got:      {got}"
  IO.println s!"l4xpointer: {pass} pass, {fail} fail (out of {pass + fail})"
  return if fail == 0 then 0 else 1
