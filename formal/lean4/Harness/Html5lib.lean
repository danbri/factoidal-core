/-
Harness.Html5lib — `l4html5lib`: the Lean HTML parser (`L4Factoidal/HTML/`)
over the html5lib test formats (https://github.com/danbri/factoidal/issues/1167,
milestone 5).

  l4html5lib tree FILE.dat ...       tree construction tests (web-platform-tests
                                     html/syntax/parsing/resources/*.dat)
  l4html5lib tokenizer FILE.test ... tokenizer tests (html5lib-tests tokenizer/)
  l4html5lib dump [--fragment CTX] [--script-on] FILE
                                     print the tree of one input in the test format

`tree` and `tokenizer` print `FILE: N pass, M fail (out of T)` per file and a
total line, and exit 0 only when no case fails. `--verbose` prints each failing
case. The test files are read and parsed here, in Lean.
-/
import L4Factoidal.HTML.TreeBuilder
import L4Factoidal.JSON.Parser

namespace Harness.Html5lib

open L4Factoidal.HTML

/-! ## The tree dump format of html5lib tree construction tests -/

def nsPrefix : NS → String
  | .html => ""
  | .svg => "svg "
  | .math => "math "

/-- "Adjust foreign attributes" (§13.2.6.1): the attribute name string of the
test format for an attribute of an SVG or MathML element. -/
def foreignAttrName (n : String) : String :=
  match n with
  | "xlink:actuate" | "xlink:arcrole" | "xlink:href" | "xlink:role" | "xlink:show" | "xlink:title"
  | "xlink:type" => "xlink " ++ (n.drop 6).toString
  | "xml:lang" | "xml:space" => "xml " ++ (n.drop 4).toString
  | "xmlns" => "xmlns xmlns"
  | "xmlns:xlink" => "xmlns xlink"
  | _ => n

def indentStr (d : Nat) : String := "| " ++ String.ofList (List.replicate (2 * d) ' ')

/-- The lines of the subtree of `id` (its children), at depth `d`. A loop with
an explicit stack of open frames, not recursion per node. -/
def dumpChildren (dom : Array DNode) (root : Nat) (d0 : Nat) : Array String := Id.run do
  let mut out : Array String := #[]
  -- frames: (node id, depth); pushed in reverse document order
  let mut work : List (Nat × Nat) := (dom[root]!.kids.toList.map (·, d0))
  for _ in [0:dom.size * 2 + 2] do
    match work with
    | [] => break
    | (id, d) :: rest =>
      work := rest
      let n := dom[id]!
      let ind := indentStr d
      match n.kind with
      | .text => out := out.push (ind ++ "\"" ++ n.data ++ "\"")
      | .comment => out := out.push (ind ++ "<!-- " ++ n.data ++ " -->")
      | .pi => out := out.push (ind ++ "<?" ++ n.name ++ " " ++ n.data ++ "?>")
      | .doctype =>
        let ids := if n.pubId.isEmpty && n.sysId.isEmpty then ""
          else " \"" ++ n.pubId ++ "\" \"" ++ n.sysId ++ "\""
        out := out.push (ind ++ "<!DOCTYPE " ++ n.name ++ ids ++ ">")
      | .doc => pure ()
      | .elem =>
        out := out.push (ind ++ "<" ++ nsPrefix n.ns ++ n.name ++ ">")
        let names := n.attrs.toList.map fun a =>
          ((if n.ns == .html then a.1 else foreignAttrName a.1), a.2)
        let sorted := names.toArray.qsort (fun a b => a.1 < b.1)
        for a in sorted do
          out := out.push (indentStr (d + 1) ++ a.1 ++ "=\"" ++ a.2 ++ "\"")
        if n.ns == .html && n.name == "template" then
          out := out.push (indentStr (d + 1) ++ "content")
          work := n.kids.toList.map (·, d + 2) ++ work
        else
          work := n.kids.toList.map (·, d + 1) ++ work
  return out

/-! ## The .dat format -/

structure DatTest where
  data : String
  errors : Nat
  fragment : Option String
  scripting : Option Bool
  document : String
  line : Nat

/-- Split a .dat file into tests (README of `resources/`). -/
def parseDat (txt : String) : Array DatTest := Id.run do
  let lines := (txt.splitOn "\n").toArray
  let mut out : Array DatTest := #[]
  let mut i := 0
  let n := lines.size
  for _ in [0:n + 1] do
    if i ≥ n then break
    if lines[i]! != "#data" then
      i := i + 1
      continue
    let start := i + 1
    i := i + 1
    let mut dataLines : Array String := #[]
    while i < n && lines[i]! != "#errors" do
      dataLines := dataLines.push lines[i]!
      i := i + 1
    i := i + 1
    let mut errs := 0
    let mut frag : Option String := none
    let mut scr : Option Bool := none
    let mut docLines : Array String := #[]
    let mut sect := "errors"
    while i < n do
      let l := lines[i]!
      if (l == "#data" || l == "#description") && sect == "document" && docLines.back? == some "" then break
      if sect != "document" && l.startsWith "#" then
        if l == "#document-fragment" then
          sect := "fragment"
        else if l == "#script-off" then scr := some false
        else if l == "#script-on" then scr := some true
        else if l == "#document" then sect := "document"
        else if l == "#new-errors" then sect := "errors"
        else sect := "other"
      else if sect == "errors" && l != "" then errs := errs + 1
      else if sect == "fragment" && l != "" then frag := some l
      else if sect == "document" then docLines := docLines.push l
      i := i + 1
    -- the blank line that separates tests, and the final newline of the file
    for _ in [0:docLines.size] do
      if docLines.back? == some "" then docLines := docLines.pop
    out := out.push { data := "\n".intercalate dataLines.toList, errors := errs, fragment := frag,
                      scripting := scr, document := "\n".intercalate docLines.toList, line := start }
  return out

def contextOf (s : String) : NS × String :=
  if s.startsWith "svg " then (.svg, (s.drop 4).toString)
  else if s.startsWith "math " then (.math, (s.drop 5).toString)
  else (.html, s)

def runTree (t : DatTest) (scripting : Bool) : String :=
  match t.fragment with
  | none =>
    let tb := parseDocumentState t.data scripting
    "\n".intercalate (dumpChildren tb.dom 0 0).toList
  | some c =>
    let (ns, nm) := contextOf c
    let (tb, root) := parseFragmentState ns nm t.data scripting
    "\n".intercalate (dumpChildren tb.dom root 0).toList

def treeFile (path : System.FilePath) (verbose : Bool) : IO (Nat × Nat) := do
  let txt ← IO.FS.readFile path
  let tests := parseDat txt
  let mut p := 0
  let mut f := 0
  for t in tests do
    let modes : List Bool := match t.scripting with
      | some b => [b]
      | none => [false, true]
    let mut ok := true
    for m in modes do
      let got := runTree t m
      if got != t.document then
        ok := false
        if verbose then
          IO.println s!"--- FAIL {path}:{t.line} scripting={m}{match t.fragment with | some c => " fragment=" ++ c | none => ""}\n#data\n{t.data}\n#expected\n{t.document}\n#got\n{got}"
    if ok then p := p + 1 else f := f + 1
  return (p, f)

end Harness.Html5lib

open Harness.Html5lib in
def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--show"
  let args := args.filter (· != "--show")
  match args with
  | "tree" :: files =>
    let mut tp := 0
    let mut tf := 0
    for fl in files do
      let (p, f) ← treeFile fl verbose
      IO.println s!"{(System.FilePath.mk fl).fileName.getD fl}: {p} pass, {f} fail (out of {p + f})"
      tp := tp + p
      tf := tf + f
    IO.println s!"tree construction: {tp} pass, {tf} fail (out of {tp + tf})"
    pure (if tf == 0 && tp > 0 then 0 else 1)
  | ["dump", file] =>
    let src ← IO.FS.readFile file
    let tb := L4Factoidal.HTML.parseDocumentState src
    for l in dumpChildren tb.dom 0 0 do IO.println l
    pure 0
  | _ =>
    IO.eprintln "usage: l4html5lib tree FILE.dat ... | tokenizer FILE.test ... | dump FILE"
    pure 2
