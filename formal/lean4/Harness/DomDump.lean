/-
Harness.DomDump — the tree dump format of the html5lib tree construction tests
(`#document` section), over the DOM arena (`L4Factoidal/DOM/Arena.lean`).

Used by `l4html5lib dom-tree` (the web-platform-tests tree construction tests,
through `DOM.ofTreeBuilder`) and by `l4dom ops` (the differential test against
jsdom, `tests/dom/diff.mjs`, which prints the same format).
-/
import L4Factoidal.DOM.Arena

namespace Harness.DomDump

open L4Factoidal.DOM

def indentStr (d : Nat) : String := "| " ++ String.ofList (List.replicate (2 * d) ' ')

/-- The display name of an element in the test format. -/
def elemName (n : Node) : String :=
  if n.ns == some htmlNS then n.lname
  else if n.ns == some svgNS then "svg " ++ n.lname
  else if n.ns == some mathmlNS then "math " ++ n.lname
  else match n.ns with
    | some u => "{" ++ u ++ "} " ++ n.lname
    | none => n.lname

/-- The display name of an attribute in the test format. -/
def attrName (a : Attr) : String :=
  if a.ns == some xlinkNS then "xlink " ++ a.lname
  else if a.ns == some xmlNS then "xml " ++ a.lname
  else if a.ns == some xmlnsNS then "xmlns " ++ a.lname
  else a.qname

/-- The lines of the tree at `root`. A document prints its children at depth
0; any other node prints itself at depth 0 and its children below it. A loop
with a work list of (node, depth), not recursion per node. -/
def dump (d : Dom) (root : NodeId) : Array String := Id.run do
  let mut out : Array String := #[]
  let r := d.get root
  let mut work : List (NodeId × Nat) :=
    if r.type == .document then r.kids.toList.map (·, 0) else [(root, 0)]
  for _ in [0:2 * d.size + 2] do
    match work with
    | [] => break
    | (id, dp) :: rest =>
      work := rest
      let n := d.get id
      let ind := indentStr dp
      match n.type with
      | .text | .cdata => out := out.push (ind ++ "\"" ++ n.data ++ "\"")
      | .comment => out := out.push (ind ++ "<!-- " ++ n.data ++ " -->")
      | .pi => out := out.push (ind ++ "<?" ++ n.lname ++ " " ++ n.data ++ "?>")
      | .doctype =>
        let ids := if n.pubId.isEmpty && n.sysId.isEmpty then ""
          else " \"" ++ n.pubId ++ "\" \"" ++ n.sysId ++ "\""
        out := out.push (ind ++ "<!DOCTYPE " ++ n.lname ++ ids ++ ">")
      | .document => out := out.push (ind ++ "#document")
      | .fragment => out := out.push (ind ++ "#document-fragment")
      | .element =>
        out := out.push (ind ++ "<" ++ elemName n ++ ">")
        let sorted := (n.attrs.map fun a => (attrName a, a.value)).qsort (fun a b => a.1 < b.1)
        for a in sorted do
          out := out.push (indentStr (dp + 1) ++ a.1 ++ "=\"" ++ a.2 ++ "\"")
        match n.content with
        | some c =>
          out := out.push (indentStr (dp + 1) ++ "content")
          work := (d.get c).kids.toList.map (·, dp + 2) ++ n.kids.toList.map (·, dp + 1) ++ rest
        | none => work := n.kids.toList.map (·, dp + 1) ++ rest
      if n.type == .document || n.type == .fragment then
        if id != root || r.type != .document then
          work := n.kids.toList.map (·, dp + 1) ++ work
  return out

end Harness.DomDump
