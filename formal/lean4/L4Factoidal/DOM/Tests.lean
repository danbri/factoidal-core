/-
L4Factoidal.DOM.Tests — `#guard` checks of the DOM arena, checked when this
module is built. They cover `moveBefore` (the "move" algorithm, DOM §4.2.3),
which the jsdom differential (`tests/dom/diff.mjs`) cannot check: jsdom 30.1.3
has no `moveBefore`. Each expected result is read from the steps of the
algorithm in whatwg/dom `3c53f93a`.
-/
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.DOM.Tests

open L4Factoidal.DOM

/-- The first element in tree order with local name `nm`. -/
def el (d : Dom) (nm : String) : NodeId :=
  ((d.treeOrder 0).find? fun k => (d.get k).type == .element && (d.get k).lname == nm).getD 0

def kidNames (d : Dom) (p : NodeId) : List String :=
  (d.get p).kids.toList.map fun k => let x := d.get k; if x.type == .text then "#" ++ x.data else x.lname

def doc0 : Dom := parseHtmlDocument "<!DOCTYPE html><body><p>a<i>i</i></p><b>x</b>t</body>"

def errOf : Res Unit → Option DomError
  | (_, .error e) => some e
  | (_, .ok _) => none

/-- The arena after an operation that must not throw. -/
def okOf : Res Unit → Option Dom
  | (d, .ok ()) => some d
  | (_, .error _) => none

-- move: `b` before `p` within body; the arena stays well-formed
#guard (okOf (doc0.move (el doc0 "b") (el doc0 "body") (some (el doc0 "p")))).map
  (fun d => (kidNames d (el d "body"), d.wellFormed)) == some (["b", "p", "#t"], true)
-- move: a node to the end of a new parent in the same tree
#guard (okOf (doc0.move (el doc0 "b") (el doc0 "p") none)).map
  (fun d => (kidNames d (el d "p"), kidNames d (el d "body"))) == some (["#a", "i", "b"], ["p", "#t"])
-- move: child is the node itself: the reference child is its next sibling (no change)
#guard (okOf (doc0.move (el doc0 "b") (el doc0 "body") (some (el doc0 "b")))).map
  (fun d => kidNames d (el d "body")) == some ["p", "b", "#t"]
-- step 1: a node of another root (a new element) cannot be moved
#guard (match doc0.createElement 0 "span" with
  | (d, .ok s) => errOf (d.move s (el d "body") none)
  | (_, .error _) => none) == some .hierarchyRequest
-- step 2: a node cannot be moved into its own descendant
#guard errOf (doc0.move (el doc0 "p") (el doc0 "i") none) == some .hierarchyRequest
-- step 3: the reference child must be a child of the new parent
#guard errOf (doc0.move (el doc0 "b") (el doc0 "body") (some (el doc0 "i"))) == some .notFound
-- step 4: a doctype is not an Element or CharacterData node
#guard errOf (doc0.move ((doc0.get 0).kids[0]!) (el doc0 "body") none) == some .hierarchyRequest
-- step 5: a Text node cannot be moved into a document
#guard errOf (doc0.move ((doc0.get (el doc0 "body")).kids[2]!) 0 none) == some .hierarchyRequest
-- step 6: the document has an element child already
#guard errOf (doc0.move (el doc0 "b") 0 none) == some .hierarchyRequest

def tpl : Dom := parseHtmlDocument "<template><p>x</p></template>"
-- a template element cannot go into its own template contents: the contents'
-- host is the element, so it is a host-including inclusive ancestor (DOM §4.2.2)
#guard errOf (tpl.appendChild ((tpl.get (el tpl "template")).content.getD 0) (el tpl "template")) ==
  some .hierarchyRequest
-- the parser's template children are the children of the contents fragment
#guard kidNames tpl ((tpl.get (el tpl "template")).content.getD 0) == ["p"] && tpl.wellFormed
-- a deep clone of a template element clones its contents
#guard (let (d, c) := tpl.cloneNode (el tpl "template") true
  kidNames d ((d.get c).content.getD 0)) == ["p"]

end L4Factoidal.DOM.Tests
