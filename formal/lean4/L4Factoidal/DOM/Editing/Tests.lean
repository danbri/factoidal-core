/-
L4Factoidal.DOM.Editing.Tests — `#guard` checks of the editing commands, checked when this
module is built. Each case is from the Web Platform Tests (`editing/data/*.js`): the input
with its selection markers (`[` and `]` in a Text node, `{` and `}` between nodes), the
commands, and the innerHTML the test expects (without the markers). The whole data set
(7,200 cases) is run by `tests/editing/run.sh`.

Also checked on each input here: the block-extended range contains the range (and a
counterexample to its idempotence), "restore the values" after "record the values" changes
nothing, and "delete the selection" leaves a collapsed range inside the editing host.
-/
import L4Factoidal.DOM.Editing.Commands
import L4Factoidal.DOM.Fragment
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.DOM.Editing.Tests
open L4Factoidal.DOM L4Factoidal.DOM.Range L4Factoidal.DOM.Editing L4Factoidal.DOM.Fragment

def page : String :=
  "<!doctype html><html><head></head><body><div id=test-container><div contenteditable></div><p>test</p></div></body></html>"

def removeChars (s : String) (cs : List Char) : String := String.ofList (s.toList.filter fun c => !cs.contains c)

/-- The editable `div` with `html` as its content and the selection its markers give. -/
def setup (html : String) : Dom × NodeId × Option Rng := Id.run do
  let d0 := parseHtmlDocument page
  let div := ((d0.treeOrder 0 true).find? fun n => (attr d0 n "contenteditable").isSome).getD 0
  let (d1, frag) := parseInto d0 0 htmlNS "div" html
  let mut d : Dom := d1
  for k in (d.get frag).kids do d := Dom.insert d k div none
  let mut start : Option BP := none
  let mut stop : Option BP := none
  for cur in d.treeOrder div false do
    if !isText d cur then continue
    let data := (d.get cur).data
    let p := (parentOf d cur).getD div
    let at_ := fun (c : Char) (drop : List Char) => ((data.toList.filter fun x => !drop.contains x).findIdx? (· == c))
    if let some i := at_ '[' [']', '{', '}'] then start := some ⟨cur, i⟩
    if let some i := at_ ']' ['[', '{', '}'] then stop := some ⟨cur, i⟩
    let i := indexOf d cur
    let clean := removeChars data ['[', ']', '{', '}']
    match at_ '{' ['[', ']', '}'] with
    | some 0 => start := some ⟨p, i⟩
    | some _ => start := some ⟨p, if clean.isEmpty then i else i + 1⟩
    | none => pure ()
    match at_ '}' ['[', ']', '{'] with
    | some 0 => stop := some ⟨p, i⟩
    | some _ => stop := some ⟨p, if clean.isEmpty then i else i + 1⟩
    | none => pure ()
    d := d.setNode cur fun x => { x with data := clean }
    if clean.isEmpty then d := d.remove cur
  match start, stop with
  | some a, some b => return (d, div, some (if position d a b == .after then ⟨a, a⟩ else ⟨a, b⟩))
  | _, _ => return (d, div, none)

/-- The innerHTML of the editable `div` after the commands, with `styleWithCSS` as given. -/
def run (html : String) (commands : List (String × String)) (css : Bool := false) : String :=
  let (d, div, sel) := setup html
  let ed := Ed.start d sel { css } {}
  let (_, ed) := (commands.forM (m := M) fun (c, v) => do let _ ← execCommand c v).run ed
  serialize ed.dom div false

/-- The answers of the three queries after the commands. -/
def query (html : String) (commands : List (String × String)) (q : String) : Bool × Bool × String :=
  let (d, _, sel) := setup html
  let ed := Ed.start d sel {} {}
  let (r, _) := (do
    commands.forM (m := M) fun (c, v) => do let _ ← execCommand c v
    return (← queryIndeterm q, ← queryState q, ← queryValue q)).run ed
  r

-- bold, italic, underline: editing/data/bold.js, italic.js, underline.js
#guard run "foo[bar]baz" [("bold", "")] == "foo<b>bar</b>baz"
#guard run "foo[bar]baz" [("bold", "")] (css := true) == "foo<span style=\"font-weight: bold\">bar</span>baz"
#guard run "foo<b>[bar]</b>baz" [("bold", "")] == "foobarbaz"
#guard run "foo[bar<i>baz]qoz</i>quz" [("bold", "")] == "foo<b>bar</b><i><b>baz</b>qoz</i>quz"
#guard run "foo[bar]baz" [("italic", "")] == "foo<i>bar</i>baz"
#guard run "foo[bar]baz" [("underline", "")] == "foo<u>bar</u>baz"
#guard run "foo[bar]baz" [("strikethrough", "")] == "foo<strike>bar</strike>baz"
#guard run "foo[bar]baz" [("subscript", "")] == "foo<sub>bar</sub>baz"
#guard query "foo[bar]baz" [("bold", "")] "bold" == (false, true, "")
#guard query "foo[bar]baz" [] "bold" == (false, false, "")
#guard query "foo[bar<b>baz]</b>" [] "bold" == (true, false, "")
-- a toggle with nothing to format sets the state override, and a second one undoes it
#guard query "foo[]bar" [("bold", "")] "bold" == (false, true, "")
#guard query "foo[]bar" [("bold", ""), ("bold", "")] "bold" == (false, false, "")
-- values: fontname.js, forecolor.js, fontsize.js, createlink.js
#guard run "foo[bar]baz" [("fontname", "sans-serif")] == "foo<font face=\"sans-serif\">bar</font>baz"
#guard run "foo[bar]baz" [("forecolor", "#0000FF")] == "foo<font color=\"#0000ff\">bar</font>baz"
#guard run "foo[bar]baz" [("fontsize", "4")] == "foo<font size=\"4\">bar</font>baz"
#guard run "foo[bar]baz" [("createlink", "http://www.google.com/")] == "foo<a href=\"http://www.google.com/\">bar</a>baz"
#guard run "foo<a href=http://www.google.com/>[bar]</a>baz" [("unlink", "")] == "foobarbaz"
#guard query "foo[bar]baz" [("forecolor", "#0000FF")] "forecolor" == (false, false, "rgb(0, 0, 255)")
-- block commands: justifycenter.js, formatblock.js, indent.js, insertorderedlist.js
#guard run "foo[]bar<p>extra" [("justifycenter", "")] (css := true) == "<div style=\"text-align: center\">foobar</div><p>extra</p>"
#guard query "<div style=text-align:center>foo[]bar</div>" [] "justifycenter" == (false, true, "center")
#guard run "<p>[foobar]</p>" [("formatblock", "<h1>")] == "<h1>foobar</h1>"
#guard run "<p>foo[bar]baz</p><p>extra</p>" [("indent", "")] == "<blockquote><p>foobarbaz</p></blockquote><p>extra</p>"
#guard run "<blockquote><p>foo[bar]</p><p>baz</p></blockquote><p>extra" [("outdent", "")] ==
  "<p>foobar</p><blockquote><p>baz</p></blockquote><p>extra</p>"
#guard run "foo[]bar" [("insertorderedlist", "")] == "<ol><li>foobar</li></ol>"
#guard run "<ol><li>foo[]bar</li></ol>" [("insertorderedlist", "")] == "<div>foobar</div>"
-- deleting and inserting: delete.js, forwarddelete.js, insertparagraph.js, inserttext.js
#guard run "foo[]bar" [("delete", "")] == "fobar"
#guard run "foo[bar]baz" [("delete", "")] == "foobaz"
#guard run "<p>foo</p><p>[]bar</p>" [("delete", "")] == "<p>foobar</p>"
#guard run "foo[]bar" [("forwarddelete", "")] == "fooar"
#guard run "<p>foo[]bar</p>" [("insertparagraph", "")] == "<p>foo</p><p>bar</p>"
#guard run "foo[]bar" [("inserttext", "a")] == "fooabar"
#guard run "foo[]bar" [("insertlinebreak", "")] == "foo<br>bar"
#guard run "foo[]bar" [("inserthorizontalrule", "")] == "foo<hr>bar"
#guard run "foo[]bar" [("inserthtml", "<b>ab</b>")] == "foo<b>ab</b>bar"
#guard run "foo[]bar" [("insertimage", "/img/lion.svg")] == "foo<img src=\"/img/lion.svg\">bar"
-- nothing outside the editing host changes: a selection outside it enables no command
#guard (let (d, _, _) := setup "foo"
  let p := ((d.treeOrder 0 true).find? fun n => isHtml d n ["p"]).getD 0
  let ed := Ed.start d (some ⟨⟨p, 0⟩, ⟨p, 1⟩⟩) {} {}
  let (ok, ed') := (execCommand "bold" "").run ed
  !ok && ed'.log.isEmpty)

/-- The inputs the properties below are checked on. -/
def inputs : List String :=
  ["foo[bar]baz", "<p>[foo</p><p>bar]</p>", "<b>foo[bar</b><i>baz]qoz</i>", "<ol><li>foo[bar]</li><li>baz</li></ol>",
   "<p>foo<br>[bar]<br>baz</p>", "<div><p>fo[o</p><blockquote><p>b]ar</p></blockquote></div>",
   "<table><tbody><tr><td>fo[o</td><td>b]ar</td></tr></tbody></table>", "foo[]bar", "<p>{}<br></p>"]

-- the block-extended range contains the range
#guard inputs.all fun html =>
  let (d, _, sel) := setup html
  let ed := Ed.start d sel {} {}
  let r := activeOf ed
  let x := blockExtend ed r
  position d x.start r.start != .after && position d x.stop r.stop != .before

-- block-extend is not idempotent: here the end stops after a `br` (a block start point,
-- not a block end point), and a second block-extend moves it to the end of the block
#guard (let (d, _, sel) := setup "<p>foo<br>[bar]<br>baz</p>"
  let ed := Ed.start d sel {} {}
  let x := blockExtend ed (activeOf ed)
  blockExtend ed x != x)

-- "restore the values" after "record the values" changes nothing
#guard inputs.all fun html =>
  let (d, div, sel) := setup html
  let ed := Ed.start d sel {} {}
  let nodes := (d.treeOrder div false).filter (isEditable ed)
  let (_, ed') := (restoreValues (recordValues ed nodes)).run ed
  ed'.log.isEmpty

-- "delete the selection" leaves a collapsed range, inside the editing host
#guard inputs.all fun html =>
  let (d, div, sel) := setup html
  let ed := Ed.start d sel {} {}
  let (_, ed') := deleteSelection.run ed
  let r := activeOf ed'
  r.collapsed && ed'.dom.isInclusiveAncestor div r.start.node

end L4Factoidal.DOM.Editing.Tests
