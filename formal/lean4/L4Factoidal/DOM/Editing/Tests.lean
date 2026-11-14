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
import L4Factoidal.DOM.Editing.Keys
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
-- blocks with different white-space (editing/other/join-different-white-space-style-paragraphs.html):
-- only the first line joins, in a span that keeps its white-space
#guard run "<div style=\"white-space:normal\">abc[]</div><div style=\"white-space:pre\">def</div>" [("forwarddelete", "")] ==
  "<div style=\"white-space:normal\">abc<span style=\"white-space: pre\">def</span></div>"
#guard run "<div style=\"white-space:normal\">abc</div><div style=\"white-space:pre\">[]def\nghi</div>" [("delete", "")] ==
  "<div style=\"white-space:normal\">abc<span style=\"white-space: pre\">def</span></div><div style=\"white-space:pre\">ghi</div>"
#guard run "<div style=\"white-space:pre\">abc[]</div><div style=\"white-space:normal\"><b>def<br></b>ghi</div>" [("forwarddelete", "")] ==
  "<div style=\"white-space:pre\">abc<span style=\"white-space: normal\"><b>def</b></span></div><div style=\"white-space:normal\">ghi</div>"
#guard run "abc[]<div style=\"white-space:pre\">def\nghi</div>" [("forwarddelete", "")] ==
  "abc<span style=\"white-space: pre\">def</span><div style=\"white-space:pre\">ghi</div>"
#guard run "<div style=\"white-space:pre\">abc[]</div>def<br>ghi" [("forwarddelete", "")] ==
  "<div style=\"white-space:pre\">abc<span style=\"white-space: normal\">def</span></div>ghi"
-- a line break where white-space keeps line feeds is a line feed (editing/other/insertlinebreak-with-white-space-style)
#guard run "<div style=\"white-space:pre\">a[]bc</div>" [("insertlinebreak", "")] == "<div style=\"white-space:pre\">a\nbc</div>"
#guard run "<div style=\"white-space:pre\">abc[]</div>" [("insertlinebreak", "")] == "<div style=\"white-space:pre\">abc\n<br></div>"
-- a block span splits like a paragraph (editing/other/insertparagraph-in-editing-host-cannot-have-div)
#guard run "<span style=\"display:block\">a[]b</span>" [("insertparagraph", "")] ==
  "<span style=\"display:block\">a</span><span style=\"display:block\">b</span>"
-- an inline box is content of the line, not a paragraph (editing/other/insertparagraph-with-white-space-style)
#guard run "<div style=\"display:inline; white-space:pre\">a[]bc</div>" [("insertparagraph", "")] ==
  "<div><div style=\"display:inline; white-space:pre\">a</div></div><div><div style=\"display:inline; white-space:pre\">bc</div></div>"
-- a flex item splits like a paragraph (editing/data/insertparagraph.js)
#guard run "<div style=display:flex><span>a[]bc</span></div>" [("insertparagraph", "")] ==
  "<div style=\"display:flex\"><span>a</span><span>bc</span></div>"
-- text typed at the edge of a link stays outside it (editing/other/typing-around-link-element-*)
#guard run "<p><a href=\"about:blank\">abc[]</a></p>" [("inserttext", "X"), ("inserttext", "Y")] ==
  "<p><a href=\"about:blank\">abc</a>XY</p>"
#guard run "<p><b><a href=\"about:blank\">[]abc</a></b></p>" [("inserttext", "X")] ==
  "<p><b>X<a href=\"about:blank\">abc</a></b></p>"
#guard run "<p><a href=\"about:blank\">a[]bc</a></p>" [("inserttext", "X")] == "<p><a href=\"about:blank\">aXbc</a></p>"
-- inline markup is inserted between the halves of the inline element at the caret
-- (editing/other/inserthtml-do-not-preserve-inline-styles.html)
#guard run "<b>a[]c</b>" [("inserthtml", "<font face=\"monospace\">b</font>")] ==
  "<b>a</b><font face=\"monospace\">b</font><b>c</b>"
#guard run "<b>abc[]</b>" [("inserthtml", "<i>def</i>")] == "<b>abc</b><i>def</i>"
-- a plaintext-only editing host takes text only (editing/plaintext-only/insertHTML.html, styling-commands.html)
#guard run "<div contenteditable=\"plaintext-only\">A[]B</div>" [("inserthtml", "<div>abc</div><div>d  ef</div>")] ==
  "<div contenteditable=\"plaintext-only\">Aabc<br>d efB</div>"
#guard run "<div contenteditable=\"plaintext-only\">A[]B</div>" [("inserthtml", "<script>x</script><b>y</b>")] ==
  "<div contenteditable=\"plaintext-only\">AyB</div>"
#guard run "<div contenteditable=\"plaintext-only\">a[b]c</div>" [("bold", "")] ==
  "<div contenteditable=\"plaintext-only\">abc</div>"
-- nothing outside the editing host changes: a selection outside it enables no command
#guard (let (d, _, _) := setup "foo"
  let p := ((d.treeOrder 0 true).find? fun n => isHtml d n ["p"]).getD 0
  let ed := Ed.start d (some ⟨⟨p, 0⟩, ⟨p, 1⟩⟩) {} {}
  let (ok, ed') := (execCommand "bold" "").run ed
  !ok && ed'.log.isEmpty)

/-- The focus after `Selection.modify("move", direction, granularity)` from the caret of
`html`: the data of its Text node and the offset. -/
def modified (html : String) (forward : Bool) (granularity : String) : Option (String × Nat) :=
  let (d, div, sel) := setup html
  let ed := Ed.start d sel {} {}
  (modifyFocus ed div true (activeOf ed).stop forward granularity).map fun bp => ((d.get bp.node).data, bp.offset)

-- Selection.modify by character and by word (selection/contenteditable/modify-around-inline-element-boundary)
#guard modified "ab[]c" true "character" == some ("abc", 3)
#guard modified "abc []<b>def</b>" true "character" == some ("def", 1)
#guard modified "abc <b>[]def</b>" false "character" == some ("abc ", 3)
#guard modified "foo []bar baz" true "word" == some ("foo bar baz", 7)
#guard modified "foo bar[] baz" false "word" == some ("foo bar baz", 4)
#guard modified "<p>fo[]o</p><p>bar</p>" true "paragraphboundary" == some ("foo", 3)
-- keys: what each does, and the caret keys
#guard keyCommand { key := "a" } == some ("inserttext", "a")
#guard keyCommand { key := "b", ctrl := true } == some ("bold", "")
#guard keyCommand { key := "ArrowLeft" } == none
#guard (let (d, _, sel) := setup "<p>ab[]c</p>"
  let ed := Ed.start d sel {} {}
  (caretKey ed { key := "ArrowRight" }).map (·.start.offset)) == some 3
#guard (let (d, _, sel) := setup "<p>ab[]c</p>"
  let ed := Ed.start d sel {} {}
  (caretKey ed { key := "Home" }).map (·.start.offset)) == some 0

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
