import L4Factoidal.Rendering.Scene
import L4Factoidal.Text.CaseMap

/-! Text selection, zoom steps and window commands of the browser. The host
sends pointer positions and command numbers. It holds no selection logic. -/
namespace WebSelection
open L4Factoidal.Rendering

/-- One selectable glyph, in reading order. -/
structure Cell where
  run : Nat
  source : Nat
  x : Float
  y : Float
  width : Float
  height : Float
  text : String
  /-- The glyph is in a right-to-left run: its logical end is its left edge. -/
  rtl : Bool := false
  deriving Repr, Inhabited

inductive Selection where
  | all
  | span (anchorX anchorY focusX focusY : Float)
  deriving Repr

/-- Move a selection up, from window coordinates into page coordinates. -/
def shift (s : Selection) (top : Float) : Selection :=
  match s with
  | .all => .all
  | .span ax ay fx fy => .span ax (ay-top) fx (fy-top)

/-- Layout emits runs in document (logical) order, one for each word or each piece
of a word at one bidi level. The clusters of a run count characters from the start
of its text node, so the lowest cluster is the base of the run text. A right-to-left
run has its glyphs in drawing order, so its clusters fall along it: its cells are
taken from the end, so that cells are in logical order
(https://github.com/danbri/factoidal/issues/1275). -/
def cells (runs : Array GlyphRun) : Array Cell := Id.run do
  let mut out := #[]
  for (run,index) in runs.zipIdx do
    let chars := run.text.toList.toArray
    let base := run.glyphs.foldl (fun low g => min low g.clusterStart)
      ((run.glyphs[0]?).map (·.clusterStart) |>.getD 0)
    let rtl := match run.glyphs[0]?, run.glyphs.back? with
      | some a, some b => a.clusterStart > b.clusterStart
      | _, _ => false
    -- The first glyph of a cluster holds its text and the others none: a base and its marks
    -- are copied once, and a cluster's text is read once (it was read for each of its glyphs).
    let mut last : Option Nat := none
    for g in (if rtl then run.glyphs.reverse else run.glyphs) do
      let text := if last == some g.clusterStart then "" else
        String.ofList (chars.extract (g.clusterStart-base) (g.clusterEnd-base)).toList
      last := some g.clusterStart
      out := out.push {run:=index,source:=run.source,x:=g.x,y:=g.y,width:=g.advance,height:=run.fontSize,text,rtl}
  return out

-- A base and its mark are one cluster: the text is copied once.
#guard (cells #[⟨0,"f",16,"n\u0308a",#[⟨1,0,0,8,0,2⟩,⟨2,4,0,0,0,2⟩,⟨3,8,0,8,2,3⟩]⟩]).toList.map (·.text) == ["n\u0308","","a"]

/-- A glyph is before a point when its line is above the point, or when the
point is on its line and past the middle of the glyph in the glyph's direction:
to its right, or to its left for a right-to-left glyph. -/
private def Cell.before (c : Cell) (x y : Float) : Bool :=
  c.y+c.height <= y || (c.y <= y && (if c.rtl then x <= c.x+c.width/2 else c.x+c.width/2 <= x))

/-- The caret position of a point: one past the last glyph before the point. -/
def caret (items : Array Cell) (x y : Float) : Nat :=
  items.zipIdx.foldl (fun at_ (c,i) => if c.before x y then i+1 else at_) 0

/-- The glyph range of a selection, `low` included and `high` not included. -/
def range (items : Array Cell) : Selection → Nat × Nat
  | .all => (0,items.size)
  | .span ax ay fx fy =>
    let a := caret items ax ay
    let f := caret items fx fy
    (min a f,max a f)

private def sameLine (a b : Cell) : Bool :=
  a.y < b.y+b.height && b.y < a.y+a.height

/-- Selected text. A soft line wrap becomes a space and a new block becomes a
new line. Words of the same line keep the gap that layout gave them. -/
def text (items : Array Cell) (selection : Selection) : String := Id.run do
  let (low,high) := range items selection
  let mut out := ""
  let mut previous : Option Cell := none
  for c in (items.extract low high) do
    if let some p := previous then
      if !sameLine p c then out := out ++ (if p.source == c.source then " " else "\n")
      else if p.run != c.run && (c.x > p.x+p.width+0.5 || p.x > c.x+c.width+0.5) then out := out ++ " "
    out := out ++ c.text
    previous := some c
  return out

/-- One rectangle for each line of the glyphs `low .. high`: x, y, width, height. -/
def rangeRects (items : Array Cell) (low high : Nat) : Array (Float × Float × Float × Float) := Id.run do
  let mut out : Array (Float × Float × Float × Float) := #[]
  let mut line : Option Cell := none
  for c in (items.extract low high) do
    match line, out.back? with
    | some first, some (x,y,w,h) =>
      if sameLine first c then
        let top := min y c.y
        let bottom := max (y+h) (c.y+c.height)
        -- Right-to-left glyphs extend the rectangle to the left.
        let left := min x c.x
        let right := max (x+w) (c.x+c.width)
        out := out.pop.push (left,top,right-left,bottom-top)
      else
        out := out.push (c.x,c.y,c.width,c.height)
        line := some c
    | _,_ =>
      out := out.push (c.x,c.y,c.width,c.height)
      line := some c
  return out

/-- One rectangle for each selected line: x, y, width, height. -/
def lineRects (items : Array Cell) (selection : Selection) : Array (Float × Float × Float × Float) :=
  let (low,high) := range items selection
  rangeRects items low high

/-- The active selection colours of the common desktop browsers (the CSS `::selection`
default, CSS Pseudo-Elements 4 §3.1): white text on blue. The address bar uses both. -/
def selectionBackground : Color := ⟨0,99/255,225/255⟩
def selectionText : Color := ⟨1,1,1⟩

/-- Translucent marks of the selection colour over the text, drawn after the page. The
glyphs keep their colour: https://github.com/danbri/factoidal/issues/1281 -/
def highlight (items : Array Cell) (selection : Selection) : List Node :=
  (lineRects items selection).toList.map fun (x,y,w,h) =>
    .paint ⟨none,{geometry := .rect x y w h,style := {fill := .solid selectionBackground,fillOpacity := 0.35}}⟩

/-! ### Find in page (Command-F)

The find text of a page is the text of its laid-out glyphs in reading order, with a space
where `text` puts a space or a new line: between lines, between blocks, and between runs of
one line with a gap between them. Runs with no gap (`a<b>b</b>`) join, so a query matches
across inline elements. Every character is case folded (Unicode simple case folding,
CaseFolding.txt statuses C and S, one character for one), and white space is one space. -/

/-- A character as find compares it. -/
def foldChar (c : Char) : Char := Char.ofNat (L4Factoidal.Text.CaseMap.caseFoldCp c.toNat)

/-- White space for find: space, tab, line breaks and no-break space. -/
def findSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 0xA0

/-- One space, unless the text is empty or already ends with one. -/
private def pushSpace (out : Array (Char × Nat)) (cell : Nat) : Array (Char × Nat) :=
  if out.isEmpty || (out.back?.map (·.1)) == some ' ' then out else out.push (' ',cell)

/-- The find text: each character folded, with the index of the glyph cell it came from. -/
def findText (items : Array Cell) : Array (Char × Nat) := Id.run do
  let mut out : Array (Char × Nat) := #[]
  let mut previous : Option Cell := none
  for (c,i) in items.zipIdx do
    if let some p := previous then
      if !sameLine p c || (p.run != c.run && (c.x > p.x+p.width+0.5 || p.x > c.x+c.width+0.5)) then
        out := pushSpace out i
    for ch in c.text.toList do
      out := if findSpace ch then pushSpace out i else out.push (foldChar ch,i)
    previous := some c
  return out

/-- A query as find compares it: folded, white space as one space, none at either end. -/
def findQuery (query : String) : Array Char := Id.run do
  let mut out : Array Char := #[]
  for ch in query.toList do
    if findSpace ch then
      if !out.isEmpty && out.back? != some ' ' then out := out.push ' '
    else out := out.push (foldChar ch)
  return if out.back? == some ' ' then out.pop else out

/-- Most matches that find reports on one page. -/
def maxMatches : Nat := 1000

/-- The matches of `query` on the page, left to right and not overlapping, at most
`maxMatches`: each is the glyph range `(low, high)`, `high` not included. An empty query
matches nothing. -/
def findMatches (items : Array Cell) (query : String) : Array (Nat × Nat) := Id.run do
  let q := findQuery query
  if q.isEmpty then return #[]
  let t := findText items
  let mut out : Array (Nat × Nat) := #[]
  let mut free := 0
  for i in [0:t.size] do
    if out.size >= maxMatches then break
    if i < free || i+q.size > t.size then continue
    let mut same := true
    for k in [0:q.size] do
      if (t[i+k]?.map (·.1)) != q[k]? then
        same := false
        break
    if same then
      out := out.push ((t[i]?.map (·.2)).getD 0,((t[i+q.size-1]?.map (·.2)).getD 0)+1)
      free := i+q.size
  return out

/-- The colours of find (as Safari and Chrome): yellow for every match, orange for the current one. -/
def findColor : Color := ⟨1,1,0⟩
def findCurrentColor : Color := ⟨1,150/255,50/255⟩

/-- Marks of the matches over the text, drawn after the page: the current match (`current`,
from 0) in its own colour. The glyphs keep their colour, as with the selection. -/
def findHighlight (items : Array Cell) (found : Array (Nat × Nat)) (current : Nat) : List Node :=
  found.toList.zipIdx.flatMap fun ((low,high),k) =>
    (rangeRects items low high).toList.map fun (x,y,w,h) =>
      .paint ⟨none,{geometry := .rect x y w h,style := {fill := .solid (if k == current then findCurrentColor else findColor),fillOpacity := 0.45}}⟩

/-- Test cells: one run for each word, on one line, each word `gap` after the one before. -/
private def cellsOf (words : List (Float × String)) : Array Cell :=
  (words.zipIdx.foldl (fun (out : Array Cell × Float) ((gap,word),run) =>
    word.toList.foldl (fun (a : Array Cell × Float) ch =>
      (a.1.push {run,source := 0,x := a.2,y := 0,width := 8,height := 16,text := ch.toString},a.2+8)) (out.1,out.2+gap)) (#[],0)).1

-- Case folding, a match across two runs with no gap (an inline element), and a word gap as a space.
#guard findMatches (cellsOf [(0,"Hel"),(0,"lo"),(8,"World")]) "LLOWO" == #[]
#guard findMatches (cellsOf [(0,"Hel"),(0,"lo"),(8,"World")]) "hello world" == #[(0,10)]
#guard findMatches (cellsOf [(0,"Hel"),(0,"lo"),(8,"World")]) "elLo" == #[(1,5)]
#guard findMatches (cellsOf [(0,"abc"),(8,"ABC")]) "ABC" == #[(0,3),(3,6)]
#guard findMatches (cellsOf [(0,"aaaa")]) "aa" == #[(0,2),(2,4)]
#guard findMatches (cellsOf [(0,"one"),(8,"two")]) "" == #[]
#guard findMatches (cellsOf [(0,"a"),(12,"b")]) " A   b " == #[(0,2)]
#guard foldChar 'Σ' == 'σ' && foldChar 'É' == 'é'

/-- A pointer that moves less than this many backing pixels is a click. -/
def clickSlop : Float := 4

def isClick (ax ay fx fy : Float) : Bool :=
  (ax-fx).abs < clickSlop && (ay-fy).abs < clickSlop

/-- The smallest text scale. There is no largest: layout cost depends on the
content, and the window shows only the glyphs near it. -/
def minPercent : Nat := 50

/-- A zoom step multiplies by about 1.1, rounded to a multiple of 5, and always moves. -/
def zoomIn (percent : Nat) : Nat :=
  max (percent+1) ((percent*11+25)/50*5)

def zoomOut (percent : Nat) : Nat :=
  if percent <= minPercent then percent
  else max minPercent (min (percent-1) ((percent*20+55)/110*5))

/-- Window commands by the number that the native menu sends. -/
def commandName : Nat → String
  | 1 => "zoomIn"
  | 2 => "zoomOut"
  | 3 => "zoomReset"
  | 4 => "copy"
  | 5 => "selectAll"
  | 6 => "back"
  | 7 => "forward"
  | 8 => "reload"
  | 9 => "focusAddress"
  | 10 => "newTab"
  | 11 => "closeTab"
  | 12 => "settings"
  | 13 => "viewSource"
  | 14 => "paste"
  | 15 => "cut"
  | 16 => "undo"
  | 17 => "redo"
  | 18 => "print"
  | 19 => "pageSetup"
  | 20 => "reopenTab"
  | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 => "selectTab"
  | 30 => "nextTab"
  | 31 => "previousTab"
  | 32 => "find"
  | 33 => "pageDown"
  | 34 => "pageUp"
  | 35 => "top"
  | 36 => "bottom"
  | 37 => "lineDown"
  | 38 => "lineUp"
  | 39 => "stop"
  | 40 => "console"
  | 41 => "about"
  | 42 => "findNext"
  | 43 => "findPrevious"
  | 44 => "openFile"
  | 45 => "savePage"
  | _ => "none"

/-! ### Text size as the reader sees it

The text zoom (`textScalePercent`) is device pixels of text for each CSS pixel, in percent.
A host whose screen has `unit`/100 device pixels to its CSS pixel (`zoomUnit`: 100 on a 1x
screen, 300 on a 3x phone; the native window keeps 100) shows the reader the zoom divided
by that: the text size, 100 being the size a usual browser gives. The settings page steps
and sets the text size; the host gets the zoom back. -/

/-- Text size of a new window, in percent of a usual browser's: 200 (it was 150). -/
def defaultPercent : Nat := 200

/-- The largest text size the settings page and a pinch reach. -/
def maxShown : Nat := 1000

/-- One step of A+ or A−: 25 points of text size, on the multiples of 25. -/
def textStep : Nat := 25

/-- The text size the reader sees for a zoom on a screen of `unit`, to the nearest 5. -/
def shownPercent (percent unit : Nat) : Nat :=
  (percent*200 + 5*max 1 unit) / (10*max 1 unit) * 5

/-- The zoom for a text size on a screen of `unit`, on multiples of 5, at least `minPercent`. -/
def unitPercent (shown unit : Nat) : Nat :=
  max minPercent ((shown*max 1 unit + 250)/500*5)

/-- A text size within the settings range. -/
def clampShown (n : Nat) : Nat := max minPercent (min maxShown n)

/-- A+: the next multiple of `textStep` above. -/
def stepUp (s : Nat) : Nat := clampShown ((s/textStep + 1)*textStep)

/-- A−: the multiple of `textStep` below. -/
def stepDown (s : Nat) : Nat := clampShown ((s + textStep - 1)/textStep*textStep - textStep)

/-- What a `foafnaut:zoom/ARGUMENT` link asks. -/
inductive ZoomAsk where
  | up
  | down
  | reset
  | to (shown : Nat)
  deriving Repr, DecidableEq

/-- `up`, `down`, `reset` or a whole number of percent; anything else is not a size. -/
def ZoomAsk.parse (argument : String) : Option ZoomAsk :=
  if argument == "up" then some .up
  else if argument == "down" then some .down
  else if argument == "reset" then some .reset
  else if !argument.isEmpty && argument.length <= 6 && argument.all Char.isDigit then argument.toNat?.map .to
  else none

/-- The text size an ask gives, from the text size `s`. -/
def zoomShown : ZoomAsk → Nat → Nat
  | .up, s => stepUp s
  | .down, s => stepDown s
  | .reset, _ => defaultPercent
  | .to n, _ => clampShown n

/-- The zoom an ask gives, from the zoom `percent` on a screen of `unit`. -/
def textZoom (ask : ZoomAsk) (percent unit : Nat) : Nat :=
  unitPercent (zoomShown ask (shownPercent percent unit)) unit

theorem clampShown_bounds (n : Nat) : minPercent ≤ clampShown n ∧ clampShown n ≤ maxShown := by
  unfold clampShown minPercent maxShown; omega

theorem zoomShown_bounds (ask : ZoomAsk) (s : Nat) :
    minPercent ≤ zoomShown ask s ∧ zoomShown ask s ≤ maxShown := by
  cases ask with
  | up => exact clampShown_bounds _
  | down => exact clampShown_bounds _
  | reset => simp only [zoomShown, defaultPercent, minPercent, maxShown]; omega
  | to n => exact clampShown_bounds _

/-- A+ always grows a text size below the largest; A− always shrinks one above the smallest. -/
theorem stepUp_grows (s : Nat) (h : s < maxShown) : s < stepUp s := by
  unfold stepUp clampShown textStep minPercent maxShown at *; omega

theorem stepDown_shrinks (s : Nat) (h : minPercent < s) : stepDown s < s := by
  unfold stepDown clampShown textStep minPercent maxShown at *; omega

/-- The zoom of a link is never below the smallest that layout takes (`scalePercent`). -/
theorem textZoom_min (ask : ZoomAsk) (percent unit : Nat) : minPercent ≤ textZoom ask percent unit := by
  unfold textZoom unitPercent; omega

/-- Window command 3 (zoom reset) gives the default text size on a screen of `unit`. -/
def commandPercent (command percent : Nat) (unit : Nat := 100) : Nat :=
  match command with
  | 1 => zoomIn percent
  | 2 => zoomOut percent
  | 3 => unitPercent defaultPercent unit
  | _ => percent

#guard zoomIn 100 == 110 && zoomIn 105 == 115 && zoomIn 150 == 165 && zoomIn 250 == 275
#guard zoomIn 2000 == 2200 && zoomIn 1 == 2
#guard zoomOut 100 == 90 && zoomOut 50 == 50 && zoomOut 105 == 95 && zoomOut 165 == 150
#guard zoomOut 51 == 50 && zoomOut 10 == 10 && zoomOut 2200 == 2000
#guard commandPercent 3 175 == 200 && commandPercent 4 175 == 175 && commandPercent 3 175 300 == 600
-- A 3x phone starts at 600 and shows 200%; A+ gives 225% (675), A− 175% (525).
#guard shownPercent 600 300 == 200 && textZoom .up 600 300 == 675 && textZoom .down 600 300 == 525
#guard textZoom (.to 400) 600 300 == 1200 && textZoom (.to 5000) 100 100 == 1000 && textZoom (.to 10) 300 300 == 150
#guard textZoom .reset 450 300 == 600 && textZoom .reset 150 100 == 200 && textZoom .reset 330 263 == 525
-- Off the steps (a pinch left 210%), A+ and A− go to the steps beside it.
#guard textZoom .up 210 100 == 225 && textZoom .down 210 100 == 200 && textZoom .down 50 100 == 50 && textZoom .up 1000 100 == 1000
#guard ZoomAsk.parse "up" == some .up && ZoomAsk.parse "150" == some (.to 150) && ZoomAsk.parse "" == none && ZoomAsk.parse "1e3" == none
-- Every text size on the steps of 5 comes back as itself on 1x, 1.5x, 2x, 2.625x and 3x screens.
#guard [100,150,200,263,300].all fun u => (List.range 191).all fun i => let s := 50+5*i;
  shownPercent (unitPercent s u) u == s
-- Zoom in then out comes back on the steps from 100 up.
#guard (List.range 40).all fun i => let p := 100+5*i; zoomOut (zoomIn p) == p || p % 10 != 0
#guard (List.range 2000).all fun p => zoomIn p > p && (p <= minPercent || (zoomOut p < p && zoomOut p >= minPercent))
#guard isClick 10 10 12 8 && !isClick 10 10 14 10

private def sampleRun (source : Nat) (text : String) (x y : Float) (start : Nat := 0) : GlyphRun :=
  ⟨source,"test",10,text,text.toList.toArray.mapIdx fun i _ =>
    ({index := 0,x := x+Float.ofNat i*6,y,advance := 6,clusterStart := start+i,clusterEnd := start+i+1} : Glyph)⟩
private def sample := cells #[sampleRun 1 "one" 0 0,sampleRun 1 "two" 24 0 4,sampleRun 1 "three" 0 12 8,sampleRun 2 "four" 0 30]
#guard text sample .all == "one two three\nfour"
#guard text sample (.span 7 5 38 5) == "ne tw"
#guard text sample (.span 38 5 7 5) == "ne tw"
#guard text sample (.span 25 5 13 16) == "two th"
#guard text sample (.span 500 500 500 500) == ""
#guard (lineRects sample .all).size == 3
#guard (lineRects sample (.span 5 5 5 5)).size == 0
-- A right-to-left run: glyphs in drawing order, clusters falling. Cells and the selected
-- text are in logical order, and a drag from the right edge selects from the start.
private def rtlRun : GlyphRun := ⟨1,"test",10,"abc",#[
  ({index := 0,x := 0,y := 0,advance := 6,clusterStart := 2,clusterEnd := 3} : Glyph),
  {index := 0,x := 6,y := 0,advance := 6,clusterStart := 1,clusterEnd := 2},
  {index := 0,x := 12,y := 0,advance := 6,clusterStart := 0,clusterEnd := 1}]⟩
#guard text (cells #[rtlRun]) .all == "abc"
#guard text (cells #[rtlRun]) (.span 18 5 5 5) == "ab"
#guard (lineRects (cells #[rtlRun]) .all) == #[(0,0,18,10)]
-- Expected failure, https://github.com/danbri/factoidal/issues/1281: the page selection is
-- marks over the text only, one rectangle for each line; no glyph is drawn again in
-- `selectionText`. When the glyphs get the selection text colour, this fails: change it.
#guard (highlight sample .all).length == (lineRects sample .all).size
end WebSelection
