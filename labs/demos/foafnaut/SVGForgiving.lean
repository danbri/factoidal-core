import SVG
import SVGText
import L4Factoidal.Unicode.Bidi
import Std.Data.HashMap

/- Forgiving front door for the strict SVG reader.

   The strict reader in SVG.lean refuses any document it can not fully draw.
   A browser must instead draw what it can. This pass removes what the strict
   reader refuses, and it records each removal. The reader itself is unchanged,
   so each thing it learns to draw leaves this log with no change here.

   `dropped` is the to-do list. A scene made here is a partial rendering. It
   makes no claim of SVG conformance. -/
namespace NativeSVGForgiving

open L4Factoidal.XML
open NativeSVGText

/-- Strict parses allowed for one document. Each one is a full reader run. -/
private def maxParses : Nat := 4000

/-- Elements the strict reader reads. Any other element is removed and logged. -/
private def readable := ["svg","g","use","symbol","defs","style","metadata","title","desc",
  "rect","circle","ellipse","line","polygon","polyline","path",
  "linearGradient","radialGradient","stop","solidColor","image"]
/-- Elements that paint nothing: their content needs no reader support. -/
private def silent := ["title","desc","metadata"]

private def isSpace (s : String) : Bool :=
  s.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')

/-! ### SVG fonts and text

   SVG Tiny 1.2 §11: a glyph is path data. Text therefore lowers to `path`
   elements, which the strict reader can already draw. -/

private structure Glyph where
  name : String
  advance : Float
  data : String
  /-- The characters of `unicode`: more than one is a ligature. -/
  text : List Char := []
  /-- `arabic-form`: none matches every form. -/
  form : Option String := none
  /-- `lang`: empty matches every language. -/
  lang : List String := []
  deriving Inhabited

/-- One side of an `hkern` by characters: a string, or a range of code points. -/
private inductive KernItem where
  | literal (text : List Char)
  | range (low high : Nat)

/-- An `hkern` that names a side by `u1` or `u2`. -/
private structure KernRule where
  left : List KernItem
  leftNames : List String
  right : List KernItem
  rightNames : List String
  k : Float

structure SVGFont where
  family : String := ""
  unitsPerEm : Float := 1000
  defaultAdvance : Float := 500
  /-- `font-face` ascent and descent, in font units, both as positive depths. -/
  ascent : Float := 800
  descent : Float := 200
  /-- `font-variant` of the `font-face`. -/
  variant : String := "normal"
  /-- Glyphs by their first character, in document order. -/
  glyphs : Std.HashMap Char (Array Glyph) := {}
  kerning : Std.HashMap (String × String) Float := {}
  kernRules : Array KernRule := #[]
  missing : Glyph := ⟨"",500,"",[],none,[]⟩
instance : Inhabited SVGFont := ⟨{}⟩

private def fontElements : Nat → NamespaceNode → List NamespaceNode
  | 0,_ => []
  | _,.other _ => []
  | fuel+1,node@(.element name _ children) =>
    if name.localPart == "font" then [node] else children.flatMap (fontElements fuel)

private def hexValue (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c && c ≤ '9' then some (n*16+c.toNat-48)
    else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (n*16+c.toLower.toNat-87)
    else none) (some 0)

/-- `U+0031-0034`, `U+003?`, `U+0031`, or a string of characters. -/
private def kernItem (source : String) : KernItem :=
  let source := source.trimAscii.toString
  if !source.startsWith "U+" then .literal source.toList else
  let body := (source.drop 2).toString
  match body.splitOn "-" with
  | [low,high] => match hexValue low,hexValue high with
    | some a,some b => .range a b
    | _,_ => .literal source.toList
  | _ => match hexValue (body.replace "?" "0"),hexValue (body.replace "?" "F") with
    | some a,some b => .range a b
    | _,_ => .literal source.toList

private def KernItem.matches (glyph : Glyph) : KernItem → Bool
  | .literal text => text == glyph.text
  | .range low high => match glyph.text with
    | [c] => low ≤ c.toNat && c.toNat ≤ high
    | _ => false

private def words (source : Option String) : List String :=
  ((source.getD "").splitOn ",").map (·.trimAscii.toString) |>.filter (!·.isEmpty)

private def SVGFont.ofElement (attrs : List NamespaceAttribute) (children : List NamespaceNode) : SVGFont := Id.run do
  let fallback := float (plainAttr attrs "horiz-adv-x") 500
  let mut font : SVGFont := {defaultAdvance:=fallback,missing:={name:="",advance:=fallback,data:=""}}
  for child in children do
    let .element name a _ := child | continue
    let advance := float (plainAttr a "horiz-adv-x") fallback
    let data := (plainAttr a "d").getD ""
    match name.localPart with
    | "font-face" => 
      let units := float (plainAttr a "units-per-em") 1000
      font := {font with unitsPerEm:=units,family:=(plainAttr a "font-family").getD "",variant:=((plainAttr a "font-variant").getD "normal").trimAscii.toString,ascent:=(float (plainAttr a "ascent") (units*0.8)).abs,descent:=(float (plainAttr a "descent") (units*0.2)).abs}
    | "missing-glyph" => font := {font with missing:={name:="",advance,data}}
    | "glyph" =>
      if let some text := plainAttr a "unicode" then
        if let c::_ := text.toList then
          let glyph : Glyph := {name:=(plainAttr a "glyph-name").getD text,advance:=advance,data:=data,text:=text.toList,form:=plainAttr a "arabic-form",lang:=words (plainAttr a "lang")}
          font := {font with glyphs:=font.glyphs.insert c ((font.glyphs.getD c #[]).push glyph)}
    | "hkern" =>
      let left := words (plainAttr a "g1")
      let right := words (plainAttr a "g2")
      let k := float (plainAttr a "k") 0
      if (plainAttr a "u1").isNone && (plainAttr a "u2").isNone then
        for l in left do
          for r in right do
            font := {font with kerning:=font.kerning.insert (l,r) k}
      else
        font := {font with kernRules:=font.kernRules.push {left:=(words (plainAttr a "u1")).map kernItem,leftNames:=left,right:=(words (plainAttr a "u2")).map kernItem,rightNames:=right,k:=k}}
    | _ => pure ()
  return font

/-- Every `font` element of a parsed SVG tree. -/
private def fontsIn (root : NamespaceNode) : List SVGFont :=
  (fontElements maxDepth root).filterMap fun
    | .element _ attrs children => some (SVGFont.ofElement attrs children)
    | _ => none

/-- Read the first `font` element of an SVG document. -/
def SVGFont.parse (xml : String) : Except String SVGFont := do
  match fontsIn (← parseNamespaceView xml) with
  | font::_ => pure font
  | [] => throw "no font element"

/-- The language of a text suits a glyph when it equals a language of the glyph or
    is a more specific form of one (`fr-ca` for `fr`). -/
private def langSuits (lang : String) (glyph : Glyph) : Bool :=
  glyph.lang.isEmpty || glyph.lang.any fun l =>
    lang.toLower == l.toLower || lang.toLower.startsWith (l.toLower ++ "-")

/-- SVG Tiny 1.2: the first glyph in document order that matches the characters
    at `i`, so a ligature wins only when it stands before its parts. -/
private def SVGFont.pick (font : SVGFont) (chars : Array Char) (i : Nat) (lang : String)
    (form : Option String) : Option Glyph :=
  (font.glyphs.getD chars[i]! #[]).find? fun g =>
    (g.text.zipIdx.all fun (c,k) => chars[i+k]? == some c) && langSuits lang g &&
      (g.form.isNone || g.form == form)

/-- A font with no glyph for a no-break space draws its space. -/
private def SVGFont.glyph (font : SVGFont) (c : Char) : Glyph :=
  match font.pick #[c] 0 "" none with
  | some g => g
  | none => if c == '\u00A0' then (font.pick #[' '] 0 "" none).getD font.missing else font.missing

private def SVGFont.kern (font : SVGFont) (a b : Glyph) : Float :=
  match font.kerning.get? (a.name,b.name) with
  | some k => k
  | none => ((font.kernRules.find? fun rule =>
      (rule.left.any (·.matches a) || rule.leftNames.contains a.name) &&
      (rule.right.any (·.matches b) || rule.rightNames.contains b.name)).map (·.k)).getD 0

/-- Unicode joining types of the Arabic block: letters that join only to the one
    before them, and marks that do not break a join. -/
private def arabicRightJoining (c : Nat) : Bool :=
  (0x622 ≤ c && c ≤ 0x625) || c == 0x627 || c == 0x629 || (0x62F ≤ c && c ≤ 0x632) || c == 0x648 ||
  (0x671 ≤ c && c ≤ 0x673) || (0x675 ≤ c && c ≤ 0x677) || (0x688 ≤ c && c ≤ 0x699) ||
  (0x6C0 ≤ c && c ≤ 0x6CB) || c == 0x6CD || c == 0x6CF || c == 0x6D2 || c == 0x6D3 || c == 0x6D5
private def arabicMark (c : Nat) : Bool := (0x64B ≤ c && c ≤ 0x65F) || c == 0x670
private def arabicLetter (c : Nat) : Bool :=
  ((0x620 ≤ c && c ≤ 0x64A) || (0x66E ≤ c && c ≤ 0x6D5)) && c != 0x621 && c != 0x640 && c != 0x674 && !arabicMark c
private def arabicDual (c : Nat) : Bool := arabicLetter c && !arabicRightJoining c

/-- The `arabic-form` of each character: from the joins on its two sides. -/
private def arabicForms (chars : Array Char) : Array (Option String) := Id.run do
  let mut forms : Array (Option String) := Array.replicate chars.size none
  let mut before := false
  for i in [:chars.size] do
    let c := chars[i]!.toNat
    if arabicMark c then continue
    if !arabicLetter c then
      before := false
      continue
    let mut after := false
    if arabicDual c then
      for j in [i+1:chars.size] do
        let n := chars[j]!.toNat
        if arabicMark n then continue
        after := arabicLetter n
        break
    forms := forms.set! i (some (match before,after with
      | false,false => "isolated" | false,true => "initial"
      | true,true => "medial" | true,false => "terminal"))
    before := arabicDual c
  return forms

/-- CSS Fonts: the first named family with a font of the wanted variant, else the
    default font. -/
private def chooseFont (fonts : List SVGFont) (family variant : String) : Option SVGFont :=
  let names := (family.splitOn ",").map (fun n => (n.trimAscii.toString.replace "'" "").replace "\"" "")
  (names.findSome? (fun name => fonts.find? (fun f => f.family == name && f.variant == variant))).orElse (fun _ => fonts.getLast?)

/-- One glyph of a text, in logical order. -/
private structure Placed where
  glyph : Glyph
  /-- The font of the glyph: the fallback font when the first font has none. -/
  font : SVGFont
  run : Nat
  /-- The first character of the glyph in the text. -/
  source : Nat
  x : Option Float := none
  y : Option Float := none
  dx : Float := 0
  dy : Float := 0
  rotate : Float
  scale : Float
  deriving Inhabited

/-- Where a glyph ended up. -/
private structure Position where
  x : Float := 0
  y : Float := 0
  deriving Inhabited

/-- Lower one `text` element to a group of glyph paths. -/
private def lowerText (font : SVGFont) (fallback : Option SVGFont) (state : TextState) (attrs : List NamespaceAttribute)
    (children : List NamespaceNode) : NamespaceNode × List String := Id.run do
  let state := state.read attrs
  let results := children.map (textRuns false false maxDepth state [])
  -- Default xml:space: no leading or trailing space on the whole text.
  let runs := spaceRuns (results.flatMap (·.1))
  let xs := numberList attrs "x"
  let ys := numberList attrs "y"
  let rotations := numberList attrs "rotate"
  -- All characters first: forms and direction depend on their neighbours.
  let chars := (runs.flatMap (·.text.toList)).toArray
  let forms := arabicForms chars
  let mut index := 0
  let mut placed : Array Placed := #[]
  for (run,runIndex) in runs.zipIdx do
    if run.size <= 0 then
      index := index+run.text.length
      continue
    let text := run.text.toList.toArray
    let start := index
    let mut position := 0
    let mut first := true
    for _ in [:text.size] do
      if position >= text.size then break
      let at_ := start+position
      -- A coordinate list places the characters it covers (SVG Tiny 1.2 §10.5).
      let x := (run.xs[position]?).orElse (fun _ => xs[at_]?)
      let y := (run.ys[position]?).orElse (fun _ => ys[at_]?)
      -- A list on the text element or on a tspan ends a ligature here; none is near.
      let found := ((font.pick chars at_ run.lang forms[at_]!).map (·,font)).orElse fun _ =>
        (fallback.bind fun f => (f.pick chars at_ run.lang forms[at_]!).map (·,f))
      let (g,owner) := found.getD (font.glyph text[position]!,font)
      let scale := run.size/owner.unitsPerEm
      -- A rotation list: the last value holds for the characters after it.
      let rotate := match rotations[at_]? with
        | some value => value
        | none => rotations.getLast?.getD 0
      placed := placed.push {glyph:=g,font:=owner,run:=runIndex,source:=at_,x:=x,y:=y,rotate:=rotate,scale:=scale,dx:=if first then run.dx else 0,dy:=if first then run.dy else 0}
      first := false
      position := position+max 1 g.text.length
    index := start+text.size
  -- An absolute position starts a text chunk (SVG Tiny 1.2 §10.6.1). Each chunk is laid
  -- out in visual order (UAX 9), and moves by its anchor and width.
  let mut positions : Array Position := Array.replicate placed.size {}
  let mut x := (numberList attrs "dx").headD 0
  let mut y := (numberList attrs "dy").headD 0
  let mut start := 0
  for i in [:placed.size] do
    let next := i+1
    let last := next == placed.size || placed[next]!.x.isSome || placed[next]!.y.isSome
    if !last then continue
    let cells := placed.extract start next
    let head := cells[0]!
    if let some value := head.x then x := value+(numberList attrs "dx").headD 0
    if let some value := head.y then y := value+(numberList attrs "dy").headD 0
    let chunkChars := cells.map fun c => chars[c.source]!
    -- The initial `direction` is ltr (W3C fonts-glyph-02-t). W3C text-align-202-t puts the
    -- start of text in `xml:lang="ar"` or `"he"` at the right, and no file sets `direction`.
    let rightToLeft := rightToLeftLanguage ((runs[head.run]?.map (·.lang)).getD "")
    let (levels,_) := L4Factoidal.Unicode.levelsOfChars chunkChars (if rightToLeft then .rtl else .ltr)
    let order := L4Factoidal.Unicode.visualOrder levels
    let origin := x
    let mut previous : Option Placed := none
    for k in order do
      let cell := cells[k]!
      x := x+cell.dx
      y := y+cell.dy
      if let some p := previous then
        x := x-(cell.font.kern p.glyph cell.glyph)*cell.scale
      positions := positions.set! (start+k) {x,y}
      x := x+cell.glyph.advance*cell.scale
      previous := some cell
    let width := x-origin
    let anchor := (runs[head.run]?.map (·.anchor)).getD "start"
    let shift := match anchor,rightToLeft with
      | "middle",_ => -width/2
      | "end",false | "start",true => -width
      | _,_ => 0
    for j in [start:next] do
      positions := positions.modify j fun p => {p with x:=p.x+shift}
    x := x+shift
    start := next
  let mut groups : Array NamespaceNode := #[]
  -- SVG Tiny 1.2 §7.11: the bounding box of a text is that of its character cells.
  let mut box : Option (Float × Float × Float × Float) := none
  let mut cursor := 0
  for (run,runIndex) in runs.zipIdx do
    let mut paths : Array NamespaceNode := #[]
    for i in [cursor:placed.size] do
      let cell := placed[i]!
      if cell.run != runIndex then break
      let left := positions[i]!.x
      let top := positions[i]!.y
      let g := cell.glyph
      let scale := cell.scale
      if !g.data.isEmpty then
        let turn := if cell.rotate == 0 then "" else s!" rotate({cell.rotate})"
        paths := paths.push (svgElement "path" [mkAttr "d" g.data,mkAttr "stroke-width" (toString (run.strokeWidth/scale)),
          mkAttr "transform" s!"translate({left},{top}){turn} scale({scale},{-scale})"] [])
      let cellTop := top-cell.font.ascent*scale
      let cellBottom := top+cell.font.descent*scale
      let cellRight := left+g.advance*scale
      box := some (match box with
        | none => (left,cellTop,cellRight,cellBottom)
        | some (x0,y0,x1,y1) => (min x0 left,min y0 cellTop,max x1 cellRight,max y1 cellBottom))
      cursor := i+1
    groups := groups.push (svgElement "g" run.paint paths.toList)
  let outer := paintOf attrs ++ (attrs.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "transform"))
  let ids := renameId attrs |>.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "id")
  let marked := match box with
    | none => groups.toList
    | some box => groups.toList.map (markGlyphs box)
  return (svgElement "g" (ids ++ outer) marked,results.flatMap (·.2))

/-! ### Text in an area (SVG Tiny 1.2 §10.11)

   `textArea` lowers to the same glyph paths as `text`. Lines come first, as
   ranges of an array of cells; then each line is placed. Every loop is over
   the cells of the element, so the work is linear in its text. -/

/-- One character, or one `tbreak` (`lineBreak`), after white space handling. -/
private structure Cell where
  glyph : Glyph
  run : Nat
  /-- Advance of the glyph and kerning before it, both in user units. -/
  advance : Float
  kern : Float
  space : Bool
  lineBreak : Bool := false
instance : Inhabited Cell := ⟨⟨default,0,0,0,false,false⟩⟩

/-- Cells `first` to `stop-1`. `run` is the run that gives the size of an empty line. -/
private structure AreaLine where
  first : Nat
  stop : Nat
  run : Nat
  width : Float

/-- §10.11.7, white space and kerning. `default`: tabs and newlines are spaces, and
    only the first space of a sequence stays, also over a change of run. -/
private def areaCells (font : SVGFont) (runs : Array Run) : Array Cell := Id.run do
  let mut cells : Array Cell := #[]
  let mut previous : Option (Nat × Glyph) := none
  let mut index := 0
  for run in runs do
    let current := index
    index := index+1
    if run.lineBreak then
      cells := cells.push {glyph:=font.missing,run:=current,advance:=0,kern:=0,space:=false,lineBreak:=true}
      previous := none
      continue
    let scale := run.size/font.unitsPerEm
    for raw in run.text.toList do
      let c := if raw == '\n' || raw == '\t' || raw == '\r' then ' ' else raw
      let space := c == ' '
      let afterGap := match cells.back? with
        | none => true
        | some last => last.space || last.lineBreak
      if space && !run.preserveSpace && afterGap then continue
      let g := font.glyph c
      let kern := match previous with
        | some (r,p) => if r == current then (font.kern p g)*scale else 0
        | none => 0
      cells := cells.push {glyph:=g,run:=current,advance:=g.advance*scale,kern,space}
      previous := some (current,g)
  return cells

private def cellWidth (cell : Cell) : Float := cell.advance-cell.kern

/-- First cell at or after `start` that ends a word. -/
private def wordEnd (cells : Array Cell) (start : Nat) : Nat := Id.run do
  for i in [start:cells.size] do
    if let some cell := cells[i]? then
      if cell.space || cell.lineBreak then return i
  return cells.size

private def rangeWidth (cells : Array Cell) (start stop : Nat) : Float := Id.run do
  let mut total := 0
  for i in [start:stop] do
    if let some cell := cells[i]? then total := total+cellWidth cell
  return total

private structure Breaker where
  lines : Array AreaLine := #[]
  start : Nat := 0
  /-- End of the last word on the line; spaces after it are not part of it yet. -/
  stop : Nat := 0
  width : Float := 0

/-- End the current line. The next line starts at `next`. -/
private def Breaker.finish (b : Breaker) (run next : Nat) (width : Float := 0) : Breaker :=
  {lines:=b.lines.push ⟨b.start,b.stop,run,b.width⟩,start:=next,stop:=next,width}

/-- §10.11.7: a `tbreak` ends a line, and a word goes to the next line when it does
    not fit. A word wider than the area breaks between characters; each line has at
    least one character, so the loop always makes progress. `limit` is the width of
    the area, and `none` is `auto`: there only a `tbreak` ends a line. -/
private def breakLines (cells : Array Cell) (limit : Option Float) (preserve : Bool) : Array AreaLine := Id.run do
  let mut b : Breaker := {}
  let mut i := 0
  let width := limit.getD 0
  for _ in [0:cells.size+1] do
    let some cell := cells[i]? | break
    if cell.lineBreak then
      b := b.finish cell.run (i+1)
      i := i+1
    else if cell.space then
      i := i+1
    else
      let stop := wordEnd cells i
      let word := rangeWidth cells i stop
      let gap := rangeWidth cells b.stop i
      if limit.isSome && b.stop > b.start && b.width+gap+word > width then
        -- A preserved space goes to the next line; another one ends with the line.
        let next := if preserve then b.stop else i
        b := b.finish cell.run next (if preserve then gap else 0)
        b := {b with stop:=i}
      else
        b := {b with stop:=i,width:=b.width+gap}
      if limit.isNone || word <= width then
        b := {b with stop,width:=b.width+word}
      else
        for k in [i:stop] do
          if let some part := cells[k]? then
            if b.stop > b.start && b.width+cellWidth part > width then b := b.finish part.run k
            b := {b with stop:=k+1,width:=b.width+cellWidth part}
      i := stop
  if b.stop > b.start then b := b.finish ((cells[b.start]?).map (·.run) |>.getD 0) b.stop
  return b.lines

/-- §10.11.4 and §10.11.7: the largest line increment of the runs on the line, where
    `auto` is 1.1 times the font size. An empty line has the size of its `tbreak`. -/
private def lineSize (runs : Array Run) (cells : Array Cell) (line : AreaLine) : Float := Id.run do
  let increment := fun (r : Run) => r.increment.getD (1.1*r.size)
  let mut size := 0
  for i in [line.first:line.stop] do
    if let some cell := cells[i]? then
      if let some run := runs[cell.run]? then size := max size (increment run)
  if line.first == line.stop then
    if let some run := runs[line.run]? then return increment run
  return size

/-- Lower one `textArea` element to a group of glyph paths. -/
private def lowerArea (font : SVGFont) (state : TextState) (attrs : List NamespaceAttribute)
    (children : List NamespaceNode) : NamespaceNode × List String := Id.run do
  let state := state.read attrs
  let results := children.map (textRuns true false maxDepth state [])
  let runs := (results.flatMap (·.1)).toArray
  let dimension := fun (key : String) => match plainAttr attrs key with
    | none => none
    | some value => if value.trimAscii.toString == "auto" then none else some (float (some value) 0)
  let left := float (plainAttr attrs "x") 0
  let top := float (plainAttr attrs "y") 0
  let width := dimension "width"
  let height := dimension "height"
  let outer := paintOf attrs ++ (attrs.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "transform"))
  let ids := renameId attrs |>.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "id")
  -- §10.11.2: a value of zero disables rendering of the element.
  if width.any (· <= 0) || height.any (· <= 0) then return (svgElement "g" (ids ++ outer) [],results.flatMap (·.2))
  let cells := areaCells font runs
  let lines := breakLines cells width state.preserveSpace
  -- §10.11.7: a line that does not fit completely in the area is not rendered.
  let mut kept : Array (AreaLine × Float) := #[]
  let mut used := 0
  for line in lines do
    let size := lineSize runs cells line
    if height.any (used+size > ·) then break
    kept := kept.push (line,size)
    used := used+size
  let shift := match height,state.displayAlign with
    | some h,"center" => (h-used)/2
    | some h,"after" => h-used
    | _,_ => 0
  let mut groups : Array NamespaceNode := #[]
  let mut box : Option (Float × Float × Float × Float) := none
  let mut lineTop := top+shift
  for (line,size) in kept do
    -- §10.11.7 rule 9: the baseline as for a font size equal to the line increment.
    let baseline := lineTop+size*font.ascent/font.unitsPerEm
    let free := width.map (·-line.width)
    let mut x := left + match free,state.textAlign with
      | some free,"center" => free/2
      | some free,"end" => free
      | _,_ => 0
    let mut paths : Array NamespaceNode := #[]
    let mut current : Option Nat := none
    let flush := fun (groups : Array NamespaceNode) (paths : Array NamespaceNode) (current : Option Nat) =>
      match current.bind (runs[·]?) with
      | some run => groups.push (svgElement "g" run.paint paths.toList)
      | none => groups
    for i in [line.first:line.stop] do
      let some cell := cells[i]? | continue
      let some run := runs[cell.run]? | continue
      if current != some cell.run then
        groups := flush groups paths current
        paths := #[]
        current := some cell.run
      if i > line.first then x := x-cell.kern
      let scale := run.size/font.unitsPerEm
      if !cell.glyph.data.isEmpty then
        paths := paths.push (svgElement "path" [mkAttr "d" cell.glyph.data,mkAttr "stroke-width" (toString (run.strokeWidth/scale)),
          mkAttr "transform" s!"translate({x},{baseline}) scale({scale},{-scale})"] [])
      let cellTop := baseline-font.ascent*scale
      let cellBottom := baseline+font.descent*scale
      let cellRight := x+cell.advance
      box := some (match box with
        | none => (x,cellTop,cellRight,cellBottom)
        | some (x0,y0,x1,y1) => (min x0 x,min y0 cellTop,max x1 cellRight,max y1 cellBottom))
      x := cellRight
    groups := flush groups paths current
    lineTop := lineTop+size
  let marked := match box with
    | none => groups.toList
    | some box => groups.toList.map (markGlyphs box)
  return (svgElement "g" (ids ++ outer) marked,results.flatMap (·.2))

/-- SVG Tiny 1.2 feature strings of what this pass and the reader draw. Animation, media,
    scripting, handlers and the DOM are outside it, and an SVG 1.1 string is unknown,
    so `requiredFeatures` with them is false (W3C struct-cond-03-t, struct-cond-205-t). -/
private def supportedFeatures : List String :=
  ["SVG-static","CoreAttribute","Structure","ConditionalProcessing","ConditionalProcessingAttribute",
   "Image","Prefetch","Shape","Text","PaintAttribute","OpacityAttribute","GraphicsAttribute",
   "Gradient","SolidColor","Hyperlinking","XlinkAttribute","ExternalResourcesRequired","Font",
   "Extensibility","TextFlow"].map ("http://www.w3.org/Graphics/SVG/feature/1.2/#" ++ ·)

private def supportedFormats : List String := ["image/svg+xml","image/png","image/jpeg"]

private def spaceList (value : String) : List String :=
  ((value.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " ").splitOn " ").filter (· != "")

/-- A list attribute that is present must be non-empty, and every item must hold. -/
private def listPasses (attrs : List NamespaceAttribute) (key : String) (holds : String → Bool) : Bool :=
  match plainAttr attrs key with
  | none => true
  | some value => let items := spaceList value; !items.isEmpty && items.all holds

/-- `requiredFonts` is a list of family names, separated by commas. -/
private def fontsPass (fonts : List SVGFont) (attrs : List NamespaceAttribute) : Bool :=
  match plainAttr attrs "requiredFonts" with
  | none => true
  | some value =>
    let names := (value.splitOn ",").map (fun n => (n.trimAscii.toString.replace "'" "").replace "\"" "")
    names.any fun name => fonts.any (·.family == name)

/-- SVG Tiny 1.2 §5.8: this agent's language is en, and it has no extensions. -/
private def conditionsPass (fonts : List SVGFont) (attrs : List NamespaceAttribute) : Bool :=
  let language := match plainAttr attrs "systemLanguage" with
    | none => true
    | some value => (value.splitOn ",").any fun tag =>
      let tag := tag.trimAscii.toString.toLower
      tag == "en" || tag.startsWith "en-"
  let extensions := match plainAttr attrs "requiredExtensions" with | none => true | some _ => false
  language && extensions && listPasses attrs "requiredFeatures" supportedFeatures.contains &&
    listPasses attrs "requiredFormats" supportedFormats.contains && fontsPass fonts attrs

/-- Elements of the tree that have an id, by id; the first one with an id wins. -/
private def idTargets : Nat → NamespaceNode → List (String × NamespaceNode)
  | 0,_ => []
  | _,.other _ => []
  | fuel+1,node@(.element _ attrs children) =>
    ((plainAttr (renameId attrs) "id").toList.map (·,node)) ++ children.flatMap (idTargets fuel)

private def hasElement (tag : String) : Nat → NamespaceNode → Bool
  | 0,_ => false
  | _,.other _ => false
  | fuel+1,.element name _ children => name.localPart == tag || children.any (hasElement tag fuel)

/-- SVG Tiny 1.2 §5.6: an instance inherits from its `use` element. Text lowers
    here, with the font values in force, so a `use` of text must lower its own
    copy. A target with a `use` inside stays with the strict reader, which has
    the cycle check. -/
private def textInstance (targets : Std.HashMap String NamespaceNode) (attrs : List NamespaceAttribute) : Option NamespaceNode := do
  let source ← NativeSVGReferences.href attrs
  if !source.startsWith "#" then none
  let target ← targets.get? (source.drop 1).toString
  let .element name _ _ := target | none
  if !["g","text","textArea"].contains name.localPart ||
    !(hasElement "text" maxDepth target || hasElement "textArea" maxDepth target) || hasElement "use" maxDepth target then none
  pure target

/-- Remove foreign and unread elements, stray text and the content of silent
    elements, and lower `text` when a font is known. Returns the new tree and
    one log line for each removal. -/
private def normalise (fonts : List SVGFont) (sfnt : Array NativeSVGText.Font) (targets : Std.HashMap String NamespaceNode) : Nat → TextState → Bool → NamespaceNode → Option NamespaceNode × List String
  | 0,_,_,_ => (none,["element: nesting exceeds 64"])
  | _,_,_,.other (.comment c) => (some (.other (.comment c)),[])
  | _,_,keepText,.other raw => match raw with
    | .text t | .cdata t =>
      if keepText || isSpace t then (some (.other raw),[]) else (none,["text outside a text element"])
    | _ => (none,["processing instruction"])
  | fuel+1,state,_,.element name attrs children =>
    if name.namespace_ != some svgURI then (none,["foreign element: " ++ name.localPart])
    else if !conditionsPass fonts attrs then (none,[])
    else if name.localPart == "text" && !fonts.isEmpty then
      let inner := state.read attrs
      match chooseFont fonts inner.family inner.variant with
      | some font => let (node,log) := lowerText font fonts.getLast? state attrs children; (some node,log)
      | none => (none,["element: text"])
    else if name.localPart == "text" && !sfnt.isEmpty then
      -- No SVG font: the SFNT fonts of the host draw the text, as they draw HTML text.
      let (node,log) := lowerSfnt sfnt targets.get? state attrs children
      (some node,log)
    else if name.localPart == "textArea" && !fonts.isEmpty then
      match chooseFont fonts (state.read attrs).family (state.read attrs).variant with
      | some font => let (node,log) := lowerArea font state attrs children; (some node,log)
      | none => (none,["element: textArea"])
    else if name.localPart == "switch" then
      -- SVG Tiny 1.2 §5.8: draw only the first child whose conditions pass.
      let selected : NamespaceNode → Bool := fun
        | .element n a _ => n.namespace_ == some svgURI && conditionsPass fonts a | _ => false
      let chosen := children.find? selected
      let inner := state.read attrs
      let result := (chosen.toList).map (normalise fonts sfnt targets fuel inner false)
      -- A child that is not drawn can still be referenced, so it stays as a definition.
      let unused := children.eraseIdx (children.findIdx selected)
      let kept := unused.map (normalise fonts sfnt targets fuel inner false)
      (some (svgElement "g" (renameId attrs) (result.filterMap (·.1) ++ [svgElement "defs" [] (kept.filterMap (·.1))])),
        result.flatMap (·.2) ++ kept.flatMap (·.2))
    else if name.localPart == "a" then
      -- A link draws its content. Link regions are not part of this pass.
      let inner := state.read attrs
      let results := children.map (normalise fonts sfnt targets fuel inner false)
      (some (svgElement "g" (renameId attrs) (results.filterMap (·.1))),results.flatMap (·.2))
    else if name.localPart == "use" && !fonts.isEmpty && (textInstance targets attrs).isSome then
      let inner := state.read attrs
      let target := (textInstance targets attrs).getD (.other (.comment ""))
      let (node,log) := normalise fonts sfnt targets fuel inner false target
      let x := float (plainAttr attrs "x") 0
      let y := float (plainAttr attrs "y") 0
      let frame := ((plainAttr attrs "transform").getD "") ++ s!" translate({x},{y})"
      let kept := (renameId attrs).filter fun a => a.name.namespace_.isNone &&
        !["x","y","width","height","transform","href","font-size","font-family","text-anchor"].contains a.name.localPart
      (some (svgElement "g" (kept ++ [mkAttr "transform" frame]) node.toList),log)
    else if !readable.contains name.localPart then (none,["element: " ++ name.localPart])
    else if silent.contains name.localPart then (some (.element name (renameId attrs) []),[])
    else
      let keepText := name.localPart == "style"
      let inner := state.read attrs
      let results := children.map (normalise fonts sfnt targets fuel inner keepText)
      (some (.element name (renameId attrs) (results.filterMap (·.1))),results.flatMap (·.2))

/-- Remove `key` from the elements named `tag`, or from all elements when `tag` is
    empty. With `value`, an attribute that has another value stays. -/
private def stripAttr (tag : String) (key : String) (value : Option String := none) : Nat → NamespaceNode → NamespaceNode × Nat
  | 0,node => (node,0)
  | _,.other raw => (.other raw,0)
  | fuel+1,.element name attrs children =>
    let kept := if tag.isEmpty || name.localPart == tag then attrs.filter (fun a => a.name.localPart != key || value.any (· != a.value)) else attrs
    let results := children.map (stripAttr tag key value fuel)
    (.element name kept (results.map (·.1)),
      attrs.length-kept.length + (results.map (·.2)).foldl (·+·) 0)

/-- Element paths, deepest first, so a removal takes the least possible. -/
private def elementPaths : Nat → List Nat → NamespaceNode → List (List Nat)
  | 0,_,_ => []
  | _,_,.other _ => []
  | fuel+1,path,.element _ _ children =>
    (children.zipIdx.flatMap fun (child,index) => elementPaths fuel (path++[index]) child) ++ [path]

private def removeAt : Nat → List Nat → NamespaceNode → NamespaceNode
  | 0,_,node => node
  | _,[],node => node
  | _,_,.other raw => .other raw
  | fuel+1,[index],.element name attrs children =>
    let _ := fuel
    .element name attrs (children.eraseIdx index)
  | fuel+1,index::rest,.element name attrs children =>
    .element name attrs (children.zipIdx.map fun (child,i) =>
      if i == index then removeAt fuel rest child else child)

private def nodeAt : Nat → List Nat → NamespaceNode → Option NamespaceNode
  | _,[],node => some node
  | 0,_,_ => none
  | _,_,.other _ => none
  | fuel+1,index::rest,.element _ _ children => do
    nodeAt fuel rest (← children[index]?)

private def tagName : NamespaceNode → String
  | .element name _ _ => name.localPart
  | _ => "node"

/-- A stroke style the reader refuses: draw with the default style, and log it. -/
private def styleError (message : String) : Option String :=
  ["stroke-linejoin","stroke-miterlimit","stroke-linecap","stroke-dashoffset"].find? fun key =>
    message.startsWith ("unsupported " ++ key ++ ":")

/-- `unsupported attribute on TAG: KEY`, with or without "qualified". -/
private def attributeError (message : String) : Option (String × String) :=
  let tail := if message.startsWith "unsupported attribute on "
    then some (message.drop 25).toString
    else if message.startsWith "qualified attribute unsupported on "
    then some (message.drop 35).toString else none
  tail.bind fun tail => match tail.splitOn ": " with
    | [tag,key] => some (tag,key)
    | _ => none

private structure Attempt where
  root : NamespaceNode
  dropped : List String
  parses : Nat
  /-- Decoded once: this pass runs the strict reader many times. -/
  images : NativeImage.Store
  documentURL : Option String

/-- Remove the deepest element whose removal changes the reader's first error.
    The reader stops at its first error, so an element that does not cause it
    can not change it, except by a reference to the element that does. -/
private def removeOffender (width height : Nat) (message : String) (a : Attempt) :
    Option Attempt := Id.run do
  let mut parses := a.parses
  for path in elementPaths maxDepth [] a.root do
    if path.isEmpty then continue
    if parses >= maxParses then return none
    parses := parses + 1
    let next := removeAt maxDepth path a.root
    let changed := match NativeSVG.parseRoot next width height {} a.documentURL (some a.images) with
      | .ok _ => true
      | .error other => other != message
    if changed then
      let tag := ((nodeAt maxDepth path a.root).map tagName).getD "node"
      return some {a with root:=next,parses,dropped:=a.dropped ++ [s!"removed {tag}: {message}"]}
  return none

private def colourProperties := ["fill","stroke","color","stop-color","solid-color","viewport-fill"]

private def repair (width height : Nat) : Nat → Attempt → Except String (NativeSVG.Scene × List String)
  | 0,_ => throw "forgiving pass exceeded its repair limit"
  | fuel+1,a =>
    match NativeSVG.parseRoot a.root width height {} a.documentURL (some a.images) with
    | .ok scene => pure (scene,a.dropped)
    | .error message =>
      let stripped := (attributeError message).bind fun (tag,key) =>
        let (root,count) := stripAttr tag key none maxDepth a.root
        if count == 0 then none
        else some {a with root,parses:=a.parses+1,dropped:=a.dropped ++ List.replicate count s!"attribute: {tag} {key}"}
      let restyled := (styleError message).bind fun key =>
        -- Only the refused value goes: other elements may have a valid one.
        let refused := (message.drop ("unsupported ".length+key.length+2)).toString
        let (root,count) := stripAttr "" key (some refused) maxDepth a.root
        if count == 0 then none
        else some {a with root,parses:=a.parses+1,dropped:=a.dropped ++ [s!"approximated: {key}"]}
      -- An unsupported colour is as if not specified, and the element stays (W3C
      -- styling-pres-01-t, "rendering continues after the element").
      let recoloured := if !message.startsWith "unsupported color: " then none else
        let refused := (message.drop "unsupported color: ".length).toString
        let (root,count) := colourProperties.foldl (fun (root,count) key =>
          let (next,n) := stripAttr "" key (some refused) maxDepth root
          (next,count+n)) (a.root,0)
        if count == 0 then none
        else some {a with root,parses:=a.parses+1,dropped:=a.dropped ++ [s!"approximated: colour {refused}"]}
      match ((stripped.orElse fun _ => restyled).orElse fun _ => recoloured).orElse (fun _ => removeOffender width height message a) with
      | some next => repair width height fuel next
      | none => throw message

/-- The `version` label names a language edition; it does not change drawing. -/
private def rootAttrs (root : NamespaceNode) : NamespaceNode × List String :=
  match root with
  | .element name attrs children =>
    let dropped := ["version","baseProfile","viewport-fill","viewport-fill-opacity"]
    let kept := attrs.filter fun a => !(a.name.namespace_.isNone && dropped.contains a.name.localPart)
    -- SVG Tiny 1.2 §11.11: viewport-fill paints the whole viewport first.
    let background := match plainAttr attrs "viewport-fill" with
      | none => []
      | some fill => if fill.trimAscii.toString == "none" then [] else
        [svgElement "rect" ([mkAttr "x" "-100000",mkAttr "y" "-100000",mkAttr "width" "200000",mkAttr "height" "200000",mkAttr "fill" fill] ++
          ((plainAttr attrs "viewport-fill-opacity").toList.map (mkAttr "fill-opacity"))) []]
    (.element name kept (background ++ children),(attrs.filter (fun a => !kept.any (fun k => k.name == a.name))).map
      (fun a => "attribute: svg " ++ a.name.localPart))
  | node => (node,[])

/-- Remove each `image` that has no pixels: its reference failed, or its bytes were
    refused. SVG Tiny 1.2 §5.7 draws nothing for it, and the rest of the document
    stays. One log line for each element, with the reason of the store. -/
private def dropBrokenImages (store : NativeImage.Store) : Nat → Option String → NamespaceNode → Option NamespaceNode × List String
  | 0,_,node => (some node,[])
  | _,_,.other raw => (some (.other raw),[])
  | fuel+1,base,.element name attrs children =>
    let base := NativeSVGReferences.elementBase attrs base
    let broken := if name.namespace_ == some svgURI && name.localPart == "image" then
        (NativeSVGReferences.href attrs).bind fun href =>
          match store.get? (NativeSVG.imageKey base href) with
          | some (.error message) => some message
          | _ => none
      else none
    match broken with
    | some message => (none,["removed image: " ++ message])
    | none =>
      let results := children.map (dropBrokenImages store fuel base)
      (some (.element name attrs (results.filterMap (·.1))),results.flatMap (·.2))

/-! ### `use` of another document (SVG Tiny 1.2 §5.6)

   A `use` that names an element of another document becomes a same-document `use`.
   The other document goes into a `defs` at the end of this one, with each id renamed
   by a prefix, so the reader needs no new case. Only bytes from the host are read,
   under the same policy as image bytes. Each document is imported once, so a cycle
   of documents ends; the reader then treats a cycle of `use` as in one document. -/

private def maxExternalDocuments : Nat := 16

private def splitFragment (url : String) : String × String :=
  match url.splitOn "#" with
  | document::rest => (document,"#".intercalate rest)
  | [] => (url,"")

private def renameUrlRefs (idPrefix value : String) : String :=
  value.replace "url(#" ("url(#" ++ idPrefix)

private def hrefName (a : NamespaceAttribute) : Bool :=
  a.name.localPart == "href" && (a.name.namespace_.isNone || a.name.namespace_ == some "http://www.w3.org/1999/xlink")

private def setHref (attrs : List NamespaceAttribute) (value : String) : List NamespaceAttribute :=
  attrs.map fun a => if hrefName a then {a with value} else a

private structure ImportState where
  documents : Array String := #[]
  missing : List String := []
  log : List String := []

private def ImportState.indexOf (s : ImportState) (key : String) : ImportState × Nat :=
  match s.documents.findIdx? (· == key) with
  | some i => (s,i)
  | none => ({s with documents:=s.documents.push key},s.documents.size)

/-- Prefix of the ids of the document at `i`. -/
private def importPrefix (i : Nat) : String := s!"external-{i}-"

/-- `self` is the document that holds this tree, with the prefix of its ids; `main` is
    the document of the page. `available` says which documents the host supplied. -/
private def rewriteImport (main self : Option String) (idPrefix : String) (available : String → Bool) :
    Nat → Option String → ImportState → NamespaceNode → Option NamespaceNode × ImportState
  | 0,_,s,_ => (none,s)
  | _,_,s,.other raw => (some (.other raw),s)
  | fuel+1,base,s,.element name attrs children =>
    let base := NativeSVGReferences.elementBase attrs base
    let imported := !idPrefix.isEmpty
    let renamed := if !imported then attrs else
      (attrs.filter fun a => !(a.name.localPart == "base" && a.name.namespace_.isSome)).map fun a =>
        if a.name.localPart == "id" then {a with value:=idPrefix ++ a.value}
        else {a with value:=renameUrlRefs idPrefix a.value}
    let isUse := name.namespace_ == some svgURI && name.localPart == "use"
    let href := NativeSVGReferences.href attrs
    let external := (href.filter fun h => !h.trimAscii.toString.startsWith "#").map fun h =>
      splitFragment (NativeSVG.imageKey base h)
    let step : Option (List NamespaceAttribute) × ImportState :=
      match isUse,external,href with
      | true,some (document,fragment),_ =>
        if some document == self then (some (setHref renamed ("#" ++ idPrefix ++ fragment)),s)
        else if some document == main then (some (setHref renamed ("#" ++ fragment)),s)
        else if available document then
          let (s,i) := s.indexOf document
          -- The new reference is in this document, whatever base is in force here.
          let attrs := setHref renamed ("#" ++ importPrefix i ++ fragment)
          let attrs := match main with
            | some url => attrs.filter (fun a => !(a.name.localPart == "base" && a.name.namespace_ == some xmlURI)) ++
                [{name:={namespace_:=some xmlURI,localPart:="base"},value:=url}]
            | none => attrs
          (some attrs,s)
        else (none,{s with missing:=s.missing ++ [document],log:=s.log ++ [s!"removed use: document not supplied: {document}"]})
      | false,some (document,fragment),_ =>
        -- An imported `image` keeps the document that named it as its base.
        if imported then (some (setHref renamed (document ++ (if fragment.isEmpty then "" else "#" ++ fragment))),s)
        else (some renamed,s)
      | _,none,some h =>
        if imported then (some (setHref renamed ("#" ++ idPrefix ++ (h.trimAscii.toString.drop 1).toString)),s)
        else (some renamed,s)
      | _,_,_ => (some renamed,s)
    match step with
    | (none,s) => (none,s)
    | (some attrs,s) =>
      let (kept,s) := children.foldl (fun ((kept,s) : Array NamespaceNode × ImportState) child =>
        match rewriteImport main self idPrefix available fuel base s child with
        | (some node,s) => (kept.push node,s)
        | (none,s) => (kept,s)) (#[],s)
      (some (.element name attrs kept.toList),s)

/-- All `use` references to other documents in `root`, resolved. The result is the
    new tree, the documents that were found and those that the host has not supplied. -/
private def importDocuments (root : NamespaceNode) (documentURL : Option String)
    (supplied : List (String × ByteArray)) : NamespaceNode × ImportState := Id.run do
  let tree := fun (key : String) => do
    let (_,bytes) ← supplied.find? (·.1 == key)
    let text ← String.fromUTF8? bytes
    (parseNamespaceView text).toOption
  let available := fun key => (tree key).isSome
  let (some main,first) := rewriteImport documentURL documentURL "" available maxDepth documentURL {} root
    | return (root,{})
  let mut state := first
  let mut defs : Array NamespaceNode := #[]
  let mut next := 0
  for _ in [:maxExternalDocuments] do
    let some key := state.documents[next]? | break
    if let some document := tree key then
      let (rewritten,after) := rewriteImport documentURL (some key) (importPrefix next) available maxDepth (some key) state document
      state := after
      if let some node := rewritten then
        -- The root stays: a `use` can name it (W3C struct-use-206-t).
        defs := defs.push (svgElement "defs" [] [node])
    next := next+1
  if state.documents.size > maxExternalDocuments then
    state := {state with log:=state.log ++ [s!"external documents past {maxExternalDocuments} are not read"]}
  match main with
  | .element name attrs children => return (.element name attrs (children ++ defs.toList),state)
  | node => return (node,state)

/-- Each `font-face-uri` that names a font in another document: the family that its
    `font-face` gives, and the reference, resolved. -/
private def fontFaceUris : Nat → Option String → Option String → NamespaceNode → List (String × String)
  | 0,_,_,_ => []
  | _,_,_,.other _ => []
  | fuel+1,family,base,.element name attrs children =>
    let base := NativeSVGReferences.elementBase attrs base
    let family := if name.localPart == "font-face" then plainAttr attrs "font-family" else family
    let own := if name.localPart != "font-face-uri" then [] else
      match family,NativeSVGReferences.href attrs with
      | some f,some h => if h.trimAscii.toString.startsWith "#" then [] else [(f,NativeSVG.imageKey base h)]
      | _,_ => []
    own ++ children.flatMap (fontFaceUris fuel family base)

/-- The font with this id in a document, or its first font. The family is the one that
    the referring `font-face` gives. -/
private def externalFont (family fragment : String) (root : NamespaceNode) : Option SVGFont :=
  let elements := fontElements maxDepth root
  let hasId : NamespaceNode → Bool := fun
    | .element _ attrs _ => attrs.any (fun a => a.name.localPart == "id" && a.value == fragment)
    | _ => false
  match (elements.find? hasId).orElse (fun _ => elements.head?) with
  | some (.element _ attrs children) => some {SVGFont.ofElement attrs children with family}
  | _ => none

/-- Fonts that a document names in other documents, and the keys the host has not
    supplied. Two faces of one reference read it once each; a document has few. -/
private def externalFonts (root : NamespaceNode) (documentURL : Option String)
    (supplied : List (String × ByteArray)) : List SVGFont × List String := Id.run do
  let mut fonts : List SVGFont := []
  let mut missing : List String := []
  for (family,reference) in fontFaceUris maxDepth none documentURL root do
    let (key,fragment) := splitFragment reference
    if key.toLower.startsWith "data:" then continue
    match supplied.find? (·.1 == key) with
    | none => missing := missing ++ [key]
    | some (_,bytes) =>
      let tree := (String.fromUTF8? bytes).bind fun text => (parseNamespaceView text).toOption
      if let some font := tree.bind (externalFont family fragment) then fonts := fonts ++ [font]
  return (fonts,missing)

/-- Parse as a browser would: draw what the strict reader can draw. A document
    that is not well-formed XML stays an error. Text with no SVG font is drawn with
    the SFNT fonts `sfnt`, the first being the primary font (`NativeSVGText.lowerSfnt`). -/
def parse (xml : String) (width height : Nat) (font : Option SVGFont := none)
    (images : List (String × ByteArray) := []) (documentURL : Option String := none)
    (sfnt : Array NativeSVGText.Font := #[]) :
    Except String (NativeSVG.Scene × List String) := do
  if xml.length > NativeSVG.maxInputChars then throw "SVG input exceeds 1048576 characters"
  let root ← parseNamespaceView xml
  let (root,rootLog) := rootAttrs root
  let (root,imports) := importDocuments root documentURL images
  -- Fonts in the document come first; the host's font is the default.
  let targets := (idTargets maxDepth root).foldl (fun map (id,node) =>
    if map.contains id then map else map.insert id node) ({} : Std.HashMap String NamespaceNode)
  let (linkedFonts,_) := externalFonts root documentURL images
  let (some root,log) := normalise (fontsIn root ++ linkedFonts ++ font.toList) sfnt targets maxDepth {} false root | throw "root element is not read"
  let store := NativeSVG.imageStore root documentURL images
  let (some root,imageLog) := dropBrokenImages store maxDepth documentURL root | throw "root element is not read"
  repair width height 1024 {root,dropped:=rootLog ++ imports.log ++ log ++ imageLog,parses:=0,documentURL,images:=store}

/-- The references of a document that a host must fetch: not the `data:` ones. These
    are images, and other documents that a `use` names. `supplied` holds what the host
    has already; a supplied document can name more, so the host asks again until no
    key is new. -/
def imageRequests (xml : String) (documentURL : Option String := none)
    (supplied : List (String × ByteArray) := []) : Except String (List String) := do
  if xml.length > NativeSVG.maxInputChars then throw "SVG input exceeds 1048576 characters"
  let root ← parseNamespaceView xml
  let (root,imports) := importDocuments root documentURL supplied
  let external := (imports.missing ++ (externalFonts root documentURL supplied).2).filter (!·.toLower.startsWith "data:")
  return (external ++ (NativeSVG.imageKeys root documentURL).filter (!·.toLower.startsWith "data:")).eraseDups

end NativeSVGForgiving
