import SVG
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

private def svgURI := "http://www.w3.org/2000/svg"
private def xmlURI := "http://www.w3.org/XML/1998/namespace"
/-- XML nesting limit of this pass; the strict reader stops at 32 groups. -/
private def maxDepth : Nat := 64
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

/-- `xml:id` is an ID (XML ID 1.0); the strict reader reads only `id`. -/
private def renameId (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.map fun a =>
    if a.name.namespace_ == some xmlURI && a.name.localPart == "id"
    then {a with name:={namespace_:=none,localPart:="id"}} else a

private def plainAttr (attrs : List NamespaceAttribute) (key : String) : Option String :=
  (attrs.find? (fun a => a.name.namespace_.isNone && a.name.localPart == key)).map (·.value)
private def mkAttr (key value : String) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=key},value}
private def svgElement (tag : String) (attrs : List NamespaceAttribute) (children : List NamespaceNode) : NamespaceNode :=
  .element {namespace_:=some svgURI,localPart:=tag} attrs children

/-! ### SVG fonts and text

   SVG Tiny 1.2 §11: a glyph is path data. Text therefore lowers to `path`
   elements, which the strict reader can already draw. -/

private structure Glyph where
  name : String
  advance : Float
  data : String

structure SVGFont where
  family : String := ""
  unitsPerEm : Float := 1000
  defaultAdvance : Float := 500
  /-- `font-face` ascent and descent, in font units, both as positive depths. -/
  ascent : Float := 800
  descent : Float := 200
  glyphs : Std.HashMap Char Glyph := {}
  kerning : Std.HashMap (String × String) Float := {}
  missing : Glyph := ⟨"",500,""⟩
instance : Inhabited SVGFont := ⟨{}⟩

private def float (source : Option String) (fallback : Float) : Float :=
  match source with
  | none => fallback
  | some s =>
    let s := s.trimAscii.toString
    let s := if s.endsWith "px" then (s.dropEnd 2).toString else s
    match (NativeSVG.number s) with | .ok value => value | .error _ => fallback

private def fontElements : Nat → NamespaceNode → List NamespaceNode
  | 0,_ => []
  | _,.other _ => []
  | fuel+1,node@(.element name _ children) =>
    if name.localPart == "font" then [node] else children.flatMap (fontElements fuel)

private def SVGFont.ofElement (attrs : List NamespaceAttribute) (children : List NamespaceNode) : SVGFont := Id.run do
  let fallback := float (plainAttr attrs "horiz-adv-x") 500
  let mut font : SVGFont := {defaultAdvance:=fallback,missing:=⟨"",fallback,""⟩}
  for child in children do
    let .element name a _ := child | continue
    let advance := float (plainAttr a "horiz-adv-x") fallback
    let data := (plainAttr a "d").getD ""
    match name.localPart with
    | "font-face" => 
      let units := float (plainAttr a "units-per-em") 1000
      font := {font with unitsPerEm:=units,family:=(plainAttr a "font-family").getD "",ascent:=(float (plainAttr a "ascent") (units*0.8)).abs,descent:=(float (plainAttr a "descent") (units*0.2)).abs}
    | "missing-glyph" => font := {font with missing:=⟨"",advance,data⟩}
    | "glyph" =>
      if let some text := plainAttr a "unicode" then
        if let [c] := text.toList then
          font := {font with glyphs:=font.glyphs.insert c ⟨(plainAttr a "glyph-name").getD text,advance,data⟩}
    | "hkern" =>
      let left := (plainAttr a "g1").getD ""
      let right := (plainAttr a "g2").getD ""
      let k := float (plainAttr a "k") 0
      for l in left.splitOn "," do
        for r in right.splitOn "," do
          font := {font with kerning:=font.kerning.insert (l.trimAscii.toString,r.trimAscii.toString) k}
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

private def SVGFont.glyph (font : SVGFont) (c : Char) : Glyph :=
  font.glyphs.getD c font.missing

/-- Attributes of a text element that the strict reader paints with. -/
private def paintKeys := ["fill","stroke","fill-opacity","stroke-opacity","color","display","visibility","opacity",
  "stroke-linejoin","stroke-linecap","stroke-miterlimit"]

private structure TextState where
  size : Float := 16
  anchor : String := "start"
  family : String := ""
  strokeWidth : Float := 1
  /-- `line-increment`, SVG Tiny 1.2 §10.11.4; `none` is `auto`. -/
  lineIncrement : Option Float := none
  textAlign : String := "start"
  displayAlign : String := "before"
  preserveSpace : Bool := false

/-- A value of a keyword property: only a listed keyword changes it. -/
private def keyword (attrs : List NamespaceAttribute) (key : String) (allowed : List String) (old : String) : String :=
  match plainAttr attrs key with
  | some value => let value := value.trimAscii.toString; if allowed.contains value then value else old
  | none => old

private def lineIncrementOf (attrs : List NamespaceAttribute) (old : Option Float) : Option Float :=
  match plainAttr attrs "line-increment" with
  | none => old
  | some value =>
    let value := value.trimAscii.toString
    if value == "inherit" then old else if value == "auto" then none else
    match NativeSVG.number value with
    | .ok n => if n >= 0 then some n else old
    | .error _ => old

private def spaceOf (attrs : List NamespaceAttribute) (old : Bool) : Bool :=
  match attrs.find? (fun a => a.name.namespace_ == some xmlURI && a.name.localPart == "space") with
  | some a => a.value == "preserve"
  | none => old

private def TextState.read (s : TextState) (attrs : List NamespaceAttribute) : TextState :=
  { size := float (plainAttr attrs "font-size") s.size,
    anchor := (plainAttr attrs "text-anchor").getD s.anchor,
    family := (plainAttr attrs "font-family").getD s.family,
    strokeWidth := float (plainAttr attrs "stroke-width") s.strokeWidth,
    lineIncrement := lineIncrementOf attrs s.lineIncrement,
    textAlign := keyword attrs "text-align" ["start","center","end"] s.textAlign,
    -- §10.11.6: for SVG, `auto` is `before`.
    displayAlign := match plainAttr attrs "display-align" with
      | some value => if value.trimAscii.toString == "auto" then "before"
        else keyword attrs "display-align" ["before","center","after"] s.displayAlign
      | none => s.displayAlign,
    preserveSpace := spaceOf attrs s.preserveSpace }

/-- CSS Fonts: the first named family that is known, else the default font. -/
private def chooseFont (fonts : List SVGFont) (family : String) : Option SVGFont :=
  let names := (family.splitOn ",").map (fun n => (n.trimAscii.toString.replace "'" "").replace "\"" "")
  (names.findSome? (fun name => fonts.find? (·.family == name))).orElse (fun _ => fonts.getLast?)

private structure Run where
  text : String
  size : Float
  strokeWidth : Float
  paint : List NamespaceAttribute
  xs : List Float := []
  ys : List Float := []
  dx : Float := 0
  dy : Float := 0
  /-- A `tbreak`: the text is empty, and the line ends here. -/
  lineBreak : Bool := false
  increment : Option Float := none
  preserveSpace : Bool := false

private def paintOf (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.filter fun a => a.name.namespace_.isNone && paintKeys.contains a.name.localPart

private def numberList (attrs : List NamespaceAttribute) (key : String) : List Float :=
  match plainAttr attrs key with
  | none => []
  | some s => ((s.splitOn " ").flatMap (·.splitOn ",") |>.filter (· != "")).map (fun n => float (some n) 0)

/-- Text runs in order. A later unsupported child is logged and skipped. -/
private def textRuns (area : Bool) : Nat → TextState → List NamespaceAttribute → NamespaceNode → List Run × List String
  | 0,_,_,_ => ([],[])
  | _,state,paint,.other raw => match raw with
    | .text t | .cdata t => ([{text := t, size := state.size, strokeWidth := state.strokeWidth, paint := paint, increment := state.lineIncrement, preserveSpace := state.preserveSpace}],[])
    | _ => ([],[])
  | fuel+1,state,paint,.element name attrs children =>
    if area && name.localPart == "tbreak" then
      ([{text := "", size := state.size, strokeWidth := state.strokeWidth, paint := paint, lineBreak := true, increment := lineIncrementOf attrs state.lineIncrement}],[])
    else if name.localPart != "tspan" then ([],["element in text: " ++ name.localPart]) else
    let inner := state.read attrs
    let results := children.map (textRuns area fuel inner (paint ++ paintOf attrs))
    let runs := results.flatMap (·.1)
    let runs := match runs with
      | run::rest =>
        let placed : Run := { run with
          xs := numberList attrs "x"
          ys := numberList attrs "y"
          dx := (numberList attrs "dx").headD 0
          dy := (numberList attrs "dy").headD 0 }
        placed::rest
      | [] => []
    (runs,results.flatMap (·.2))

private def collapse (s : String) : String :=
  let spaced := s.toList.map (fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c)
  String.ofList (spaced.foldr (fun c acc => match acc with
    | ' '::_ => if c == ' ' then acc else c::acc
    | _ => c::acc) [])

private def runAdvance (font : SVGFont) (run : Run) : Float :=
  let scale := run.size/font.unitsPerEm
  let (total,_) := run.text.toList.foldl (fun (total,previous) c =>
    let g := font.glyph c
    let kern := (previous.bind (fun (p : Glyph) => font.kerning.get? (p.name,g.name))).getD 0
    (total+(g.advance-kern)*scale,some g)) ((0 : Float),(none : Option Glyph))
  total

/-- Tell each glyph path of a run the bounding box of the whole text, x0 y0 x1 y1. -/
private def markGlyphs (box : Float × Float × Float × Float) : NamespaceNode → NamespaceNode
  | .element name attrs paths =>
    let (x0,y0,x1,y1) := box
    let mark : NamespaceAttribute := {name:={namespace_:=some NativeSVG.internalURI,localPart:=NativeSVG.textBoxAttribute},value:=s!"{x0} {y0} {x1-x0} {y1-y0}"}
    .element name attrs (paths.map fun
      | .element n a c => .element n (a ++ [mark]) c
      | node => node)
  | node => node

/-- Lower one `text` element to a group of glyph paths. -/
private def lowerText (font : SVGFont) (state : TextState) (attrs : List NamespaceAttribute)
    (children : List NamespaceNode) : NamespaceNode × List String := Id.run do
  let state := state.read attrs
  let results := children.map (textRuns false maxDepth state [])
  let raw := (results.flatMap (·.1)).map (fun r => {r with text:=collapse r.text})
  -- Default xml:space: no leading or trailing space on the whole text.
  let lastIndex := raw.length-1
  let runs := raw.zipIdx.map fun (r,i) =>
    let text := if i == 0 then r.text.trimAsciiStart.toString else r.text
    {r with text:=if i == lastIndex then text.trimAsciiEnd.toString else text}
  let width := (runs.map (runAdvance font)).foldl (·+·) 0
  let shift := match state.anchor with | "middle" => -width/2 | "end" => -width | _ => 0
  let xs := numberList attrs "x"
  let ys := numberList attrs "y"
  let mut x := xs.headD 0 + (numberList attrs "dx").headD 0 + shift
  let mut y := ys.headD 0 + (numberList attrs "dy").headD 0
  let mut index := 0
  let mut groups : Array NamespaceNode := #[]
  -- SVG Tiny 1.2 §7.11: the bounding box of a text is that of its character cells.
  let mut box : Option (Float × Float × Float × Float) := none
  for run in runs do
    x := x+run.dx
    y := y+run.dy
    if run.size <= 0 then continue
    let scale := run.size/font.unitsPerEm
    let mut paths : Array NamespaceNode := #[]
    let mut previous : Option Glyph := none
    for (c,position) in run.text.toList.zipIdx do
      -- A coordinate list places the characters it covers (SVG Tiny 1.2 §10.5).
      if let some value := run.xs[position]? then x := value
      if let some value := run.ys[position]? then y := value
      if position > 0 || index > 0 then
        if let some value := xs[index]? then x := value
        if let some value := ys[index]? then y := value
      index := index+1
      let g := font.glyph c
      let kern := (previous.bind (fun p => font.kerning.get? (p.name,g.name))).getD 0
      x := x-kern*scale
      if !g.data.isEmpty then
        paths := paths.push (svgElement "path" [mkAttr "d" g.data,mkAttr "stroke-width" (toString (run.strokeWidth/scale)),
          mkAttr "transform" s!"translate({x},{y}) scale({scale},{-scale})"] [])
      let cellTop := y-font.ascent*scale
      let cellBottom := y+font.descent*scale
      let cellRight := x+g.advance*scale
      box := some (match box with
        | none => (x,cellTop,cellRight,cellBottom)
        | some (x0,y0,x1,y1) => (min x0 x,min y0 cellTop,max x1 cellRight,max y1 cellBottom))
      x := x+g.advance*scale
      previous := some g
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
instance : Inhabited Cell := ⟨⟨⟨"",0,""⟩,0,0,0,false,false⟩⟩

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
        | some (r,p) => if r == current then ((font.kerning.get? (p.name,g.name)).getD 0)*scale else 0
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
  let results := children.map (textRuns true maxDepth state [])
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

/-- SVG Tiny 1.2 §5.8.2: this agent's language is en, and it has no extensions. -/
private def conditionsPass (attrs : List NamespaceAttribute) : Bool :=
  let language := match plainAttr attrs "systemLanguage" with
    | none => true
    | some value => (value.splitOn ",").any fun tag =>
      let tag := tag.trimAscii.toString.toLower
      tag == "en" || tag.startsWith "en-"
  let extensions := match plainAttr attrs "requiredExtensions" with | none => true | some _ => false
  language && extensions

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
private def normalise (fonts : List SVGFont) (targets : Std.HashMap String NamespaceNode) : Nat → TextState → Bool → NamespaceNode → Option NamespaceNode × List String
  | 0,_,_,_ => (none,["element: nesting exceeds 64"])
  | _,_,_,.other (.comment c) => (some (.other (.comment c)),[])
  | _,_,keepText,.other raw => match raw with
    | .text t | .cdata t =>
      if keepText || isSpace t then (some (.other raw),[]) else (none,["text outside a text element"])
    | _ => (none,["processing instruction"])
  | fuel+1,state,_,.element name attrs children =>
    if name.namespace_ != some svgURI then (none,["foreign element: " ++ name.localPart])
    else if !conditionsPass attrs then (none,[])
    else if name.localPart == "text" && !fonts.isEmpty then
      let inner := state.read attrs
      match chooseFont fonts inner.family with
      | some font => let (node,log) := lowerText font state attrs children; (some node,log)
      | none => (none,["element: text"])
    else if name.localPart == "textArea" && !fonts.isEmpty then
      match chooseFont fonts (state.read attrs).family with
      | some font => let (node,log) := lowerArea font state attrs children; (some node,log)
      | none => (none,["element: textArea"])
    else if name.localPart == "switch" then
      -- SVG Tiny 1.2 §5.8: draw only the first child whose conditions pass.
      let selected : NamespaceNode → Bool := fun
        | .element n a _ => n.namespace_ == some svgURI && conditionsPass a | _ => false
      let chosen := children.find? selected
      let inner := state.read attrs
      let result := (chosen.toList).map (normalise fonts targets fuel inner false)
      -- A child that is not drawn can still be referenced, so it stays as a definition.
      let unused := children.eraseIdx (children.findIdx selected)
      let kept := unused.map (normalise fonts targets fuel inner false)
      (some (svgElement "g" (renameId attrs) (result.filterMap (·.1) ++ [svgElement "defs" [] (kept.filterMap (·.1))])),
        result.flatMap (·.2) ++ kept.flatMap (·.2))
    else if name.localPart == "a" then
      -- A link draws its content. Link regions are not part of this pass.
      let inner := state.read attrs
      let results := children.map (normalise fonts targets fuel inner false)
      (some (svgElement "g" (renameId attrs) (results.filterMap (·.1))),results.flatMap (·.2))
    else if name.localPart == "use" && !fonts.isEmpty && (textInstance targets attrs).isSome then
      let inner := state.read attrs
      let target := (textInstance targets attrs).getD (.other (.comment ""))
      let (node,log) := normalise fonts targets fuel inner false target
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
      let results := children.map (normalise fonts targets fuel inner keepText)
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
          (some (setHref renamed ("#" ++ importPrefix i ++ fragment)),s)
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

/-- Parse as a browser would: draw what the strict reader can draw. A document
    that is not well-formed XML stays an error. -/
def parse (xml : String) (width height : Nat) (font : Option SVGFont := none)
    (images : List (String × ByteArray) := []) (documentURL : Option String := none) :
    Except String (NativeSVG.Scene × List String) := do
  if xml.length > NativeSVG.maxInputChars then throw "SVG input exceeds 1048576 characters"
  let root ← parseNamespaceView xml
  let (root,rootLog) := rootAttrs root
  let (root,imports) := importDocuments root documentURL images
  -- Fonts in the document come first; the host's font is the default.
  let targets := (idTargets maxDepth root).foldl (fun map (id,node) =>
    if map.contains id then map else map.insert id node) ({} : Std.HashMap String NamespaceNode)
  let (some root,log) := normalise (fontsIn root ++ font.toList) targets maxDepth {} false root | throw "root element is not read"
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
  let external := imports.missing.filter (!·.toLower.startsWith "data:")
  return (external ++ (NativeSVG.imageKeys root documentURL).filter (!·.toLower.startsWith "data:")).eraseDups

end NativeSVGForgiving
