import L4Factoidal.Rendering.Scene

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

/-- Layout emits runs in document order, one for each word. The clusters of a
run count characters from the start of its text node, so the first cluster is
the base of the run text. -/
def cells (runs : Array GlyphRun) : Array Cell := Id.run do
  let mut out := #[]
  for (run,index) in runs.zipIdx do
    let chars := run.text.toList
    let base := run.glyphs.foldl (fun low g => min low g.clusterStart)
      ((run.glyphs[0]?).map (·.clusterStart) |>.getD 0)
    for g in run.glyphs do
      let text := String.ofList ((chars.drop (g.clusterStart-base)).take (g.clusterEnd-g.clusterStart))
      out := out.push {run:=index,source:=run.source,x:=g.x,y:=g.y,width:=g.advance,height:=run.fontSize,text}
  return out

/-- A glyph is before a point when its line is above the point, or when the
point is on its line and past the middle of the glyph. -/
private def Cell.before (c : Cell) (x y : Float) : Bool :=
  c.y+c.height <= y || (c.y <= y && c.x+c.width/2 <= x)

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
      else if p.run != c.run && c.x > p.x+p.width+0.5 then out := out ++ " "
    out := out ++ c.text
    previous := some c
  return out

/-- One rectangle for each selected line: x, y, width, height. -/
def lineRects (items : Array Cell) (selection : Selection) : Array (Float × Float × Float × Float) := Id.run do
  let (low,high) := range items selection
  let mut out : Array (Float × Float × Float × Float) := #[]
  let mut line : Option Cell := none
  for c in (items.extract low high) do
    match line, out.back? with
    | some first, some (x,y,w,h) =>
      if sameLine first c then
        let top := min y c.y
        let bottom := max (y+h) (c.y+c.height)
        out := out.pop.push (x,top,c.x+c.width-x,bottom-top)
      else
        out := out.push (c.x,c.y,c.width,c.height)
        line := some c
    | _,_ =>
      out := out.push (c.x,c.y,c.width,c.height)
      line := some c
  return out

/-- Translucent marks over the text, drawn after the page. -/
def highlight (items : Array Cell) (selection : Selection) : List Node :=
  (lineRects items selection).toList.map fun (x,y,w,h) =>
    .paint ⟨none,{geometry := .rect x y w h,style := {fill := .solid ⟨0.2,0.45,0.95⟩,fillOpacity := 0.35}}⟩

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
  | _ => "none"

/-- Text size of a new window on a desktop screen. -/
def defaultPercent : Nat := 150

def commandPercent (command percent : Nat) : Nat :=
  match command with
  | 1 => zoomIn percent
  | 2 => zoomOut percent
  | 3 => defaultPercent
  | _ => percent

#guard zoomIn 100 == 110 && zoomIn 105 == 115 && zoomIn 150 == 165 && zoomIn 250 == 275
#guard zoomIn 2000 == 2200 && zoomIn 1 == 2
#guard zoomOut 100 == 90 && zoomOut 50 == 50 && zoomOut 105 == 95 && zoomOut 165 == 150
#guard zoomOut 51 == 50 && zoomOut 10 == 10 && zoomOut 2200 == 2000
#guard commandPercent 3 175 == 150 && commandPercent 4 175 == 175
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
end WebSelection
