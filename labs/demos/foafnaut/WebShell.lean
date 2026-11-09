import L4Factoidal.Rendering.ClipTheorems
import WebRender
import WebRoute
import WebSelection

/-! The browser's own face: tabs, the address bar and its buttons, drawn into the
same scene as the page, so one WebGPU pass draws the window. All of it is pixel
art from the engine's bitmap font: NeXT bevels, arcade lettering.

The host keeps the `Shell` value between calls and sends it back. It makes no
decision here: Lean says what a click, a key or an address means. -/
namespace WebShell
open L4Factoidal

/-- The icon of a tab, as `WebDocument.iconPrepare` gives it: SVG text (`kind` "svg"),
or RGBA pixels in Base64 (`kind` "bitmap"). -/
structure TabIcon where
  kind : String
  width : Nat := 0
  height : Nat := 0
  data : String
  deriving Repr, BEq

structure Tab where
  title : String := ""
  icon : Option TabIcon := none
  deriving Repr, BEq

/-- The address text with its cursor and selection anchor, as an undo step keeps it. -/
structure Snapshot where
  address : String
  cursor : Nat
  anchor : Nat
  deriving Repr, BEq

structure Shell where
  tabs : Array Tab := #[{}]
  active : Nat := 0
  address : String := ""
  cursor : Nat := 0
  /-- The other end of the selection: the text between `anchor` and `cursor` is
  selected. `anchor == cursor` is no selection. -/
  anchor : Nat := 0
  /-- One undo step and one redo step (Command-Z, Shift-Command-Z). -/
  undo : Option Snapshot := none
  redo : Option Snapshot := none
  /-- The last edit typed text: more typed text joins the same undo step. -/
  typing : Bool := false
  focused : Bool := false
  canBack : Bool := false
  canForward : Bool := false
  loading : Bool := false
  /-- Backing pixels for one logical pixel. -/
  scale : Nat := 1
  theme : String := "next"
  pages : Nat := 0
  /-- How far the page has moved up, in backing pixels. -/
  scroll : Nat := 0
  /-- The control the pointer is pressed on (`:active`), or "". -/
  pressed : String := ""
  /-- How far the chrome has folded away as the page scrolls down (owner, 2026-11-08), in
  percent: 0 is the full chrome, 100 the strip that shows only the domain. The host sets
  it from the scroll's direction and distance; with the classic UI it stays 0. -/
  collapse : Nat := 0
  /-- The chrome may fold (the classic UI is off): a band then covers the view under the
  strip, so a change of `collapse` needs no new band. -/
  collapsible : Bool := false
  /-- A back or forward swipe under way (WebGesture.hint): −100 .. 100, negative for back. -/
  swipe : Int := 0
  /-- The address menu is open: "Copy address" and "Paste and go" in the navigation row
  (`menuControls`). `edit "menu"` opens it on a focused bar (`opensMenu` says when); an
  edit, a key, typed text or the bar losing the focus closes it. -/
  menu : Bool := false
  deriving Repr, BEq

private structure Theme where
  base : Rendering.Color
  light : Rendering.Color
  dark : Rendering.Color
  ink : Rendering.Color
  well : Rendering.Color
  wellInk : Rendering.Color
  back : Rendering.Color
  muted : Rendering.Color
  accent : Rendering.Color
  coin : Rendering.Color
  /-- Behind selected address text. -/
  selected : Rendering.Color
  /-- Selected address text: the `::selection` colours of the theme (CSS Pseudo-Elements 4 §3.1). -/
  selectedInk : Rendering.Color

private def hex (r g b : Nat) : Rendering.Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
/-- The selection colours of the NeXT theme: those of the page (`WebSelection.highlight`). -/
def selectionBackground : Rendering.Color := WebSelection.selectionBackground
def selectionText : Rendering.Color := WebSelection.selectionText
private def next : Theme :=
  ⟨hex 170 170 170,hex 255 255 255,hex 85 85 85,hex 0 0 0,hex 255 255 255,hex 0 0 0,hex 128 128 128,hex 32 32 32,hex 224 32 138,hex 255 196 0,selectionBackground,selectionText⟩
private def arcade : Theme :=
  ⟨hex 34 38 54,hex 84 92 128,hex 10 12 20,hex 216 240 255,hex 10 12 20,hex 120 255 170,hex 20 23 34,hex 150 160 200,hex 57 255 136,hex 255 196 0,hex 57 255 136,hex 10 12 20⟩
private def themeOf (s : Shell) : Theme := if s.theme == "arcade" then arcade else next

/-! ### Measures, in backing pixels -/

private def unit (s : Shell) : Nat := max 1 s.scale
/-- One lettering pixel: 2 backing pixels at scale 1, 3 at scale 2. -/
private def dot (s : Shell) : Nat := (3*unit s+1)/2
private def narrow (s : Shell) (width : Nat) : Bool := width/unit s < 560
private def tabRow (s : Shell) (width : Nat) : Nat := if narrow s width then 0 else 26*unit s
private def navRow (s : Shell) : Nat := 36*unit s
private def edge (s : Shell) : Nat := 3*unit s
/-- The full chrome, as the classic UI always has it. The layout reads this one, so a
change of `collapse` lays nothing out again (`WebDocument.layoutTop_collapse`). -/
def fullHeight (s : Shell) (width : Nat) : Nat := tabRow s width+navRow s+edge s
/-- One lettering pixel of the folded strip: two thirds of `dot`. -/
private def smallDot (s : Shell) : Nat := max 1 (dot s*2/3)
/-- The folded chrome: one line of small lettering, and the edge. -/
def stripHeight (s : Shell) : Nat := 7*smallDot s+8*unit s+edge s
/-- `a` moved towards `b` by `p` percent (`p ≤ 100`), in whole pixels. -/
def lerp (a b p : Nat) : Nat := if a ≤ b then a+(b-a)*p/100 else a-(a-b)*p/100
/-- The chrome's height on screen: from `fullHeight` at collapse 0 to the strip at 100,
in proportion. -/
def height (s : Shell) (width : Nat) : Nat :=
  let full := fullHeight s width
  full-(full-min full (stripHeight s))*min 100 s.collapse/100

theorem height_classic (s : Shell) (width : Nat) (h : s.collapse = 0) : height s width = fullHeight s width := by
  simp [height,h]

/-- The fold over plain numbers: `F` rows unfolded, `D` rows that fold away, `c` percent. -/
private theorem fold_part_le (D c : Nat) : D*min 100 c/100 ≤ D := by
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm 100]
  exact Nat.mul_le_mul_left D (Nat.min_le_left 100 c)

private theorem fold_antitone (F D : Nat) {a b : Nat} (le : a ≤ b) : F-D*min 100 b/100 ≤ F-D*min 100 a/100 := by
  have : D*min 100 a/100 ≤ D*min 100 b/100 := Nat.div_le_div_right (Nat.mul_le_mul_left D (by omega))
  omega

theorem height_le_full (s : Shell) (width : Nat) : height s width ≤ fullHeight s width :=
  Nat.sub_le _ _

/-- The chrome never folds smaller than the strip (or the full chrome, if that is smaller). -/
theorem strip_le_height (s : Shell) (width : Nat) : min (fullHeight s width) (stripHeight s) ≤ height s width := by
  have part := fold_part_le (fullHeight s width-min (fullHeight s width) (stripHeight s)) s.collapse
  have : min (fullHeight s width) (stripHeight s) ≤ fullHeight s width := Nat.min_le_left _ _
  show min (fullHeight s width) (stripHeight s) ≤
    fullHeight s width-(fullHeight s width-min (fullHeight s width) (stripHeight s))*min 100 s.collapse/100
  omega

/-- Folding further never makes the chrome taller: the height falls as `collapse` rises. -/
theorem height_antitone (s : Shell) (width : Nat) {a b : Nat} (le : a ≤ b) :
    height {s with collapse := b} width ≤ height {s with collapse := a} width :=
  fold_antitone (fullHeight s width) (fullHeight s width-min (fullHeight s width) (stripHeight s)) le

/-- The full chrome does not read the collapse or the scroll. -/
theorem fullHeight_collapse (s : Shell) (collapse scroll width : Nat) :
    fullHeight {s with collapse,scroll} width = fullHeight s width := rfl

private structure Box where
  name : String
  x : Nat
  y : Nat
  w : Nat
  h : Nat

/-! ### The address menu

On a phone there is no menu bar and no keyboard shortcut, so the address bar has its own
two buttons: "Copy address" copies the whole address, "Paste and go" goes to the address
on the clipboard. They are in the navigation row, right of the address bar, while
`Shell.menu` is set and the chrome is not folded. -/

/-- The controls of the address menu, left to right. -/
def menuControls : List String := ["copyAddress","pasteGo"]

def menuLabel : String → String
  | "copyAddress" => "Copy address"
  | "pasteGo" => "Paste and go"
  | _ => ""

/-- The menu is drawn: open, and the chrome full. -/
def menuShown (s : Shell) : Bool := s.menu && s.collapse == 0

/-- Whether a press opens the address menu. `how` is "tap" (a press), "hold" (a long press,
`WebGesture.hold`) or "context" (a right click); `touch` says a finger made it. A long press
or a right click on the address bar opens it, and so does a tap on it with a finger, since a
touch screen has no other way to copy or paste. -/
def opensMenu (control : Option String) (how : String) (touch : Bool) : Bool :=
  control == some "address" && (how == "hold" || how == "context" || (how == "tap" && touch))

theorem opensMenu_address {control : Option String} {how : String} {touch : Bool}
    (h : opensMenu control how touch = true) : control = some "address" := by
  unfold opensMenu at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- A mouse click (no finger, no hold, no right click) never opens the menu. -/
theorem click_never_opens (control : Option String) : opensMenu control "tap" false = false := by
  simp [opensMenu]

private def tabWidth (s : Shell) (width : Nat) : Nat :=
  let room := width-(90*unit s)
  min (180*unit s) (room/max 1 s.tabs.size)

/-- A menu button: its label and 6 lettering pixels of margin on each side. -/
private def menuButtonWidth (s : Shell) (size : Nat) (name : String) : Nat :=
  (menuLabel name).length*6*size+12*unit s

/-- The lettering size of the menu: the bar's, or the folded strip's smaller one when the
two buttons would leave the address bar less than 80 logical pixels. -/
private def menuSize (s : Shell) (width : Nat) : Nat :=
  let u := unit s
  let need := menuButtonWidth s (dot s) "copyAddress"+menuButtonWidth s (dot s) "pasteGo"+(2+4+4+4)*u+80*u
  if width ≥ need then dot s else smallDot s

/-- Every control and where it is. Drawing and hit testing both read this. -/
private def boxes (s : Shell) (width : Nat) : List Box := Id.run do
  let u := unit s
  let top := tabRow s width
  let button := 28*u
  let pad := 4*u
  let by_ := top+pad
  let mut out : List Box := []
  if !narrow s width then
    let w := tabWidth s width
    for i in [:s.tabs.size] do
      out := out ++ [⟨s!"tab:{i}",2*u+i*w,3*u,w-2*u,top-3*u⟩]
      if s.tabs.size > 1 then
        out := out ++ [⟨s!"close:{i}",2*u+i*w+w-20*u,6*u,16*u,top-11*u⟩]
    out := out ++ [⟨"newTab",2*u+s.tabs.size*w,4*u,22*u,top-7*u⟩]
  let mut x := pad
  out := out ++ [⟨"back",x,by_,button,button⟩]
  x := x+button+2*u
  if !narrow s width then
    out := out ++ [⟨"forward",x,by_,button,button⟩]
    x := x+button+2*u
  out := out ++ [⟨"reload",x,by_,button,button⟩]
  x := x+button+2*u
  if !narrow s width then
    out := out ++ [⟨"home",x,by_,button,button⟩]
    x := x+button+2*u
  x := x+4*u
  if menuShown s then
    -- The menu's buttons take the right of the row; on a narrow window the bar starts at
    -- the left edge, so it keeps room for the end of the address.
    let size := menuSize s width
    let paste := menuButtonWidth s size "pasteGo"
    let copy := menuButtonWidth s size "copyAddress"
    let pasteX := width-min width (pad+paste)
    let copyX := pasteX-min pasteX (2*u+copy)
    let left := if narrow s width then pad else x
    let kept := if narrow s width then out.filter (fun b => b.name != "back" && b.name != "reload") else out
    return kept ++ [⟨"address",left,by_,copyX-min copyX (left+4*u),button⟩,
      ⟨"copyAddress",copyX,by_,copy,button⟩,⟨"pasteGo",pasteX,by_,paste,button⟩]
  let tail := if narrow s width then 2*button+8*u+pad else 2*button+8*u+pad
  out := out ++ [⟨"address",x,by_,width-x-tail,button⟩]
  out := out ++ [⟨if narrow s width then "tabs" else "source",width-pad-2*button-2*u,by_,button,button⟩]
  out := out ++ [⟨"settings",width-pad-button,by_,button,button⟩]
  return out

private def Box.contains (b : Box) (x y : Nat) : Bool :=
  x >= b.x && x < b.x+b.w && y >= b.y && y < b.y+b.h

/-- A control that is drawn pressed while the pointer is down on it. -/
def pressable (s : Shell) (name : String) : Bool :=
  match name.splitOn ":" with
  | ["back"] => s.canBack
  | ["forward"] => s.canForward
  | ["reload"] | ["home"] | ["source"] | ["settings"] | ["newTab"] | ["tabs"] | ["close",_] => true
  | ["copyAddress"] | ["pasteGo"] => s.menu
  | _ => false

/-- The box of a pressable control: `(x,y,w,h)` in window pixels. -/
def pressBox (s : Shell) (width : Nat) (name : String) : Option (Nat × Nat × Nat × Nat) :=
  if !pressable s name then none else
  ((boxes s width).find? (·.name == name)).map fun b => (b.x,b.y,b.w,b.h)

/-- The control under a point; none means the page. Close wins over its tab. -/
def hit (s : Shell) (width x y : Nat) : Option String :=
  if y >= height s width then none else
  -- A folded chrome has one control: a tap unfolds it, as on a phone.
  if s.collapse > 0 then some "expand" else
  match ((boxes s width).filter (·.contains x y)).getLast? with
  | some box => some box.name
  | none => some "chrome"

/-! ### The pointer -/

/-- The system pointer the window shows (issue 1268). -/
inductive Pointer where
  | arrow
  | hand
  | text
  deriving Repr, BEq

def Pointer.name : Pointer → String
  | .arrow => "arrow"
  | .hand => "hand"
  | .text => "text"

/-- The pointer over `control`, the answer of `hit`: the I-beam over the address bar,
the pointing hand over a control that acts on a click, else the arrow. A back or
forward button with no entry does nothing, so it gets the arrow. `none` is the page:
`onPage` says that a click there acts (a link, a graph node). -/
def pointer (s : Shell) (control : Option String) (onPage : Bool) : Pointer :=
  match control with
  | none => if onPage then .hand else .arrow
  | some "address" => .text
  | some "chrome" => .arrow
  | some "back" => if s.canBack then .hand else .arrow
  | some "forward" => if s.canForward then .hand else .arrow
  | some _ => .hand

/-! ### Drawing -/

private def paint (c : Rendering.Color) (x y w h : Nat) : Rendering.Node :=
  .paint {primitive := {geometry := .rect (Float.ofNat x) (Float.ofNat y) (Float.ofNat w) (Float.ofNat h),style := {fill := .solid c}}}

/-- NeXT bevel: light on the top and left, dark on the bottom and right. -/
private def bevel (s : Shell) (t : Theme) (face : Rendering.Color) (raised : Bool) (x y w h : Nat) : List Rendering.Node :=
  let u := unit s
  let (a,b) := if raised then (t.light,t.dark) else (t.dark,t.light)
  [paint face x y w h,paint a x y w u,paint a x y u h,paint b x (y+h-u) w u,paint b (x+w-u) y u h]

/-- Rows of a bitmap as runs, one rectangle for each run. -/
private def bitmapNodes (c : Rendering.Color) (rows : List Nat) (columns x y size : Nat) : List Rendering.Node := Id.run do
  let mut out : List Rendering.Node := []
  for (bits,row) in rows.zipIdx do
    let mut start : Option Nat := none
    for col in [:columns+1] do
      let on := col < columns && bits / (2^(columns-1-col)) % 2 == 1
      match start,on with
      | none,true => start := some col
      | some first,false =>
        out := paint c (x+first*size) (y+row*size) ((col-first)*size) size :: out
        start := none
      | _,_ => pure ()
  return out

private def glyphRows (c : Char) : List Nat :=
  let r := NativeFont.bitmap c
  [r.row0,r.row1,r.row2,r.row3,r.row4,r.row5,r.row6]

private def text (c : Rendering.Color) (value : String) (x y size : Nat) : List Rendering.Node :=
  value.toList.zipIdx.flatMap fun (ch,i) =>
    if ch == ' ' then [] else bitmapNodes c (glyphRows ch) 5 (x+i*6*size) y size

private def charWidth (s : Shell) : Nat := 6*dot s
private def fit (s : Shell) (value : String) (room : Nat) : String :=
  let limit := room/charWidth s
  if value.length <= limit then value
  else (String.ofList (value.toList.take (limit-min limit 2))) ++ ".."
/-- The end of a long address is the part that tells pages apart. -/
private def fitEnd (s : Shell) (value : String) (room : Nat) : String :=
  let limit := room/charWidth s
  if value.length <= limit then value
  else ".." ++ String.ofList (value.toList.drop (value.length-(limit-min limit 2)))

/-- 7 by 7 icons. -/
private def icon : String → List Nat
  | "back" => [0b0001000,0b0011000,0b0111111,0b1111111,0b0111111,0b0011000,0b0001000]
  | "forward" => [0b0001000,0b0001100,0b1111110,0b1111111,0b1111110,0b0001100,0b0001000]
  | "reload" => [0b0111101,0b1000011,0b1000111,0b1000000,0b1000001,0b1000001,0b0111110]
  | "stop" => [0b1000001,0b0100010,0b0010100,0b0001000,0b0010100,0b0100010,0b1000001]
  | "home" => [0b0001000,0b0011100,0b0111110,0b1111111,0b0100010,0b0101010,0b0101010]
  | "source" => [0b0000100,0b0100100,0b0101000,0b1001001,0b0101010,0b0110010,0b0010000]
  | "settings" => [0b0010100,0b1011101,0b0100010,0b1101011,0b0100010,0b1011101,0b0010100]
  | "newTab" => [0b0001000,0b0001000,0b0001000,0b1111111,0b0001000,0b0001000,0b0001000]
  | "close" => [0,0b0100010,0b0010100,0b0001000,0b0010100,0b0100010,0]
  | "coin" => [0b0011100,0b0100010,0b1011001,0b1011001,0b1011001,0b0100010,0b0011100]
  | _ => []

private def iconAt (s : Shell) (c : Rendering.Color) (name : String) (box : Box) : List Rendering.Node :=
  let size := dot s
  bitmapNodes c (icon name) 7 (box.x+(box.w-7*size)/2) (box.y+(box.h-7*size)/2) size

/-- The paint id of the bitmap of tab `index`: page images use small ids. -/
private def iconPaintId (index : Nat) : Nat := 1048576+index

/-- A tab icon in a square of `side` backing pixels at `x`, `y`: an SVG icon drawn by the
SVG engine at that size, a bitmap scaled to fit it. An icon that does not draw is left out. -/
def iconNodes (icon : TabIcon) (index x y side : Nat) : List Rendering.Node :=
  let at_ : Rendering.Transform := ⟨1,0,0,1,Float.ofNat x,Float.ofNat y⟩
  let clip : Rendering.ClipRect := ⟨0,0,Float.ofNat side,Float.ofNat side,Rendering.identity⟩
  if icon.kind == "svg" then
    match NativeSVG.parse icon.data side side with
    | .ok scene =>
      let m := scene.mapping
      let fit : Rendering.Transform := ⟨m.sx,0,0,m.sy,m.tx-m.minX*m.sx,m.ty-m.minY*m.sy⟩
      [.group none at_ [.clipped none fit clip (WebRenderSVG.fromScene scene).tree]]
    | .error _ => []
  else match NativeImage.base64 icon.data.toUTF8 0 with
    | .ok rgba =>
      if icon.width == 0 || icon.height == 0 || rgba.size != icon.width*icon.height*4 then [] else
      let large := Float.ofNat (max icon.width icon.height)
      let w := Float.ofNat side*Float.ofNat icon.width/large
      let h := Float.ofNat side*Float.ofNat icon.height/large
      let left := (Float.ofNat side-w)/2
      let top := (Float.ofNat side-h)/2
      let map : Rendering.Transform := ⟨Float.ofNat icon.width/w,0,0,Float.ofNat icon.height/h,0,0⟩
      let bitmap : Rendering.Bitmap := {width := icon.width,height := icon.height,rgba}
      [.group none ⟨1,0,0,1,Float.ofNat x+left,Float.ofNat y+top⟩
        [.paint ⟨none,{geometry := .rect 0 0 w h,style := {fill := .image ⟨map,iconPaintId index,bitmap⟩}}⟩]]
    | .error _ => []

private def tabNodes (s : Shell) (t : Theme) (width : Nat) (box : Box) (index : Nat) : List Rendering.Node :=
  let u := unit s
  let active := index == s.active
  let face := if active then t.base else t.back
  let title := ((s.tabs[index]?).map (·.title)).getD ""
  -- The icon, 16 points square, before the title (HTML §4.6.7.8).
  let icon := (s.tabs[index]?).bind (·.icon)
  let iconSide := 16*u
  let shift := if icon.isSome then iconSide+4*u else 0
  let iconPaint := match icon with
    | some i => iconNodes i index (box.x+7*u) (box.y+(box.h-min box.h iconSide)/2+u) iconSide
    | none => []
  -- Arcade capitals: the bitmap font is at its best here.
  let title := (if title.isEmpty then "new tab" else title).toUpper
  let room := box.w-(if s.tabs.size > 1 then 32*u else 14*u)-min (box.w/2) shift
  let colour := if active then t.ink else t.muted
  let mark := if active then [paint t.accent (box.x+u) (box.y+u) (box.w-2*u) (2*u)] else []
  let _ := width
  bevel s t face true box.x box.y box.w (box.h+(if active then u else 0)) ++ mark ++ iconPaint ++
    text colour (fit s title room) (box.x+7*u+shift) (box.y+(box.h-7*dot s)/2+u) (dot s)

private def addressNodes (s : Shell) (t : Theme) (box : Box) : List Rendering.Node :=
  let u := unit s
  let size := dot s
  let textX := box.x+22*u
  let textY := box.y+(box.h-7*size)/2
  let room := box.w-28*u
  let prompt := text t.accent ">" (box.x+8*u) textY size
  let shown := if s.focused then fitEnd s s.address room else fitEnd s s.address room
  -- The column of address position `i` in the shown text: the start of a long
  -- address is cut off, so the columns count from its end.
  let column := fun (i : Nat) => min shown.length (i+shown.length-s.address.length)
  let lo := column (min s.anchor s.cursor)
  let hi := column (max s.anchor s.cursor)
  let selecting := s.focused && hi > lo
  -- Selected text has its own colour on the selection colour; the text before and after it
  -- keeps the well's ink. Every letter stays in its column.
  let piece := fun (c : Rendering.Color) (a b : Nat) =>
    text c (String.ofList ((shown.toList.drop a).take (b-a))) (textX+a*charWidth s) textY size
  let body := if s.address.isEmpty && !s.focused
    then text t.dark (fit s "url, search or :command" room) textX textY size
    else if selecting then piece t.wellInk 0 lo ++ piece t.selectedInk lo hi ++ piece t.wellInk hi shown.length
    else text t.wellInk shown textX textY size
  let marked := if selecting
    then [paint t.selected (textX+lo*charWidth s-u) (textY-u) ((hi-lo)*charWidth s) (7*size+2*u)] else []
  -- As in a macOS text field, a selection hides the caret.
  let cursor := if s.focused && hi == lo then [paint t.accent (textX+column s.cursor*charWidth s) (textY-u) (5*size) (7*size+2*u)] else []
  bevel s t t.well false box.x box.y box.w box.h ++ prompt ++ marked ++ cursor ++ body

/-- The bar under the chrome: a thin accent line, or a level bar while loading. -/
private def edgeNodes (s : Shell) (t : Theme) (width : Nat) : List Rendering.Node := Id.run do
  let y := height s width-edge s
  if !s.loading then return [paint t.dark 0 y width (unit s),paint t.accent 0 (y+unit s) width (edge s-unit s)]
  let block := 12*unit s
  let mut out := [paint t.dark 0 y width (edge s)]
  for i in [:width/block] do
    if i % 2 == 0 then out := paint t.accent (i*block) y (block-2*unit s) (edge s) :: out
  return out

/-- The hint of a back or forward swipe (WebGesture): a dark tile with the back or forward
arrow, which comes in from its edge across the navigation row as the swipe goes on, and an
ink line along the chrome's edge from that side. At 100 the tile is the accent colour:
lifting the finger now goes. A folded chrome (`collapse` above 0) has room only for the line. -/
private def swipeNodes (s : Shell) (t : Theme) (width : Nat) : List Rendering.Node :=
  if s.swipe == 0 then [] else
  let u := unit s
  let size := 28*u
  let percent := min 100 s.swipe.natAbs
  let inset := min (width-min width size) (64*u*percent/100)
  let back := s.swipe < 0
  let x := if back then inset else width-size-inset
  let y := tabRow s width+(navRow s-size)/2
  let box : Box := {name := "swipe",x,y,w := size,h := size}
  let done := percent >= 100
  let lineY := height s width-edge s
  let fill := width*percent/100
  (if s.collapse == 0 then [paint (if done then t.accent else t.ink) x y size size] ++
    iconAt s (if done then t.ink else t.base) (if back then "back" else "forward") box else []) ++
    [paint t.ink (if back then 0 else width-fill) lineY fill (edge s)]

/-- The controls of the full chrome in theme `t`, with no edge. -/
private def controlNodes (s : Shell) (t : Theme) (width : Nat) : List Rendering.Node := Id.run do
  let u := unit s
  let row := tabRow s width
  let mut out := [paint t.back 0 0 width row,paint t.base 0 row width (navRow s)]
  out := out ++ [paint t.light 0 row width u]
  -- A pressed control (`s.pressed`) is sunken: dark face, light and dark edges swapped,
  -- and its icon one unit down and to the right.
  let down := fun (name : String) => s.pressed == name && pressable s name
  let face := fun (box : Box) => if down box.name then bevel s t t.back false box.x box.y box.w box.h
    else bevel s t t.base true box.x box.y box.w box.h
  let sink := fun (name : String) (box : Box) => if down name then {box with x := box.x+u,y := box.y+u} else box
  for box in boxes s width do
    match box.name.splitOn ":" with
    | ["tab",i] => out := out ++ tabNodes s t width box (i.toNat?.getD 0)
    | ["close",_] =>
      out := out ++ (if down box.name then bevel s t t.back false box.x box.y box.w box.h else []) ++
        iconAt s t.ink "close" (sink box.name box)
    | ["newTab"] => out := out ++ face box ++ iconAt s t.ink "newTab" (sink box.name box)
    | ["address"] => out := out ++ addressNodes s t box
    | ["copyAddress"] | ["pasteGo"] =>
      let size := menuSize s width
      let label := menuLabel box.name
      let at_ := sink box.name box
      -- Raised, with the accent line along its top, as the active tab.
      out := out ++ face box ++ [paint t.accent (at_.x+2*u) (at_.y+2*u) (at_.w-4*u) u] ++
        text t.ink label (at_.x+(at_.w-min at_.w (label.length*6*size-size))/2) (at_.y+(at_.h-7*size)/2+u) size
    | ["tabs"] =>
      let at_ := sink box.name box
      out := out ++ face box ++
        text t.ink (toString s.tabs.size) (at_.x+(at_.w-5*dot s)/2) (at_.y+(at_.h-7*dot s)/2) (dot s)
    | [name] =>
      let enabled := (name != "back" || s.canBack) && (name != "forward" || s.canForward)
      let shape := if name == "reload" && s.loading then "stop" else name
      out := out ++ face box ++
        iconAt s (if enabled then t.ink else t.dark) shape (sink box.name box)
    | _ => pure ()
  if !narrow s width then
    let label := toString s.pages
    let x := width-(label.length*charWidth s)-16*u
    let y := (row-7*dot s)/2+u
    out := out ++ bitmapNodes t.coin (icon "coin") 7 (x-10*dot s) y (dot s) ++ text t.coin label x y (dot s)
  return out

/-- Colour `c` faded `p` percent of the way to `to`: the chrome has no alpha, and over
its own opaque face this is the same as `c` at opacity `1-p`. -/
private def mix (c to : Rendering.Color) (p : Nat) : Rendering.Color :=
  let f := Float.ofNat (min 100 p)/100
  ⟨c.r+(to.r-c.r)*f,c.g+(to.g-c.g)*f,c.b+(to.b-c.b)*f⟩
/-- The theme with every colour faded `p` percent into the chrome's face. -/
private def fade (t : Theme) (p : Nat) : Theme :=
  let m := fun c => mix c t.base p
  ⟨t.base,m t.light,m t.dark,m t.ink,m t.well,m t.wellInk,m t.back,m t.muted,m t.accent,m t.coin,m t.selected,m t.selectedInk⟩

/-- The site part of an address: the host of `scheme://host/...`; other addresses
(`foafnaut:graph`) whole. -/
def domainOf (address : String) : String :=
  match address.splitOn "://" with
  | [_,rest] =>
    let host := (rest.splitOn "/").headD rest
    let host := (host.splitOn "?").headD host
    let host := (host.splitOn "#").headD host
    -- No user part: what follows the last `@`.
    (host.splitOn "@").getLastD host
  | _ => address

/-- The domain as the chrome folds: from where the address text starts in the bar, at
the bar's lettering size, to the middle of the strip in small lettering; it fades in. -/
private def domainNodes (s : Shell) (t : Theme) (width : Nat) (p : Nat) : List Rendering.Node :=
  let u := unit s
  let shown := domainOf s.address
  let size := lerp (dot s) (smallDot s) p
  let label := fit s shown (width-16*u)
  let wide := label.length*6*size
  let bar := ((boxes {s with collapse := 0} width).find? (·.name == "address")).getD ⟨"address",0,0,width,28*u⟩
  let x0 := bar.x+22*u
  -- The bar's text slides up with the bar (`nodes`); the domain leaves it and comes to rest.
  let y0 := bar.y+(bar.h-7*dot s)/2-(fullHeight s width-height s width)
  let x1 := (width-min width wide)/2
  let y1 := (stripHeight s-edge s-7*smallDot s)/2
  -- It shows only in the second half of the fold, after the controls have faded out, so
  -- the two texts never lie over each other half drawn.
  text (mix t.base t.ink (2*p-100)) label (lerp x0 x1 p) (lerp y0 y1 p) size

/-- The chrome as scene nodes. It is drawn over the page. With `collapse` above 0 it is
folding: the controls slide up and fade into the chrome's face over the first half of the
fold, the chrome is shorter (`height`), and the domain shrinks to the middle of the strip
and fades in over the second half. -/
def nodes (s : Shell) (width : Nat) : List Rendering.Node :=
  let t := themeOf s
  if s.collapse == 0 then controlNodes s t width ++ edgeNodes s t width ++ swipeNodes s t width else
  let p := min 100 s.collapse
  let lift := fullHeight s width-height s width
  let slide : Rendering.Transform := ⟨1,0,0,1,0,-(Float.ofNat lift)⟩
  [paint t.base 0 0 width (height s width),.group none slide (controlNodes {s with collapse := 0} (fade t (2*p)) width)] ++
    domainNodes s t width p ++ edgeNodes s t width ++ swipeNodes s t width

/-- The page's part of the window: rows from the chrome's bottom to the window's. -/
def pageClip (s : Shell) (width height' : Nat) : Rendering.ClipRect :=
  ⟨0,Float.ofNat (height s width),Float.ofNat width,Float.ofNat height'-Float.ofNat (height s width),Rendering.identity⟩

/-- Put a page rendered below the chrome and the chrome into one scene. The page is clipped to its part of the window
(`pageClip`), so no page ink reaches the chrome (`compose_page_clipped`). -/
def compose (s : Shell) (page : Rendering.Scene) (width height' : Nat) : Rendering.Scene :=
  let top := Float.ofNat (height s width)-Float.ofNat s.scroll
  let shift : Rendering.Transform := ⟨1,0,0,1,0,top⟩
  {page with
    height := height'
    mapping := {page.mapping with viewportHeight := Float.ofNat height'}
    tree := [.clipped none Rendering.identity (pageClip s width height') [.group none shift page.tree]] ++ nodes s width
    links := Rendering.moveLinks (· + top) page.links}

/-- Security: every primitive of the page in a composed frame carries the page's part
of the window as a clip, so its ink can not paint the chrome. -/
theorem compose_page_clipped (s : Shell) (page : Rendering.Scene) (width height' : Nat)
    (parent : Rendering.Transform) (groups : List (Option String)) (item : Rendering.PaintItem)
    (node : Rendering.Node) (head : (compose s page width height').tree.head? = some node)
    (h : item ∈ node.lower parent groups) :
    (pageClip s width height').lowerUnder parent ∈ item.primitive.clips := by
  have e : node = .clipped none Rendering.identity (pageClip s width height')
      [.group none ⟨1,0,0,1,0,Float.ofNat (height s width)-Float.ofNat s.scroll⟩ page.tree] := by
    simp only [compose, List.cons_append, List.head?_cons, Option.some.injEq] at head
    exact head.symm
  subst e
  exact Rendering.lower_clipped _ _ _ _ _ _ _ h

/-- The page under the chrome keeps every link of the page, moved down by the chrome less
the scroll and nothing else (`LinkTheorems.moveLinks_getElem`; issue 1268). -/
theorem compose_links (s : Shell) (page : Rendering.Scene) (width height' : Nat) :
    (compose s page width height').links =
      Rendering.moveLinks (· + (Float.ofNat (height s width)-Float.ofNat s.scroll)) page.links := rfl

/-! ### Editing the address -/

/-- The longest address the bar takes. -/
def maxAddress : Nat := 2048

/-- The start and the end of the selection. -/
def Shell.lo (s : Shell) : Nat := min s.anchor s.cursor
def Shell.hi (s : Shell) : Nat := max s.anchor s.cursor
def Shell.selected (s : Shell) : String :=
  String.ofList ((s.address.toList.take s.hi).drop s.lo)

private def snapshot (s : Shell) : Snapshot := ⟨s.address,s.cursor,s.anchor⟩
private def restore (s : Shell) (v : Snapshot) : Shell :=
  {s with address := v.address,cursor := min v.cursor v.address.length,anchor := min v.anchor v.address.length}

/-- Put the cursor at `i`. With `extend` the anchor stays, so the selection grows or shrinks. -/
private def moveTo (s : Shell) (i : Nat) (extend : Bool) : Shell :=
  let i := min i s.address.length
  {s with cursor := i,anchor := if extend then s.anchor else i,typing := false}

/-- The text from `lo` to `hi` becomes `text`. The state before is the undo step,
except that typing after typing stays in one step. -/
private def replaceRange (s : Shell) (lo hi : Nat) (text : String) (typing : Bool) : Shell :=
  let chars := s.address.toList
  let next := String.ofList (chars.take lo) ++ text ++ String.ofList (chars.drop hi)
  if next.length > maxAddress || next == s.address then s else
  let undo := if typing && s.typing then s.undo else some (snapshot s)
  {s with address := next,cursor := lo+text.length,anchor := lo+text.length,undo,redo := none,typing}

/-- Only printable characters go into the address; a line break and the white space
around it go away, so a pasted address that wraps reads as one line. -/
def clean (value : String) : String :=
  let lines := (value.splitOn "\n").flatMap (·.splitOn "\r")
  let joined := if lines.length > 1
    then (String.join (lines.map (fun line => line.trimAscii.toString))).trimAscii.toString else value
  String.ofList (joined.toList.filter (fun c => c.toNat >= 32 && c.toNat != 127))

/-- Typed text replaces the selection, as in any text field. -/
def Shell.typed (s : Shell) (value : String) : Shell :=
  let text := clean value
  if text.isEmpty then s else {replaceRange s s.lo s.hi text true with menu := false}

private def wordChar (c : Char) : Bool := c.isAlphanum || c.toNat > 127
/-- Option-Left: past the separators before `i`, then past the word. -/
def wordStart (value : String) (i : Nat) : Nat :=
  let before := (value.toList.take i).reverse
  let gap := (before.takeWhile (!wordChar ·)).length
  let word := ((before.drop gap).takeWhile wordChar).length
  i-gap-word
/-- Option-Right: past the separators after `i`, then past the word. -/
def wordEnd (value : String) (i : Nat) : Nat :=
  let after := value.toList.drop i
  let gap := (after.takeWhile (!wordChar ·)).length
  let word := ((after.drop gap).takeWhile wordChar).length
  min value.length (i+gap+word)

/-- Modifier bits of a key event: 1 Shift, 2 Command, 4 Option, 8 Control. -/
def shiftBit : Nat := 1
def commandBit : Nat := 2
def optionBit : Nat := 4
private def has (modifiers bit : Nat) : Bool := modifiers / bit % 2 == 1

/-- macOS key codes that edit: delete, forward delete, left, right, up, down, home,
end. Shift extends the selection; Option moves or deletes by word; Command moves to
the end of the line. With a selection, delete removes it, and left or right with no
Shift goes to its start or end. -/
def Shell.key (s : Shell) (code : Nat) (modifiers : Nat := 0) : Shell :=
  -- A key closes the address menu, as typing does.
  let s := {s with menu := false}
  let extend := has modifiers shiftBit
  let word := has modifiers optionBit
  let line := has modifiers commandBit
  let size := s.address.length
  match code with
  | 51 =>
    if s.lo < s.hi then replaceRange s s.lo s.hi "" false
    else if s.cursor == 0 then s
    else replaceRange s (if line then 0 else if word then wordStart s.address s.cursor else s.cursor-1) s.cursor "" false
  | 117 =>
    if s.lo < s.hi then replaceRange s s.lo s.hi "" false
    else if s.cursor >= size then s
    else replaceRange s s.cursor (if line then size else if word then wordEnd s.address s.cursor else s.cursor+1) "" false
  | 123 =>
    if !extend && s.lo < s.hi && !word && !line then moveTo s s.lo false
    else moveTo s (if line then 0 else if word then wordStart s.address s.cursor else s.cursor-1) extend
  | 124 =>
    if !extend && s.lo < s.hi && !word && !line then moveTo s s.hi false
    else moveTo s (if line then size else if word then wordEnd s.address s.cursor else s.cursor+1) extend
  | 115 | 126 => moveTo s 0 extend
  | 119 | 125 => moveTo s size extend
  | _ => s

/-- `edit` for every action but `menu`, before it closes the menu. -/
def Shell.editStep (s : Shell) (action : String) (text : String) : Shell × Option String :=
  match action with
  | "focus" =>
    let value := String.ofList (text.toList.take maxAddress)
    ({s with address := value,cursor := value.length,anchor := 0,undo := none,redo := none,typing := false,focused := true},none)
  | "pasteGo" =>
    let value := String.ofList ((clean text).trimAscii.toString.toList.take maxAddress)
    if value.isEmpty then (s,none) else
    ({s with address := value,cursor := value.length,anchor := value.length,undo := some (snapshot s),redo := none,typing := false},some value)
  | "selectAll" => ({s with anchor := 0,cursor := s.address.length,typing := false},none)
  | "copy" => (s,if s.lo < s.hi then some s.selected else none)
  | "cut" => if s.lo < s.hi then (replaceRange s s.lo s.hi "" false,some s.selected) else (s,none)
  | "paste" => let value := clean text; (if value.isEmpty then s else replaceRange s s.lo s.hi value false,none)
  | "undo" => match s.undo with
    | some v => ({restore s v with undo := none,redo := some (snapshot s),typing := false},none)
    | none => (s,none)
  | "redo" => match s.redo with
    | some v => ({restore s v with redo := none,undo := some (snapshot s),typing := false},none)
    | none => (s,none)
  | _ => (s,none)

/-- An edit command from the menu or a key, and the text it puts on the clipboard. Every
edit but `menu` closes the address menu. `menu` opens it on a focused bar; `closeMenu`
closes it. `pasteGo` puts the clipboard `text` in the bar, cleaned as a paste is, and
answers the address to go to (`none` for a clipboard with no text). -/
def Shell.edit (s : Shell) (action : String) (text : String := "") : Shell × Option String :=
  if action == "menu" then ({s with menu := s.focused},none) else
  let step := s.editStep action text
  ({step.1 with menu := false},step.2)

/-- The address menu opens only on a focused bar, and any other edit closes it. -/
theorem edit_menu (s : Shell) : (s.edit "menu").1.menu = s.focused := by
  simp [Shell.edit]

theorem edit_closes (s : Shell) (action text : String) (h : action ≠ "menu") :
    (s.edit action text).1.menu = false := by
  simp [Shell.edit, h]

/-- What the host does for one button of the address menu: `action` is "copy" or "paste",
`rect` the button in window CSS pixels `(x,y,w,h)` (backing pixels over `scale`, rounded
out), and `text` for "copy" the address to write. A web host runs the action inside the
tap that lifts on the rectangle, since the clipboard wants a user gesture. -/
structure MenuAction where
  action : String
  control : String
  rect : Nat × Nat × Nat × Nat
  text : Option String := none
  deriving Repr, BEq

/-- The address the menu copies: the whole text of the bar, as Lean cleans a paste. -/
def copyText (s : Shell) : String := clean s.address

/-- The action table of the shown menu, for `width` backing pixels; empty with the menu
closed or the chrome folded. -/
def menuActions (s : Shell) (width : Nat) : List MenuAction :=
  if !menuShown s then [] else
  let u := unit s
  let css := fun (b : Box) => (b.x/u,b.y/u,(b.x+b.w+u-1)/u-b.x/u,(b.y+b.h+u-1)/u-b.y/u)
  (boxes s width).filterMap fun b =>
    if b.name == "copyAddress" then some {action := "copy",control := b.name,rect := css b,text := some (copyText s)}
    else if b.name == "pasteGo" then some {action := "paste",control := b.name,rect := css b}
    else none

/-- A closed menu gives the host no actions: a tap can not copy or paste. -/
theorem menuActions_closed (s : Shell) (width : Nat) (h : s.menu = false) : menuActions s width = [] := by
  simp [menuActions, menuShown, h]

def MenuAction.json (a : MenuAction) : JSON.Json :=
  let n := fun (v : Nat) => JSON.Json.number (toString v)
  .object ([("action",.string a.action),("control",.string a.control),
    ("rect",.array [n a.rect.1,n a.rect.2.1,n a.rect.2.2.1,n a.rect.2.2.2])] ++
    (match a.text with | some t => [("text",.string t)] | none => []))

/-- The menu commands that act on the address bar when it has the focus. -/
def addressCommands : List String := ["copy","selectAll","cut","paste","undo","redo"]

/-! ### What an address and a link mean -/

/-- Pages this engine can not draw yet go to the host's default browser (WebRoute). -/
def externalHosts := WebRoute.externalHosts

private def hostOf (url : String) : String :=
  match url.splitOn "://" with
  | [_,rest] => ((rest.splitOn "/").headD "").toLower
  | _ => ""

inductive Go where
  | page (url : String)
  | system (url : String)
  | command (name : String) (argument : String)
  deriving Repr, BEq

/-- The FOAF graph is a page of the browser, so it goes into the session history of the
tab it opens in, and back leaves it (issue 1268). The host draws this URL with the graph app. -/
def graphURL : String := "foafnaut:graph"

/-- A browser command. `graph` is the graph page, not a command. -/
def command (name argument : String) : Go :=
  if name == "graph" && argument.isEmpty then .page graphURL else .command name argument

def link (href : String) : Go :=
  if href.startsWith "foafnaut:" then
    match ((href.drop 9).toString.splitOn "/") with
    | [name,argument] => command name argument
    | [name] => command name ""
    | _ => .command "help" ""
  else if externalHosts.contains (hostOf href) then .system href
  else .page href

private def encodeQuery (value : String) : String :=
  String.join (value.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '_' || c == '.' then c.toString
    else if c == ' ' then "+"
    else
      let digit := fun (n : Nat) => "0123456789ABCDEF".toList[n]!
      String.ofList ['%',digit (b.toNat/16),digit (b.toNat%16)])

/-- The bar reads a `:command`, a URL, or a search. -/
def submit (input : String) : Go :=
  let value := input.trimAscii.toString
  if value.startsWith ":" then
    match ((value.drop 1).toString.splitOn " ").filter (· != "") with
    -- `:sparql QUERY` keeps the whole rest of the line, encoded (WebSparql).
    | "sparql" :: _ :: _ =>
      command "sparql" ("q=" ++ encodeQuery ((((value.drop 1).toString.trimAscii.toString.drop 6).toString).trimAscii.toString))
    | [name] => command name ""
    | ["open",url] => .system url
    | name::argument::_ => command name argument
    | [] => .command "help" ""
  else if (value.splitOn "://").length > 1 || value.startsWith "file:" || value.startsWith "about:" then link value
  else if !value.contains ' ' && value.contains '.' then link ("https://" ++ value)
  else .system ("https://duckduckgo.com/?q=" ++ encodeQuery value)

/-- Where an address typed in the bar goes (WebRoute): a URL as a link would, a
`:command` as `foafnaut:command/argument`, and a search or `:open URL` to the system. -/
def routeAddress (site : WebRoute.Site) (base input : String) : WebRoute.Route :=
  let value := input.trimAscii.toString
  if (value.toList.take 9).map Char.toLower == WebRoute.foafnautPrefix then WebRoute.route site base value else
  match submit value with
  | .page url => WebRoute.route site base url
  | .command name argument => WebRoute.commandRoute site name argument
  | .system url => match WebRoute.route site base url with
    | .navigate address => .system address
    | other => other

/-- The answer of the op `shellRoute` (docs/web/hub/foafnaut/link-route.mjs). -/
def routeJson : WebRoute.Route → JSON.Json
  | .page name url => .object [("route",.string "page"),("name",.string name),("url",.string url)]
  | .graph => .object [("route",.string "graph"),("url",.string WebRoute.graphURL)]
  | .navigate url => .object [("route",.string "navigate"),("url",.string url)]
  | .system url => .object [("route",.string "system"),("url",.string url)]
  | .command name argument => .object [("route",.string "command"),("name",.string name),("argument",.string argument)]
  | .refuse url reason => .object [("route",.string "refuse"),("url",.string url),("reason",.string reason)]

def Go.json : Go → JSON.Json
  | .page url => .object [("go",.string "page"),("url",.string url)]
  | .system url => .object [("go",.string "system"),("url",.string url)]
  | .command name argument => .object [("go",.string "command"),("name",.string name),("argument",.string argument)]

/-! ### View source -/

/-- Characters shown of one source: the page limit is 49152 paint items. -/
def sourceLimit : Nat := 8000

private def escapeText (value : String) : String :=
  String.join (value.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c.toNat < 32 || c.toNat > 126 then "?" else c.toString)

/-- Spaces at the start of a line become padding, so indentation survives. -/
private def sourceLine (line : String) : String :=
  let chars := line.toList.map (fun c => if c == '\t' then ' ' else c)
  let indent := (chars.takeWhile (· == ' ')).length
  let body := String.ofList (chars.drop indent)
  if body.isEmpty then "<p style=\"height:16px\"></p>" else
  s!"<p style=\"padding-left:{indent*6}px\">{escapeText body}</p>"

/-- A page that shows a source as text. The kind says what the source is. -/
def sourcePage (kind url source : String) : String :=
  let shown := String.ofList (source.toList.take sourceLimit)
  let cut := if source.length > sourceLimit
    then s!"<h2>Shown: the first {sourceLimit} of {source.length} characters</h2>" else ""
  let name := ((url.splitOn "/").getLast?).getD url
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>" ++ escapeText (kind ++ ": " ++ name) ++
  "</title><style>body{margin:12px;font-size:12px;line-height:16px;color:#203040;background:#f4f4ee}" ++
  "h1{margin:0;padding-bottom:8px;font-size:14px;line-height:20px;color:#a0186a}h2{margin:0;padding-bottom:8px;font-size:12px;color:#a0186a}p{margin:0}</style></head><body><h1>" ++
  escapeText (kind ++ " of " ++ url) ++ "</h1>" ++ cut ++
  String.join ((shown.splitOn "\n").map sourceLine) ++ "</body></html>"

/-! ### The value the host keeps -/

private def str (j : JSON.Json) (key : String) (fallback := "") : String :=
  match j.field? key with | some (.string value) => value | _ => fallback
private def nat (j : JSON.Json) (key : String) (fallback := 0) : Nat :=
  match j.field? key with | some (.number value) => value.toNat?.getD fallback | _ => fallback
private def flag (j : JSON.Json) (key : String) : Bool :=
  match j.field? key with | some (.bool value) => value | _ => false

/-- The icon of a tab in the JSON of the shell: `WebDocument.iconPrepare`'s answer. -/
private def tabIcon (item : JSON.Json) : Option TabIcon :=
  match item.field? "icon" with
  | some i@(.object _) =>
    let kind := str i "kind"
    let data := if kind == "svg" then str i "source" else str i "rgba"
    some ⟨kind,nat i "width",nat i "height",data⟩
  | _ => none

def Shell.ofJson (j : JSON.Json) : Shell :=
  let tabs : Array Tab := match j.field? "tabs" with
    | some (.array items) => (items.map (fun item => ({title := str item "title",icon := tabIcon item} : Tab))).toArray
    | _ => #[{}]
  let tabs := if tabs.isEmpty then #[{}] else tabs
  let address := str j "address"
  let cursor := min (nat j "cursor") address.length
  let step := fun (key : String) => match j.field? key with
    | some v@(.object _) => some (⟨str v "address",nat v "cursor",nat v "anchor"⟩ : Snapshot)
    | _ => none
  { tabs,active := min (nat j "active") (tabs.size-1),address,cursor,
    -- No anchor is no selection.
    anchor := min (nat j "anchor" cursor) address.length,undo := step "undo",redo := step "redo",typing := flag j "typing",
    focused := flag j "focused",canBack := flag j "canBack",canForward := flag j "canForward",
    loading := flag j "loading",scale := max 1 (nat j "scale" 1),theme := str j "theme" "next",pages := nat j "pages",
    scroll := nat j "scroll", pressed := str j "pressed",
    collapse := min 100 (nat j "collapse"), collapsible := flag j "collapsible",
    swipe := match j.field? "swipe" with
      | some (.number value) => max (-100) (min 100 (value.toInt?.getD 0)) | _ => 0,
    menu := flag j "menu" }

private def Snapshot.json (v : Snapshot) : JSON.Json :=
  .object [("address",.string v.address),("cursor",.number (toString v.cursor)),("anchor",.number (toString v.anchor))]

/-- The edit state the host keeps and sends back in `shell`. -/
def Shell.editJson (s : Shell) : JSON.Json :=
  .object [("address",.string s.address),("cursor",.number (toString s.cursor)),("anchor",.number (toString s.anchor)),
    ("undo",(s.undo.map Snapshot.json).getD .null),("redo",(s.redo.map Snapshot.json).getD .null),("typing",.bool s.typing),
    ("menu",.bool s.menu)]

#guard submit "http://example.org/" == .page "http://example.org/"
#guard submit "example.org" == .page "https://example.org"
#guard submit "github.com/danbri" == .system "https://github.com/danbri"
#guard submit "lean browser" == .system "https://duckduckgo.com/?q=lean+browser"
#guard submit ":zoom 150" == .command "zoom" "150"
#guard submit ":source" == .command "source" ""
#guard submit ":sparql SELECT ?s WHERE { ?s a <x:y> }" == .command "sparql" "q=SELECT+%3Fs+WHERE+%7B+%3Fs+a+%3Cx%3Ay%3E+%7D"
#guard link "foafnaut:sparql/q=ASK+%7B%7D" == .command "sparql" "q=ASK+%7B%7D"
#guard (sourcePage "Source" "file:///a.html" "<p>\n  x</p>").contains '&'
#guard ((sourcePage "Source" "a" (String.ofList (List.replicate 8001 'x'))).splitOn "first 8000").length == 2
#guard submit ":open https://x.org" == .system "https://x.org"
#guard link "https://github.com/danbri/factoidal-core" == .system "https://github.com/danbri/factoidal-core"
#guard link "foafnaut:theme/arcade" == .command "theme" "arcade"
#guard link "status.html" == .page "status.html"
-- The graph is a page: a link or `:graph` loads it in the tab and pushes it on the history.
#guard link "foafnaut:graph" == .page graphURL && submit ":graph" == .page graphURL
#guard link "foafnaut:settings" == .command "settings" ""
-- The address bar routes as a link does (WebRoute).
private def hubSite : WebRoute.Site := {origin := "https://x.org",pages := "https://x.org/p/"}
#guard routeAddress hubSite "https://x.org/p/index.html" ":graph" == .graph
#guard routeAddress hubSite "https://x.org/p/index.html" "foafnaut:graph" == .graph
#guard routeAddress hubSite "https://x.org/p/index.html" ":settings" == .page "settings" "https://x.org/p/settings.html"
#guard routeAddress hubSite "https://x.org/p/index.html" ":zoom 150" == .command "zoom" "150"
#guard routeAddress hubSite "https://x.org/p/index.html" "x.org/p/a.html" == .navigate "https://x.org/p/a.html"
#guard routeAddress hubSite "https://x.org/p/index.html" "lean browser" == .system "https://duckduckgo.com/?q=lean+browser"
#guard routeAddress hubSite "https://x.org/p/index.html" ":open https://x.org/a" == .system "https://x.org/a"
#guard routeAddress hubSite "https://x.org/p/index.html" ":open foafnaut:graph" == .graph
-- A struct literal sets the anchor too: `anchor := 0` would select from the start.
#guard (({address := "ac",cursor := 1,anchor := 1} : Shell).typed "b").address == "abc"
#guard (({address := "abc",cursor := 3,anchor := 3} : Shell).key 51).address == "ab"
#guard (({address := "abc",cursor := 0} : Shell).key 123).cursor == 0
#guard pointer {} none true == .hand && pointer {} none false == .arrow
#guard pointer {} (hit {} 1000 10 40) false == .arrow && pointer {canBack := true} (hit {} 1000 10 40) false == .hand
#guard pointer {} (some "address") true == .text && pointer {} (some "chrome") true == .arrow
#guard pointer {} (some "settings") false == .hand && pointer {tabs := #[{},{}]} (hit {tabs := #[{},{}]} 1000 40 12) false == .hand
-- Address editing (issue 1268): a new window or tab selects the whole address, and typing replaces it.
private def opened : Shell := (({} : Shell).edit "focus" "https://example.org/a").1
#guard opened.selected == "https://example.org/a" && opened.focused
#guard (opened.typed "w").address == "w" && (opened.typed "w").cursor == 1
#guard (opened.key 51).address == "" && ((opened.key 51).edit "undo").1.address == "https://example.org/a"
-- Selected address text (issue 1268): white letters on the selection blue, and no caret.
-- With the caret only, no paint has the selection colour.
private def sameColor (a b : Rendering.Color) : Bool := a.r == b.r && a.g == b.g && a.b == b.b
private def paintsOf (c : Rendering.Color) (nodes : List Rendering.Node) : Nat :=
  nodes.foldl (fun n node => match node with
    | .paint p => match p.primitive.style.fill with
      | .solid k => if sameColor k c then n+1 else n
      | _ => n
    | _ => n) 0
private def caretOnly : Shell := {opened with anchor := opened.cursor}
#guard paintsOf selectionBackground (nodes opened 1000) == 1 && paintsOf selectionBackground (nodes caretOnly 1000) == 0
-- The letters of the selected address are drawn in the selection text colour: more white
-- paints than with the same address unselected, and the same number of paints of text in all.
#guard paintsOf selectionText (nodes opened 1000) > paintsOf selectionText (nodes caretOnly 1000)
#guard paintsOf selectionBackground (nodes {opened with theme := "arcade"} 1000) == 0
-- Command-A, Command-C, Command-X, Command-V, Command-Z and Shift-Command-Z.
private def typedAb : Shell := ((({} : Shell).edit "focus" "").1.typed "a").typed "b"
#guard typedAb.address == "ab" && (typedAb.edit "copy").2 == none
#guard ((typedAb.edit "selectAll").1.edit "copy").2 == some "ab"
#guard ((typedAb.edit "selectAll").1.edit "cut").2 == some "ab" && ((typedAb.edit "selectAll").1.edit "cut").1.address == ""
#guard ((((typedAb.edit "selectAll").1.edit "cut").1.edit "undo").1).address == "ab"
#guard ((((((typedAb.edit "selectAll").1.edit "cut").1.edit "undo").1.edit "redo").1)).address == ""
#guard ((typedAb.key 123).edit "paste" "X\n  y").1.address == "aXyb"
#guard (((typedAb.key 123).edit "paste" "X").1.edit "undo").1.address == "ab"
-- Typing is one undo step; `undo` with no step changes nothing.
#guard (typedAb.edit "undo").1.address == "" && ((typedAb.edit "undo").1.edit "undo").1.address == ""
-- A space typed alone stays: a search has spaces.
#guard (typedAb.typed " ").address == "ab "
-- Shift extends the selection; left with a selection goes to its start.
#guard ((typedAb.key 123 shiftBit).key 123 shiftBit).selected == "ab"
#guard (((typedAb.key 123 shiftBit).key 123 shiftBit).key 123).cursor == 0
#guard ((typedAb.key 115 shiftBit).typed "z").address == "z"
-- Option moves and deletes by word; Command goes to the end of the line.
private def deep : Shell := (({} : Shell).edit "focus" "http://x.org/one/two").1.key 124
#guard wordStart "http://x.org/one/two" 20 == 17 && wordEnd "http://x.org/one/two" 0 == 4
#guard (deep.key 123 optionBit).cursor == 17 && (deep.key 51 optionBit).address == "http://x.org/one/"
#guard (deep.key 123 commandBit).cursor == 0 && ((deep.key 123 commandBit).key 124 (commandBit+shiftBit)).selected == "http://x.org/one/two"
#guard (Shell.ofJson (opened.editJson)).anchor == 0 && (Shell.ofJson (((opened.typed "x").edit "undo").1.editJson)).redo.isSome
#guard (Shell.ofJson (JSON.Json.object [("address",.string "abc"),("cursor",.number "2")])).lo == 2
#guard hit {} 1000 10 1000 == none
#guard hit {} 1000 10 40 == some "back"
#guard hit {} 300 10 10 == some "back"
#guard hit {tabs := #[{},{}]} 1000 40 12 == some "tab:0"
#guard height {} 1000 > height {} 300
#guard pressBox {} 1000 "back" == none
#guard pressBox {canBack := true} 1000 "back" == some (4,30,28,28)
#guard pressBox {} 1000 "reload" == some (64,30,28,28)
#guard pressBox {} 1000 "address" == none
-- A pressed button draws other paint than a raised one; another name changes nothing.
#guard reprStr (nodes {pressed := "reload"} 1000) != reprStr (nodes {} 1000)
#guard reprStr (nodes {pressed := "address"} 1000) == reprStr (nodes {} 1000)
#guard reprStr (nodes {pressed := "back"} 1000) == reprStr (nodes {} 1000)
#guard (Shell.ofJson (.object [("pressed",.string "home")])).pressed == "home"
-- The folding chrome (owner, 2026-11-08): classic at 0, the strip at 100, a tap on it unfolds.
#guard height {} 400 == fullHeight {} 400 && height {collapse := 100} 400 == stripHeight {}
#guard height {collapse := 50} 400 < height {} 400 && height {collapse := 50} 400 > height {collapse := 100} 400
#guard hit {collapse := 100} 400 10 5 == some "expand" && hit {collapse := 100} 400 10 (stripHeight {}) == none
#guard reprStr (nodes {collapse := 0} 1000) == reprStr (nodes {} 1000)
#guard reprStr (nodes {collapse := 40,address := "https://x.org/a"} 1000) != reprStr (nodes {address := "https://x.org/a"} 1000)
#guard domainOf "https://danbri.github.io/factoidal/web/hub/" == "danbri.github.io" && domainOf "foafnaut:graph" == "foafnaut:graph"
#guard domainOf "http://u@x.org:8080?q#f" == "x.org:8080"
#guard (Shell.ofJson (.object [("collapse",.number "250"),("collapsible",.bool true)])).collapse == 100
-- A swipe's hint (WebGesture): kept from the host's shell, drawn only while it is not 0.
#guard (Shell.ofJson (.object [("swipe",.number "-60")])).swipe == -60 && (Shell.ofJson (.object [("swipe",.number "900")])).swipe == 100
#guard (nodes {swipe := -60} 800).length > (nodes {} 800).length && (nodes {swipe := 0} 800).length == (nodes {} 800).length
-- The address menu: a finger's tap, a long press or a right click on the bar opens it; a click does not.
#guard opensMenu (some "address") "tap" true && opensMenu (some "address") "hold" false && opensMenu (some "address") "context" false
#guard !opensMenu (some "address") "tap" false && !opensMenu (some "reload") "hold" true && !opensMenu none "context" true
private def menuOpen : Shell := (opened.edit "menu").1
#guard menuOpen.menu && !(({} : Shell).edit "menu").1.menu
-- A phone, 390 CSS px at 3x: both buttons in the navigation row, right of a shorter bar.
private def phone : Shell := {menuOpen with scale := 3}
#guard hit phone 1170 1100 60 == some "pasteGo" && hit phone 1170 700 60 == some "copyAddress"
#guard hit phone 1170 60 60 == some "address" && hit {phone with menu := false} 1170 1100 60 == some "settings"
#guard (menuActions phone 1170).map (·.action) == ["copy","paste"]
#guard (menuActions phone 1170).head?.bind (·.text) == some "https://example.org/a"
#guard (menuActions phone 1170).all fun a => a.rect.1+a.rect.2.2.1 ≤ 390 && a.rect.2.1+a.rect.2.2.2 ≤ fullHeight phone 1170/3
#guard menuActions {phone with menu := false} 1170 == [] && menuActions {phone with collapse := 50} 1170 == []
-- A desktop window keeps back, forward, reload and home; the menu replaces source and settings.
#guard hit menuOpen 1000 10 40 == some "back" && (menuActions menuOpen 1000).length == 2
#guard reprStr (nodes menuOpen 1000) != reprStr (nodes opened 1000)
-- Typing, a key and any other edit close the menu; Paste and go answers the cleaned address.
#guard !(menuOpen.typed "x").menu && !(menuOpen.key 123).menu && !(menuOpen.edit "selectAll").1.menu
#guard (menuOpen.edit "pasteGo" "  example.org/b\n").2 == some "example.org/b" && (menuOpen.edit "pasteGo" "\n").2 == none
#guard (Shell.ofJson menuOpen.editJson).menu && pressable menuOpen "pasteGo" && !pressable opened "pasteGo"

end WebShell
