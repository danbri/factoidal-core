import L4Factoidal.Rendering.ClipTheorems
import WebRender
import WebRoute
import WebSelection
import L4Factoidal.Rendering.Smil
import L4Factoidal.HTML.AccessibleTree

/-! The browser's own face: tabs, the address bar and its buttons, drawn into the
same scene as the page, so one WebGPU pass draws the window. The default look is flat
(owner, 2026-11-16: the old toolbar looked "like 1993"): light or dark faces, a rounded
address field with a focus ring, and line icons drawn as vector strokes. The older looks stay
as themes: "classic" (NeXT bevels) and "arcade". The default address field uses the host's held monospace face when available.

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
  /-- Which engine runs this page's scripts ("JS BUBBLEPOP", "JS QUICKJS-NG", "JS OFF"), or "". -/
  script : String := ""
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
  /-- The context menu of a press on the page (issue 1031; `openContext`): "" closed, "link"
  for a press on a link, "page" for a press elsewhere on the page. Its items are in the
  navigation row, where the address menu's are (`contextItems`). Any edit, key or typed text
  closes it, as it closes the address menu. -/
  context : String := ""
  /-- The address of the link the context menu is for ("" for the page menu). -/
  contextLink : String := ""
  /-- The page had a selection when the context menu opened: the menu has "Copy". -/
  contextSelection : Bool := false
  /-- Find in page (Command-F): the find field is shown in the navigation row. -/
  findOpen : Bool := false
  /-- The text looked for. -/
  find : String := ""
  /-- The find field has the keyboard focus (the address bar then has not). -/
  findFocused : Bool := false
  /-- Matches on the page (`WebSelection.findMatches`), and the current one from 1 (0: none). -/
  findCount : Nat := 0
  findCurrent : Nat := 0
  /-- The system asks for dark colours (`prefers-color-scheme: dark`, as the host reports it).
  The theme "next" (the default setting) then draws dark. -/
  dark : Bool := false
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
  /-- The flat look: no bevels, rounded fields, vector line icons (`flatControlNodes`). -/
  flat : Bool

private def hex (r g b : Nat) : Rendering.Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
/-- The selection colours of the NeXT theme: those of the page (`WebSelection.highlight`). -/
def selectionBackground : Rendering.Color := WebSelection.selectionBackground
def selectionText : Rendering.Color := WebSelection.selectionText
private def next : Theme :=
  ⟨hex 170 170 170,hex 255 255 255,hex 85 85 85,hex 0 0 0,hex 255 255 255,hex 0 0 0,hex 128 128 128,hex 32 32 32,hex 224 32 138,hex 255 196 0,selectionBackground,selectionText,false⟩
private def arcade : Theme :=
  ⟨hex 34 38 54,hex 84 92 128,hex 10 12 20,hex 216 240 255,hex 10 12 20,hex 120 255 170,hex 20 23 34,hex 150 160 200,hex 57 255 136,hex 255 196 0,hex 57 255 136,hex 10 12 20,false⟩
/-! The flat looks. Fields as in `Theme`: `base` the toolbar and the active tab, `light` the
pressed circle behind a control, `dark` the hairline under the chrome, `well` the address
field, `back` the tab strip, `muted` inactive text and disabled icons, `accent` the focus ring,
the caret and the loading bar, `coin` the small marks of the tab strip. -/
private def light : Theme :=
  ⟨hex 250 251 252,hex 222 227 233,hex 210 215 222,hex 31 35 40,hex 236 239 243,hex 31 35 40,hex 226 230 235,hex 104 112 124,hex 11 87 208,hex 104 112 124,selectionBackground,selectionText,true⟩
private def darkTheme : Theme :=
  ⟨hex 41 44 50,hex 66 71 80,hex 22 24 28,hex 230 233 238,hex 26 28 33,hex 230 233 238,hex 30 32 37,hex 152 161 172,hex 138 180 248,hex 152 161 172,selectionBackground,selectionText,true⟩
/-- The theme of a setting: "light", "dark", "classic" (NeXT grey), "arcade"; anything else,
"next" (the default setting) among them, follows the system: dark when the host says so. -/
private def themeOf (s : Shell) : Theme :=
  match s.theme with
  | "arcade" => arcade
  | "classic" => next
  | "light" => light
  | "dark" => darkTheme
  | _ => if s.dark then darkTheme else light

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
  | "openLinkTab" => "Open link in new tab"
  | "copyLink" => "Copy link address"
  | "menuBack" => "Back"
  | "menuForward" => "Forward"
  | "menuReload" => "Reload"
  | "menuSource" => "View source"
  | "menuCopy" => "Copy"
  | _ => ""

/-! ### The context menu (issue 1031)

A right click, or Control-click on macOS (`linkGesture` answers "menu"), on the page opens a
context menu, as in Chrome, Firefox and Safari. Its items are drawn and pressed as the address
menu's buttons are, in the navigation row. On a link: "Open link in new tab" and "Copy link
address". Elsewhere on the page: Back, Forward, Reload and View source. Both have "Copy" when
the page has a selection. The host sends the link under the press, from the frame on screen,
and whether there is a selection; it decides nothing. -/

/-- The items of an open context menu, left to right; empty when it is closed. -/
def contextItems (s : Shell) : List String :=
  let copy := if s.contextSelection then ["menuCopy"] else []
  match s.context with
  | "link" => ["openLinkTab","copyLink"] ++ copy
  | "page" => ["menuBack","menuForward","menuReload","menuSource"] ++ copy
  | _ => []

/-- Every name a menu button can have. -/
def menuItemNames : List String :=
  menuControls ++ ["openLinkTab","copyLink","menuBack","menuForward","menuReload","menuSource","menuCopy"]

/-- The buttons of the open menu, left to right: the context menu's, else the address menu's. -/
def menuItems (s : Shell) : List String :=
  if s.context != "" then contextItems s else if s.menu then menuControls else []

/-- The menu is drawn: open, and the chrome full. -/
def menuShown (s : Shell) : Bool := (s.menu || s.context != "") && s.collapse == 0

/-- Open the context menu for a press on the page: on `link` when the press is on one, else
the page menu. It closes the address menu and leaves the focus as it is. -/
def Shell.openContext (s : Shell) (link : Option String) (selection : Bool) : Shell :=
  {s with menu := false, context := if link.isSome then "link" else "page",
          contextLink := link.getD "", contextSelection := selection}

/-- A press on a link opens the link menu, and a press elsewhere the page menu. -/
theorem openContext_link (s : Shell) (href : String) (selection : Bool) :
    contextItems (s.openContext (some href) selection) =
      ["openLinkTab","copyLink"] ++ (if selection then ["menuCopy"] else []) := by
  simp [Shell.openContext, contextItems]

theorem openContext_page (s : Shell) (selection : Bool) :
    contextItems (s.openContext none selection) =
      ["menuBack","menuForward","menuReload","menuSource"] ++ (if selection then ["menuCopy"] else []) := by
  simp [Shell.openContext, contextItems]

/-- "Copy" is in the context menu exactly when the page had a selection. -/
theorem openContext_copy (s : Shell) (link : Option String) (selection : Bool) :
    (contextItems (s.openContext link selection)).contains "menuCopy" = selection := by
  cases link <;> cases selection <;> simp [Shell.openContext, contextItems]

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

/-- What a press on the page does, from the button (0 primary, 1 secondary, 2 middle), the
modifier bits of `native_window.m` and `native_window_linux.c` (1 Shift, 2 Command, 4 Option,
8 Control) and the platform ("mac" or "other"). Issue 1031; the rules are those Chrome, Firefox
and Safari share:

- secondary button: the context menu;
- macOS, Control with the primary button: the context menu;
- middle button: a new tab in the background, in front with Shift;
- primary button with Command (macOS) or Control (other systems): a new tab in the background,
  in front with Shift;
- else the press is a normal one ("follow").

The answer is one of "follow", "backgroundTab", "foregroundTab", "menu". -/
def linkGesture (platform : String) (button modifiers : Nat) : String :=
  let shift := modifiers.testBit 0
  let command := modifiers.testBit 1
  let control := modifiers.testBit 3
  let mac := platform == "mac"
  let tab := if shift then "foregroundTab" else "backgroundTab"
  if button == 1 then "menu"
  else if button == 2 then tab
  else if mac && control then "menu"
  else if (if mac then command else control) then tab
  else "follow"

/-- A press with no modifier and the primary button is a normal press, on every platform. -/
theorem linkGesture_plain (platform : String) : linkGesture platform 0 0 = "follow" := by
  simp [linkGesture]

/-- Command-click on macOS opens a background tab; Shift-Command-click a tab in front. -/
example : linkGesture "mac" 0 2 = "backgroundTab" := by decide
example : linkGesture "mac" 0 3 = "foregroundTab" := by decide
/-- Control-click on macOS is the context menu; on other systems it opens a background tab. -/
example : linkGesture "mac" 0 8 = "menu" := by decide
example : linkGesture "other" 0 8 = "backgroundTab" := by decide
/-- The middle button opens a background tab; the secondary button the menu. -/
example : linkGesture "other" 2 0 = "backgroundTab" := by decide
example : linkGesture "mac" 1 0 = "menu" := by decide

private def tabWidth (s : Shell) (width : Nat) : Nat :=
  let room := width-(90*unit s)
  min (180*unit s) (room/max 1 s.tabs.size)

/-- A menu button: its label and 6 lettering pixels of margin on each side. -/
private def menuButtonWidth (s : Shell) (size : Nat) (name : String) : Nat :=
  (menuLabel name).length*6*size+12*unit s

/-- The lettering size of the menu: the bar's, or the folded strip's smaller one when the
buttons would leave the address bar less than 80 logical pixels. -/
private def menuSize (s : Shell) (width : Nat) : Nat :=
  let u := unit s
  let items := menuItems s
  let need := (items.map (menuButtonWidth s (dot s))).sum+(2*(items.length-1)+4+4+4)*u+80*u
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
    -- Right to left from the row's right edge, 2 logical pixels apart.
    let mut right := width-min width pad
    let mut items : List Box := []
    for name in (menuItems s).reverse do
      let w := menuButtonWidth s size name
      let at_ := right-min right w
      items := ⟨name,at_,by_,w,button⟩ :: items
      right := at_-min at_ (2*u)
    let firstX := (items.head?.map (·.x)).getD right
    let left := if narrow s width then pad else x
    let kept := if narrow s width then out.filter (fun b => b.name != "back" && b.name != "reload") else out
    return kept ++ [⟨"address",left,by_,firstX-min firstX (left+4*u),button⟩] ++ items
  let tail := if narrow s width then 2*button+8*u+pad else 2*button+8*u+pad
  -- The find field takes up to 240 logical pixels of the bar's right, at most half of it.
  let room := width-min width (x+tail)
  let findW := if s.findOpen then min (240*u) (room/2) else 0
  out := out ++ [⟨"address",x,by_,room-findW,button⟩]
  if s.findOpen then out := out ++ [⟨"find",x+room-findW+2*u,by_,findW-min findW (2*u),button⟩]
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
  | ["copyAddress"] | ["pasteGo"] => s.menu && s.context == ""
  | ["menuBack"] => (contextItems s).contains "menuBack" && s.canBack
  | ["menuForward"] => (contextItems s).contains "menuForward" && s.canForward
  | [name] => (contextItems s).contains name
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

/-! ### The chrome for assistive technology

The controls are drawn, and most are icons, so a screen reader is given them in words: a
toolbar, and below it each control of `boxes` with a role, a name, its state and its box in
window pixels (`HTML.AccessibleTree.Entry`, as the page's own tree). A press on one is a
press at its box, which `hit` answers as for a pointer. -/

/-- The name of a control in words. -/
def controlLabel (s : Shell) (name : String) : String :=
  let title := fun (i : String) => match i.toNat? with
    | some n => match s.tabs[n]? with
      | some tab => if tab.title.isEmpty then s!"Tab {n + 1}" else tab.title
      | none => s!"Tab {n + 1}"
    | none => "Tab"
  match name.splitOn ":" with
  | ["back"] => "Back"
  | ["forward"] => "Forward"
  | ["reload"] => "Reload"
  | ["home"] => "Home"
  | ["address"] => "Address"
  | ["find"] => "Find in page"
  | ["source"] => "View source"
  | ["tabs"] => "Tabs"
  | ["settings"] => "Settings"
  | ["newTab"] => "New tab"
  | ["expand"] => "Show toolbar"
  | ["tab", i] => title i
  | ["close", i] => "Close " ++ title i
  | _ => menuLabel name

/-- The chrome's accessibility entries, numbered from `base`: the toolbar, then its controls
left to right, top to bottom. A folded chrome is one button that unfolds it. -/
def accessible (s : Shell) (width base : Nat) : List HTML.AccessibleTree.Entry :=
  let rect := fun (x y w h : Nat) => some (⟨Int.ofNat x, Int.ofNat y, w, h⟩ : HTML.AccessibleTree.Rect)
  let bar : HTML.AccessibleTree.Entry :=
    { depth := 0, id := base, role := "toolbar", name := "Browser toolbar", box := rect 0 0 width (height s width) }
  if s.collapse > 0 then
    [bar, { depth := 1, id := base + 1, role := "button", name := controlLabel s "expand", focusable := true,
            box := rect 0 0 width (height s width) }]
  else
    bar :: (boxes s width).zipIdx.map fun (b, i) =>
      let kind := (b.name.splitOn ":").headD ""
      let label := controlLabel s b.name
      let box := rect b.x b.y b.w b.h
      if kind == "address" || kind == "find" then
        let focused := if kind == "address" then s.focused else s.findFocused
        { depth := 1, id := base + 1 + i, role := "textbox", name := label, focusable := true, box,
          props := [("value", if kind == "address" then s.address else s.find)] ++
            (if focused then [("focused", "true")] else []) }
      else if kind == "tab" then
        { depth := 1, id := base + 1 + i, role := "tab", name := label, focusable := true, box,
          props := [("selected", if b.name == s!"tab:{s.active}" then "true" else "false")] }
      else
        { depth := 1, id := base + 1 + i, role := "button", name := label, focusable := pressable s b.name, box,
          props := if pressable s b.name then [] else [("disabled", "true")] }

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
  | some "find" => .text
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

/-- Glyph outlines for printable ASCII, indexed from U+0020. Prepared once
when the host supplies its bundled monospace face. -/
structure AddressFont where
  advance : Nat := 1
  glyphs : Array (Option (List Rendering.Geometry)) := #[]

private def addressText (font : AddressFont) (c : Rendering.Color)
    (value : String) (x y size : Nat) : List Rendering.Node :=
  if font.glyphs.isEmpty then text c value x y size else
  let scale := Float.ofNat (6*size) / Float.ofNat (max 1 font.advance)
  let baseline := Float.ofNat (y+7*size)
  value.toList.zipIdx.flatMap fun (ch,i) =>
    if ch == ' ' then [] else
    let left := x+i*6*size
    let paths := if ch.toNat < 32 then none else font.glyphs[ch.toNat-32]?.join
    match paths with
    | none => bitmapNodes c (glyphRows ch) 5 left y size
    | some shapes =>
      [.group none ⟨scale,0,0,scale,Float.ofNat left,baseline⟩
        (shapes.map fun geometry => .paint {primitive := {geometry, style := {fill := .solid c}}})]

/-- With no held face, address text is drawn by the existing bitmap path. -/
theorem addressText_empty (c : Rendering.Color) (value : String) (x y size : Nat) :
    addressText {} c value x y size = text c value x y size := rfl

#print axioms addressText_empty

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
        [.paint ⟨none,{geometry := .rect 0 0 w h,style := {fill := .image {map,id := iconPaintId index,bitmap}}}⟩]]
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

/-- What the find field shows after the text: the current match and the count, or none. -/
def findLabel (s : Shell) : String :=
  if s.find.isEmpty then "" else if s.findCount == 0 then "none" else s!"{s.findCurrent}/{s.findCount}"

/-- The find field (Command-F): a well like the address bar, with the text looked for, a caret
when it has the focus, and the current match and the count at its right. -/
private def findNodes (s : Shell) (t : Theme) (box : Box) : List Rendering.Node :=
  let u := unit s
  let size := dot s
  let textX := box.x+22*u
  let textY := box.y+(box.h-7*size)/2
  let label := findLabel s
  let labelW := label.length*charWidth s
  let room := box.w-min box.w (30*u+labelW)
  let shown := fitEnd s s.find room
  let body := if s.find.isEmpty && !s.findFocused then text t.dark (fit s "find" room) textX textY size
    else text t.wellInk shown textX textY size
  let cursor := if s.findFocused then [paint t.accent (textX+shown.length*charWidth s) (textY-u) (5*size) (7*size+2*u)] else []
  bevel s t t.well false box.x box.y box.w box.h ++ text t.accent "?" (box.x+8*u) textY size ++ body ++ cursor ++
    text t.dark label (box.x+box.w-min (box.x+box.w) (8*u+labelW)) textY size

/-! ### The flat look

Flat faces, a rounded address field with a focus ring, and line icons as vector strokes on a
16-unit grid. The boxes, and so every hit test, press box and height, are the classic ones
(`boxes`): only the paint differs. -/

private def fl (n : Nat) : Float := Float.ofNat n

/-- 16 points of the unit circle, from angle 0 (right) clockwise on screen. Circles of the
chrome are these polygons: the chrome is drawn again on each change of the fold, and a
16-sided polygon costs the engine far less than a curve to flatten. -/
private def unitCircle : List (Float × Float) :=
  (List.range 16).map fun i => let a := Float.ofNat i*0.39269908169872414; (Float.cos a,Float.sin a)

/-- A filled circle, as a 16-sided polygon. -/
private def disk (c : Rendering.Color) (cx cy r : Float) : Rendering.Node :=
  .paint {primitive := {geometry := .polygon (unitCircle.map fun (x,y) => ⟨cx+r*x,cy+r*y⟩),style := {fill := .solid c}}}

/-- A filled rectangle with corners of radius `r` (at most half the shorter side): two
rectangles and four circles. Opaque colours only, as the overlaps paint twice. -/
private def rounded (c : Rendering.Color) (x y w h r : Nat) : List Rendering.Node :=
  let r := min r (min w h/2)
  if r == 0 then [paint c x y w h] else
  -- A pill (the corners meet): one rectangle and the two end circles.
  if 2*r ≥ h then [paint c (x+r) y (w-2*r) h,disk c (fl (x+r)) (fl y+fl h/2) (fl h/2),disk c (fl (x+w-r)) (fl y+fl h/2) (fl h/2)] else
  [paint c (x+r) y (w-2*r) h,paint c x (y+r) w (h-2*r),
   disk c (fl (x+r)) (fl (y+r)) (fl r),disk c (fl (x+w-r)) (fl (y+r)) (fl r),
   disk c (fl (x+r)) (fl (y+h-r)) (fl r),disk c (fl (x+w-r)) (fl (y+h-r)) (fl r)]

/-- A stroke with square caps and mitred joins: no round piece for the engine to flatten. -/
private def strokeStyle (c : Rendering.Color) (w : Float) : Rendering.Style :=
  {fill := .none,stroke := .solid c,strokeWidth := w,lineCap := .square,lineJoin := .miter}

/-- An open line through `points`. -/
private def polyline (c : Rendering.Color) (w : Float) : List (Float × Float) → List Rendering.Node
  | [] => []
  | (x,y)::rest =>
    [.paint {primitive := {geometry := .path [.path ⟨x,y⟩ (rest.map fun (a,b) => .line ⟨a,b⟩) false],style := strokeStyle c w}}]

/-- One line icon on the 16-unit grid, as strokes in grid units: polylines, rings (centre and
radius, a closed 16-sided line) and arcs (centre, radius and the `unitCircle` points, in order). -/
private inductive Stroke where
  | line (points : List (Float × Float))
  | ring (cx cy r : Float)
  | arc (cx cy r : Float) (points : List Nat)
  /-- A filled shape: closed outlines, filled even-odd (an outline inside another is a hole). -/
  | solid (outlines : List (List (Float × Float)))

/-- The gear: one filled shape, eight teeth round a ring (the 16 points of `unitCircle`
alternate between radius 7 and 5.2, each two points wide so a tooth has a flat top), with
the hub as a hole. -/
private def gear : List Stroke :=
  let teeth := (List.range 16).flatMap fun i =>
    match unitCircle[i]? with
    | some (x,y) =>
      let r := if i % 2 == 0 then 7 else 5.2
      [(8+r*(x*0.98+y*0.2),8+r*(y*0.98-x*0.2)),(8+r*(x*0.98-y*0.2),8+r*(y*0.98+x*0.2))]
    | none => []
  [.solid [teeth,unitCircle.map fun (x,y) => (8+2.3*x,8+2.3*y)]]

private def lineIcon : String → List Stroke
  | "back" => [.line [(3.5,8),(12.5,8)],.line [(7.5,4),(3.5,8),(7.5,12)]]
  | "forward" => [.line [(3.5,8),(12.5,8)],.line [(8.5,4),(12.5,8),(8.5,12)]]
  -- Three quarters of a circle from the upper right, back over the top, with the arrow at its start.
  | "reload" => [.arc 8 8 4.8 [14,13,12,11,10,9,8,7,6,5,4,3,2],.line [(11.4,1.6),(11.4,4.6),(14.4,4.6)]]
  | "stop" => [.line [(4.5,4.5),(11.5,11.5)],.line [(11.5,4.5),(4.5,11.5)]]
  | "home" => [.line [(2.5,8),(8,3),(13.5,8)],.line [(4.5,6.5),(4.5,13),(11.5,13),(11.5,6.5)],.line [(7,13),(7,9.5),(9,9.5),(9,13)]]
  | "settings" => gear
  | "source" => [.line [(5.5,4.5),(2,8),(5.5,11.5)],.line [(10.5,4.5),(14,8),(10.5,11.5)],.line [(9,3.5),(7,12.5)]]
  | "newTab" => [.line [(8,3.5),(8,12.5)],.line [(3.5,8),(12.5,8)]]
  | "close" => [.line [(5,5),(11,11)],.line [(11,5),(5,11)]]
  | "search" => [.ring 7 7 4,.line [(10,10),(13.5,13.5)]]
  | "tabs" => [.line [(3,3),(13,3),(13,13),(3,13),(3,3)]]
  | _ => []

/-- Icon `name` in colour `c`, `side` backing pixels square, centred in `box`; the strokes are
`weight` grid units wide. -/
private def lineIconAt (c : Rendering.Color) (name : String) (box : Box) (side : Nat) (weight : Float := 1.8) :
    List Rendering.Node :=
  let k := fl side/16
  let x0 := fl box.x+(fl box.w-fl side)/2
  let y0 := fl box.y+(fl box.h-fl side)/2
  let p := fun (x y : Float) => (x0+x*k,y0+y*k)
  let w := weight*k
  let around := fun (cx cy r : Float) (q : Float × Float) => p (cx+r*q.1) (cy+r*q.2)
  let contour := fun (closed : Bool) (pts : List (Float × Float)) => match pts with
    | [] => Rendering.Contour.empty closed
    | (sx,sy)::rest => Rendering.Contour.path ⟨sx,sy⟩ (rest.map fun (a,b) => .line ⟨a,b⟩) closed
  -- A line is not stroked (stroking is the costly part of the chrome): each segment is a filled
  -- quadrilateral `w` wide, lengthened by half of `w` at both ends so joins have no gaps. Every
  -- quadrilateral winds the same way, so with the nonzero rule their overlaps stay filled.
  let h := w/2
  let quad := fun (a b : Float × Float) =>
    let dx := b.1-a.1
    let dy := b.2-a.2
    let len := Float.sqrt (dx*dx+dy*dy)
    if len == 0 then [] else
    let ux := dx/len*h
    let uy := dy/len*h
    let (ax,ay) := (a.1-ux,a.2-uy)
    let (bx,by_) := (b.1+ux,b.2+uy)
    [contour true [(ax-uy,ay+ux),(bx-uy,by_+ux),(bx+uy,by_-ux),(ax+uy,ay-ux)]]
  let segments := fun (closed : Bool) (pts : List (Float × Float)) =>
    let next := pts.drop 1 ++ (if closed then pts.take 1 else [])
    (pts.zip next).flatMap fun (a,b) => quad a b
  -- One filled path for an icon's lines and one for its solid shapes: at most two primitives.
  let lines := (lineIcon name).flatMap fun
    | .line points => segments false (points.map fun (x,y) => p x y)
    | .ring cx cy r => segments true (unitCircle.map (around cx cy r))
    | .arc cx cy r points => segments false (points.filterMap fun i => (unitCircle[i]?).map (around cx cy r))
    | .solid _ => []
  let fills := (lineIcon name).flatMap fun
    | .solid outlines => outlines.map fun o => contour true (o.map fun (x,y) => p x y)
    | _ => []
  (if lines.isEmpty then [] else [.paint {primitive := {geometry := .path lines,style := {fill := .solid c,rule := .nonzero}}}]) ++
  (if fills.isEmpty then [] else [.paint {primitive := {geometry := .path fills,style := {fill := .solid c,rule := .evenodd}}}])

/-- A tab of the flat look: the active one a raised card in the toolbar's face, joined to it;
the others plain, with a hairline between them. -/
private def flatTab (s : Shell) (t : Theme) (box : Box) (index : Nat) : List Rendering.Node :=
  let u := unit s
  let active := index == s.active
  let title := ((s.tabs[index]?).map (·.title)).getD ""
  let icon := (s.tabs[index]?).bind (·.icon)
  let iconSide := 16*u
  let shift := if icon.isSome then iconSide+6*u else 0
  let iconPaint := match icon with
    | some i => iconNodes i index (box.x+9*u) (box.y+(box.h-min box.h iconSide)/2+u) iconSide
    | none => []
  let title := if title.isEmpty then "New tab" else title
  let room := box.w-(if s.tabs.size > 1 then 34*u else 18*u)-min (box.w/2) shift
  let card := if active then rounded t.base box.x (box.y+u) box.w (box.h+8*u) (8*u) else
    [paint t.dark (box.x+box.w-u) (box.y+6*u) u (box.h-min box.h (10*u))]
  card ++ iconPaint ++
    text (if active then t.ink else t.muted) (fit s title room) (box.x+9*u+shift) (box.y+(box.h-7*dot s)/2+2*u) (dot s)

/-- The address field of the flat look: a pill in the field colour, ringed in the accent while
it has the focus; a search mark, then the text, the selection and a thin caret. The text
columns are those of the classic field (`addressNodes`), so a press lands on the same letter. -/
private def flatAddress (font : AddressFont) (s : Shell) (t : Theme) (box : Box) : List Rendering.Node :=
  let u := unit s
  let size := dot s
  let textX := box.x+22*u
  let textY := box.y+(box.h-7*size)/2
  let room := box.w-28*u
  let shown := fitEnd s s.address room
  let column := fun (i : Nat) => min shown.length (i+shown.length-s.address.length)
  let lo := column (min s.anchor s.cursor)
  let hi := column (max s.anchor s.cursor)
  let selecting := s.focused && hi > lo
  let piece := fun (c : Rendering.Color) (a b : Nat) =>
    addressText font c (String.ofList ((shown.toList.drop a).take (b-a))) (textX+a*charWidth s) textY size
  let body := if s.address.isEmpty && !s.focused
    then addressText font t.muted (fit s "Search or type a URL" room) textX textY size
    else if selecting then piece t.wellInk 0 lo ++ piece t.selectedInk lo hi ++ piece t.wellInk hi shown.length
    else addressText font t.wellInk shown textX textY size
  let marked := if selecting
    then [paint t.selected (textX+lo*charWidth s-u) (textY-u) ((hi-lo)*charWidth s) (7*size+2*u)] else []
  let cursor := if s.focused && hi == lo then [paint t.accent (textX+column s.cursor*charWidth s) (textY-2*u) (max 1 (3*u/2)) (7*size+4*u)] else []
  let r := box.h/2
  let field := if s.focused
    then rounded t.accent (box.x-2*u) (box.y-2*u) (box.w+4*u) (box.h+4*u) (r+2*u) ++ rounded t.base box.x box.y box.w box.h r
    else rounded t.well box.x box.y box.w box.h r
  let mark := lineIconAt t.muted "search" {name := "search",x := box.x+5*u,y := box.y,w := 14*u,h := box.h} (12*u) 1.8
  field ++ mark ++ marked ++ cursor ++ body

/-- The find field of the flat look: a pill like the address field, with the count at its right. -/
private def flatFind (s : Shell) (t : Theme) (box : Box) : List Rendering.Node :=
  let u := unit s
  let size := dot s
  let textX := box.x+22*u
  let textY := box.y+(box.h-7*size)/2
  let label := findLabel s
  let labelW := label.length*charWidth s
  let room := box.w-min box.w (30*u+labelW)
  let shown := fitEnd s s.find room
  let body := if s.find.isEmpty && !s.findFocused then text t.muted (fit s "Find in page" room) textX textY size
    else text t.wellInk shown textX textY size
  let cursor := if s.findFocused then [paint t.accent (textX+shown.length*charWidth s) (textY-2*u) (max 1 (3*u/2)) (7*size+4*u)] else []
  let r := box.h/2
  let field := if s.findFocused
    then rounded t.accent (box.x-2*u) (box.y-2*u) (box.w+4*u) (box.h+4*u) (r+2*u) ++ rounded t.base box.x box.y box.w box.h r
    else rounded t.well box.x box.y box.w box.h r
  field ++ lineIconAt t.muted "search" {name := "search",x := box.x+5*u,y := box.y,w := 14*u,h := box.h} (12*u) 1.8 ++ body ++ cursor ++
    text t.muted label (box.x+box.w-min (box.x+box.w) (10*u+labelW)) textY size

/-- The controls of the full chrome in a flat theme: the tab strip, the toolbar, round
buttons that show a circle while pressed, and the settings button always in a circle of the
field colour, so it is easy to find. -/
private def flatControlNodes (s : Shell) (t : Theme) (width : Nat) (font : AddressFont) : List Rendering.Node := Id.run do
  let u := unit s
  let row := tabRow s width
  let mut out := [paint t.back 0 0 width row,paint t.base 0 row width (navRow s)]
  let down := fun (name : String) => s.pressed == name && pressable s name
  let circle := fun (c : Rendering.Color) (box : Box) => disk c (fl box.x+fl box.w/2) (fl box.y+fl box.h/2) (fl (min box.w box.h)/2)
  let iconSide := 20*u
  for box in boxes s width do
    match box.name.splitOn ":" with
    | ["tab",i] => out := out ++ flatTab s t box (i.toNat?.getD 0)
    | ["close",_] =>
      out := out ++ (if down box.name then [circle t.light box] else []) ++ lineIconAt t.muted "close" box (12*u) 1.8
    | ["newTab"] => out := out ++ (if down box.name then [circle t.light box] else []) ++ lineIconAt t.ink "newTab" box (14*u)
    | ["address"] => out := out ++ flatAddress font s t box
    | ["find"] => out := out ++ flatFind s t box
    | [name] =>
      if menuItemNames.contains name then
        let size := menuSize s width
        let label := menuLabel box.name
        out := out ++ rounded (if down box.name then t.light else t.well) box.x box.y box.w box.h (box.h/2) ++
          text (if pressable s name then t.ink else t.muted) label (box.x+(box.w-min box.w (label.length*6*size-size))/2) (box.y+(box.h-7*size)/2) size
      else match name with
      | "tabs" =>
        out := out ++ (if down box.name then [circle t.light box] else []) ++ lineIconAt t.ink "tabs" box iconSide ++
          text t.ink (toString s.tabs.size) (box.x+(box.w-5*dot s)/2) (box.y+(box.h-7*dot s)/2) (dot s)
      | "settings" =>
        out := out ++ [circle (if down box.name then t.light else t.well) box] ++ lineIconAt t.ink "settings" box iconSide 1.6
      | _ =>
        let enabled := (name != "back" || s.canBack) && (name != "forward" || s.canForward)
        let shape := if name == "reload" && s.loading then "stop" else name
        out := out ++ (if down box.name then [circle t.light box] else []) ++
          lineIconAt (if enabled then t.ink else t.muted) shape box iconSide
    | _ => pure ()
  if !narrow s width then
    let label := toString s.pages
    let x := width-(label.length*charWidth s)-16*u
    let y := (row-7*dot s)/2+u
    out := out ++ [disk t.coin (fl (x-6*u)) (fl y+fl (7*dot s)/2) (fl (2*u))] ++ text t.coin label x y (dot s)
    if !s.script.isEmpty then
      out := out ++ text t.coin s.script (x-14*u-(s.script.length+1)*charWidth s) y (dot s)
  return out

/-- The bar under the chrome: a thin accent line, or a level bar while loading. -/
private def edgeNodes (s : Shell) (t : Theme) (width : Nat) : List Rendering.Node := Id.run do
  let y := height s width-edge s
  -- Flat: a hairline under the toolbar's face; while loading, an accent bar over it.
  if t.flat then
    let u := unit s
    let bar := if s.loading then [paint t.accent 0 (y+edge s-2*u) (width*2/5) (2*u)] else []
    return [paint t.base 0 y width (edge s-u),paint t.dark 0 (y+edge s-u) width u] ++ bar
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
  (if s.collapse == 0 then
    (if t.flat then rounded (if done then t.accent else t.ink) x y size size (size/2) ++
      lineIconAt t.base (if back then "back" else "forward") box (18*u)
    else [paint (if done then t.accent else t.ink) x y size size] ++
      iconAt s (if done then t.ink else t.base) (if back then "back" else "forward") box) else []) ++
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
    | ["find"] => out := out ++ findNodes s t box
    | [name] =>
      if menuItemNames.contains name then
        let size := menuSize s width
        let label := menuLabel box.name
        let at_ := sink box.name box
        -- Raised, with the accent line along its top, as the active tab.
        out := out ++ face box ++ [paint t.accent (at_.x+2*u) (at_.y+2*u) (at_.w-4*u) u] ++
          text (if pressable s name then t.ink else t.dark) label (at_.x+(at_.w-min at_.w (label.length*6*size-size))/2) (at_.y+(at_.h-7*size)/2+u) size
      else if name == "tabs" then
        let at_ := sink box.name box
        out := out ++ face box ++
          text t.ink (toString s.tabs.size) (at_.x+(at_.w-5*dot s)/2) (at_.y+(at_.h-7*dot s)/2) (dot s)
      else
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
    -- The script engine of this page, left of the page count.
    if !s.script.isEmpty then
      out := out ++ text t.coin s.script (x-10*dot s-(s.script.length+2)*charWidth s) y (dot s)
  return out

/-- Colour `c` faded `p` percent of the way to `to`: the chrome has no alpha, and over
its own opaque face this is the same as `c` at opacity `1-p`. -/
private def mix (c to : Rendering.Color) (p : Nat) : Rendering.Color :=
  let f := Float.ofNat (min 100 p)/100
  ⟨c.r+(to.r-c.r)*f,c.g+(to.g-c.g)*f,c.b+(to.b-c.b)*f⟩
/-- The theme with every colour faded `p` percent into the chrome's face. -/
private def fade (t : Theme) (p : Nat) : Theme :=
  let m := fun c => mix c t.base p
  ⟨t.base,m t.light,m t.dark,m t.ink,m t.well,m t.wellInk,m t.back,m t.muted,m t.accent,m t.coin,m t.selected,m t.selectedInk,t.flat⟩

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

/-! ### The splash (start of the app)

The name and release over the first page while it loads, in the chrome's lettering: the
letters grow until they are too big to read while they fade out, over `splashMs`. With
reduced motion they only fade, over `splashReducedMs`. The values at a time are SMIL's
animation function (`Smil.valueAt`, values with keyTimes, linear), from the time since the
splash began, which the host sends; after its duration the splash has no nodes. -/
def splashMs : Nat := 600
def splashReducedMs : Nat := 200

def splashDuration (reduce : Bool) : Nat := if reduce then splashReducedMs else splashMs

/-- The growth (1 at the start) and the opacity at `ms`, or none once the splash is over.
Growth speeds up as it goes, as something coming at the viewer; the letters hold their
opacity for the first fifth. -/
def splashState (ms : Nat) (reduce : Bool) : Option (Float × Float) := do
  let dur := splashDuration reduce
  if ms ≥ dur then none
  let f := Float.ofNat ms/Float.ofNat dur
  let grow ← if reduce then some #[1] else
    Rendering.Smil.valueAt #[#[1],#[1.5],#[3],#[12]] (some #[0,0.4,0.75,1]) false f
  let opacity ← Rendering.Smil.valueAt #[#[1],#[1],#[0]] (some #[0,0.2,1]) false f
  return ((grow[0]?).getD 1,(opacity[0]?).getD 0)

/-- The ink of the splash: the blue of the about page's heading. -/
def splashColor : Rendering.Color := hex 24 64 120

private def faded (o : Float) : Rendering.Node → Rendering.Node
  | .paint item => .paint {item with primitive := {item.primitive with style := {item.primitive.style with fillOpacity := o}}}
  | node => node

/-- The splash at `ms` over the view of `rows` rows from page row `top`, `width` wide: the
label in the lettering, centred, about seven tenths of the width at the start. -/
def splashNodes (label : String) (ms width top rows : Nat) (reduce : Bool) : List Rendering.Node :=
  match splashState ms reduce with
  | none => []
  | some (grow,o) =>
    let columns := max 1 (label.length*6)
    let base := Float.ofNat (max 1 (min (width*7/10/columns) (rows/14)))
    let size := base*grow
    let w := Float.ofNat (columns-1)*size
    let h := 7*size
    let x := Float.ofNat width/2-w/2
    let y := Float.ofNat top+Float.ofNat rows/2-h/2
    [.group none ⟨size,0,0,size,x,y⟩ ((text splashColor label 0 0 1).map (faded o))]

#guard (splashState 0 false).map (·.1) == some 1 && (splashState 0 false).map (·.2) == some 1
#guard (splashState splashMs false).isNone && (splashState splashReducedMs true).isNone
#guard (splashNodes "Foafnaut 0.36.0" splashMs 800 0 500 false).isEmpty
#guard (splashNodes "Foafnaut 0.36.0" 0 800 0 500 false).length == 1
-- Reduced motion: no growth, and over sooner.
#guard (splashState 150 true).map (·.1) == some 1 && (splashNodes "F" 250 800 0 500 true).isEmpty
-- It grows and fades as it goes.
#guard match splashState 300 false, splashState 500 false with
  | some (g1,o1), some (g2,o2) => g1 < g2 && o2 < o1 | _, _ => false

/-- The chrome as scene nodes. It is drawn over the page. With `collapse` above 0 it is
folding: the controls slide up and fade into the chrome's face over the first half of the
fold, the chrome is shorter (`height`), and the domain shrinks to the middle of the strip
and fades in over the second half. -/
def nodes (s : Shell) (width : Nat) (font : AddressFont := {}) : List Rendering.Node :=
  let t := themeOf s
  let controlNodes := fun (s : Shell) (t : Theme) (width : Nat) =>
    if t.flat then flatControlNodes s t width font else controlNodes s t width
  if s.collapse == 0 then controlNodes s t width ++ edgeNodes s t width ++ swipeNodes s t width else
  let p := min 100 s.collapse
  let lift := fullHeight s width-height s width
  let slide : Rendering.Transform := ⟨1,0,0,1,0,-(Float.ofNat lift)⟩
  -- From half way the controls have faded into the face (`fade` at 100%): not drawn.
  [paint t.base 0 0 width (height s width)] ++
    (if p < 50 then [.group none slide (controlNodes {s with collapse := 0} (fade t (2*p)) width)] else []) ++
    domainNodes s t width p ++ edgeNodes s t width ++ swipeNodes s t width

/-- The page's part of the window: rows from the chrome's bottom to the window's. -/
def pageClip (s : Shell) (width height' : Nat) : Rendering.ClipRect :=
  ⟨0,Float.ofNat (height s width),Float.ofNat width,Float.ofNat height'-Float.ofNat (height s width),Rendering.identity⟩

/-- Put a page rendered below the chrome and the chrome into one scene. The page is clipped to its part of the window
(`pageClip`), so no page ink reaches the chrome (`compose_page_clipped`). -/
def compose (s : Shell) (page : Rendering.Scene) (width height' : Nat) (font : AddressFont := {}) : Rendering.Scene :=
  let top := Float.ofNat (height s width)-Float.ofNat s.scroll
  let shift : Rendering.Transform := ⟨1,0,0,1,0,top⟩
  {page with
    height := height'
    mapping := {page.mapping with viewportHeight := Float.ofNat height'}
    tree := [.clipped none Rendering.identity (pageClip s width height') [.group none shift page.tree]] ++ nodes s width font
    links := Rendering.moveLinks (· + top) page.links}

/-- Security: every primitive of the page in a composed frame carries the page's part
of the window as a clip, so its ink can not paint the chrome. -/
theorem composeWithFont_page_clipped (font : AddressFont) (s : Shell) (page : Rendering.Scene) (width height' : Nat)
    (parent : Rendering.Transform) (groups : List (Option String)) (item : Rendering.PaintItem)
    (node : Rendering.Node) (head : (compose s page width height' font).tree.head? = some node)
    (h : item ∈ node.lower parent groups) :
    (pageClip s width height').lowerUnder parent ∈ item.primitive.clips := by
  have e : node = .clipped none Rendering.identity (pageClip s width height')
      [.group none ⟨1,0,0,1,0,Float.ofNat (height s width)-Float.ofNat s.scroll⟩ page.tree] := by
    simp only [compose, List.cons_append, List.head?_cons, Option.some.injEq] at head
    exact head.symm
  subst e
  exact Rendering.lower_clipped _ _ _ _ _ _ _ h

theorem compose_page_clipped (s : Shell) (page : Rendering.Scene) (width height' : Nat)
    (parent : Rendering.Transform) (groups : List (Option String)) (item : Rendering.PaintItem)
    (node : Rendering.Node) (head : (compose s page width height').tree.head? = some node)
    (h : item ∈ node.lower parent groups) :
    (pageClip s width height').lowerUnder parent ∈ item.primitive.clips :=
  composeWithFont_page_clipped {} s page width height' parent groups item node head h

#print axioms composeWithFont_page_clipped

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
  if text.isEmpty then s else {replaceRange s s.lo s.hi text true with menu := false, context := ""}

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

/-- Left and Right move, and Delete removes, one extended grapheme cluster (UAX #29): an
emoji sequence (ZWJ, skin tone, flag, keycap) or a letter with its marks is one step. -/
def graphemeBefore (value : String) (i : Nat) : Nat :=
  let breaks := L4Factoidal.Unicode.Segmentation.graphemeBreaks value.toList.toArray
  breaks.foldl (fun best b => if b < i then max best b else best) 0
def graphemeAfter (value : String) (i : Nat) : Nat :=
  let breaks := L4Factoidal.Unicode.Segmentation.graphemeBreaks value.toList.toArray
  breaks.foldl (fun best b => if b > i then min best b else best) value.length

-- A family (three people joined by ZWJ) is one step; plain letters are one each.
private def family : String := String.ofList ([0x61,0x1F468,0x200D,0x1F469,0x200D,0x1F467,0x62].map Char.ofNat)
#guard graphemeBefore family 6 == 1 && graphemeAfter family 1 == 6 && graphemeAfter family 6 == 7
#guard graphemeBefore "abc" 2 == 1 && graphemeAfter "abc" 2 == 3 && graphemeBefore "abc" 0 == 0

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
  let s := {s with menu := false, context := ""}
  let extend := has modifiers shiftBit
  let word := has modifiers optionBit
  let line := has modifiers commandBit
  let size := s.address.length
  match code with
  | 51 =>
    if s.lo < s.hi then replaceRange s s.lo s.hi "" false
    else if s.cursor == 0 then s
    else replaceRange s (if line then 0 else if word then wordStart s.address s.cursor else graphemeBefore s.address s.cursor) s.cursor "" false
  | 117 =>
    if s.lo < s.hi then replaceRange s s.lo s.hi "" false
    else if s.cursor >= size then s
    else replaceRange s s.cursor (if line then size else if word then wordEnd s.address s.cursor else graphemeAfter s.address s.cursor) "" false
  | 123 =>
    if !extend && s.lo < s.hi && !word && !line then moveTo s s.lo false
    else moveTo s (if line then 0 else if word then wordStart s.address s.cursor else graphemeBefore s.address s.cursor) extend
  | 124 =>
    if !extend && s.lo < s.hi && !word && !line then moveTo s s.hi false
    else moveTo s (if line then size else if word then wordEnd s.address s.cursor else graphemeAfter s.address s.cursor) extend
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
  if action == "menu" then ({s with menu := s.focused, context := ""},none) else
  let step := s.editStep action text
  ({step.1 with menu := false, context := ""},step.2)

/-- The address menu opens only on a focused bar, and any other edit closes it. -/
theorem edit_menu (s : Shell) : (s.edit "menu").1.menu = s.focused := by
  simp [Shell.edit]

theorem edit_closes (s : Shell) (action text : String) (h : action ≠ "menu") :
    (s.edit action text).1.menu = false := by
  simp [Shell.edit, h]

/-- Every edit closes the context menu, `menu` (the address menu) included. -/
theorem edit_closes_context (s : Shell) (action text : String) :
    (s.edit action text).1.context = "" := by
  unfold Shell.edit; split <;> rfl

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

/-- What a button of a menu asks the host to do: "copy" (write `text`), "paste", and for the
context menu "openTab" (open `text` in a new tab), "back", "forward", "reload", "viewSource"
and "copySelection" (copy the page's selection). A button that is not pressable (Back with no
page before) asks nothing. -/
def menuItemAction (s : Shell) (name : String) : Option (String × Option String) :=
  if !pressable s name then none else
  match name with
  | "copyAddress" => some ("copy",some (copyText s))
  | "pasteGo" => some ("paste",none)
  | "openLinkTab" => some ("openTab",some s.contextLink)
  | "copyLink" => some ("copy",some s.contextLink)
  | "menuBack" => some ("back",none)
  | "menuForward" => some ("forward",none)
  | "menuReload" => some ("reload",none)
  | "menuSource" => some ("viewSource",none)
  | "menuCopy" => some ("copySelection",none)
  | _ => none

/-- The action table of the shown menu, for `width` backing pixels; empty with the menu
closed or the chrome folded. -/
def menuActions (s : Shell) (width : Nat) : List MenuAction :=
  if !menuShown s then [] else
  let u := unit s
  let css := fun (b : Box) => (b.x/u,b.y/u,(b.x+b.w+u-1)/u-b.x/u,(b.y+b.h+u-1)/u-b.y/u)
  (boxes s width).filterMap fun b =>
    (menuItemAction s b.name).map fun (action,text) => {action,control := b.name,rect := css b,text}

/-- A closed menu gives the host no actions: a tap can not copy or paste. -/
theorem menuActions_closed (s : Shell) (width : Nat) (h : s.menu = false) (hc : s.context = "") :
    menuActions s width = [] := by
  simp [menuActions, menuShown, h, hc]

def MenuAction.json (a : MenuAction) : JSON.Json :=
  let n := fun (v : Nat) => JSON.Json.number (toString v)
  .object ([("action",.string a.action),("control",.string a.control),
    ("rect",.array [n a.rect.1,n a.rect.2.1,n a.rect.2.2.1,n a.rect.2.2.2])] ++
    (match a.text with | some t => [("text",.string t)] | none => []))

/-- The menu commands that act on the address bar when it has the focus. -/
def addressCommands : List String := ["copy","selectAll","cut","paste","undo","redo"]

/-! ### What an address and a link mean -/

inductive Go where
  | page (url : String)
  /-- `:open URL`, typed: the person asks for the system to open the address. -/
  | system (url : String)
  | command (name : String) (argument : String)
  /-- Words that are not an address. They go to no one: the browser's own search page
  shows them, unless a search engine was chosen in Settings (`routeAddress`). -/
  | search (words : String)
  deriving Repr, BEq

/-- The FOAF graph is a page of the browser, so it goes into the session history of the
tab it opens in, and back leaves it (issue 1268). The host draws this URL with the graph app. -/
def graphURL : String := "foafnaut:graph"

/-- A browser command. `graph` is the graph page, not a command. -/
def command (name argument : String) : Go :=
  if name == "graph" && argument.isEmpty then .page graphURL else .command name argument

/-- An href: a `foafnaut:` command, or a page. No host goes to the system (WebRoute). -/
def link (href : String) : Go :=
  if href.startsWith "foafnaut:" then
    match ((href.drop 9).toString.splitOn "/") with
    | [name,argument] => command name argument
    | [name] => command name ""
    | _ => .command "help" ""
  else .page href

private def encodeQuery := WebRoute.encodeQuery

/-- The bar reads a `:command`, a URL, or words. There is no default search engine (owner,
2026-11-16): words are `.search`, which sends nothing anywhere by itself. -/
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
  else .search value

/-- An address typed in the bar is not the press of a button on a page: a route to the
system becomes the Outside page. -/
def typedRoute : WebRoute.Route → WebRoute.Route
  | .system u => .outside u
  | r => r

/-- Words typed in the bar. With no search engine chosen, the browser's own search page
(`WebRoute.searchPageURL`), which nothing outside the browser sees. With one chosen in
Settings, its address for the words, routed as any typed address: in the tab when the
browser can read it, else the Outside page; never the system by itself. -/
def searchRoute (site : WebRoute.Site) (base search words : String) : WebRoute.Route :=
  match WebRoute.searchTemplate search with
  | some template => typedRoute (WebRoute.route site base (WebRoute.expandSearch template words))
  | none => .page "search" (WebRoute.searchPageURL words)

/-- Where an address typed in the bar goes (WebRoute): a URL as a link would, a
`:command` as `foafnaut:command/argument`, words by `searchRoute` with the search engine
`search` chosen in Settings ("" for none), and `:open URL` to the system: the one typed
command that asks for it. -/
def routeAddress (site : WebRoute.Site) (base input : String) (search : String := "") : WebRoute.Route :=
  let value := input.trimAscii.toString
  if (value.toList.take 9).map Char.toLower == WebRoute.foafnautPrefix || value.toList.map Char.toLower == "about:foafnaut".toList then typedRoute (WebRoute.routeAddress site base value) else
  match submit value with
  | .page url => typedRoute (WebRoute.route site base url)
  | .command name argument => typedRoute (WebRoute.commandRoute site name argument)
  | .search words => searchRoute site base search words
  | .system url => match WebRoute.route site base url with
    | .navigate address => .system address
    | .outside address => .system address
    | other => other

/-- The answer of the op `shellRoute` (docs/web/hub/foafnaut/link-route.mjs). -/
def routeJson : WebRoute.Route → JSON.Json
  | .page name url => .object [("route",.string "page"),("name",.string name),("url",.string url)]
  | .graph => .object [("route",.string "graph"),("url",.string WebRoute.graphURL)]
  | .navigate url => .object [("route",.string "navigate"),("url",.string url)]
  | .outside url => .object [("route",.string "outside"),("url",.string url)]
  | .system url => .object [("route",.string "system"),("url",.string url)]
  | .command name argument => .object [("route",.string "command"),("name",.string name),("argument",.string argument)]
  | .refuse url reason => .object [("route",.string "refuse"),("url",.string url),("reason",.string reason)]

/-- The answer of the older op `shellSubmit`: words are the browser's search page. -/
def Go.json : Go → JSON.Json
  | .page url => .object [("go",.string "page"),("url",.string url)]
  | .system url => .object [("go",.string "system"),("url",.string url)]
  | .command name argument => .object [("go",.string "command"),("name",.string name),("argument",.string argument)]
  | .search words => .object [("go",.string "page"),("url",.string (WebRoute.searchPageURL words))]

/-! ### Theorems: words typed in the bar go to no one -/

theorem link_not_system (href u : String) : link href ≠ .system u := by
  intro h
  unfold link at h
  split at h
  · split at h
    all_goals (try simp only [command] at h)
    all_goals (try split at h)
    all_goals simp at h
  · simp at h

/-- Text in the bar that is not a `:command` never goes to the system. -/
theorem submit_not_system (input u : String) (h : (input.trimAscii.toString).startsWith ":" = false) :
    submit input ≠ .system u := by
  intro hs
  unfold submit at hs
  simp only [h, Bool.false_eq_true, if_false] at hs
  split at hs
  · exact link_not_system _ _ hs
  · split at hs
    · exact link_not_system _ _ hs
    · simp at hs

/-- A typed address reaches the system only by `:open URL`. -/
theorem routeAddress_system_only_open (site : WebRoute.Site) (base input search u : String)
    (h : routeAddress site base input search = .system u) :
    ∃ url, submit (input.trimAscii.toString) = .system url := by
  have typed : ∀ r, typedRoute r ≠ .system u := by
    intro r; cases r <;> simp [typedRoute]
  unfold routeAddress at h
  dsimp only at h
  split at h
  · exact absurd h (typed _)
  · split at h
    · exact absurd h (typed _)
    · exact absurd h (typed _)
    · rename_i words _
      unfold searchRoute at h
      split at h
      · exact absurd h (typed _)
      · simp at h
    · rename_i url hs
      exact ⟨url, hs⟩

/-- With no search engine chosen, words typed in the bar open the browser's own search
page: a `foafnaut:` address, so no request carries them anywhere. -/
theorem words_stay_local (site : WebRoute.Site) (base input search words : String)
    (hs : WebRoute.searchTemplate search = none)
    (hw : submit (input.trimAscii.toString) = .search words)
    (hp : ((((input.trimAscii.toString).toList.take 9).map Char.toLower == WebRoute.foafnautPrefix) ||
      ((input.trimAscii.toString).toList.map Char.toLower == "about:foafnaut".toList)) = false) :
    routeAddress site base input search = .page "search" (WebRoute.searchPageURL words) := by
  simp only [routeAddress, hp, Bool.false_eq_true, if_false, hw, searchRoute, hs]

/-- No setting means no search engine: words never go into an outbound address. -/
theorem no_engine_by_default (site : WebRoute.Site) (base words : String) :
    searchRoute site base "" words = .page "search" (WebRoute.searchPageURL words) := by
  simp [searchRoute, WebRoute.no_default_search]

/-- The words reach a web address only through the template of the engine chosen. -/
theorem words_only_to_chosen (site : WebRoute.Site) (base search words : String) (r : WebRoute.Route)
    (h : searchRoute site base search words = r) (hl : ∀ n u, r ≠ .page n u) :
    ∃ template, WebRoute.searchTemplate search = some template ∧
      r = typedRoute (WebRoute.route site base (WebRoute.expandSearch template words)) := by
  unfold searchRoute at h
  split at h
  · rename_i template ht; exact ⟨template, ht, h.symm⟩
  · exact absurd h.symm (hl _ _)

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
  "</title><style>body{font-family:sans-serif;margin:12px;font-size:12px;line-height:16px;color:#203040;background:#f4f4ee}" ++
  "h1{margin:0;padding-bottom:8px;font-size:14px;line-height:20px;color:#a0186a}h2{margin:0;padding-bottom:8px;font-size:12px;color:#a0186a}p{margin:0}</style></head><body><h1>" ++
  escapeText (kind ++ " of " ++ url) ++ "</h1>" ++ cut ++
  String.join ((shown.splitOn "\n").map sourceLine) ++ "</body></html>"

/-! ### The browser's own pages for words and for other programs

Written here, by the browser (AGENT-BRIEF: the browser's own words are Lean). -/

/-- Text for HTML: `&`, `<`, `>` and `"` escaped; controls dropped; other characters kept. -/
def htmlText (value : String) : String :=
  String.join (value.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;" else if c == '"' then "&quot;"
    else if c.toNat < 32 || c.toNat == 127 then "" else c.toString)

def ownPageStyle : String :=
  "<style>body{margin:24px;font-family:system-ui,sans-serif;font-size:16px;line-height:24px;color:#1f2328;background:#f7f8fb}" ++
  "h1{margin:0 0 12px;font-size:22px;line-height:30px;color:#184078}h2{margin:20px 0 8px;font-size:18px;line-height:26px;color:#184078}" ++
  "p{margin:0 0 12px;max-width:640px}.url{font-family:monospace;overflow-wrap:anywhere;color:#3b4652}.dim{color:#5d666c}" ++
  ".go{display:inline-block;margin-top:8px;padding:10px 18px;border-radius:20px;background:#0b57d0;color:#ffffff;font-weight:bold;text-decoration:none}</style>"

/-- The English Wikipedia article address for the words (the Hub reads it in the tab
through the Wikimedia REST API, which allows it; the native browser reads it directly). -/
def wikipediaURL (words : String) : String := "https://en.wikipedia.org/wiki/" ++ WebRoute.encodeTitle words

/-- The page `foafnaut:search/WORDS`: what was typed, and the choices. `found` is (kind,
url, title) from the browser's own data (`WebState.searchFound` and the open tabs);
`stateOn` says whether history and bookmarks are kept in this window; `search` is the
search engine chosen in Settings. Nothing on this page is fetched to show it; each link
is a choice the person makes. -/
def searchPage (words : String) (found : List (String × String × String)) (stateOn : Bool) (search : String) : String :=
  let shown := htmlText words
  let item := fun (e : String × String × String) =>
    let (kind, url, title) := e
    s!"<p><a href=\"{htmlText url}\">{htmlText (if title.isEmpty then url else title)}</a> <span class=\"dim\">{kind}</span><br><span class=\"url\">{htmlText url}</span></p>"
  let local_ :=
    if !found.isEmpty then String.join (found.map item)
    else if stateOn then "<p>Nothing in your open tabs, bookmarks or history matches.</p>"
    else "<p>Nothing in your open tabs matches. History and bookmarks are not kept in this window.</p>"
  let engine := match WebRoute.searchTemplate search with
    | some template =>
      s!"<p><a class=\"go\" href=\"{htmlText (WebRoute.expandSearch template words)}\">Search with {htmlText (WebRoute.searchName search)}</a></p>" ++
      "<p>The search engine you chose in <a href=\"foafnaut:settings\">Settings</a> gets the words when you press the button.</p>"
    | none =>
      "<p>No search engine is chosen, so the words were sent to no one. " ++
      "<a href=\"foafnaut:settings\">Choose a search engine in Settings</a>; until you do, words typed in the address bar open this page.</p>"
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>" ++ shown ++ " (search)</title>" ++ ownPageStyle ++ "</head><body>" ++
  s!"<h1>You typed: {shown}</h1>" ++
  "<p>This page was made inside Foafnaut. The words have not left this browser.</p>" ++
  "<h2>In this browser</h2>" ++ local_ ++
  "<h2>Look it up</h2>" ++
  s!"<p><a class=\"go\" href=\"{htmlText (wikipediaURL words)}\">Look it up on Wikipedia</a></p>" ++
  "<p>Opens the English Wikipedia article with this title, read inside Foafnaut. Wikipedia gets the words when you press the button.</p>" ++
  "<h2>Search the web</h2>" ++ engine ++ "</body></html>"

/-- The Settings section (`<!--foafnaut:search-->`): the choice now, a button for each
engine and for none, and how to give an engine of one's own. None is chosen by default and
the list is in alphabetical order. -/
def searchChoicesHTML (setting : String) : String :=
  let chosen := WebRoute.searchSetting setting
  let button := fun (id label : String) =>
    let cls := if id == chosen || (id == "none" && chosen.isEmpty) then " class=\"chosen\"" else ""
    s!"<a{cls} href=\"foafnaut:search-engine/{id}\">{htmlText label}</a>"
  s!"<h2 class=\"size\">Search engine: {htmlText (WebRoute.searchName chosen)}</h2>" ++
  "<p>Words typed in the address bar that are not an address go to no one until you choose a search engine here. " ++
  "Until then they open a page of this browser that looks in your open tabs, bookmarks and history, and offers Wikipedia. " ++
  "Once you choose one, the words you type go to it and to no one else.</p>" ++
  "<p class=\"presets\">" ++ button "none" "None" ++ " " ++
  " ".intercalate (WebRoute.searchEngines.map fun e => button e.id e.name) ++ "</p>" ++
  "<p>Your own: type :search-engine and an address with %s where the words go, for example " ++
  "<span class=\"url\">:search-engine https://example.org/search?q=%s</span></p>"

/-- The Outside page for an address that leaves the browser only by a press: a web
address the tab can not read (the Hub: the site does not allow it), Textnaut's own Hub
page, or another program's address (`mailto:`, `tel:`, `sms:`). Its one button is a link to
the same address; while this page is shown, that link is the press (`WebRoute.Site.outside`)
and the host hands the address to the system. -/
def outsidePage (url : String) (hub textnaut : Bool) : String :=
  let web := url.startsWith "http://" || url.startsWith "https://"
  let (heading, why, button) :=
    if textnaut then ("Textnaut opens in its own page",
      "<p>Textnaut has its own page on the Hub; it does not open inside this one.</p>", "Open in a new browser tab")
    else if web && hub then ("This site can not be read from inside the Hub page",
      "<p>The browser this page runs in lets a page read another site only when that site allows it (cross-origin rules, CORS), and this one does not. " ++
      "The Hub keeps copies of some openly licensed pages, but not of this one. The Foafnaut app on a computer, and Textnaut in a terminal, read it directly.</p>",
      "Open in a new browser tab")
    else if web then ("This address opens in your default browser",
      "<p>Foafnaut opens it in your default browser only if you press the button.</p>", "Open in your browser")
    else ("This link opens another program",
      "<p>This address belongs to another program (mail, phone or messages). Foafnaut opens it only if you press the button.</p>",
      if url.startsWith "mailto:" then "Open in your mail app" else if url.startsWith "tel:" then "Open in your phone app" else "Open in your messages app")
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>Another site</title>" ++ ownPageStyle ++ "</head><body>" ++
  s!"<h1>{heading}</h1><p class=\"url\">{htmlText url}</p>{why}" ++
  s!"<p><a class=\"go\" href=\"{htmlText url}\">{button}</a></p>" ++
  "<p>Back (the arrow, or Command-Left) returns to the page before.</p></body></html>"

#guard ((searchPage "a <b>" [] true "").splitOn "&lt;b&gt;").length == 3
#guard ((searchPage "lean browser" [] true "").splitOn "duckduckgo").length == 1
#guard ((searchPage "lean browser" [] true "").splitOn "https://en.wikipedia.org/wiki/lean_browser").length == 2
#guard ((searchChoicesHTML "").splitOn "class=\"chosen\" href=\"foafnaut:search-engine/none\"").length == 2
#guard ((searchChoicesHTML "mojeek").splitOn "class=\"chosen\"").length == 2
#guard ((outsidePage "mailto:a@example.org" false false).splitOn "Open in your mail app").length == 2

/-! ### Editing the find text -/

/-- The longest text find takes. -/
def maxFind : Nat := 256

/-- What a key or typed text in the find field asks: the text after it, and a step. -/
inductive FindStep where
  | none
  | next
  | previous
  | close
  deriving Repr, BEq, DecidableEq

def FindStep.name : FindStep → String
  | .none => "none" | .next => "next" | .previous => "previous" | .close => "close"

/-- Typed text is added at the end (line breaks and control characters dropped, at most
`maxFind` characters); Delete (key 51) removes the last grapheme; Return and Enter (36, 76)
go to the next match, with Shift the one before; Escape (53) closes find. The field has no
caret to move: other keys change nothing. -/
def findEdit (query : String) (typed : Option String) (code modifiers : Nat) : String × FindStep :=
  match typed with
  | some value => ((String.ofList ((query ++ clean value).toList.take maxFind)),.none)
  | none =>
    if code == 51 then (String.ofList (query.toList.take (graphemeBefore query query.length)),.none)
    else if code == 36 || code == 76 then (query,if has modifiers shiftBit then .previous else .next)
    else if code == 53 then (query,.close)
    else (query,.none)

#guard findEdit "ab" (some "c") 0 0 == ("abc",.none)
#guard findEdit "ab" none 51 0 == ("a",.none)
#guard findEdit "" none 51 0 == ("",.none)
#guard findEdit "ab" none 36 0 == ("ab",.next) && findEdit "ab" none 36 1 == ("ab",.previous)
#guard findEdit "ab" none 53 0 == ("ab",.close)
#guard (findEdit (String.ofList (List.replicate 300 'x')) (some "y") 0 0).1.length == maxFind

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
    loading := flag j "loading",scale := max 1 (nat j "scale" 1),theme := str j "theme" "next",pages := nat j "pages",script := str j "script" "",
    dark := flag j "dark",
    scroll := nat j "scroll", pressed := str j "pressed",
    collapse := min 100 (nat j "collapse"), collapsible := flag j "collapsible",
    swipe := match j.field? "swipe" with
      | some (.number value) => max (-100) (min 100 (value.toInt?.getD 0)) | _ => 0,
    menu := flag j "menu",
    context := (match str j "context" with | "link" => "link" | "page" => "page" | _ => ""),
    contextLink := str j "contextLink", contextSelection := flag j "contextSelection",
    findOpen := flag j "findOpen",find := String.ofList ((str j "find").toList.take maxFind),findFocused := flag j "findFocused",
    findCount := nat j "findCount",findCurrent := nat j "findCurrent" }

private def Snapshot.json (v : Snapshot) : JSON.Json :=
  .object [("address",.string v.address),("cursor",.number (toString v.cursor)),("anchor",.number (toString v.anchor))]

/-- The edit state the host keeps and sends back in `shell`. -/
def Shell.editJson (s : Shell) : JSON.Json :=
  .object [("address",.string s.address),("cursor",.number (toString s.cursor)),("anchor",.number (toString s.anchor)),
    ("undo",(s.undo.map Snapshot.json).getD .null),("redo",(s.redo.map Snapshot.json).getD .null),("typing",.bool s.typing),
    ("menu",.bool s.menu),("context",.string s.context),("contextLink",.string s.contextLink),
    ("contextSelection",.bool s.contextSelection)]

#guard submit "http://example.org/" == .page "http://example.org/"
#guard submit "example.org" == .page "https://example.org"
#guard submit "github.com/danbri" == .page "https://github.com/danbri"
#guard submit "lean browser" == .search "lean browser"
#guard (submit "lean browser").json.toString == "{\"go\":\"page\",\"url\":\"foafnaut:search/lean+browser\"}"
#guard submit ":zoom 150" == .command "zoom" "150"
#guard submit ":source" == .command "source" ""
#guard submit ":sparql SELECT ?s WHERE { ?s a <x:y> }" == .command "sparql" "q=SELECT+%3Fs+WHERE+%7B+%3Fs+a+%3Cx%3Ay%3E+%7D"
#guard link "foafnaut:sparql/q=ASK+%7B%7D" == .command "sparql" "q=ASK+%7B%7D"
#guard (sourcePage "Source" "file:///a.html" "<p>\n  x</p>").contains '&'
#guard ((sourcePage "Source" "a" (String.ofList (List.replicate 8001 'x'))).splitOn "first 8000").length == 2
#guard submit ":open https://x.org" == .system "https://x.org"
#guard link "https://github.com/danbri/factoidal-core" == .page "https://github.com/danbri/factoidal-core"
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
-- Words: the browser's own search page, with no search engine chosen; the chosen one's address otherwise.
#guard routeAddress hubSite "https://x.org/p/index.html" "lean browser" == .page "search" "foafnaut:search/lean+browser"
#guard routeAddress hubSite "https://x.org/p/index.html" "lean browser" "none" == .page "search" "foafnaut:search/lean+browser"
#guard routeAddress hubSite "https://x.org/p/index.html" "lean browser" "mojeek" == .outside "https://www.mojeek.com/search?q=lean+browser"
#guard routeAddress {} "file:///p/index.html" "lean browser" "mojeek" == .navigate "https://www.mojeek.com/search?q=lean+browser"
#guard routeAddress {} "file:///p/index.html" "lean browser" "https://example.org/s?q=%s" == .navigate "https://example.org/s?q=lean+browser"
#guard routeAddress {hubSite with outside := "https://www.mojeek.com/search?q=a"} "https://www.mojeek.com/search?q=a" "a" "mojeek" == .outside "https://www.mojeek.com/search?q=a"
-- Hosts the old list sent out: the tab (native) or the Outside page (Hub).
#guard routeAddress {} "file:///p/index.html" "github.com/danbri" == .navigate "https://github.com/danbri"
#guard routeAddress hubSite "https://x.org/p/index.html" "github.com/danbri" == .outside "https://github.com/danbri"
#guard routeAddress hubSite "https://x.org/p/index.html" ":search-engine mojeek" == .command "search-engine" "mojeek"
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
-- The context menu (issue 1031): a link menu, a page menu; any edit closes it; JSON keeps it.
private def linkMenu : Shell := ({} : Shell).openContext (some "https://x.org/l") false
private def pageMenu : Shell := ({canForward := true} : Shell).openContext none true
#guard (menuActions linkMenu 1000).map (·.action) == ["openTab","copy"]
#guard (menuActions linkMenu 1000).all (·.text == some "https://x.org/l")
-- Back is shown but asks nothing with no page before; Forward, Reload, View source and Copy act.
#guard (menuActions pageMenu 1000).map (·.action) == ["forward","reload","viewSource","copySelection"]
#guard ((boxes pageMenu 1000).filter (fun b => menuItemNames.contains b.name)).length == 5
#guard (menuActions linkMenu 1000).all fun a => a.rect.1+a.rect.2.2.1 ≤ 1000
#guard (Shell.ofJson linkMenu.editJson).context == "link" && (Shell.ofJson pageMenu.editJson).contextSelection
#guard (linkMenu.edit "closeMenu").1.context == "" && (linkMenu.typed "x").context == "" && (linkMenu.key 123).context == ""
#guard menuActions (menuOpen.openContext none false) 1000 |>.all (·.control != "copyAddress")
#guard reprStr (nodes linkMenu 1000) != reprStr (nodes {} 1000)

-- The flat look (2026-11-16) is the default; "classic" keeps the NeXT bevels. The system's dark
-- mode turns the default dark; an explicit "light" or "dark" setting wins over it.
#guard reprStr (nodes {dark := true} 1000) != reprStr (nodes {} 1000)
#guard reprStr (nodes {theme := "dark"} 1000) == reprStr (nodes {dark := true} 1000)
#guard reprStr (nodes {theme := "light",dark := true} 1000) == reprStr (nodes {} 1000)
#guard reprStr (nodes {theme := "classic"} 1000) != reprStr (nodes {} 1000)
#guard (Shell.ofJson (.object [("dark",.bool true)])).dark && !(Shell.ofJson (.object [])).dark
-- Loading draws the accent bar in the flat look too, and a pressed control a circle.
#guard reprStr (nodes {loading := true} 1000) != reprStr (nodes {} 1000)
#guard reprStr (nodes {pressed := "settings"} 1000) != reprStr (nodes {} 1000)

/-- Kind: cost theorem. Says: the look (theme and the system's dark mode) changes no chrome
height, so a theme change or a switch to dark lays nothing out again. -/
theorem fullHeight_look (s : Shell) (theme : String) (dark : Bool) (width : Nat) :
    fullHeight {s with theme,dark} width = fullHeight s width := rfl

theorem height_look (s : Shell) (theme : String) (dark : Bool) (width : Nat) :
    height {s with theme,dark} width = height s width := rfl

/-- Kind: behaviour theorem. Says: the look changes no hit test: a press lands on the same
control in every theme, light or dark. -/
theorem hit_look (s : Shell) (theme : String) (dark : Bool) (width x y : Nat) :
    hit {s with theme,dark} width x y = hit s width x y := rfl

end WebShell
