import WebRender

/-! The browser's own face: tabs, the address bar and its buttons, drawn into the
same scene as the page, so one WebGPU pass draws the window. All of it is pixel
art from the engine's bitmap font: NeXT bevels, arcade lettering.

The host keeps the `Shell` value between calls and sends it back. It makes no
decision here: Lean says what a click, a key or an address means. -/
namespace WebShell
open L4Factoidal

structure Tab where
  title : String := ""
  deriving Repr, BEq

structure Shell where
  tabs : Array Tab := #[{}]
  active : Nat := 0
  address : String := ""
  cursor : Nat := 0
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

private def hex (r g b : Nat) : Rendering.Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
private def next : Theme :=
  ⟨hex 170 170 170,hex 255 255 255,hex 85 85 85,hex 0 0 0,hex 255 255 255,hex 0 0 0,hex 128 128 128,hex 32 32 32,hex 224 32 138,hex 255 196 0⟩
private def arcade : Theme :=
  ⟨hex 34 38 54,hex 84 92 128,hex 10 12 20,hex 216 240 255,hex 10 12 20,hex 120 255 170,hex 20 23 34,hex 150 160 200,hex 57 255 136,hex 255 196 0⟩
private def themeOf (s : Shell) : Theme := if s.theme == "arcade" then arcade else next

/-! ### Measures, in backing pixels -/

private def unit (s : Shell) : Nat := max 1 s.scale
/-- One lettering pixel: 2 backing pixels at scale 1, 3 at scale 2. -/
private def dot (s : Shell) : Nat := (3*unit s+1)/2
private def narrow (s : Shell) (width : Nat) : Bool := width/unit s < 560
private def tabRow (s : Shell) (width : Nat) : Nat := if narrow s width then 0 else 26*unit s
private def navRow (s : Shell) : Nat := 36*unit s
private def edge (s : Shell) : Nat := 3*unit s
def height (s : Shell) (width : Nat) : Nat := tabRow s width+navRow s+edge s

private structure Box where
  name : String
  x : Nat
  y : Nat
  w : Nat
  h : Nat

private def tabWidth (s : Shell) (width : Nat) : Nat :=
  let room := width-(90*unit s)
  min (180*unit s) (room/max 1 s.tabs.size)

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
  let tail := if narrow s width then 2*button+8*u+pad else 2*button+8*u+pad
  out := out ++ [⟨"address",x,by_,width-x-tail,button⟩]
  out := out ++ [⟨if narrow s width then "tabs" else "source",width-pad-2*button-2*u,by_,button,button⟩]
  out := out ++ [⟨"settings",width-pad-button,by_,button,button⟩]
  return out

private def Box.contains (b : Box) (x y : Nat) : Bool :=
  x >= b.x && x < b.x+b.w && y >= b.y && y < b.y+b.h

/-- The control under a point; none means the page. Close wins over its tab. -/
def hit (s : Shell) (width x y : Nat) : Option String :=
  if y >= height s width then none else
  match ((boxes s width).filter (·.contains x y)).getLast? with
  | some box => some box.name
  | none => some "chrome"

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

private def tabNodes (s : Shell) (t : Theme) (width : Nat) (box : Box) (index : Nat) : List Rendering.Node :=
  let u := unit s
  let active := index == s.active
  let face := if active then t.base else t.back
  let title := ((s.tabs[index]?).map (·.title)).getD ""
  -- Arcade capitals: the bitmap font is at its best here.
  let title := (if title.isEmpty then "new tab" else title).toUpper
  let room := box.w-(if s.tabs.size > 1 then 32*u else 14*u)
  let colour := if active then t.ink else t.muted
  let mark := if active then [paint t.accent (box.x+u) (box.y+u) (box.w-2*u) (2*u)] else []
  let _ := width
  bevel s t face true box.x box.y box.w (box.h+(if active then u else 0)) ++ mark ++
    text colour (fit s title room) (box.x+7*u) (box.y+(box.h-7*dot s)/2+u) (dot s)

private def addressNodes (s : Shell) (t : Theme) (box : Box) : List Rendering.Node :=
  let u := unit s
  let size := dot s
  let textX := box.x+22*u
  let textY := box.y+(box.h-7*size)/2
  let room := box.w-28*u
  let prompt := text t.accent ">" (box.x+8*u) textY size
  let shown := if s.focused then fitEnd s s.address room else fitEnd s s.address room
  let body := if s.address.isEmpty && !s.focused
    then text t.dark (fit s "url, search or :command" room) textX textY size
    else text t.wellInk shown textX textY size
  let cursorColumn := min (shown.length) (s.cursor+shown.length-min s.address.length (s.address.length))
  let cursor := if s.focused then [paint t.accent (textX+cursorColumn*charWidth s) (textY-u) (5*size) (7*size+2*u)] else []
  bevel s t t.well false box.x box.y box.w box.h ++ prompt ++ cursor ++ body

/-- The bar under the chrome: a thin accent line, or a level bar while loading. -/
private def edgeNodes (s : Shell) (t : Theme) (width : Nat) : List Rendering.Node := Id.run do
  let y := height s width-edge s
  if !s.loading then return [paint t.dark 0 y width (unit s),paint t.accent 0 (y+unit s) width (edge s-unit s)]
  let block := 12*unit s
  let mut out := [paint t.dark 0 y width (edge s)]
  for i in [:width/block] do
    if i % 2 == 0 then out := paint t.accent (i*block) y (block-2*unit s) (edge s) :: out
  return out

/-- The chrome as scene nodes. It is drawn over the page. -/
def nodes (s : Shell) (width : Nat) : List Rendering.Node := Id.run do
  let t := themeOf s
  let u := unit s
  let row := tabRow s width
  let mut out := [paint t.back 0 0 width row,paint t.base 0 row width (navRow s)]
  out := out ++ [paint t.light 0 row width u]
  for box in boxes s width do
    match box.name.splitOn ":" with
    | ["tab",i] => out := out ++ tabNodes s t width box (i.toNat?.getD 0)
    | ["close",_] => out := out ++ iconAt s t.ink "close" box
    | ["newTab"] => out := out ++ bevel s t t.base true box.x box.y box.w box.h ++ iconAt s t.ink "newTab" box
    | ["address"] => out := out ++ addressNodes s t box
    | ["tabs"] =>
      out := out ++ bevel s t t.base true box.x box.y box.w box.h ++
        text t.ink (toString s.tabs.size) (box.x+(box.w-5*dot s)/2) (box.y+(box.h-7*dot s)/2) (dot s)
    | [name] =>
      let enabled := (name != "back" || s.canBack) && (name != "forward" || s.canForward)
      let shape := if name == "reload" && s.loading then "stop" else name
      out := out ++ bevel s t t.base true box.x box.y box.w box.h ++
        iconAt s (if enabled then t.ink else t.dark) shape box
    | _ => pure ()
  if !narrow s width then
    let label := toString s.pages
    let x := width-(label.length*charWidth s)-16*u
    let y := (row-7*dot s)/2+u
    out := out ++ bitmapNodes t.coin (icon "coin") 7 (x-10*dot s) y (dot s) ++ text t.coin label x y (dot s)
  return out ++ edgeNodes s t width

/-- Put a page rendered below the chrome and the chrome into one scene. -/
def compose (s : Shell) (page : Rendering.Scene) (width height' : Nat) : Rendering.Scene :=
  let top := Float.ofNat (height s width)-Float.ofNat s.scroll
  let shift : Rendering.Transform := ⟨1,0,0,1,0,top⟩
  {page with
    height := height'
    mapping := {page.mapping with viewportHeight := Float.ofNat height'}
    tree := [.group none shift page.tree] ++ nodes s width
    links := page.links.map (fun link => {link with y := link.y+top})}

/-! ### Editing the address -/

private def insertAt (value : String) (at_ : Nat) (extra : String) : String :=
  String.ofList (value.toList.take at_) ++ extra ++ String.ofList (value.toList.drop at_)
private def removeAt (value : String) (at_ : Nat) : String :=
  String.ofList (value.toList.take at_ ++ value.toList.drop (at_+1))

def Shell.typed (s : Shell) (value : String) : Shell :=
  let clean := String.ofList (value.toList.filter (fun c => c.toNat >= 32 && c.toNat != 127))
  if s.address.length+clean.length > 2048 then s else
  {s with address := insertAt s.address s.cursor clean,cursor := s.cursor+clean.length}

/-- macOS key codes that edit: delete, forward delete, left, right, home, end. -/
def Shell.key (s : Shell) (code : Nat) : Shell :=
  match code with
  | 51 => if s.cursor == 0 then s else {s with address := removeAt s.address (s.cursor-1),cursor := s.cursor-1}
  | 117 => {s with address := removeAt s.address s.cursor}
  | 123 => {s with cursor := s.cursor-1}
  | 124 => {s with cursor := min s.address.length (s.cursor+1)}
  | 115 => {s with cursor := 0}
  | 119 => {s with cursor := s.address.length}
  | _ => s

/-! ### What an address and a link mean -/

/-- Pages this engine can not draw yet go to the host's default browser. -/
def externalHosts := ["github.com","www.github.com","duckduckgo.com"]

private def hostOf (url : String) : String :=
  match url.splitOn "://" with
  | [_,rest] => ((rest.splitOn "/").headD "").toLower
  | _ => ""

inductive Go where
  | page (url : String)
  | system (url : String)
  | command (name : String) (argument : String)
  deriving Repr, BEq

def link (href : String) : Go :=
  if href.startsWith "foafnaut:" then
    match ((href.drop 9).toString.splitOn "/") with
    | [name,argument] => .command name argument
    | [name] => .command name ""
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
    | [name] => .command name ""
    | ["open",url] => .system url
    | name::argument::_ => .command name argument
    | [] => .command "help" ""
  else if (value.splitOn "://").length > 1 || value.startsWith "file:" || value.startsWith "about:" then link value
  else if !value.contains ' ' && value.contains '.' then link ("https://" ++ value)
  else .system ("https://duckduckgo.com/?q=" ++ encodeQuery value)

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

def Shell.ofJson (j : JSON.Json) : Shell :=
  let tabs : Array Tab := match j.field? "tabs" with
    | some (.array items) => (items.map (fun item => ({title := str item "title"} : Tab))).toArray
    | _ => #[{}]
  let tabs := if tabs.isEmpty then #[{}] else tabs
  let address := str j "address"
  { tabs,active := min (nat j "active") (tabs.size-1),address,cursor := min (nat j "cursor") address.length,
    focused := flag j "focused",canBack := flag j "canBack",canForward := flag j "canForward",
    loading := flag j "loading",scale := max 1 (nat j "scale" 1),theme := str j "theme" "next",pages := nat j "pages",
    scroll := nat j "scroll" }

def Shell.editJson (s : Shell) : JSON.Json :=
  .object [("address",.string s.address),("cursor",.number (toString s.cursor))]

#guard submit "http://example.org/" == .page "http://example.org/"
#guard submit "example.org" == .page "https://example.org"
#guard submit "github.com/danbri" == .system "https://github.com/danbri"
#guard submit "lean browser" == .system "https://duckduckgo.com/?q=lean+browser"
#guard submit ":zoom 150" == .command "zoom" "150"
#guard submit ":source" == .command "source" ""
#guard (sourcePage "Source" "file:///a.html" "<p>\n  x</p>").contains '&'
#guard ((sourcePage "Source" "a" (String.ofList (List.replicate 8001 'x'))).splitOn "first 8000").length == 2
#guard submit ":open https://x.org" == .system "https://x.org"
#guard link "https://github.com/danbri/factoidal-core" == .system "https://github.com/danbri/factoidal-core"
#guard link "foafnaut:theme/arcade" == .command "theme" "arcade"
#guard link "status.html" == .page "status.html"
#guard (({address := "ac",cursor := 1} : Shell).typed "b").address == "abc"
#guard (({address := "abc",cursor := 3} : Shell).key 51).address == "ab"
#guard (({address := "abc",cursor := 0} : Shell).key 123).cursor == 0
#guard hit {} 1000 10 1000 == none
#guard hit {} 1000 10 40 == some "back"
#guard hit {} 300 10 10 == some "back"
#guard hit {tabs := #[{},{}]} 1000 40 12 == some "tab:0"
#guard height {} 1000 > height {} 300

end WebShell
