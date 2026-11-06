import L4Factoidal.Rendering.Scene
import L4Factoidal.DOM.OfHtml
import Std.Data.TreeMap

/-! Computed styles for an explicitly bounded CSS block/inline profile.
Selectors: universal, type, id and class compound selectors, selector lists and
descendants. CSS error handling applies: what this profile does not understand
is dropped, and the rest of the sheet still applies. A page is never refused
for its style sheet. -/
namespace L4Factoidal.Rendering.CSS
open DOM
private def trim (s : String) := s.trimAscii.toString
inductive Length where
  | auto | px (value : Float) | percent (value : Float)
  | vw (value : Float) | vh (value : Float)
  deriving Repr
structure Edges where
  top : Float := 0
  right : Float := 0
  bottom : Float := 0
  left : Float := 0
  deriving Repr
inductive Display where | none | block | inline | inlineBlock
  deriving Repr, BEq
structure Computed where
  display : Display := .inline
  width : Length := .auto
  height : Length := .auto
  margin : Edges := {}
  padding : Edges := {}
  color : Color := ⟨0,0,0⟩
  background : Option Color := none
  fontSize : Float := 16
  fontFamily : String := "monospace"
  lineHeight : Float := 19.2
  lineHeightFactor : Option Float := some 1.2
  visible : Bool := true
  clipOverflow : Bool := false
  underline : Bool := false
  decorationColor : Option Color := none
  /-- Line breaks in the source are kept (pre and its older relatives). -/
  preformatted : Bool := false
  deriving Repr
instance : Inhabited Computed := ⟨{}⟩

/-- Properties consumed by HTML style/layout, including an embedded SVG root.
The DOM-to-SVG adapter uses this same list to avoid a second interpretation. -/
def htmlProperties : List String :=
  ["display","width","height","margin","padding",
   "margin-top","margin-right","margin-bottom","margin-left",
   "padding-top","padding-right","padding-bottom","padding-left",
   "color","background","background-color","font-size","font-family",
   "line-height","visibility","overflow","text-decoration","text-decoration-line"]

structure Declaration where
  property : String
  value : String
  important : Bool := false
  deriving Repr
structure Compound where
  tag : Option String := none
  id : Option String := none
  classes : List String := []
  deriving Repr
structure Selector where
  /-- Rightmost compound first; ancestors follow. -/
  parts : List Compound
  specificity : Nat × Nat × Nat
  deriving Repr
structure Rule where
  selectors : List Selector
  declarations : List Declaration
  deriving Repr

def attrValue (n : DOM.Node) (key : String) : String :=
  ((n.attrs.find? fun a => a.ns.isNone && a.lname == key).map (·.value)).getD ""
def hasAttribute (n : DOM.Node) (key : String) : Bool :=
  n.attrs.any (fun a => a.ns.isNone && a.lname == key)

private def words (s : String) : List String :=
  (s.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " ").splitOn " " |>.filter (· != "")
private def ident (s : String) : Bool := !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '-' || c == '_')
private def compound (s : String) : Except String Compound := do
  let chunks := s.toList.foldl (fun (acc : List String) c =>
    if c == '#' || c == '.' then String.singleton c :: acc
    else match acc with | [] => [String.singleton c] | a::rest => (a.push c)::rest) []
  let mut out : Compound := {}
  for chunk in chunks.reverse do
    if chunk.startsWith "#" then
      let value := (chunk.drop 1).toString
      if !ident value || out.id.isSome then throw "unsupported CSS id selector"
      out := {out with id := some value}
    else if chunk.startsWith "." then
      let value := (chunk.drop 1).toString
      if !ident value then throw "unsupported CSS class selector"
      out := {out with classes := value :: out.classes}
    else if chunk == "*" then pure ()
    else if ident chunk then out := {out with tag := some chunk.toLower}
    else throw s!"unsupported CSS selector: {s}"
  return out
private def selector (s : String) : Except String Selector := do
  let parts ← (words (trim s)).mapM compound
  if parts.isEmpty || parts.length > 16 then throw "CSS selector exceeds supported depth"
  let specificity := parts.foldl (fun (n : Nat × Nat × Nat) p =>
    (n.1 + (if p.id.isSome then 1 else 0), n.2.1 + p.classes.length,
      n.2.2 + (if p.tag.isSome then 1 else 0))) (0,0,0)
  return ⟨parts.reverse,specificity⟩

private def expandEdges (key value : String) (important : Bool) : Except String (List Declaration) := do
  let values ← match words value with
    | [a] => pure [a,a,a,a]
    | [a,b] => pure [a,b,a,b]
    | [a,b,c] => pure [a,b,c,b]
    | [a,b,c,d] => pure [a,b,c,d]
    | _ => throw "CSS edge shorthand requires one to four values"
  return (["top","right","bottom","left"].zip values).map fun (side,v) =>
    ⟨key ++ "-" ++ side,v,important⟩

/-- A declaration this profile can not read is dropped; the others stand. -/
def declarations (s : String) : Except String (List Declaration) := do
  let mut out : List Declaration := []
  for item in s.splitOn ";" do
    let item := trim item
    if let key::first::more := item.splitOn ":" then
      let value := trim (":".intercalate (first::more))
      let important := value.endsWith "!important"
      let value := if important then trim ((value.dropEnd 10).toString) else value
      let key := (trim key).toLower
      let key := if key == "background" then "background-color" else key
      let expanded := if ["margin","padding"].contains key then
          (expandEdges key value important).toOption.getD []
        else [⟨key,value,important⟩]
      for declaration in expanded do out := declaration :: out
  return out.reverse

/-- CSS comments are removed before tokenizing this deliberately small grammar.
A comment that never closes runs to the end of the input. -/
private def comments (s : String) : String := Id.run do
  let pieces := s.splitOn "/*"
  let mut out := pieces.headD ""
  for p in pieces.drop 1 do
    if let _::first::more := p.splitOn "*/" then out := out ++ "*/".intercalate (first::more)
  return out

/-- The top level of a sheet, as (prelude, block) pairs. Blocks nest inside
at-rules and strings hide braces, so this counts them. A sheet that stops early
closes itself, as CSS says. One pass over the characters: no recursion. -/
private def topLevel (source : String) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  let mut prelude := ""
  let mut body := ""
  let mut depth := 0
  let mut quote : Option Char := none
  let mut escaped := false
  for c in source.toList do
    let structural := quote.isNone && (c == '{' || c == '}' || (c == ';' && depth == 0))
    if let some q := quote then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == q then quote := none
    else if c == '"' || c == '\'' then quote := some c
    if !structural then
      if depth == 0 then prelude := prelude.push c else body := body.push c
    else if c == '{' then
      if depth > 0 then body := body.push c
      depth := depth+1
    else if c == '}' then
      if depth == 0 then prelude := ""
      else if depth == 1 then
        out := (prelude,body) :: out
        prelude := ""
        body := ""
        depth := 0
      else
        body := body.push c
        depth := depth-1
    else if (trim prelude).startsWith "@" then prelude := ""
    else prelude := prelude.push c
  if depth > 0 then out := (prelude,body) :: out
  return out.reverse

/-- At-rules are skipped whole, and a rule with a selector this profile can not
read is dropped whole, as CSS drops an invalid selector list. Only the first
131072 characters of a sheet are read. -/
def parse (source : String) : Except String (List Rule) := do
  let mut out : List Rule := []
  for (head,body) in topLevel (comments (source.take 131072).toString) do
    if !(trim head).startsWith "@" then
      if let .ok selectors := (head.splitOn ",").mapM selector then
        out := ⟨selectors,← declarations body⟩ :: out
  return out.reverse
private def selectorMatchesCompound (n : DOM.Node) (s : Compound) : Bool :=
  n.type == .element && (s.tag.map (· == n.lname)).getD true &&
    (s.id.map (· == attrValue n "id")).getD true &&
    s.classes.all ((words (attrValue n "class")).contains ·)
private def matchAncestors (dom : Dom) : Nat → Option Nat → Compound → Option Nat
  | 0, _, _ => none
  | _+1, none, _ => none
  | f+1, some id, sel =>
    let n := dom.get id
    if selectorMatchesCompound n sel then some id else matchAncestors dom f n.parent sel
private def selectorMatchesParts (dom : Dom) : List Compound → Option Nat → Bool
  | [], _ => true
  | sel::rest, ancestor => match matchAncestors dom (dom.size+1) ancestor sel with
    | none => false
    | some id => selectorMatchesParts dom rest (dom.get id).parent

def selectorMatches (dom : Dom) (id : Nat) (sel : Selector) : Bool :=
  match sel.parts with
  | [] => false
  | head::rest => selectorMatchesCompound (dom.get id) head && selectorMatchesParts dom rest (dom.get id).parent

/-- Strict finite decimal conversion for CSS lengths; exponent syntax is outside
this first profile, and malformed declarations are refused. -/
def number (source : String) : Except String Float := do
  let s := trim source
  let negative := s.startsWith "-"
  let s := if negative || s.startsWith "+" then (s.drop 1).toString else s
  if s.length > 24 || s.isEmpty then throw "unsupported CSS number"
  let parts := s.splitOn "."
  if parts.length > 2 || parts.any (fun p => !p.toList.all Char.isDigit) || parts.all String.isEmpty then throw "invalid CSS number"
  let whole := (parts.headD "").toNat?.getD 0
  let fraction := parts[1]?.getD ""
  let scale := fraction.toList.foldl (fun (n : Float) _ => n*10) 1
  let value := Float.ofNat whole + Float.ofNat (fraction.toNat?.getD 0)/scale
  let value := if negative then -value else value
  if !value.isFinite || value.abs > 1000000 then throw "CSS number exceeds finite range"
  return value

def length (s : String) : Except String Length := do
  let s := trim s
  if s == "auto" then return .auto
  if s.endsWith "px" then return .px (← number ((s.dropEnd 2).toString))
  if s.endsWith "%" then return .percent ((← number ((s.dropEnd 1).toString))/100)
  if s.endsWith "vw" then return .vw ((← number ((s.dropEnd 2).toString))/100)
  if s.endsWith "vh" then return .vh ((← number ((s.dropEnd 2).toString))/100)
  if s == "0" then return .px 0
  throw s!"unsupported CSS length unit: {s}"
def resolve (basis : Float) : Length → Option Float
  | .auto | .vw _ | .vh _ => none | .px n => some n | .percent n => some (basis*n)
/-- CSS Values 4 §6.2: viewport units, computed once the viewport is known. -/
def Length.atViewport (width height : Float) : Length → Length
  | .vw n => .px (n*width).floor
  | .vh n => .px (n*height).floor
  | other => other
private def pixels (s : String) : Except String Float := do
  match ← length s with | .px n => return n | _ => throw "box edges require px in this CSS profile"
private def color (source : String) : Except String Color := do
  let s := (trim source).toLower
  let named : List (String × Color) := [("black",⟨0,0,0⟩),("white",⟨1,1,1⟩),("red",⟨1,0,0⟩),("green",⟨0,0.5019607843137255,0⟩),("lime",⟨0,1,0⟩),("blue",⟨0,0,1⟩),("yellow",⟨1,1,0⟩),("gray",⟨0.5019607843137255,0.5019607843137255,0.5019607843137255⟩),("navy",⟨0,0,0.5019607843137255⟩)]
  if let some (_,c) := named.find? (fun p => p.1 == s) then return c
  let hex := fun c => if c >= '0' && c <= '9' then some (c.toNat-48) else if c >= 'a' && c <= 'f' then some (c.toNat-87) else none
  if s.startsWith "#" then
    let some ds := ((s.drop 1).toString.toList.mapM hex) | throw "invalid CSS hex color"
    let rgb (r g b : Nat) : Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
    match ds with
    | [a,b,c] => return rgb (a*17) (b*17) (c*17)
    | [a,b,c,d,e,f] => return rgb (a*16+b) (c*16+d) (e*16+f)
    | _ => throw "unsupported CSS hex color length"
  -- CSS Color 4 §4.1: rgb() with commas or spaces, numbers or percentages.
  if s.startsWith "rgb(" && s.endsWith ")" then
    let inner := ((s.drop 4).toString.dropEnd 1).toString
    let channels := (inner.splitOn ",").flatMap (·.splitOn " ") |>.filter (· != "")
    let channel := fun (c : String) => do
      let value ← if c.endsWith "%" then (fun n => n/100) <$> number (c.dropEnd 1).toString
        else (fun n => n/255) <$> number c
      pure (max 0 (min 1 value))
    match channels with
    | [r,g,b] => return ⟨← channel r,← channel g,← channel b⟩
    | _ => throw s!"unsupported CSS color: {source}"
  throw s!"unsupported CSS color: {source}"
private def edgeValues (s : String) : Except String Edges := do
  let vals ← (words s).mapM pixels
  if vals.any (· < 0) then throw "negative edges outside first CSS profile"
  match vals with
  | [a] => return ⟨a,a,a,a⟩
  | [a,b] => return ⟨a,b,a,b⟩
  | [a,b,c] => return ⟨a,b,c,b⟩
  | [a,b,c,d] => return ⟨a,b,c,d⟩
  | _ => throw "CSS edge shorthand requires one to four values"
private def edgePixel (source : String) : Except String Float := do
  let value ← pixels source
  if value < 0 then throw "negative edges outside first CSS profile"
  return value
private def apply (s : Computed) (d : Declaration) : Except String Computed := do
  match d.property with
  | "display" => match d.value with
    | "none" => return {s with display := .none}
    | "block" => return {s with display := .block}
    | "inline" => return {s with display := .inline}
    | "inline-block" => return {s with display := .inlineBlock}
    | _ => throw "unsupported CSS display"
  | "width" => return {s with width := ← length d.value}
  | "height" => return {s with height := ← length d.value}
  | "margin" => return {s with margin := ← edgeValues d.value}
  | "padding" => return {s with padding := ← edgeValues d.value}
  | "margin-top" => return {s with margin := {s.margin with top := ← edgePixel d.value}}
  | "margin-right" => return {s with margin := {s.margin with right := ← edgePixel d.value}}
  | "margin-bottom" => return {s with margin := {s.margin with bottom := ← edgePixel d.value}}
  | "margin-left" => return {s with margin := {s.margin with left := ← edgePixel d.value}}
  | "padding-top" => return {s with padding := {s.padding with top := ← edgePixel d.value}}
  | "padding-right" => return {s with padding := {s.padding with right := ← edgePixel d.value}}
  | "padding-bottom" => return {s with padding := {s.padding with bottom := ← edgePixel d.value}}
  | "padding-left" => return {s with padding := {s.padding with left := ← edgePixel d.value}}
  | "color" => return {s with color := ← color d.value}
  | "background" | "background-color" =>
    let bg ← if d.value == "transparent" then pure none else some <$> color d.value
    return {s with background := bg}
  | "font-size" =>
    let v ← pixels d.value
    if v <= 0 then throw "font-size must be positive"
    return {s with fontSize := v, lineHeight := s.lineHeightFactor.map (v*·) |>.getD s.lineHeight}
  | "line-height" =>
    let factor ← if d.value.endsWith "px" then pure none
      else some <$> (if d.value == "normal" then pure 1.2 else number d.value)
    let v ← match factor with | none => pixels d.value | some n => pure (n*s.fontSize)
    if v <= 0 then throw "line-height must be positive"
    return {s with lineHeight := v, lineHeightFactor := factor}
  | "visibility" => match d.value with
    | "visible" => return {s with visible := true}
    | "hidden" | "collapse" => return {s with visible := false}
    | _ => throw "unsupported CSS visibility"
  | "overflow" =>
    if d.value == "visible" then return {s with clipOverflow := false}
    if d.value == "hidden" || d.value == "clip" then return {s with clipOverflow := true}
    throw "unsupported CSS overflow mode"
  | "text-decoration" | "text-decoration-line" =>
    if d.value == "underline" then return {s with underline := true}
    if d.value == "none" then return {s with underline := false}
    throw "unsupported CSS text decoration"
  | "font-family" =>
    let raw := trim d.value
    let quoted := (raw.startsWith "'" && raw.endsWith "'") || (raw.startsWith "\"" && raw.endsWith "\"")
    let family := if quoted then ((raw.drop 1).dropEnd 1).toString else raw
    if family.isEmpty || family.contains ',' || family.contains '\\' ||
        (!quoted && !ident family) then throw s!"unsupported font family syntax: {d.value}"
    return {s with fontFamily := family}
  | _ => throw s!"unsupported CSS property: {d.property}"

/-- A value or property this profile can not use leaves the style as it was. -/
private def applyOrKeep (s : Computed) (d : Declaration) : Computed :=
  (apply s d).toOption.getD s

/-- Spacing an unstyled page starts with. Margins here do not collapse, so each
side has half of what a browser's single collapsed margin would be. -/
private def startMargin (tag : String) (size : Float) : Edges :=
  let gap := size/2
  if tag == "body" then ⟨8,8,8,8⟩
  else if ["p","pre","dl","listing","xmp","plaintext","address","h1","h2","h3","h4","h5","h6"].contains tag then ⟨gap,0,gap,0⟩
  else if ["ul","ol","dir","menu"].contains tag then ⟨gap,0,gap,40⟩
  else if tag == "blockquote" then ⟨gap,40,gap,40⟩
  else if tag == "dd" then ⟨0,0,0,40⟩
  else {}

private def headingScale : String → Float
  | "h1" => 2 | "h2" => 1.5 | "h3" => 1.17 | "h5" => 0.83 | "h6" => 0.67 | _ => 1

private def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a == b then lexLE as bs else a < b

/-- Winning declarations are keyed by property, with importance, specificity
and source order compared lexicographically. Inheritance is applied first. -/
def computed (dom : Dom) (id : Nat) (rules : List Rule) (parent : Computed) : Except String Computed := do
  let n := dom.get id
  let block := ["html","body","div","p","section","main","article","header","footer","nav","aside",
    "h1","h2","h3","h4","h5","h6","ul","ol","li","dir","menu","dl","dt","dd","pre","listing","xmp","plaintext",
    "blockquote","address","center","hr","form","fieldset","figure","figcaption",
    "table","caption","thead","tbody","tfoot","tr","td","th"].contains n.lname
  let hidden := ["head","style","script","title","meta","link","template","base","area","param"].contains n.lname
  let hyperlink := n.lname == "a" && hasAttribute n "href"
  let svgViewport := n.ns == some DOM.svgNS && n.lname == "svg"
  let svgOverflow := attrValue n "overflow"
  let scale := headingScale n.lname
  let fontSize := if scale == 1 then parent.fontSize else (parent.fontSize*scale).round
  let mut initial : Computed := {
    color := if hyperlink then ⟨0,0,1⟩ else parent.color, underline := hyperlink,
    clipOverflow := svgViewport && svgOverflow != "visible", fontSize, fontFamily := parent.fontFamily,
    lineHeight := parent.lineHeightFactor.map (fontSize*·) |>.getD parent.lineHeight,
    lineHeightFactor := parent.lineHeightFactor, visible := parent.visible,
    preformatted := parent.preformatted || ["pre","listing","xmp","plaintext"].contains n.lname,
    display := if hidden then .none else if block then .block else .inline,
    margin := startMargin n.lname fontSize}
  -- SVG presentation attributes have lower priority than author CSS.
  -- These properties affect HTML layout/inheritance, so compute them here.
  if svgViewport then
    for property in ["color","visibility","display"] do
      let value := attrValue n property
      if !value.isEmpty then initial := applyOrKeep initial ⟨property,value,false⟩
    for property in ["width","height"] do
      let value := trim (attrValue n property)
      if !value.isEmpty then
        let dimension ← if value == "auto" || value.endsWith "px" || value.endsWith "%" || value.endsWith "vw" || value.endsWith "vh" then length value
          else pure (.px (← number value))
        initial := if property == "width" then {initial with width := dimension}
          else {initial with height := dimension}
  let mut winners : Std.TreeMap String (List Nat × Declaration) := {}
  let mut order : Nat := 0
  for rule in rules do
    let specificity := (rule.selectors.filter (selectorMatches dom id)).foldl (fun m s => if lexLE [m.1,m.2.1,m.2.2] [s.specificity.1,s.specificity.2.1,s.specificity.2.2] then s.specificity else m) (0,0,0)
    if rule.selectors.any (selectorMatches dom id) then
      for d in rule.declarations do
        let key := [if d.important then 1 else 0,0,specificity.1,specificity.2.1,specificity.2.2,order]
        if (winners.get? d.property).all (fun old => lexLE old.1 key) then
          winners := winners.insert d.property (key,d)
        order := order+1
  for d in ← declarations (attrValue n "style") do
    let key := [if d.important then 1 else 0,1,0,0,0,order]
    if (winners.get? d.property).all (fun old => lexLE old.1 key) then winners := winners.insert d.property (key,d)
    order := order+1
  -- Font size precedes line-height and inheritance-sensitive dependent values.
  let mut result := initial
  if let some (_,d) := winners.get? "font-size" then result := applyOrKeep result d
  for (key,(priority,d)) in winners.toList do
    if key != "font-size" then
      -- Inline SVG paint declarations stay with the existing SVG producer.
      -- External HTML paint rules are refused until that cascade is unified.
      if n.ns == some DOM.svgNS && priority[1]? == some 1 && !htmlProperties.contains key then pure ()
      else result := applyOrKeep result d
  -- A root or body never clips here: the window scrolls instead.
  if ["html","body"].contains n.lname then result := {result with clipOverflow := false}
  let decoration := parent.decorationColor.orElse (fun _ => if result.underline then some result.color else none)
  return {result with underline := decoration.isSome, decorationColor := decoration}

/-- Reader text scaling is applied once after inheritance/cascade. Pixel sizes
are rounded to match the supplied-font raster contract; explicit line heights
scale too. Geometry, SVG viewports and DOM source are unchanged. -/
def Computed.scaleText (s : Computed) (scale : Float) : Computed :=
  if scale == 1 then s else
  let size := max 1 (s.fontSize*scale).round
  let height := (s.lineHeightFactor.map (size*·)).getD (s.lineHeight*scale)
  {s with fontSize := size, lineHeight := height}

/-- Visit parents before children, using a work list and bounded arena size. -/
def computeAll (dom : Dom) (rules : List Rule) (textScale : Float := 1) : Except String (Array Computed) := do
  if !textScale.isFinite || textScale < 0.5 || textScale > 2.5 then throw "text scale must be 50% to 250%"
  let mut pending := [0]
  let mut styles := Array.replicate dom.size ({} : Computed)
  for _ in [:dom.size+1] do
    match pending with
    | [] => return styles.map (·.scaleText textScale)
    | id::rest =>
      let n := dom.get id
      let parent := (n.parent.bind (styles[·]?)).getD {}
      let svgDescendant := n.ns == some DOM.svgNS && (n.parent.map (fun p => (dom.get p).ns == some DOM.svgNS)).getD false
      let style ← if n.type == .element && !svgDescendant then computed dom id rules parent else pure {parent with
        display := .inline, width := .auto, height := .auto,
        margin := {}, padding := {}, background := none, clipOverflow := false}
      styles := styles.set! id style
      pending := n.kids.toList ++ rest
  throw "DOM style traversal exceeds arena bound"

end L4Factoidal.Rendering.CSS
