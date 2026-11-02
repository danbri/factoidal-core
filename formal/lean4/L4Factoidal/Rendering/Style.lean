import L4Factoidal.Rendering.Scene
import L4Factoidal.DOM.OfHtml
import Std.Data.TreeMap

/-! Computed styles for an explicitly bounded CSS block/inline profile.
Selectors: universal, type, id and class compound selectors, selector lists and
descendants. Unsupported syntax/properties produce a named refusal. -/
namespace L4Factoidal.Rendering.CSS
open DOM
private def trim (s : String) := s.trimAscii.toString
inductive Length where
  | auto | px (value : Float) | percent (value : Float)
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
  lineHeight : Float := 19.2
  lineHeightFactor : Option Float := some 1.2
  visible : Bool := true
  deriving Repr
instance : Inhabited Computed := ⟨{}⟩

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

def declarations (s : String) : Except String (List Declaration) := do
  let mut out : List Declaration := []
  for item in s.splitOn ";" do
    let item := trim item
    if !item.isEmpty then
      let parts := item.splitOn ":"
      let [key,value] := parts | throw "unsupported CSS declaration syntax"
      let value := trim value
      let important := value.endsWith "!important"
      let value := if important then trim ((value.dropEnd 10).toString) else value
      let key := (trim key).toLower
      let key := if key == "background" then "background-color" else key
      out := ⟨key,value,important⟩ :: out
  return out.reverse

/-- CSS comments are removed before tokenizing this deliberately small grammar. -/
private def comments (s : String) : Except String String := do
  let pieces := s.splitOn "/*"
  let mut out := pieces.headD ""
  for p in pieces.drop 1 do
    let cut := p.splitOn "*/"
    if cut.length != 2 then throw "unsupported nested or unterminated CSS comment"
    out := out ++ cut[1]!
  return out

def parse (source : String) : Except String (List Rule) := do
  if source.length > 131072 then throw "CSS input exceeds 131072 characters"
  let source ← comments source
  let pieces := source.splitOn "}"
  if !(trim (pieces.getLast!)).isEmpty then throw "unterminated CSS rule"
  let mut out : List Rule := []
  for piece in pieces.dropLast do
    let [head,body] := piece.splitOn "{" | throw "unsupported CSS rule syntax"
    let selectors ← (head.splitOn ",").mapM selector
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
  if s == "0" then return .px 0
  throw s!"unsupported CSS length unit: {s}"
def resolve (basis : Float) : Length → Option Float
  | .auto => none | .px n => some n | .percent n => some (basis*n)
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
  | "font-family" =>
    if ["monospace","ascii-bitmap"].contains d.value then return s
    throw "unsupported font family: this build uses the explicit ASCII bitmap font profile"
  | _ => throw s!"unsupported CSS property: {d.property}"

private def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a == b then lexLE as bs else a < b

/-- Winning declarations are keyed by property, with importance, specificity
and source order compared lexicographically. Inheritance is applied first. -/
def computed (dom : Dom) (id : Nat) (rules : List Rule) (parent : Computed) : Except String Computed := do
  let n := dom.get id
  let block := ["html","body","div","p","section","main","article","header","footer","h1","h2","ul","li"].contains n.lname
  let hidden := ["head","style","script","title","meta","link","template"].contains n.lname
  let initial : Computed := {
    color := parent.color, fontSize := parent.fontSize,
    lineHeight := parent.lineHeight, lineHeightFactor := parent.lineHeightFactor, visible := parent.visible,
    display := if hidden then .none else if block then .block else .inline,
    margin := if n.lname == "body" then ⟨8,8,8,8⟩ else {}}
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
  if let some (_,d) := winners.get? "font-size" then result ← apply result d
  for (key,(_,d)) in winners.toList do
    if key != "font-size" then result ← apply result d
  return result

/-- Visit parents before children, using a work list and bounded arena size. -/
def computeAll (dom : Dom) (rules : List Rule) : Except String (Array Computed) := do
  let mut pending := [0]
  let mut styles := Array.replicate dom.size ({} : Computed)
  for _ in [:dom.size+1] do
    match pending with
    | [] => return styles
    | id::rest =>
      let n := dom.get id
      let parent := (n.parent.bind (styles[·]?)).getD {}
      let style ← if n.type == .element then computed dom id rules parent else pure {parent with
        display := .inline, width := .auto, height := .auto,
        margin := {}, padding := {}, background := none}
      styles := styles.set! id style
      pending := n.kids.toList ++ rest
  throw "DOM style traversal exceeds arena bound"

end L4Factoidal.Rendering.CSS
