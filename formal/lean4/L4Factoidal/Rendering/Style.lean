import L4Factoidal.Rendering.Scene
import L4Factoidal.DOM.OfHtml
import L4Factoidal.Unicode.Bidi
import L4Factoidal.Rendering.MediaQuery
import L4Factoidal.Rendering.CssValues.Properties
import L4Factoidal.Rendering.FlexStyle
import Std.Data.TreeMap
import Std.Data.HashMap

/-! Computed styles for an explicitly bounded CSS block/inline profile.
Selectors: universal, type, id and class compound selectors, selector lists and
descendants, and the pseudo-classes `:link`, `:visited`, `:any-link`, `:hover`
and `:active` (Selectors Level 4 §8 and §9) over an `ElementState` that the
host supplies. CSS error handling applies: what this profile does not understand
is dropped, and the rest of the sheet still applies. A page is never refused
for its style sheet. -/
namespace L4Factoidal.Rendering.CSS
open DOM
private def trim (s : String) := s.trimAscii.toString
-- `Length` is in `Rendering/BoxAlign.lean`, which the flex and alignment values also use.
structure Edges where
  top : Float := 0
  right : Float := 0
  bottom : Float := 0
  left : Float := 0
  deriving Repr
/-- CSS Display 3 outer and inner display types that this profile lays out.
The table values are those of CSS 2.1 §17.2 (CSS Tables 3 §2). -/
inductive Display where
  | none | block | inline | inlineBlock
  | table | inlineTable | tableRowGroup | tableHeaderGroup | tableFooterGroup
  | tableRow | tableCell | tableCaption | tableColumn | tableColumnGroup
  /-- Flex and grid containers (CSS Display 3 §2.2): block-level, or inline-level. -/
  | flex | inlineFlex | grid | inlineGrid
  deriving Repr, BEq

/-- Boxes that are laid out by the table layout. `inline-table` is laid out as a
block-level table: this profile has no atomic inline boxes
(https://github.com/danbri/factoidal/issues/1272). -/
def Display.isTable : Display → Bool
  | .table | .inlineTable => true | _ => false
/-- Internal table boxes (CSS 2.1 §17.2): outside a table they get an anonymous table. -/
def Display.isTableInternal : Display → Bool
  | .tableRowGroup | .tableHeaderGroup | .tableFooterGroup | .tableRow | .tableCell
  | .tableCaption | .tableColumn | .tableColumnGroup => true
  | _ => false
/-- Boxes that stack in block flow: blocks and tables. -/
def Display.isBlockLevel (d : Display) : Bool := d == .block || d.isTable || d == .flex || d == .grid
/-- A flex container (CSS Flexbox 1 §3): its children are flex items. -/
def Display.isFlex (d : Display) : Bool := d == .flex || d == .inlineFlex
/-- A grid container (CSS Grid 2 §5.1). -/
def Display.isGrid (d : Display) : Bool := d == .grid || d == .inlineGrid
/-- CSS Display 3 §2.7: the display of a flex or grid item is blockified. -/
def Display.blockified : Display → Display
  | .inline | .inlineBlock => .block
  | .inlineTable => .table
  | .inlineFlex => .flex
  | .inlineGrid => .grid
  | .tableRowGroup | .tableHeaderGroup | .tableFooterGroup | .tableRow | .tableCell
  | .tableCaption | .tableColumn | .tableColumnGroup => .block
  | d => d
/-- An inline-level flex or grid container: one atomic box on a line. -/
def Display.isInlineContainer (d : Display) : Bool := d == .inlineFlex || d == .inlineGrid
/-- Boxes whose contents are one block formatting context (the strut of their lines). -/
def Display.isBlockContainer (d : Display) : Bool :=
  d == .block || d == .tableCell || d == .tableCaption

/-- `vertical-align` as it applies to table cells (CSS 2.1 §17.5.3). -/
inductive VerticalAlign where | baseline | top | middle | bottom
  deriving Repr, BEq
/-- CSS Images 3 §5.5 `object-fit`: how a replaced element's content fills its box. -/
inductive ObjectFit where | fill | contain | cover | none | scaleDown
  deriving Repr, BEq
/-- CSS Text 3 §6.1 `text-align` of this profile. `start` and `end_` (`end`)
follow `direction`; `left` and `right` do not. -/
inductive TextAlign where | start | right | center | left | end_
  deriving Repr, BEq
/-- CSS Writing Modes 3 §2.1 `direction` (inherited). -/
inductive Direction where | ltr | rtl
  deriving Repr, BEq
/-- CSS Writing Modes 3 §2.2 `unicode-bidi` (not inherited): how an inline box
takes part in the Unicode Bidirectional Algorithm (§2.4.2 gives the bidi
control characters of each value). -/
inductive UnicodeBidi where | normal | embed | isolate | bidiOverride | isolateOverride | plaintext
  deriving Repr, BEq
/-- CSS Backgrounds 3 §4.2 line styles of this profile. -/
inductive BorderStyle where | none | solid | inset | outset
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
  /-- Border widths as specified; `Computed.borderEdges` is the used width (0 with no style). -/
  borderWidth : Edges := ⟨3,3,3,3⟩
  borderStyle : BorderStyle := .none
  /-- None: `currentColor`. -/
  borderColor : Option Color := none
  /-- `border-spacing`, horizontal and vertical (inherited). -/
  borderSpacingX : Float := 0
  borderSpacingY : Float := 0
  /-- `border-collapse: collapse` (inherited). -/
  borderCollapse : Bool := false
  /-- `caption-side: bottom` (inherited). -/
  captionBottom : Bool := false
  verticalAlign : VerticalAlign := .baseline
  /-- `table-layout: fixed`. -/
  tableFixed : Bool := false
  /-- CSS 2.1 §10.4 and §10.7: `auto` is 0 for a minimum and `none` for a maximum. -/
  minWidth : Length := .auto
  maxWidth : Length := .auto
  minHeight : Length := .auto
  maxHeight : Length := .auto
  objectFit : ObjectFit := .fill
  /-- `text-align` (inherited): where the lines of a block container sit. -/
  textAlign : TextAlign := .start
  /-- `direction` (inherited), from CSS or the HTML `dir` attribute. -/
  direction : Direction := .ltr
  /-- `unicode-bidi` (not inherited). -/
  unicodeBidi : UnicodeBidi := .normal
  /-- `margin-left: auto` and `margin-right: auto` (CSS 2.1 §10.3.3): the used margin
  takes the room a block-level box leaves; `margin` holds 0 on such a side. -/
  autoMarginLeft : Bool := false
  autoMarginRight : Bool := false
  /-- `margin-top: auto` and `margin-bottom: auto`: read by flex and grid layout (in block
  flow they are 0, CSS 2.1 §10.6.3). -/
  autoMarginTop : Bool := false
  autoMarginBottom : Bool := false
  /-- Box alignment, gaps and `order` (`Rendering/BoxAlign.lean`): read by flex and grid. -/
  align : AlignStyle := {}
  /-- The flex container and flex item values (`Rendering/FlexStyle.lean`). -/
  flex : FlexStyle := {}
  /-- Positioning, floats and box sizing (`Rendering/BoxPosition.lean`). -/
  pos : PositionStyle := {}
  deriving Repr
instance : Inhabited Computed := ⟨{}⟩

/-- Properties consumed by HTML style/layout, including an embedded SVG root.
The DOM-to-SVG adapter uses this same list to avoid a second interpretation. -/
def htmlProperties : List String :=
  ["display","width","height","margin","padding",
   "margin-top","margin-right","margin-bottom","margin-left",
   "padding-top","padding-right","padding-bottom","padding-left",
   "color","background","background-color","font-size","font-family",
   "line-height","visibility","overflow","text-decoration","text-decoration-line",
   "border","border-width","border-style","border-color",
   "border-spacing","border-collapse","caption-side","vertical-align","table-layout",
   "min-width","max-width","min-height","max-height","object-fit","text-align",
   "direction","unicode-bidi"]

/-- CSS Backgrounds 3 §4.3: the computed border width is 0 when the style is none. -/
def Computed.borderEdges (s : Computed) : Edges :=
  if s.borderStyle == .none then {} else s.borderWidth

structure Declaration where
  property : String
  value : String
  important : Bool := false
  deriving Repr
/-- Selectors Level 4 location (§8) and user action (§9) pseudo-classes. -/
inductive PseudoClass where | link | visited | anyLink | hover | active
  deriving Repr, BEq
structure Compound where
  tag : Option String := none
  id : Option String := none
  classes : List String := []
  pseudo : List PseudoClass := []
  /-- `:host` or `:host(compound)` (CSS Scoping 1 §3.2.1): it matches only the shadow host
  of the rule's shadow tree, and the other fields test that host. -/
  host : Bool := false
  deriving Repr
structure Selector where
  /-- Rightmost compound first; ancestors follow. -/
  parts : List Compound
  specificity : Nat × Nat × Nat
  /-- `::slotted(compound)` after the rightmost compound (CSS Scoping 1 §3.2.2): the
  selector matches an element assigned to a slot that `parts` matches. -/
  slotted : Option Compound := none
  deriving Repr
/-- A selector that names `:visited` anywhere. Such a rule sets only colours. -/
def Selector.visitedDependent (sel : Selector) : Bool :=
  sel.parts.any (·.pseudo.contains .visited) || (sel.slotted.any (·.pseudo.contains .visited))

/-- The element state the host says (Selectors Level 4 §9.1-§9.2, HTML §4.16.3):
the element the pointer designates, the element being activated (each with its
ancestors), and the hyperlinks whose target is in the session history. -/
structure ElementState where
  hover : Option Nat := none
  active : Option Nat := none
  visited : List Nat := []
  deriving Repr, BEq, Inhabited
structure Rule where
  selectors : List Selector
  declarations : List Declaration
  /-- The shadow root whose style sheet the rule is from (CSS Scoping 1 §3.1); none for
  the document's. -/
  scope : Option Nat := none
  deriving Repr

def attrValue (n : DOM.Node) (key : String) : String :=
  ((n.attrs.find? fun a => a.ns.isNone && a.lname == key).map (·.value)).getD ""
def hasAttribute (n : DOM.Node) (key : String) : Bool :=
  n.attrs.any (fun a => a.ns.isNone && a.lname == key)

private def words (s : String) : List String :=
  (s.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " ").splitOn " " |>.filter (· != "")
private def ident (s : String) : Bool := !s.isEmpty && s.toList.all (fun c => c.isAlphanum || c == '-' || c == '_')
/-- Splits `source` at the commas outside quotes and parentheses (CSS Syntax 3 §5.3.11,
for a comma-separated list of component values). One pass, no recursion. -/
def splitTopCommas (source : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut item := ""
  let mut depth := 0
  let mut quote : Option Char := none
  for c in source.toList do
    if let some q := quote then
      item := item.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      quote := some c
      item := item.push c
    else if c == '(' then
      depth := depth+1
      item := item.push c
    else if c == ')' then
      depth := depth-1
      item := item.push c
    else if c == ',' && depth == 0 then
      out := out.push item
      item := ""
    else item := item.push c
  return (out.push item).toList

/-- CSS Fonts 4 §2.1 `<family-name>#`: a quoted string, or identifiers separated by
white space (joined by one space). Generic family keywords stay as they are. `none`
for a list this profile can not read: an empty item, a backslash escape, an
unclosed quote, or an unquoted item that is not identifiers. -/
def familyNames (value : String) : Option (List String) := do
  let items ← (splitTopCommas value).mapM fun item => do
    let raw := trim item
    if raw.isEmpty || raw.contains '\\' then none
    if raw.startsWith "\"" || raw.startsWith "'" then
      let q := raw.front
      if raw.length < 2 || !raw.endsWith q.toString then none
      let inner := ((raw.drop 1).dropEnd 1).toString
      if inner.contains q || inner.isEmpty then none
      pure inner
    else
      let parts := words raw
      if parts.isEmpty || !parts.all ident then none
      pure (" ".intercalate parts)
  if items.isEmpty then none else some items

/-- The list of `familyNames` as `Computed.fontFamily` holds it: the names joined by
", ". One family stays the name itself, as before. -/
def familyValue (names : List String) : String := ", ".intercalate names

/-- The names of a `Computed.fontFamily` value. -/
def familyList (value : String) : List String :=
  ((value.splitOn ", ").map trim).filter (!·.isEmpty)

private def pseudoClass : String → Option PseudoClass
  | "link" => some .link | "visited" => some .visited | "any-link" => some .anyLink
  | "hover" => some .hover | "active" => some .active | _ => none
private def compoundBody (s : String) : Except String Compound := do
  let chunks := s.toList.foldl (fun (acc : List String) c =>
    if c == '#' || c == '.' || c == ':' then String.singleton c :: acc
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
    else if chunk.startsWith ":" then
      let some value := pseudoClass ((chunk.drop 1).toString.toLower) | throw s!"unsupported CSS pseudo-class: {chunk}"
      out := {out with pseudo := value :: out.pseudo}
    else if chunk == "*" then pure ()
    else if ident chunk then out := {out with tag := some chunk.toLower}
    else throw s!"unsupported CSS selector: {s}"
  return out
/-- A compound, or `:host` and `:host(compound)` (CSS Scoping 1 §3.2.1). -/
private def compound (s : String) : Except String Compound := do
  if s == ":host" then return {host := true}
  if s.startsWith ":host(" && s.endsWith ")" then
    let inner ← compoundBody ((s.drop 6).dropEnd 1).toString
    return {inner with host := true}
  compoundBody s
private def compoundSpecificity (n : Nat × Nat × Nat) (p : Compound) : Nat × Nat × Nat :=
  (n.1 + (if p.id.isSome then 1 else 0), n.2.1 + p.classes.length + p.pseudo.length + (if p.host then 1 else 0),
    n.2.2 + (if p.tag.isSome then 1 else 0))
private def selector (s : String) : Except String Selector := do
  let ws := words (trim s)
  -- `::slotted(compound)` ends the last compound (CSS Scoping 1 §3.2.2).
  let (ws, slotted) ← match ws.getLast? with
    | some w =>
      match w.splitOn "::slotted(" with
      | [before, inner] => do
        if !inner.endsWith ")" then throw "unsupported ::slotted() selector"
        let c ← compoundBody (inner.dropEnd 1).toString
        pure (ws.dropLast ++ [if before.isEmpty then "*" else before], some c)
      | _ => pure (ws, none)
    | none => pure (ws, none)
  let parts ← ws.mapM compound
  if parts.isEmpty || parts.length > 16 then throw "CSS selector exceeds supported depth"
  let specificity := (parts ++ slotted.toList).foldl compoundSpecificity (0,0,0)
  -- `::slotted` is a pseudo-element: one more in the last count.
  let specificity := if slotted.isSome then (specificity.1, specificity.2.1, specificity.2.2 + 1) else specificity
  return {parts := parts.reverse, specificity, slotted}

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
        else match layoutShorthand key value with
          -- `flex`, `flex-flow`, `gap`, `place-*`: their longhands, so the cascade orders them
          | some longhands => longhands.map fun (k,v) => ⟨k,v,important⟩
          | none => [⟨key,value,important⟩]
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

/-- A media query list of `@media` (Media Queries Level 4 §2) holds for the media
type `medium` when one of its queries is that type or `all`, with an optional
`only`. A query with a media feature, `not`, or `and` is not read by this profile,
and so does not hold. -/
def mediaMatches (medium queries : String) : Bool :=
  (queries.splitOn ",").any fun query =>
    let words := ((trim query).toLower.splitOn " ").filter (· != "")
    let words := if words.head? == some "only" then words.drop 1 else words
    match words with
    | [kind] => kind == medium || kind == "all"
    | _ => false

/-- Rules of a sheet in the media environment `env` (`MediaQuery.Env`: the media type,
and the viewport and colour scheme when the host gives them). The rules of an `@media`
block whose query list holds in `env` (`MediaQuery.applies`) are read in place; a list
that `MediaQuery` can not read does not hold. Other at-rules are skipped whole, as is an
`@media` block in an `@media` block. A rule with a selector this profile can not read
is dropped whole, as CSS drops an invalid selector list. Only the first 131072
characters of a sheet are read. -/
def parseInBlocks (env : MediaQuery.Env) (source : String) : Except String (List Rule) := do
  let mut out : List Rule := []
  for (head,body) in topLevel (comments (source.take 131072).toString) do
    let head := trim head
    let blocks := if !head.startsWith "@" then [(head,body)]
      else if (head.take 6).toString.toLower == "@media" && MediaQuery.applies env (head.drop 6).toString
        then topLevel body
      else []
    for (inner,content) in blocks do
      if !(trim inner).startsWith "@" then
        if let .ok selectors := (inner.splitOn ",").mapM selector then
          out := {selectors, declarations := ← declarations content} :: out
  return out.reverse

/-- The rules of a sheet, each with the query list of its `@media` block (none outside
one), before any media environment is read: what `parseIn` filters. -/
def parseRaw (source : String) : Except String (List (Option String × Rule)) := do
  let mut out : List (Option String × Rule) := []
  for (head,body) in topLevel (comments (source.take 131072).toString) do
    let head := trim head
    let blocks : List (Option String × String × String) := if !head.startsWith "@" then [(none,head,body)]
      else if (head.take 6).toString.toLower == "@media" then
        let query := (head.drop 6).toString
        (topLevel body).map fun (inner,content) => (some query,inner,content)
      else []
    for (query,inner,content) in blocks do
      if !(trim inner).startsWith "@" then
        if let .ok selectors := (inner.splitOn ",").mapM selector then
          out := (query,{selectors, declarations := ← declarations content}) :: out
  return out.reverse

/-- The rules of `parseRaw` that hold in the media environment `env`: those outside an
`@media` block or in one whose query list holds. A relayout at another width needs only
this step; a host may keep what `parseRaw` read (realperf: reading Wikipedia's sheets
again was 30 ms of each relayout). -/
def parseInRaw (env : MediaQuery.Env) (raw : List (Option String × Rule)) : List Rule :=
  raw.filterMap fun (query,rule) => if query.all (MediaQuery.applies env) then some rule else none

/-- Rules of a sheet in the media environment `env`: `parseRaw`, then `parseInRaw`. Agrees
with `parseInBlocks`, which reads the blocks in place (`CascadeTests`). -/
def parseIn (env : MediaQuery.Env) (source : String) : Except String (List Rule) := do
  return parseInRaw env (← parseRaw source)

/-- Rules of a sheet for the media type `medium` ("screen" or "print") with no viewport:
an `@media` query with a width or colour-scheme feature does not hold. -/
def parseFor (medium source : String) : Except String (List Rule) := parseIn {medium} source

/-- The descriptor blocks of the `@font-face` rules of a sheet (CSS Fonts 4 §4.1), in
order, with those inside an `@media` block whose query list holds in `env` (by default
the media type `medium` with no viewport). Only
the first 131072 characters of a sheet are read, as for `parseFor`. -/
def fontFaceBlocks (medium source : String) (env : MediaQuery.Env := {medium}) : List String := Id.run do
  let mut out : List String := []
  for (head,body) in topLevel (comments (source.take 131072).toString) do
    let head := trim head
    let blocks := if (head.take 6).toString.toLower == "@media" && MediaQuery.applies env (head.drop 6).toString
        then topLevel body else [(head,body)]
    for (inner,content) in blocks do
      if (trim inner).toLower == "@font-face" then out := content :: out
  return out.reverse

/-- `id` is `target` or one of its ancestors. The walk is bounded by the arena size. -/
def inclusiveAncestor (dom : Dom) (id : Nat) : Nat → Option Nat → Bool
  | 0, _ => false
  | _+1, none => false
  | f+1, some at_ => at_ == id || inclusiveAncestor dom id f (dom.get at_).parent

/-- HTML §4.16.3: an `a` or `area` element with an `href` attribute is a hyperlink. -/
def isHyperlink (n : DOM.Node) : Bool :=
  (n.lname == "a" || n.lname == "area") && hasAttribute n "href"

private def pseudoMatches (dom : Dom) (state : ElementState) (id : Nat) (n : DOM.Node) : PseudoClass → Bool
  | .anyLink => isHyperlink n
  | .link => isHyperlink n && !state.visited.contains id
  | .visited => isHyperlink n && state.visited.contains id
  | .hover => inclusiveAncestor dom id (dom.size+1) state.hover
  | .active => inclusiveAncestor dom id (dom.size+1) state.active

/-- The rules of a sheet on a screen. -/
def parse (source : String) : Except String (List Rule) := parseFor "screen" source

/-- What the matcher reads of an element besides its tag and pseudo-classes: its class
words and its `id` attribute. `ElemKey.read` reads them from the node; a cascade reads
them once per element (`ElemKeys`), not once per element and rule (realperf, record
docs/designissues/2026-11-09-real-site-layout-speed.md: splitting `class` for every
element and rule was 95% of a Wikipedia layout). -/
structure ElemKey where
  classes : List String := []
  id : String := ""
  deriving Inhabited
def ElemKey.read (n : DOM.Node) : ElemKey := ⟨words (attrValue n "class"), attrValue n "id"⟩
/-- The keys of each node, read from the arena when asked: the reference. -/
def readKeys (dom : Dom) : Nat → ElemKey := fun i => ElemKey.read (dom.get i)

/-- The fields of a compound on element `id`, the test of `:host` apart. -/
private def compoundFieldsK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) (id : Nat) (s : Compound) : Bool :=
  let n := dom.get id
  n.type == .element && (s.tag.map (· == n.lname)).getD true &&
    (s.id.map (· == (keys id).id)).getD true &&
    s.classes.all ((keys id).classes.contains ·) &&
    s.pseudo.all (pseudoMatches dom state id n)
/-- A compound on element `id` of a tree with no shadow scope: `:host` matches nothing. -/
private def compoundMatchesK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) (id : Nat) (s : Compound) : Bool :=
  !s.host && compoundFieldsK keys dom state id s
private def matchAncestorsK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) : Nat → Option Nat → Compound → Option Nat
  | 0, _, _ => none
  | _+1, none, _ => none
  | f+1, some id, sel =>
    if compoundMatchesK keys dom state id sel then some id else matchAncestorsK keys dom state f (dom.get id).parent sel
private def partsMatchK (keys : Nat → ElemKey) (dom : Dom) (state : ElementState) : List Compound → Option Nat → Bool
  | [], _ => true
  | sel::rest, ancestor => match matchAncestorsK keys dom state (dom.size+1) ancestor sel with
    | none => false
    | some id => partsMatchK keys dom state rest (dom.get id).parent

/-- `selectorMatches` with the element keys `keys` (`readKeys dom` or a table of them). -/
def selectorMatchesK (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState := {}) : Bool :=
  match sel.parts with
  | [] => false
  | head::rest => sel.slotted.isNone && compoundMatchesK keys dom state id head && partsMatchK keys dom state rest (dom.get id).parent

def selectorMatches (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState := {}) : Bool :=
  selectorMatchesK (readKeys dom) dom id sel state

/-- The keys of every node of an arena, read once. -/
def ElemKeys := Array ElemKey
def ElemKeys.of (dom : Dom) : ElemKeys := dom.nodes.map ElemKey.read
/-- The keys of node `i`: from the table, or read (a node outside the table). -/
def ElemKeys.get (ks : ElemKeys) (dom : Dom) (i : Nat) : ElemKey :=
  match (show Array ElemKey from ks)[i]? with
  | some k => k
  | none => ElemKey.read (dom.get i)

/-- The table gives the keys that the arena gives. -/
theorem ElemKeys.get_of (dom : Dom) : (ElemKeys.of dom).get dom = readKeys dom := by
  funext i
  unfold ElemKeys.get ElemKeys.of readKeys Dom.get
  rw [Array.getElem?_map]
  cases h : dom.nodes[i]? with
  | none => simp [Array.getD]
  | some n =>
    have hi := (Array.getElem?_eq_some_iff.mp h)
    simp [Array.getD, hi.1, hi.2]

/-- The matcher over a key table is the matcher of the arena. -/
theorem selectorMatchesK_of (dom : Dom) (id : Nat) (sel : Selector) (state : ElementState) :
    selectorMatchesK ((ElemKeys.of dom).get dom) dom id sel state = selectorMatches dom id sel state := by
  rw [ElemKeys.get_of]; rfl

/-! ### Selectors of shadow trees (CSS Scoping 1 §3)

A page with a shadow tree is laid out on its flat tree (`DOM.Dom.flat`); its selectors
match on the node tree, each rule in its own tree: a rule of the document's style sheets
matches elements of the document tree, a rule of a shadow tree's `style` elements matches
elements of that shadow tree, its `:host` the shadow host, and its `::slotted()` the
elements assigned to its slots. A page with no shadow tree never takes this path. -/

/-- The node tree of a flat-tree layout and each node's shadow root (none in the document
tree). -/
structure TreeScope where
  tree : Dom
  scopes : Array (Option Nat)
  deriving Inhabited

def TreeScope.of (tree : Dom) : TreeScope := Id.run do
  let mut scopes := Array.replicate tree.size (none : Option Nat)
  for i in [0:tree.size] do
    if tree.isShadowRoot i then
      for k in tree.treeOrder i do scopes := scopes.set! k (some i)
  return {tree, scopes}

/-- The shadow root of node `id`'s tree; none in the document tree. -/
def TreeScope.scopeOf (ts : TreeScope) (id : Nat) : Option Nat := ts.scopes.getD id none

def hostOfScope (ts : TreeScope) (scope : Option Nat) : Option Nat :=
  scope.bind fun r => (ts.tree.get r).host

/-- A compound of a rule of tree `scope`: a `:host` compound matches only the host of that
tree, and no other compound matches it (the host is featureless there). -/
private def compoundInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (s : Compound) : Bool :=
  s.host == (hostOfScope ts scope == some id) && compoundFieldsK keys ts.tree state id s

/-- The next node up for a selector of tree `scope`: the parent, and from that tree's
shadow root its host. -/
private def upIn (ts : TreeScope) (scope : Option Nat) (n : Nat) : Option Nat :=
  match (ts.tree.get n).parent with
  | some p => some p
  | none => if scope == some n then (ts.tree.get n).host else none

private def matchAncestorsInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) : Nat → Option Nat → Compound → Option Nat
  | 0, _, _ => none
  | _+1, none, _ => none
  | f+1, some id, sel =>
    if compoundInK keys ts state scope id sel then some id else matchAncestorsInK keys ts state scope f (upIn ts scope id) sel
private def partsInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) : List Compound → Option Nat → Bool
  | [], _ => true
  | sel::rest, ancestor => match matchAncestorsInK keys ts state scope (ts.tree.size+1) ancestor sel with
    | none => false
    | some id => partsInK keys ts state scope rest (upIn ts scope id)

/-- `sel`, of a rule of tree `scope`, matches element `id` (keys from `keys`). -/
def selectorMatchesInK (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (sel : Selector) : Bool :=
  match sel.parts with
  | [] => false
  | head::rest =>
    match sel.slotted with
    | none =>
      (head.host || ts.scopeOf id == scope) &&
        compoundInK keys ts state scope id head && partsInK keys ts state scope rest (upIn ts scope id)
    | some c =>
      scope.isSome && compoundFieldsK keys ts.tree state id c &&
      match ts.tree.findSlot id with
      | some sl => ts.scopeOf sl == scope && compoundInK keys ts state scope sl head &&
          partsInK keys ts state scope rest (upIn ts scope sl)
      | none => false

/-- `selectorMatchesInK` with the arena's keys: the reference. -/
def selectorMatchesIn (ts : TreeScope) (state : ElementState) (scope : Option Nat) (id : Nat) (sel : Selector) : Bool :=
  selectorMatchesInK (readKeys ts.tree) ts state scope id sel

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
  -- the sizing keywords of `width`, `height` and their limits (CSS Sizing 3 §3.2)
  if let some keyword := sizeKeyword? s.toLower then return keyword
  if s.endsWith "px" then return .px (← number ((s.dropEnd 2).toString))
  if s.endsWith "%" then return .percent ((← number ((s.dropEnd 1).toString))/100)
  if s.endsWith "vw" then return .vw ((← number ((s.dropEnd 2).toString))/100)
  if s.endsWith "vh" then return .vh ((← number ((s.dropEnd 2).toString))/100)
  if s == "0" then return .px 0
  if s.startsWith "calc(" then
    if let some l := calcLengthOfText s then return l
  throw s!"unsupported CSS length unit: {s}"
def resolve (basis : Float) : Length → Option Float
  | .auto | .vw _ | .vh _ => none | .px n => some n | .percent n => some (basis*n)
  | .calc p n => some (basis*p+n)
  | .minContent | .maxContent | .fitContent | .stretch => none
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
private def borderStyle (source : String) : Except String BorderStyle :=
  match (trim source).toLower with
  | "none" | "hidden" => pure .none
  | "solid" => pure .solid
  | "inset" => pure .inset
  | "outset" => pure .outset
  | _ => throw "unsupported CSS border style"
/-- A `min-*` or `max-*` value: `none` and `auto` are `auto` here; a negative length is
invalid (CSS 2.1 §10.4). -/
private def limit (source : String) : Except String Length := do
  let v := (trim source).toLower
  if v == "none" || v == "auto" then return .auto
  match ← length v with
  | .px n => if n < 0 then throw "negative CSS size limit" else return .px n
  | .percent n => if n < 0 then throw "negative CSS size limit" else return .percent n
  | other => return other
private def apply (s : Computed) (d : Declaration) : Except String Computed := do
  match d.property with
  | "display" => match d.value with
    | "none" => return {s with display := .none}
    | "block" => return {s with display := .block}
    | "inline" => return {s with display := .inline}
    | "inline-block" => return {s with display := .inlineBlock}
    | "table" => return {s with display := .table}
    | "inline-table" => return {s with display := .inlineTable}
    | "table-row-group" => return {s with display := .tableRowGroup}
    | "table-header-group" => return {s with display := .tableHeaderGroup}
    | "table-footer-group" => return {s with display := .tableFooterGroup}
    | "table-row" => return {s with display := .tableRow}
    | "table-cell" => return {s with display := .tableCell}
    | "table-caption" => return {s with display := .tableCaption}
    | "table-column" => return {s with display := .tableColumn}
    | "table-column-group" => return {s with display := .tableColumnGroup}
    | "flex" => return {s with display := .flex}
    | "inline-flex" => return {s with display := .inlineFlex}
    | "grid" => return {s with display := .grid}
    | "inline-grid" => return {s with display := .inlineGrid}
    | _ => throw "unsupported CSS display"
  | "width" => return {s with width := ← length d.value}
  | "height" => return {s with height := ← length d.value}
  | "margin" => return {s with margin := ← edgeValues d.value}
  | "padding" => return {s with padding := ← edgeValues d.value}
  | "margin-top" =>
    if (trim d.value).toLower == "auto" then return {s with margin := {s.margin with top := 0}, autoMarginTop := true}
    return {s with margin := {s.margin with top := ← edgePixel d.value}, autoMarginTop := false}
  | "margin-right" =>
    if (trim d.value).toLower == "auto" then return {s with margin := {s.margin with right := 0}, autoMarginRight := true}
    return {s with margin := {s.margin with right := ← edgePixel d.value}, autoMarginRight := false}
  | "margin-bottom" =>
    if (trim d.value).toLower == "auto" then return {s with margin := {s.margin with bottom := 0}, autoMarginBottom := true}
    return {s with margin := {s.margin with bottom := ← edgePixel d.value}, autoMarginBottom := false}
  | "margin-left" =>
    if (trim d.value).toLower == "auto" then return {s with margin := {s.margin with left := 0}, autoMarginLeft := true}
    return {s with margin := {s.margin with left := ← edgePixel d.value}, autoMarginLeft := false}
  | "text-align" => match (trim d.value).toLower with
    | "start" => return {s with textAlign := .start}
    | "left" => return {s with textAlign := .left}
    | "right" => return {s with textAlign := .right}
    | "end" => return {s with textAlign := .end_}
    | "center" => return {s with textAlign := .center}
    | _ => throw "unsupported CSS text-align"
  | "direction" => match (trim d.value).toLower with
    | "ltr" => return {s with direction := .ltr}
    | "rtl" => return {s with direction := .rtl}
    | _ => throw "unsupported CSS direction"
  | "unicode-bidi" => match (trim d.value).toLower with
    | "normal" => return {s with unicodeBidi := .normal}
    | "embed" => return {s with unicodeBidi := .embed}
    | "isolate" => return {s with unicodeBidi := .isolate}
    | "bidi-override" => return {s with unicodeBidi := .bidiOverride}
    | "isolate-override" => return {s with unicodeBidi := .isolateOverride}
    | "plaintext" => return {s with unicodeBidi := .plaintext}
    | _ => throw "unsupported CSS unicode-bidi"
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
  | "border-style" => return {s with borderStyle := ← borderStyle d.value}
  | "border-width" => return {s with borderWidth := ← edgeValues d.value}
  | "border-color" => return {s with borderColor := some (← color d.value)}
  | "border" =>
    -- CSS Backgrounds 3 §4.4: width, style and colour in any order; each omitted one is reset.
    let mut out := {s with borderWidth := ⟨3,3,3,3⟩, borderStyle := .none, borderColor := none}
    for part in words d.value do
      if let .ok style := borderStyle part then out := {out with borderStyle := style}
      else if let .ok w := edgePixel part then out := {out with borderWidth := ⟨w,w,w,w⟩}
      else out := {out with borderColor := some (← color part)}
    return out
  | "border-spacing" =>
    match ← (words d.value).mapM pixels with
    | [a] => if a < 0 then throw "negative border-spacing" else return {s with borderSpacingX := a, borderSpacingY := a}
    | [a,b] => if a < 0 || b < 0 then throw "negative border-spacing" else return {s with borderSpacingX := a, borderSpacingY := b}
    | _ => throw "border-spacing requires one or two lengths"
  | "border-collapse" => match d.value with
    | "collapse" => return {s with borderCollapse := true}
    | "separate" => return {s with borderCollapse := false}
    | _ => throw "unsupported CSS border-collapse"
  | "caption-side" => match d.value with
    | "top" => return {s with captionBottom := false}
    | "bottom" => return {s with captionBottom := true}
    | _ => throw "unsupported CSS caption-side"
  | "table-layout" => match d.value with
    | "fixed" => return {s with tableFixed := true}
    | "auto" => return {s with tableFixed := false}
    | _ => throw "unsupported CSS table-layout"
  | "vertical-align" => match d.value with
    | "top" | "text-top" => return {s with verticalAlign := .top}
    | "middle" => return {s with verticalAlign := .middle}
    | "bottom" | "text-bottom" => return {s with verticalAlign := .bottom}
    | "baseline" | "sub" | "super" => return {s with verticalAlign := .baseline}
    | _ => throw "unsupported CSS vertical-align"
  | "min-width" => return {s with minWidth := ← limit d.value}
  | "max-width" => return {s with maxWidth := ← limit d.value}
  | "min-height" => return {s with minHeight := ← limit d.value}
  | "max-height" => return {s with maxHeight := ← limit d.value}
  | "object-fit" => match (trim d.value).toLower with
    | "fill" => return {s with objectFit := .fill}
    | "contain" => return {s with objectFit := .contain}
    | "cover" => return {s with objectFit := .cover}
    | "none" => return {s with objectFit := .none}
    | "scale-down" => return {s with objectFit := .scaleDown}
    | _ => throw "unsupported CSS object-fit"
  | "font-family" =>
    -- CSS Fonts 4 §2.1: a list of families, tried in order (`familyNames`).
    let some names := familyNames d.value | throw s!"unsupported font family syntax: {d.value}"
    if names.any (·.contains ',') then throw s!"unsupported font family syntax: {d.value}"
    return {s with fontFamily := familyValue names}
  | property =>
    -- The values of flex and grid layout: each reader checks the property name first.
    if let some flex := s.flex.set s.fontSize property d.value then return {s with flex}
    if let some align := s.align.set s.fontSize property d.value then return {s with align}
    if let some pos := s.pos.set s.fontSize property d.value then return {s with pos}
    throw s!"unsupported CSS property: {d.property}"

/-- A value or property this profile can not use leaves the style as it was. -/
private def applyOrKeep (s : Computed) (d : Declaration) : Computed :=
  (apply s d).toOption.getD s

/-- The declarations of `rules` and of `style` attributes that this profile can not
read, each once, in source order, as "property: value (reason)". Such a declaration is
dropped (`applyOrKeep`), as CSS error handling drops it; this list says which, so that
a page that renders wrong can be grouped by the feature it lacks. It reads each
declaration alone, with no cascade: a declaration that an overriding one hides is
listed too. -/
def droppedDeclarations (dom : Dom) (rules : List Rule) : Array String := Id.run do
  let mut seen : Std.TreeMap String Unit := {}
  let mut out : Array String := #[]
  let mut all : Array Declaration := #[]
  for rule in rules do all := all ++ rule.declarations.toArray
  for n in dom.nodes do
    if n.type == .element && hasAttribute n "style" then
      if let .ok ds := declarations (attrValue n "style") then all := all ++ ds.toArray
  for d in all do
    match apply {} d with
    | .ok _ => pure ()
    | .error reason =>
      let line := s!"{d.property}: {d.value} ({reason})"
      if !seen.contains line && out.size < 1024 then
        seen := seen.insert line ()
        out := out.push line
  return out

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

/-- HTML §3.2.6.4 `dir=auto`: the direction of the first character of bidi class
L, R or AL in the element's text, skipping `bdi`, `script`, `style` and
`textarea` elements and elements with their own `dir`; left to right if there is
none. One pass over a work list, at most the size of the arena. -/
def autoDirection (dom : Dom) (id : Nat) : Direction := Id.run do
  let mut pending : List Nat := (dom.get id).kids.toList
  for _ in [:dom.size+1] do
    match pending with
    | [] => return .ltr
    | k::rest =>
      let n := dom.get k
      pending := rest
      if n.type == .text then
        for c in n.data.toList do
          match Unicode.bidiClassOf c with
          | .L => return .ltr
          | .R | .AL => return .rtl
          | _ => pure ()
      else if n.type == .element && !["bdi","script","style","textarea"].contains n.lname &&
          !hasAttribute n "dir" then
        pending := n.kids.toList ++ pending
  return .ltr

/-- The HTML rendering section's display for table elements (HTML §15.3.8). -/
private def tableDisplay : String → Display
  | "table" => .table | "caption" => .tableCaption | "thead" => .tableHeaderGroup
  | "tbody" => .tableRowGroup | "tfoot" => .tableFooterGroup | "tr" => .tableRow
  | "td" | "th" => .tableCell | "col" => .tableColumn | "colgroup" => .tableColumnGroup
  | _ => .inline

/-- A non-negative integer attribute value with an optional `%`, as HTML's rules
for dimension values read it (HTML §2.3.4.4), in this profile's lengths. -/
def dimensionAttribute (value : String) : Option Length :=
  let v := trim value
  let digits := v.toList.takeWhile Char.isDigit
  if digits.isEmpty then none else
  let n := Float.ofNat (String.ofList digits).toNat!
  if (v.drop digits.length).toString.startsWith "%" then some (.percent (n/100)) else some (.px n)

/-- The nearest table element above a cell, within three levels (row, row group). -/
private def tableAncestor (dom : Dom) (id : Nat) : Option DOM.Node := Id.run do
  let mut cursor := (dom.get id).parent
  for _ in [0:3] do
    match cursor with
    | none => return none
    | some p =>
      if (dom.get p).lname == "table" then return some (dom.get p)
      cursor := (dom.get p).parent
  return none

/-- Presentational hints and the user agent table rules of HTML §15.3.8 and §15.3.10:
`table { border-spacing: 2px }`, `td, th { padding: 1px }`, the `cellspacing`,
`cellpadding`, `width`, `height`, `bgcolor` and `valign` attributes, and the
`vertical-align: middle` of rows and row groups that cells inherit. Author CSS
overrides them all, as it does presentation attributes. -/
private def tableHints (dom : Dom) (id : Nat) (s parent : Computed) : Computed := Id.run do
  let n := dom.get id
  let mut s := s
  let tag := n.lname
  if !["table","caption","thead","tbody","tfoot","tr","td","th","col","colgroup"].contains tag then return s
  if tag == "table" then
    let spacing := (dimensionAttribute (attrValue n "cellspacing")).bind (resolve 0)
    let v := spacing.getD 2
    s := {s with borderSpacingX := v, borderSpacingY := v, borderCollapse := false, captionBottom := false}
  if ["thead","tbody","tfoot","tr"].contains tag then s := {s with verticalAlign := .middle}
  if tag == "td" || tag == "th" then
    let pad := ((tableAncestor dom id).bind fun t => (dimensionAttribute (attrValue t "cellpadding")).bind (resolve 0)).getD 1
    s := {s with padding := ⟨pad,pad,pad,pad⟩, verticalAlign := parent.verticalAlign}
  if ["table","td","th","col"].contains tag then
    if let some w := dimensionAttribute (attrValue n "width") then
      if !(tag == "table" && (match w with | .px 0 => true | _ => false)) then s := {s with width := w}
  if ["table","td","th","tr"].contains tag then
    if let some h := dimensionAttribute (attrValue n "height") then
      if let .px _ := h then s := {s with height := h}
  if ["table","tr","td","th"].contains tag then
    let bg := attrValue n "bgcolor"
    if !bg.isEmpty then if let .ok c := color bg then s := {s with background := some c}
  if ["tr","td","th","thead","tbody","tfoot"].contains tag then
    match (attrValue n "valign").toLower with
    | "top" => s := {s with verticalAlign := .top}
    | "middle" => s := {s with verticalAlign := .middle}
    | "bottom" => s := {s with verticalAlign := .bottom}
    | "baseline" => s := {s with verticalAlign := .baseline}
    | _ => pure ()
  return s

/-- HTML §15.4.3: the `width` and `height` attributes of `img`, `video` and `canvas`
map to the `width` and `height` properties, below author CSS. -/
private def replacedHints (n : DOM.Node) (s : Computed) : Computed := Id.run do
  if !["img","video","canvas"].contains n.lname then return s
  let mut s := s
  if let some w := dimensionAttribute (attrValue n "width") then s := {s with width := w}
  if let some h := dimensionAttribute (attrValue n "height") then
    if let .px _ := h then s := {s with height := h}
  return s

private def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _::_, [] => false
  | a::as, b::bs => if a == b then lexLE as bs else a < b

/-- The user agent style sheet of this profile: HTML §15.3.4 (phrasing content:
hyperlink colours and underline) and §15.5.4 (the `button` element as an
inline-block with a raised border, sunken while it is `:active`). The colours are
the ones that HTML gives (`#0000EE`, `#551A8B`, `#FF0000`); the button colours are
this profile's choice, since HTML leaves a button's look to the platform. -/
def userAgentSheet : String :=
  ":link{color:#0000ee}" ++
  ":visited{color:#551a8b}" ++
  -- `:link,:visited` in HTML; one `:any-link` rule, so that the `:visited` colour rule stays colour only.
  ":any-link{text-decoration:underline}" ++
  ":link:active,:visited:active{color:#ff0000}" ++
  "button{display:inline-block;padding:1px 6px;border:2px outset #767676;background-color:#efefef;color:#000000}" ++
  "button:hover{background-color:#e5e5e5}" ++
  "button:active{border-style:inset;background-color:#c8c8c8}"

def userAgentRules : List Rule := (parse userAgentSheet).toOption.getD []

/-- A rule that matches only through `:visited` sets only colours (Selectors 4 §8.2,
the privacy restriction that browsers apply to visited links). -/
def visitedProperties : List String := ["color","background-color","border-color"]

/-- A rule that matches an element: its origin (0 the user agent, 1 the author), the rule,
and those of its selectors that match. -/
abbrev Match := Nat × Rule × List Selector

/-- Every rule with its origin, the user agent's first, in sheet order. -/
def ruleEntries (rules : List Rule) : List (Nat × Rule) := userAgentRules.map (0,·) ++ rules.map (1,·)

/-- The entry `e` as a match of element `id`, when one of its selectors matches. -/
def matchEntry (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (state : ElementState) (e : Nat × Rule) : Option Match :=
  let m := e.2.selectors.filter (selectorMatchesK keys dom id · state)
  if m.isEmpty then none else some (e.1,e.2,m)

/-- The reference: every rule tried, in order. -/
def matchedRules (dom : Dom) (id : Nat) (rules : List Rule) (state : ElementState := {}) : List Match :=
  (ruleEntries rules).filterMap (matchEntry (readKeys dom) dom id state)

/-! ### Rule buckets

As browsers do, each selector goes in one bucket by its rightmost compound: its id, else
its first class, else its tag, else the bucket of every element. An element tries only
the rules of the buckets it is in (`RuleIndex.candidates`), in sheet order. A selector
outside those buckets can not match (`selectorMatchesK_admits`), so the rules matched
are those of the plain loop (`matchedRules`); `RuleIndex.matched_eq` checks this on
the test pages (`CascadeTests.lean`) and `computeAll_eq_linear` lifts it to the styles. -/
inductive Bucket where
  | id (s : String) | cls (s : String) | tag (s : String) | any
  /-- A selector no element of a tree without shadow scope matches: `:host` and `::slotted()`. -/
  | never
/-- The bucket of a compound by its fields alone. -/
def Compound.fieldBucket (c : Compound) : Bucket :=
  match c.id with
  | some i => .id i
  | none => match c.classes with
    | k :: _ => .cls k
    | [] => match c.tag with
      | some t => .tag t
      | none => .any
def Compound.bucket (c : Compound) : Bucket :=
  if c.host then .never else c.fieldBucket
def Selector.bucket (sel : Selector) : Bucket :=
  if sel.slotted.isSome then .never else
  match sel.parts with
  | [] => .any
  | c :: _ => c.bucket
/-- An element with keys `k` and local name `lname` is in bucket `b`. -/
def Bucket.admits (k : ElemKey) (lname : String) : Bucket → Bool
  | .id i => i == k.id
  | .cls c => k.classes.contains c
  | .tag t => t == lname
  | .any => true
  | .never => false

/-- A compound's fields that match an element have the element in the compound's bucket. -/
private theorem compoundFieldsK_admits (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (c : Compound)
    (state : ElementState) (hc : compoundFieldsK keys dom state id c = true) :
    c.fieldBucket.admits (keys id) (dom.get id).lname = true := by
  unfold compoundFieldsK at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, htag⟩, hid⟩, hcls⟩, _⟩ := hc
  cases hi : c.id with
  | some i =>
    rw [hi] at hid
    simpa [Compound.fieldBucket, hi, Bucket.admits] using hid
  | none =>
    cases hk : c.classes with
    | cons k ks =>
      rw [hk] at hcls
      simp only [List.all_cons, Bool.and_eq_true] at hcls
      simpa [Compound.fieldBucket, hi, hk, Bucket.admits] using hcls.1
    | nil =>
      cases ht : c.tag with
      | some t =>
        rw [ht] at htag
        simpa [Compound.fieldBucket, hi, hk, ht, Bucket.admits] using htag
      | none => simp [Compound.fieldBucket, hi, hk, ht, Bucket.admits]

/-- A selector that matches an element has the element in its bucket. -/
theorem selectorMatchesK_admits (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (sel : Selector)
    (state : ElementState) (h : selectorMatchesK keys dom id sel state = true) :
    sel.bucket.admits (keys id) (dom.get id).lname = true := by
  unfold selectorMatchesK at h
  cases hp : sel.parts with
  | nil => simp [hp] at h
  | cons c rest =>
    rw [hp] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hs, hc⟩, _⟩ := h
    unfold compoundMatchesK at hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hsome : sel.slotted.isSome = false := by
      cases hsl : sel.slotted with
      | none => rfl
      | some _ => rw [hsl] at hs; simp at hs
    have := compoundFieldsK_admits keys dom id c state hc.2
    simpa [Selector.bucket, hsome, hp, Compound.bucket, hc.1] using this

/-- A selector of tree `scope` that matches element `id` has it where the scoped index
(`ScopedIndex`) looks: under `::slotted(c)`, in the bucket of `c` with a slot of that tree
assigned; under a `:host` compound, as that tree's host; otherwise, in the bucket of the
rightmost compound and in that tree. -/
theorem selectorMatchesInK_admits (keys : Nat → ElemKey) (ts : TreeScope) (state : ElementState)
    (scope : Option Nat) (id : Nat) (sel : Selector)
    (h : selectorMatchesInK keys ts state scope id sel = true) :
    match sel.slotted, sel.parts with
    | some c, _ => c.fieldBucket.admits (keys id) (ts.tree.get id).lname = true ∧
        ∃ sl, ts.tree.findSlot id = some sl ∧ ts.scopeOf sl = scope
    | none, c :: _ =>
      if c.host then hostOfScope ts scope = some id
      else c.fieldBucket.admits (keys id) (ts.tree.get id).lname = true ∧ ts.scopeOf id = scope
    | none, [] => False := by
  unfold selectorMatchesInK at h
  cases hp : sel.parts with
  | nil => simp [hp] at h
  | cons c rest =>
    rw [hp] at h
    simp only at h
    cases hs : sel.slotted with
    | none =>
      simp only [hs, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hscope, hc⟩, _⟩ := h
      unfold compoundInK at hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hhost, hfields⟩ := hc
      cases hh : c.host with
      | true =>
        simp only [hh, if_true]
        rw [hh] at hhost
        have : (hostOfScope ts scope == some id) = true := by simpa using hhost
        exact beq_iff_eq.mp this
      | false =>
        simp only [hh, Bool.false_eq_true, if_false]
        refine ⟨compoundFieldsK_admits keys ts.tree id c state hfields, ?_⟩
        rcases hscope with hb | hsc
        · rw [hh] at hb; cases hb
        · exact hsc
    | some cc =>
      simp only [hs, Bool.and_eq_true] at h
      obtain ⟨⟨_, hfields⟩, hslot⟩ := h
      refine ⟨compoundFieldsK_admits keys ts.tree id cc state hfields, ?_⟩
      cases hfs : ts.tree.findSlot id with
      | none => rw [hfs] at hslot; cases hslot
      | some sl =>
        rw [hfs] at hslot
        simp only [Bool.and_eq_true, beq_iff_eq] at hslot
        exact ⟨sl, rfl, hslot.1.1⟩

/-- The rules in buckets: `entries` is `ruleEntries`, and each bucket lists the entries
(by index, ascending, each once) with a selector in that bucket. -/
structure RuleIndex where
  entries : Array (Nat × Rule)
  byId : Std.HashMap String (Array Nat) := {}
  byClass : Std.HashMap String (Array Nat) := {}
  byTag : Std.HashMap String (Array Nat) := {}
  universal : Array Nat := #[]

private def bucketAdd (m : Std.HashMap String (List Nat)) (k : String) (i : Nat) : Std.HashMap String (List Nat) :=
  match m.get? k with
  | some (j :: rest) => if j == i then m else m.insert k (i :: j :: rest)
  | _ => m.insert k [i]
private def bucketArrays (m : Std.HashMap String (List Nat)) : Std.HashMap String (Array Nat) :=
  m.map fun _ l => l.reverse.toArray

/-- Buckets being filled, descending by entry. -/
structure RuleIndexB where
  byId : Std.HashMap String (List Nat) := {}
  byClass : Std.HashMap String (List Nat) := {}
  byTag : Std.HashMap String (List Nat) := {}
  universal : List Nat := []
  deriving Inhabited

def RuleIndexB.add (b : RuleIndexB) (bk : Bucket) (i : Nat) : RuleIndexB :=
  match bk with
  | .id k => {b with byId := bucketAdd b.byId k i}
  | .cls k => {b with byClass := bucketAdd b.byClass k i}
  | .tag k => {b with byTag := bucketAdd b.byTag k i}
  | .any => if b.universal.head? != some i then {b with universal := i :: b.universal} else b
  | .never => b

def RuleIndexB.finish (b : RuleIndexB) (entries : Array (Nat × Rule)) : RuleIndex :=
  ⟨entries, bucketArrays b.byId, bucketArrays b.byClass, bucketArrays b.byTag, b.universal.reverse.toArray⟩

/-- The buckets of `rules` (and the user agent's): one pass over the selectors. -/
def RuleIndex.build (rules : List Rule) : RuleIndex := Id.run do
  let entries := (ruleEntries rules).toArray
  let mut b : RuleIndexB := {}
  for h : i in [:entries.size] do
    for sel in entries[i].2.selectors do
      b := b.add sel.bucket i
  return b.finish entries

/-- The union of two ascending arrays, ascending, each value once: one pass, no recursion. -/
def RuleIndex.mergeAsc (a b : Array Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.mkEmpty (a.size+b.size)
  let mut i := 0
  let mut j := 0
  for _ in [:a.size+b.size] do
    match a[i]?, b[j]? with
    | some x, some y =>
      if x < y then
        out := out.push x
        i := i+1
      else if y < x then
        out := out.push y
        j := j+1
      else
        out := out.push x
        i := i+1
        j := j+1
    | some x, none =>
      out := out.push x
      i := i+1
    | none, some y =>
      out := out.push y
      j := j+1
    | none, none => break
  return out

/-- The union of ascending arrays: pairs merged in passes, so that an element with many
classes costs its candidates times the logarithm of its classes. Loops only: a sort here
recursed as deep as its input. -/
def RuleIndex.mergeRuns (runs : Array (Array Nat)) : Array Nat := Id.run do
  let mut current := runs
  for _ in [:runs.size] do
    if current.size ≤ 1 then break
    let mut next : Array (Array Nat) := Array.mkEmpty (current.size/2+1)
    let mut k := 0
    for _ in [:current.size] do
      if k+1 < current.size then
        next := next.push (RuleIndex.mergeAsc (current.getD k #[]) (current.getD (k+1) #[]))
        k := k+2
      else if k < current.size then
        next := next.push (current.getD k #[])
        k := k+2
      else break
    current := next
  return current.getD 0 #[]

/-- The entries that element (keys `k`, local name `lname`) may match: those of its
buckets, ascending, each once. -/
def RuleIndex.candidates (ix : RuleIndex) (k : ElemKey) (lname : String) : Array Nat := Id.run do
  let mut runs : Array (Array Nat) := #[ix.universal]
  if let some a := ix.byTag[lname]? then runs := runs.push a
  if !k.id.isEmpty then
    if let some a := ix.byId[k.id]? then runs := runs.push a
  for cl in k.classes do
    if let some a := ix.byClass[cl]? then runs := runs.push a
  return RuleIndex.mergeRuns runs

/-- The rules that match element `id`, from its buckets. -/
def RuleIndex.matched (ix : RuleIndex) (keys : Nat → ElemKey) (dom : Dom) (id : Nat) (state : ElementState := {}) : List Match :=
  (ix.candidates (keys id) (dom.get id).lname).toList.filterMap fun i =>
    match ix.entries[i]? with
    | some e => matchEntry keys dom id state e
    | none => none

/-! ### Rule buckets on a page with shadow trees

The same buckets, one set per tree: an element tries the user agent's rules, the rules
of its own tree, the `:host` rules of the tree it hosts, and the `::slotted()` rules of the
tree its parent hosts (the shadow root its slot is in). Numbers index the one entry
array of `ruleEntries`, so the union stays in sheet order as in `RuleIndex.matched`.
Nothing here runs on a page with no shadow host (`computeFor`, `computeAll`). -/

/-- The buckets of the rules of one tree. -/
structure TreeRules where
  normal : RuleIndex
  /-- Rules with a `:host` compound rightmost: tried only on that tree's host. -/
  hostRules : Array Nat := #[]
  slotted : RuleIndex

/-- A tree's rules while being filled. -/
structure TreeRulesB where
  normal : RuleIndexB := {}
  hostRules : List Nat := []
  slotted : RuleIndexB := {}
  deriving Inhabited

/-- The rules of each tree, in buckets: `doc` the document's, `shadow` by shadow root. -/
structure ScopedIndex where
  entries : Array (Nat × Rule)
  ua : RuleIndex
  doc : TreeRules
  shadow : Std.HashMap Nat TreeRules := {}
  empty : TreeRules

private def TreeRulesB.add (b : TreeRulesB) (sel : Selector) (i : Nat) : TreeRulesB :=
  match sel.slotted with
  | some c => {b with slotted := b.slotted.add c.fieldBucket i}
  | none => match sel.parts with
    | [] => b
    | c :: _ => if c.host then
        (if b.hostRules.head? != some i then {b with hostRules := i :: b.hostRules} else b)
      else {b with normal := b.normal.add c.fieldBucket i}

private def TreeRulesB.finish (b : TreeRulesB) (entries : Array (Nat × Rule)) : TreeRules :=
  {normal := b.normal.finish entries, hostRules := b.hostRules.reverse.toArray, slotted := b.slotted.finish entries}

/-- The scoped buckets of `rules` (and the user agent's): one pass over the selectors. -/
def ScopedIndex.build (rules : List Rule) : ScopedIndex := Id.run do
  let entries := (ruleEntries rules).toArray
  let mut ua : RuleIndexB := {}
  let mut doc : TreeRulesB := {}
  let mut shadow : Std.HashMap Nat TreeRulesB := {}
  for h : i in [:entries.size] do
    let (origin,rule) := entries[i]
    for sel in rule.selectors do
      if origin == 0 then
        ua := ua.add sel.bucket i
      else match rule.scope with
        | none => doc := doc.add sel i
        | some r => shadow := shadow.insert r ((shadow.getD r {}).add sel i)
  let none_ : TreeRulesB := {}
  return {entries, ua := ua.finish entries, doc := doc.finish entries,
          shadow := shadow.map fun _ b => b.finish entries, empty := none_.finish entries}

/-- The rules of tree `scope`. -/
def ScopedIndex.treeOf (ix : ScopedIndex) (scope : Option Nat) : TreeRules :=
  match scope with
  | none => ix.doc
  | some r => ix.shadow.getD r ix.empty

/-- The entries that element `id` (keys `k`) may match: those of the buckets above,
ascending, each once. -/
def ScopedIndex.candidates (ix : ScopedIndex) (ts : TreeScope) (k : ElemKey) (id : Nat) : Array Nat := Id.run do
  let n := ts.tree.get id
  let scope := ts.scopeOf id
  let own := ix.treeOf scope
  let mut runs : Array (Array Nat) := #[ix.ua.candidates k n.lname, own.normal.candidates k n.lname]
  if let some r := n.shadow then
    runs := runs.push (ix.treeOf (some r)).hostRules
  if let some p := n.parent then
    if let some r := (ts.tree.get p).shadow then
      runs := runs.push ((ix.treeOf (some r)).slotted.candidates k n.lname)
  return RuleIndex.mergeRuns runs

/-- The entry `e` as a match of element `id` in its tree: the user agent's rules match in
the element's tree, an author rule in the tree of its sheet. -/
def matchEntryIn (keys : Nat → ElemKey) (ts : TreeScope) (id : Nat) (state : ElementState) (e : Nat × Rule) : Option Match :=
  let scope := if e.1 == 0 then ts.scopeOf id else e.2.scope
  let m := e.2.selectors.filter (selectorMatchesInK keys ts state scope id ·)
  if m.isEmpty then none else some (e.1,e.2,m)

/-- The reference on a page with shadow trees: every rule tried, in order. -/
def matchedRulesIn (ts : TreeScope) (id : Nat) (rules : List Rule) (state : ElementState := {}) : List Match :=
  (ruleEntries rules).filterMap (matchEntryIn (readKeys ts.tree) ts id state)

/-- The rules that match element `id`, from its buckets. -/
def ScopedIndex.matched (ix : ScopedIndex) (keys : Nat → ElemKey) (ts : TreeScope) (id : Nat) (state : ElementState := {}) : List Match :=
  (ix.candidates ts (keys id) id).toList.filterMap fun i =>
    match ix.entries[i]? with
    | some e => matchEntryIn keys ts id state e
    | none => none

/-- Winning declarations are keyed by property, with importance, origin, specificity
and source order compared lexicographically (CSS Cascade 4 §6.1). The user agent
origin (`userAgentRules`) is below the author origin. Inheritance is applied first.
`matched` are the rules that match the element, in sheet order (`matchedRules`). In one
list position with the origin, a shadow tree's normal declarations lose to the document's
and its important ones win (CSS Cascade 4 §6.1 "context"), above the style attribute. -/
def computedFrom (dom : Dom) (id : Nat) (matched : List Match) (parent : Computed) : Except String Computed := do
  let n := dom.get id
  let block := ["html","body","div","p","section","main","article","header","footer","nav","aside",
    "h1","h2","h3","h4","h5","h6","ul","ol","li","dir","menu","dl","dt","dd","pre","listing","xmp","plaintext",
    "blockquote","address","center","hr","form","fieldset","figure","figcaption"].contains n.lname
  -- HTML §15.3.1 and §6.12 (the user agent's `dialog:not([open])` and
  -- `[popover]:not(:popover-open)` rules, `display: none`): a dialog that is not open and a
  -- popover that is not showing (`Node.states` bit 1) start as not rendered, as the elements
  -- of `head` do; an author rule for `display` still wins.
  let hasAttr := fun (name : String) => n.attrs.any fun a => a.ns.isNone && a.lname == name
  let hidden := ["head","style","script","title","meta","link","template","base","area","param"].contains n.lname ||
    (n.ns == some DOM.htmlNS && ((n.lname == "dialog" && !hasAttr "open") || (hasAttr "popover" && n.states % 2 == 0)))
  let svgViewport := n.ns == some DOM.svgNS && n.lname == "svg"
  let svgOverflow := attrValue n "overflow"
  let scale := headingScale n.lname
  let fontSize := if scale == 1 then parent.fontSize else (parent.fontSize*scale).round
  let mut initial : Computed := {
    color := parent.color,
    clipOverflow := svgViewport && svgOverflow != "visible", fontSize, fontFamily := parent.fontFamily,
    lineHeight := parent.lineHeightFactor.map (fontSize*·) |>.getD parent.lineHeight,
    lineHeightFactor := parent.lineHeightFactor, visible := parent.visible,
    preformatted := parent.preformatted || ["pre","listing","xmp","plaintext"].contains n.lname,
    display := if hidden then .none else if block then .block else tableDisplay n.lname,
    margin := startMargin n.lname fontSize,
    borderSpacingX := parent.borderSpacingX, borderSpacingY := parent.borderSpacingY,
    borderCollapse := parent.borderCollapse, captionBottom := parent.captionBottom,
    textAlign := parent.textAlign, direction := parent.direction}
  -- HTML §3.2.6.4 and §15.3.5: the `dir` attribute sets `direction` and isolates the
  -- element; `bdi` isolates, and `bdo` overrides with isolation. Author CSS wins.
  if n.ns == some DOM.htmlNS || n.ns.isNone then
    let dirAttr := (attrValue n "dir").toLower
    if dirAttr == "rtl" then initial := {initial with direction := .rtl}
    else if dirAttr == "ltr" then initial := {initial with direction := .ltr}
    else if dirAttr == "auto" || (n.lname == "bdi" && !hasAttribute n "dir") then
      initial := {initial with direction := autoDirection dom id}
    if n.lname == "bdo" then initial := {initial with unicodeBidi := .isolateOverride}
    else if ["rtl","ltr","auto"].contains dirAttr || n.lname == "bdi" then
      initial := {initial with unicodeBidi := .isolate}
  if n.ns == some DOM.htmlNS || n.ns.isNone then initial := replacedHints n (tableHints dom id initial parent)
  -- SVG presentation attributes have lower priority than author CSS.
  -- These properties affect HTML layout/inheritance, so compute them here.
  if svgViewport then
    for property in ["color","visibility","display"] do
      let value := attrValue n property
      if !value.isEmpty then initial := applyOrKeep initial ⟨property,value,false⟩
    for property in ["width","height"] do
      let value := trim (attrValue n property)
      if !value.isEmpty then
        -- `em` is the font size of the element (CSS Values 4 §6.1.1; BBC News draws its icons
        -- with width="1em"), `rem` that of the initial 16 px.
        let dimension ← if value == "auto" || value.endsWith "px" || value.endsWith "%" || value.endsWith "vw" || value.endsWith "vh" then length value
          else if value.endsWith "rem" then pure (.px ((← number (value.dropEnd 3).toString) * 16))
          else if value.endsWith "em" then pure (.px ((← number (value.dropEnd 2).toString) * initial.fontSize))
          else pure (.px (← number value))
        initial := if property == "width" then {initial with width := dimension}
          else {initial with height := dimension}
  let mut winners : Std.TreeMap String (List Nat × Declaration) := {}
  let mut order : Nat := 0
  for (origin,rule,matched) in matched do
    let specificity := matched.foldl (fun m s => if lexLE [m.1,m.2.1,m.2.2] [s.specificity.1,s.specificity.2.1,s.specificity.2.2] then s.specificity else m) (0,0,0)
    let onlyVisited := matched.all (·.visitedDependent)
    for d in rule.declarations do
      if !onlyVisited || visitedProperties.contains d.property then
        let context := if (origin == 1 && rule.scope.isSome) == d.important then 1 else 0
        let key := [if d.important then 1 else 0,origin*2+context,0,specificity.1,specificity.2.1,specificity.2.2,order]
        if (winners.get? d.property).all (fun old => lexLE old.1 key) then
          winners := winners.insert d.property (key,d)
      order := order+1
  for d in ← declarations (attrValue n "style") do
    let key := [if d.important then 1 else 0,2+(if d.important then 0 else 1),1,0,0,0,order]
    if (winners.get? d.property).all (fun old => lexLE old.1 key) then winners := winners.insert d.property (key,d)
    order := order+1
  -- Font size precedes line-height and inheritance-sensitive dependent values.
  let mut result := initial
  if let some (_,d) := winners.get? "font-size" then result := applyOrKeep result d
  for (key,(priority,d)) in winners.toList do
    if key != "font-size" then
      -- Inline SVG paint declarations stay with the existing SVG producer.
      -- External HTML paint rules are refused until that cascade is unified.
      if n.ns == some DOM.svgNS && priority[2]? == some 1 && !htmlProperties.contains key then pure ()
      else result := applyOrKeep result d
  -- A root or body never clips here: the window scrolls instead.
  if ["html","body"].contains n.lname then result := {result with clipOverflow := false}
  -- The children of a flex or grid container are its items: blockified.
  if parent.display.isFlex || parent.display.isGrid then result := {result with display := result.display.blockified}
  -- CSS 2.1 §9.7: an absolutely positioned or floated box is a block.
  if result.pos.isAbsolute || result.pos.float != .none then result := {result with display := result.display.blockified}
  let decoration := parent.decorationColor.orElse (fun _ => if result.underline then some result.color else none)
  return {result with underline := decoration.isSome, decorationColor := decoration}

/-- The style of element `id` with every rule tried (`matchedRules`): the reference. -/
def computed (dom : Dom) (id : Nat) (rules : List Rule) (parent : Computed)
    (state : ElementState := {}) : Except String Computed :=
  computedFrom dom id (matchedRules dom id rules state) parent

/-- Reader text scaling is applied once after inheritance/cascade. Pixel sizes
are rounded to match the supplied-font raster contract; explicit line heights
scale too. Geometry, SVG viewports and DOM source are unchanged. -/
def Computed.scaleText (s : Computed) (scale : Float) : Computed :=
  if scale == 1 then s else
  let size := max 1 (s.fontSize*scale).round
  let height := (s.lineHeightFactor.map (size*·)).getD (s.lineHeight*scale)
  {s with fontSize := size, lineHeight := height}

/-- Visit parents before children, using a work list and bounded arena size.
`matchesOf id` are the rules that match element `id`, in sheet order. -/
def computeAllWith (matchesOf : Nat → List Match) (dom : Dom) (textScale : Float := 1) : Except String (Array Computed) := do
  if !textScale.isFinite || textScale < 0.5 then throw "text scale must be finite and at least 50%"
  let mut pending := [0]
  let mut styles := Array.replicate dom.size ({} : Computed)
  for _ in [:dom.size+1] do
    match pending with
    | [] => return styles.map (·.scaleText textScale)
    | id::rest =>
      let n := dom.get id
      let parent := (n.parent.bind (styles[·]?)).getD {}
      let svgDescendant := n.ns == some DOM.svgNS && (n.parent.map (fun p => (dom.get p).ns == some DOM.svgNS)).getD false
      let style ← if n.type == .element && !svgDescendant then computedFrom dom id (matchesOf id) parent else pure {parent with
        display := .inline, width := .auto, height := .auto,
        margin := {}, padding := {}, background := none, clipOverflow := false,
        borderStyle := .none, borderWidth := ⟨3,3,3,3⟩, borderColor := none,
        autoMarginLeft := false, autoMarginRight := false, unicodeBidi := .normal,
        autoMarginTop := false, autoMarginBottom := false, align := {}, flex := {}, pos := {}}
      styles := styles.set! id style
      pending := n.kids.toList ++ rest
  throw "DOM style traversal exceeds arena bound"

/-- The styles of every node with every rule tried for every element: the reference. -/
def computeAllLinear (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  computeAllWith (fun id => matchedRules dom id rules state) dom textScale

/-- The styles of every node: the element keys read once, the rules in buckets. -/
def computeAll (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  let ix := RuleIndex.build rules
  let ks := ElemKeys.of dom
  computeAllWith (fun id => ix.matched (ks.get dom) dom id state) dom textScale

/-- The styles on a page with shadow trees, laid out on `dom` (its flat tree): the element
keys read once, the rules in buckets per tree. -/
def computeAllIn (ts : TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  let ix := ScopedIndex.build rules
  let ks := ElemKeys.of ts.tree
  computeAllWith (fun id => ix.matched (ks.get ts.tree) ts id state) dom textScale

/-- The reference for `computeAllIn`: every rule tried for every element. -/
def computeAllInLinear (ts : TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  computeAllWith (fun id => matchedRulesIn ts id rules state) dom textScale

/-- `computeAll` for a page with no shadow tree; `computeAllIn` for one with shadow trees. -/
def computeFor (treeScope : Option TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float := 1)
    (state : ElementState := {}) : Except String (Array Computed) :=
  match treeScope with
  | none => computeAll dom rules textScale state
  | some ts => computeAllIn ts dom rules textScale state

/-- The buckets give the styles of the plain loop wherever they give its matches. -/
theorem computeAll_eq_linear (dom : Dom) (rules : List Rule) (textScale : Float) (state : ElementState)
    (h : ∀ id, (RuleIndex.build rules).matched ((ElemKeys.of dom).get dom) dom id state = matchedRules dom id rules state) :
    computeAll dom rules textScale state = computeAllLinear dom rules textScale state := by
  unfold computeAll computeAllLinear
  simp only []
  rw [show (fun id => (RuleIndex.build rules).matched ((ElemKeys.of dom).get dom) dom id state) =
    (fun id => matchedRules dom id rules state) from funext h]

/-- Scoped buckets give the styles of the plain loop wherever they give its matches. -/
theorem computeAllIn_eq_linear (ts : TreeScope) (dom : Dom) (rules : List Rule) (textScale : Float) (state : ElementState)
    (h : ∀ id, (ScopedIndex.build rules).matched ((ElemKeys.of ts.tree).get ts.tree) ts id state = matchedRulesIn ts id rules state) :
    computeAllIn ts dom rules textScale state = computeAllInLinear ts dom rules textScale state := by
  unfold computeAllIn computeAllInLinear
  simp only []
  rw [show (fun id => (ScopedIndex.build rules).matched ((ElemKeys.of ts.tree).get ts.tree) ts id state) =
    (fun id => matchedRulesIn ts id rules state) from funext h]

/-- With no shadow tree, nothing about the cascade differs. -/
theorem computeFor_none (dom : Dom) (rules : List Rule) (textScale : Float) (state : ElementState) :
    computeFor none dom rules textScale state = computeAll dom rules textScale state := rfl

end L4Factoidal.Rendering.CSS

namespace L4Factoidal.Rendering.CSS
/-- `CSS.supports(property, value)` (CSS Conditional 3 §8.1): the declaration parses under
the grammar of the property table (`CssValues.supports`, the function that the style
declaration block and computed values use). Until 2026-11-14 this answered for the layout
profile alone (`apply`); it now answers for the parser, as the standard says, so a
property that parses and is not yet laid out is supported here. -/
def supportsDeclaration (property value : String) : Bool :=
  CssValues.supports (property.trimAscii.toString) value

/-! ### Tests: a dialog that is not open and a popover that is not showing are not rendered -/

private def hiddenDoc : DOM.Dom :=
  DOM.parseHtmlDocument "<dialog>x</dialog><dialog open>y</dialog><div popover>z</div><div>w</div>"

/-- The initial `display` of the nodes named `lname`, in tree order: `true` for `none`. -/
private def displayNone (d : DOM.Dom) (lname : String) : List (Option Bool) :=
  (d.nodes.toList.zipIdx.filter fun (n, _) => n.lname == lname).map fun (_, i) =>
    (computedFrom d i [] {}).toOption.map (·.display == .none)

#guard displayNone hiddenDoc "dialog" == [some true, some false]
#guard displayNone hiddenDoc "div" == [some true, some false]
-- a showing popover (`Node.states` bit 1) is rendered
#guard displayNone ({ nodes := hiddenDoc.nodes.map fun n => if n.lname == "div" then { n with states := 1 } else n } : DOM.Dom) "div" ==
  [some false, some false]

end L4Factoidal.Rendering.CSS
