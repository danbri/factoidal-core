import L4Factoidal.Rendering.Layout

/-! Printing (issue 1268). The host lays the document out for the paper with the
`print` media type, and Lean says where the pages break. A page breaks:

1. at a forced break: `break-before` or `break-after` with `page` (CSS Fragmentation
   Level 3 §3.1), or the CSS 2 `page-break-before` and `page-break-after: always`;
2. else at the lowest row of the page that no line box, image or block with
   `break-inside: avoid` (or `page-break-inside: avoid`) crosses;
3. else, when one such box is taller than a page, at the page edge: the box is cut.

Rows are device pixels from the top of the document. The host draws each page with
`printPage` and gives the images to the system print panel. -/
namespace WebPrint
open L4Factoidal

/-- A box of the layout, in device rows. -/
structure Piece where
  top : Nat
  bottom : Nat
  /-- A line box, an image, or a block with `break-inside: avoid`: a page edge does
  not cut it when it fits on a page. -/
  keep : Bool := false
  /-- A forced page break before the box. -/
  before : Bool := false
  /-- A forced page break after the box. -/
  after : Bool := false
  deriving Repr, BEq

/-- A document prints at most this many pages. -/
def maxPages : Nat := 200

/-- The page edge for a page from row `top` that can go down to row `limit`: the
lowest of `limit` and the tops of boxes on the page, that no kept box crosses.
`top` when there is none. -/
def cutAt (pieces : List Piece) (top limit pageHeight : Nat) : Nat :=
  let crosses := fun (y : Nat) => pieces.any fun p =>
    p.keep && p.top < y && y < p.bottom && p.bottom-p.top ≤ pageHeight
  let candidates := limit :: pieces.filterMap fun p => if top < p.top && p.top < limit then some p.top else none
  (candidates.filter (!crosses ·)).foldl max top

/-- A forced break at row `y` after a page from `top` acts only when a kept box
(text) starts on that page: two breaks with only margins between them give one. -/
private def forcedAfter (pieces : List Piece) (top y : Nat) : Bool :=
  top < y && pieces.any fun p => p.keep && top ≤ p.top && p.top < y

/-- The pages, as (first row, row count). Every row of `0 .. contentHeight` is on
exactly one page (`paginate_covers` below checks it on examples), up to `maxPages`. -/
def paginate (pieces : List Piece) (contentHeight pageHeight : Nat) : List (Nat × Nat) := Id.run do
  let pageHeight := max 1 pageHeight
  let forced := ((pieces.filter (·.before)).map (·.top) ++ (pieces.filter (·.after)).map (·.bottom)).filter
    (fun y => 0 < y && y < contentHeight)
  let mut top := 0
  let mut out : Array (Nat × Nat) := #[]
  for _ in [:maxPages] do
    if top >= contentHeight then break
    let limit := top+pageHeight
    let next := (forced.filter (forcedAfter pieces top ·)).foldl min limit
    let cut := if next < limit then next
      else if contentHeight ≤ limit then contentHeight
      else
        let c := cutAt pieces top limit pageHeight
        if c > top then c else limit
    out := out.push (top,cut-top)
    top := cut
  if out.isEmpty then out := #[(0,min pageHeight (max 1 contentHeight))]
  return out.toList

/-! ### The break properties of an element -/

private def lexLess : List Nat → List Nat → Bool
  | [], _ => false
  | _::_, [] => false
  | a::as, b::bs => if a == b then lexLess as bs else a < b

/-- The value of `property` for element `id`: the declaration that wins in the
cascade, of the rules that match and the `style` attribute (importance, then the
`style` attribute, then specificity, then order). These properties do not inherit. -/
def declared (dom : DOM.Dom) (rules : List Rendering.CSS.Rule) (id : Nat) (property : String) : Option String := Id.run do
  let mut best : Option (List Nat × String) := none
  let mut order := 0
  for rule in rules do
    let matching := rule.selectors.filter (Rendering.CSS.selectorMatches dom id)
    let specificity := matching.foldl (fun m s =>
      if lexLess [m.1,m.2.1,m.2.2] [s.specificity.1,s.specificity.2.1,s.specificity.2.2] then s.specificity else m) (0,0,0)
    for d in rule.declarations do
      if !matching.isEmpty && d.property == property then
        let key := [if d.important then 1 else 0,0,specificity.1,specificity.2.1,specificity.2.2,order]
        if !((best.map (fun b => lexLess key b.1)).getD false) then best := some (key,d.value)
      order := order+1
  let inline := (Rendering.CSS.declarations (Rendering.CSS.attrValue (dom.get id) "style")).toOption.getD []
  for d in inline do
    if d.property == property then
      let key := [if d.important then 1 else 0,1,0,0,0,order]
      if !((best.map (fun b => lexLess key b.1)).getD false) then best := some (key,d.value)
    order := order+1
  return best.map (·.2.trimAscii.toString.toLower)

/-- `break-before` or `break-after` with a page break, or its CSS 2 form. -/
def forcedBreak (modern legacy : Option String) : Bool :=
  (modern.map (["page","always","left","right","recto","verso"].contains ·)).getD false ||
  (legacy.map (["always","left","right"].contains ·)).getD false

/-- `break-inside: avoid` or `avoid-page`, or `page-break-inside: avoid`. -/
def avoidBreak (modern legacy : Option String) : Bool :=
  (modern.map (["avoid","avoid-page"].contains ·)).getD false || legacy == some "avoid"

private def rows (v : Float) (up : Bool) : Nat :=
  if !v.isFinite || v ≤ 0 then 0 else (if up then v.ceil else v.floor).toUInt64.toNat

/-- The pieces of a layout. A box of a block element carries its break properties;
any other box (text, an inline element, an image) is kept whole. -/
def pieces (dom : DOM.Dom) (rules : List Rendering.CSS.Rule) (styles : Array Rendering.CSS.Computed)
    (boxes : Array Rendering.Layout.Box) : List Piece :=
  boxes.toList.map fun b =>
    let top := rows b.y false
    let bottom := max (top+1) (rows (b.y+b.height) true)
    let node := dom.get b.source
    let block := node.type == .element && (styles[b.source]?.map (·.display == .block)).getD false
    if !block then {top,bottom,keep := true} else
    let get := declared dom rules b.source
    {top,bottom,keep := avoidBreak (get "break-inside") (get "page-break-inside"),
     before := forcedBreak (get "break-before") (get "page-break-before"),
     after := forcedBreak (get "break-after") (get "page-break-after")}

/-- The lowest row of the layout. -/
def contentHeight (boxes : Array Rendering.Layout.Box) : Nat :=
  boxes.foldl (fun m b => max m (rows (b.y+b.height) true)) 0

/-- White over the rows of a page image below its slice, so a line that begins on
the next page does not show at the bottom of this one. -/
def cover (width top height : Nat) : Rendering.Node :=
  let geometry : Rendering.Geometry := .rect 0 (Float.ofNat top) (Float.ofNat width) (Float.ofNat height)
  .paint {primitive := {geometry,style := {fill := .solid ⟨1,1,1⟩}}}

/-! ### Checks -/

private def line (top : Nat) : Piece := {top,bottom := top+20,keep := true}
private def lines (n : Nat) : List Piece := (List.range n).map (fun i => line (i*20))
/-- Every row from 0 to the end is on one page, in order. -/
private def covers (pages : List (Nat × Nat)) (contentHeight : Nat) : Bool :=
  (pages.foldl (fun at_ (top,height) => if at_ == some top && height > 0 then some (top+height) else none) (some 0)) == some contentHeight

-- Ten lines on 50-row pages: two lines a page, no line cut.
#guard paginate (lines 10) 200 50 == [(0,40),(40,40),(80,40),(120,40),(160,40)]
#guard covers (paginate (lines 10) 200 50) 200
-- One page when it fits.
#guard paginate (lines 3) 60 1000 == [(0,60)]
#guard paginate [] 0 100 == [(0,1)]
-- A forced break before the third line.
#guard paginate (lines 5 ++ [{top := 40,bottom := 100,before := true}]) 100 1000 == [(0,40),(40,60)]
-- Two forced breaks with no text between them make one break.
#guard paginate (lines 2 ++ [{top := 40,bottom := 40,after := true},{top := 41,bottom := 80,before := true},{top := 45,bottom := 65,keep := true}]) 80 1000 == [(0,40),(40,40)]
-- A kept block that fits on a page moves to the next page whole.
#guard paginate [line 0,{top := 30,bottom := 90,keep := true}] 90 70 == [(0,30),(30,60)]
-- A kept box taller than a page is cut at the page edge.
#guard paginate [{top := 0,bottom := 250,keep := true}] 250 100 == [(0,100),(100,100),(200,50)]
#guard covers (paginate [{top := 0,bottom := 250,keep := true}] 250 100) 250
#guard (paginate (lines 1000) 20000 10).length == maxPages
#guard forcedBreak (some "page") none && forcedBreak none (some "always") && !forcedBreak (some "auto") none
#guard avoidBreak (some "avoid") none && avoidBreak none (some "avoid") && !avoidBreak (some "auto") none
#guard cutAt [line 0,line 20,line 40] 0 50 50 == 40

end WebPrint
