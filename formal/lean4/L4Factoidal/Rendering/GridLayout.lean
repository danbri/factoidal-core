import L4Factoidal.Rendering.Fragment
import L4Factoidal.Rendering.FlexLayout
import L4Factoidal.Rendering.Grid.Align
import L4Factoidal.Rendering.Grid.Abspos
import L4Factoidal.Rendering.Grid.Baseline

/-! Grid layout (CSS Grid Layout 2) of a container's items: this module reads the
computed values (`Computed.grid`, `Computed.align`), asks the pure modules under
`Rendering/Grid/` for the explicit grid, the placement of the items, the track sizes
and the alignment offsets, all in layout units, and lays the items out through the
`Children` callbacks (`Rendering/Fragment.lean`), as flex layout does.

The steps (§5 to §12 of the specification):

1. the explicit grid from `grid-template-*` (line names, areas, `repeat()` with
   `auto-fill` and `auto-fit` counted against the container), `Grid.Template`;
2. the placement of the items in order-modified document order, `Grid.Placement`;
3. the columns: each item's min-content and max-content widths are its contributions,
   `Grid.Sizing`;
4. each item's content laid out at the width its columns give it: its height is its
   contribution to the rows; then the rows;
5. the tracks placed by `justify-content` and `align-content`, each item placed in its
   area by `justify-self` and `align-self` (auto margins first), `Grid.Align`.

Cost: an item that is not itself a flex or grid container has its content laid out
once and is then framed at its final height; an item that is such a container is laid
out a second time only when its final height differs from its natural height. A
document with no grid container never reaches this module.

Not here yet: baseline alignment (read as start), subgrid
(laid out as a nested grid), positioned children, percentage tracks resolved a second
time against a content-sized container, `aspect-ratio`. -/
namespace L4Factoidal.Rendering.Layout
open DOM CSS

/-- A px size in layout units (not negative). -/
def gridUnits (x : Float) : Nat := (LU.ofPx x).toNat

/-- Layout units in px. -/
def gridPx (u : Nat) : Float := LU.toPx (Int.ofNat u)

/-- `justify-content` or `align-content` as the distribution of free space. `normal` and
`stretch` leave the tracks at the start (auto tracks stretch in track sizing, §12.8);
`baseline` is read as `start`. `reverse`: the start of the axis is the physical right
(a right-to-left container), for `left` and `right`. -/
def gridDistribution (c : ContentAlign) (reverse : Bool) : Grid.Distribution :=
  match c with
  | .normal | .stretch | .start | .flexStart | .baseline => .start
  | .end_ | .flexEnd => .end_
  | .left => if reverse then .end_ else .start
  | .right => if reverse then .start else .end_
  | .center => .center
  | .spaceBetween => .spaceBetween
  | .spaceAround => .spaceAround
  | .spaceEvenly => .spaceEvenly

/-- Auto tracks stretch (§12.8) when the content distribution is `normal` or `stretch`. -/
def gridStretches (c : ContentAlign) : Bool := c == .normal || c == .stretch

/-- `justify-self` or `align-self` of an item (`auto` is the container's `justify-items`
or `align-items`) as the alignment in its area. `normal` is `stretch` for a grid item;
the baseline values are read as `start`. `reverse`: the start of the axis is the physical
right (a right-to-left container), for `left` and `right`. `flip`: the item's own start
side is the container's end side (an item whose direction is not the container's), for
`self-start` and `self-end`. -/
def gridSelfAlign (own container : ItemAlign) (reverse : Bool) (flip : Bool := false) : Grid.SelfAlign :=
  match (if own == .auto then container else own) with
  | .auto | .normal | .stretch => .stretch
  | .start | .flexStart | .baseline => .start
  | .end_ | .flexEnd | .lastBaseline => .end_
  | .selfStart => if flip then .end_ else .start
  | .selfEnd => if flip then .start else .end_
  | .left => if reverse then .end_ else .start
  | .right => if reverse then .start else .end_
  | .center => .center

/-- The item takes part in baseline alignment in its row (`align-self: baseline`, or
`auto` with `align-items: baseline`). `last baseline` is read as `start`. -/
def gridBaselineSelf (own container : ItemAlign) : Bool :=
  (if own == .auto then container else own) == .baseline

#guard gridSelfAlign .selfStart .normal false true == .end_
#guard gridSelfAlign .selfEnd .normal false true == .start
#guard gridSelfAlign .auto .selfStart false false == .start
#guard gridSelfAlign .left .normal true == .end_

/-- The explicit grid and the placement of the items of a grid container. -/
structure GridPlan where
  /-- The area of each item, in tracks of the implicit grid. -/
  areas : Array Grid.Area
  rows : Nat
  cols : Nat
  /-- Implicit tracks before the explicit grid. -/
  rowLead : Nat
  colLead : Nat
  colAxis : Grid.Axis
  rowAxis : Grid.Axis
  /-- The names of the lines of the explicit grid, those of the areas included. -/
  colNames : Array (List String) := #[]
  rowNames : Array (List String) := #[]

/-- §7 and §8: the explicit grid of `s` for a content box of `availW` by `availH` units
(`none`: indefinite), and the areas of `items` (already in order-modified document
order). An anonymous item (a run of text) has automatic placement. -/
def gridPlan (kids : Children) (s : Computed) (items : Array Item) (availW availH : Option Nat)
    (colGap rowGap : Nat) : GridPlan :=
  let g := s.grid
  let colAxis := g.templateColumns.expand (g.templateColumns.autoCount availW colGap)
  let rowAxis := g.templateRows.expand (g.templateRows.autoCount availH rowGap)
  let (areas, areaCols) := (Grid.parseAreas g.templateAreas).getD ([], 0)
  let areaRows := if areaCols == 0 then 0 else g.templateAreas.length
  let explicitCols := max colAxis.tracks.size areaCols
  let explicitRows := max rowAxis.tracks.size areaRows
  let colNames := Grid.lineNames colAxis.names explicitCols areas false
  let rowNames := Grid.lineNames rowAxis.names explicitRows areas true
  let raw := items.toList.map fun item =>
    let lines : GridStyle := match item with
      | .element _ => (kids.style item).grid
      | .anonymous _ _ => {}
    let row := Grid.resolveAxis rowNames lines.rowStart lines.rowEnd
    let col := Grid.resolveAxis colNames lines.columnStart lines.columnEnd
    ({row := row.1, rowSpan := row.2, col := col.1, colSpan := col.2} : Grid.RawItem)
  let shifted := Grid.shift raw
  let p := Grid.place g.flowColumn g.dense (shifted.2.1 + explicitRows) (shifted.2.2 + explicitCols) shifted.1
  {areas := p.areas, rows := p.rows, cols := p.cols, rowLead := shifted.2.1, colLead := shifted.2.2,
   colAxis, rowAxis, colNames, rowNames}

/-- The sizing function of each of the `count` tracks of an axis of the implicit grid, in
a container of `avail` units in that axis. -/
def gridTrackFns (axis : Grid.Axis) (auto : List Grid.TrackSize) (lead count : Nat) (avail : Option Nat) :
    Array Grid.TrackFn :=
  let autoTracks := auto.toArray
  Array.ofFn (n := count) fun i => (Grid.trackAt axis.tracks autoTracks lead i.val).toFn avail

/-- §12.5: what an item asks of its columns: the min-content and max-content widths of
its margin box, within its `min-width` and `max-width`; a px `width` is all three. The
minimum contribution is the min-content width (the automatic minimum size, §6.6), the
`min-width` when one is given, or the edges alone for an item that clips. -/
def gridInlineContribution (kids : Children) (item : Item) (is : Computed) (start span : Nat) :
    Except String Grid.Contribution := do
  let m := is.margin
  let b := is.borderEdges
  let p := is.padding
  let edges := m.left+m.right+b.left+b.right+p.left+p.right
  let lo := match is.minWidth with | .px v => v | _ => 0
  let hi := match is.maxWidth with | .px v => some v | _ => none
  match is.width with
  | .px w =>
    let outer := gridUnits (clampOpt lo hi w+edges)
    return {start, span, minimum := outer, minContent := outer, maxContent := outer}
  | _ =>
    let (a,c) ← kids.intrinsic item
    let minC := clampOpt lo hi (max 0 (a-edges))+edges
    let maxC := clampOpt lo hi (max 0 (c-edges))+edges
    let minimum := match is.minWidth with
      | .px v => v+edges
      | _ => if is.clipOverflow then edges else minC
    return {start, span, minimum := gridUnits minimum, minContent := gridUnits minC, maxContent := gridUnits maxC}

/-- The used border-box width of an item in an area `areaW` wide (§6.2): its `width`
(a percentage is of the area); else, stretched, the area less its margins; else its
fit-content width. -/
def gridItemWidth (kids : Children) (item : Item) (is : Computed) (areaW : Float) (stretch : Bool) :
    Except String Float := do
  let m := is.margin
  let b := is.borderEdges
  let p := is.padding
  let padH := b.left+b.right+p.left+p.right
  let content ← match CSS.resolve areaW is.width with
    | some w => pure w
    | none =>
      if stretch && !is.autoMarginLeft && !is.autoMarginRight then pure (areaW-m.left-m.right-padH)
      else do
        let (a,c) ← kids.intrinsic item
        let e := m.left+m.right+padH
        pure (min (c-e) (max (a-e) (areaW-e)))
  return max 0 (clampOpt ((CSS.resolve areaW is.minWidth).getD 0) (CSS.resolve areaW is.maxWidth) content)+padH

/-- The tracks of an axis that are collapsed (§7.2.3.2): the tracks of a
`repeat(auto-fit, …)` that no item spans. `spans` are the start track and the span of
every item in this axis. -/
def gridCollapsed (axis : Grid.Axis) (lead count : Nat) (spans : Array (Nat × Nat)) : Array Bool :=
  if !axis.autoFit.any id then Array.replicate count false
  else Array.ofFn (n := count) fun i =>
    decide (lead ≤ i.val) && axis.autoFit.getD (i.val - lead) false &&
      !spans.any fun sp => decide (sp.1 ≤ i.val) && decide (i.val < sp.1 + sp.2)

/-- The tracks that are not collapsed. -/
def gridLive (sizes : Array Nat) (collapsed : Array Bool) : Nat :=
  ((List.range sizes.size).filter fun i => !collapsed.getD i false).length

/-- The used sizes of the tracks of an axis (§12): `Grid.sizeTracks` over the tracks that
are not collapsed; a collapsed track is 0 and takes no gap. With no collapsed track
(every grid without `auto-fit`) this is `Grid.sizeTracks` itself. -/
def gridSizes (fns : Array Grid.TrackFn) (collapsed : Array Bool) (gap : Nat) (items : Array Grid.Contribution)
    (space : Grid.Space) (stretch : Bool) : Array Nat :=
  if !collapsed.any id then Grid.sizeTracks fns gap items space stretch
  else
    -- `before[i]`: the tracks before track `i` that are not collapsed
    let before := (List.range fns.size).foldl (fun (acc : Array Nat) i =>
      acc.push (acc.getD i 0 + (if collapsed.getD i false then 0 else 1))) #[0]
    let live := ((List.range fns.size).filter fun i => !collapsed.getD i false).map fun i => fns.getD i default
    let moved := items.map fun c =>
      {c with start := before.getD c.start 0, span := before.getD (c.start + c.span) 0 - before.getD c.start 0}
    let sizes := Grid.sizeTracks live.toArray gap moved space stretch
    Array.ofFn (n := fns.size) fun i => if collapsed.getD i.val false then 0 else sizes.getD (before.getD i.val 0) 0

/-- The sizes of the tracks of an axis with the gaps between those not collapsed, in units. -/
def gridExtent (sizes : Array Nat) (collapsed : Array Bool) (gap : Nat) : Nat :=
  sizes.toList.sum+gap*(gridLive sizes collapsed-1)

/-- The start of every track: the first at `offset`, each next one after the track
before it, the gap and `between`; a collapsed track starts where the next track does and
adds nothing (`Grid.trackStarts` when no track is collapsed). -/
def gridStarts (sizes : Array Nat) (collapsed : Array Bool) (gap : Nat) (offset between : Int) : Array Int :=
  if !collapsed.any id then Grid.trackStarts sizes gap offset between
  else ((List.range sizes.size).foldl (fun (acc : Array Int × Int) i =>
    if collapsed.getD i false then (acc.1.push acc.2, acc.2)
    else (acc.1.push acc.2, acc.2 + Int.ofNat (sizes.getD i 0) + Int.ofNat gap + between)) (#[], offset)).1

/-- The resolved value of `grid-template-columns` or `grid-template-rows` of a grid
container (§7.2.6): the used size of every track, implicit tracks included, with the
names of the lines of the explicit grid; `none` for no tracks. -/
def gridResolvedText (axis : Grid.Axis) (lead : Nat) (sizes : Array Nat) : String :=
  if sizes.isEmpty then "none"
  else
    let names := fun (line : Nat) =>
      if line < lead then []
      else match axis.names.getD (line - lead) [] with
        | [] => []
        | ns => ["[" ++ " ".intercalate ns ++ "]"]
    let parts := (List.range sizes.size).foldl (fun (acc : Array String) i =>
      (acc ++ (names i).toArray).push (CssValues.fmtRat (((sizes.getD i 0 : Nat) : Rat) / 64) ++ "px")) #[]
    " ".intercalate (parts ++ (names sizes.size).toArray).toList

/-- The name of the record of a grid container's used tracks in its fragment: an empty
group whose id is this name, the resolved columns and the resolved rows, separated by
tabs. -/
def gridRecordName (source : Nat) : String := s!"grid-tracks {source}"

/-- The contents of a grid container in its content box `box`: the grid formatting
context. The result's `height` is the height of the content box. -/
def gridLayout (kids : Children) (s : Computed) (items0 : Array Item) (box : ContentBox) : Except String Result := do
  let items := orderItems kids items0
  let g := s.grid
  let n := items.size
  let rtl := s.direction == .rtl
  let colGap := gridUnits (max 0 ((CSS.resolve box.width s.align.columnGap).getD 0))
  let rowGap := gridUnits (max 0 ((resolveOpt box.height s.align.rowGap).getD 0))
  let availW := gridUnits box.width
  let availH := box.height.map gridUnits
  let plan := gridPlan kids s items (some availW) availH colGap rowGap
  let styles := items.map kids.style
  -- §12.3 step 1: the columns.
  let colFns := gridTrackFns plan.colAxis g.autoColumns plan.colLead plan.cols (some availW)
  let colCollapsed := gridCollapsed plan.colAxis plan.colLead plan.cols (plan.areas.map fun a => (a.col, a.colSpan))
  let mut colItems : Array Grid.Contribution := #[]
  for i in [0:n] do
    let a := plan.areas.getD i default
    colItems := colItems.push (← gridInlineContribution kids items[i]! styles[i]! a.col a.colSpan)
  let colSizes := gridSizes colFns colCollapsed colGap colItems (.definite availW) (gridStretches s.align.justifyContent)
  let colFree : Int := Int.ofNat availW - Int.ofNat (gridExtent colSizes colCollapsed colGap)
  let colSpread := Grid.contentOffsetsInt (gridDistribution s.align.justifyContent rtl) colFree (gridLive colSizes colCollapsed)
  let colStarts := gridStarts colSizes colCollapsed colGap colSpread.1 colSpread.2
  -- §12.3 step 2: each item at the width its columns give it; its height is what it asks
  -- of its rows.
  let mut laid : Array (Result × Float × Float × Float × Float) := #[]   -- measured, x, border-box width, natural border-box height, area width
  -- the baseline-aligned items (§11.6): index, row, baseline from the margin box's top
  let mut baselined : Array (Nat × Nat × Nat) := #[]
  let mut rowItems : Array Grid.Contribution := #[]
  for i in [0:n] do
    let item := items[i]!
    let is := styles[i]!
    let a := plan.areas.getD i default
    let m := is.margin
    let extent := Grid.spanExtent colStarts colSizes a.col a.colSpan
    let areaW := gridPx extent.2
    let areaX := if rtl then box.width-LU.toPx extent.1-areaW else LU.toPx extent.1
    let justify := gridSelfAlign is.align.justifySelf s.align.justifyItems rtl (is.direction != s.direction)
    let width ← gridItemWidth kids item is areaW (justify == .stretch)
    let outerW := width+m.left+m.right
    let dx := match autoCrossOffset is.autoMarginLeft is.autoMarginRight (areaW-outerW) with
      | some d => d
      | none =>
        let d := LU.toPx (Grid.selfOffset justify (gridUnits areaW) (gridUnits outerW))
        if rtl then areaW-outerW-d else d
    let x := box.x+areaX+dx
    let padV := is.borderEdges.top+is.borderEdges.bottom+is.padding.top+is.padding.bottom
    let minH := match is.minHeight with | .px v => v | _ => 0
    let maxH := match is.maxHeight with | .px v => some v | _ => none
    let fixed := match is.height with
      | .px h => some (clampOpt minH maxH h+padV)
      | _ => none
    let r ← if kids.heightSensitive item then
        kids.layout item x box.y {available := areaW, width := some width, height := fixed}
      else kids.content item x box.y width
    let natural := if kids.heightSensitive item then r.height-m.top-m.bottom
      else fixed.getD (clampOpt minH maxH r.height+padV)
    let outerH := gridUnits (natural+m.top+m.bottom)
    rowItems := rowItems.push {start := a.row, span := a.rowSpan, minimum := outerH, minContent := outerH, maxContent := outerH}
    laid := laid.push (r,x,width,natural,areaW)
    if a.rowSpan == 1 && gridBaselineSelf is.align.alignSelf s.align.alignItems then
      -- no line box: the baseline is synthesized from the border box's bottom edge
      baselined := baselined.push (i, a.row, gridUnits ((r.baseline.map (·-box.y)).getD (m.top+natural)))
  -- §11.6: a baseline-aligned item asks of its row its height and its shift.
  let aligned := baselined.toList.map fun (_,row,b) => (row,b)
  let mut shifts : Array Nat := Array.replicate n 0
  for (i,row,b) in baselined do
    let shift := Grid.baselineShift aligned row b
    shifts := shifts.modify i fun _ => shift
    rowItems := rowItems.modify i fun c => {c with minimum := c.minimum+shift, minContent := c.minContent+shift,
                                                   maxContent := c.maxContent+shift}
  -- §12.3 step 3: the rows. A container with no definite height is as high as its rows,
  -- within its min-height and max-height; when those change the height, the rows are
  -- sized again in it.
  let rowFns := gridTrackFns plan.rowAxis g.autoRows plan.rowLead plan.rows availH
  let rowCollapsed := gridCollapsed plan.rowAxis plan.rowLead plan.rows (plan.areas.map fun a => (a.row, a.rowSpan))
  let stretchRows := gridStretches s.align.alignContent
  let firstRows := gridSizes rowFns rowCollapsed rowGap rowItems
    (match availH with | some h => .definite h | none => .indefinite) stretchRows
  let contentH := match box.height with
    | some h => h
    | none => clampOpt box.minHeight box.maxHeight (gridPx (gridExtent firstRows rowCollapsed rowGap))
  -- §7.2.1: a percentage row of a container with no definite height counts as `auto` for
  -- that height, and is then resolved against it.
  let percentRows := availH.isNone &&
    (plan.rowAxis.tracks.any (·.hasPercent) || g.autoRows.any (·.hasPercent))
  let rowFns := if percentRows then gridTrackFns plan.rowAxis g.autoRows plan.rowLead plan.rows (some (gridUnits contentH))
    else rowFns
  let rowSizes := if box.height.isNone && (percentRows || gridUnits contentH != gridExtent firstRows rowCollapsed rowGap) then
      gridSizes rowFns rowCollapsed rowGap rowItems (.definite (gridUnits contentH)) stretchRows
    else firstRows
  let rowFree : Int := Int.ofNat (gridUnits contentH) - Int.ofNat (gridExtent rowSizes rowCollapsed rowGap)
  let rowSpread := Grid.contentOffsetsInt (gridDistribution s.align.alignContent false) rowFree (gridLive rowSizes rowCollapsed)
  let rowStarts := gridStarts rowSizes rowCollapsed rowGap rowSpread.1 rowSpread.2
  -- §7.2.6: the used tracks, kept in the fragment for `getComputedStyle` (an empty group).
  let mut out : Result := match box.source with
    | some source => {nodes := #[.group (some (gridRecordName source ++ "\t" ++
        gridResolvedText plan.colAxis plan.colLead colSizes ++ "\t" ++
        gridResolvedText plan.rowAxis plan.rowLead rowSizes)) ⟨1,0,0,1,0,0⟩ []]}
    | none => {}
  -- §11: each item in its area.
  for i in [0:n] do
    let item := items[i]!
    let is := styles[i]!
    let a := plan.areas.getD i default
    let m := is.margin
    let (r,x,width,natural,areaW) := laid[i]!
    let extent := Grid.spanExtent rowStarts rowSizes a.row a.rowSpan
    let areaH := gridPx extent.2
    let padV := is.borderEdges.top+is.borderEdges.bottom+is.padding.top+is.padding.bottom
    let align := gridSelfAlign is.align.alignSelf s.align.alignItems false
    let minH := (CSS.resolve areaH is.minHeight).getD 0
    let maxH := CSS.resolve areaH is.maxHeight
    let height := match CSS.resolve areaH is.height with
      | some h => clampOpt minH maxH h+padV
      | none =>
        if align == .stretch && !is.autoMarginTop && !is.autoMarginBottom then
          max padV (clampOpt (minH+padV) (maxH.map (·+padV)) (areaH-m.top-m.bottom))
        else natural
    let outerH := height+m.top+m.bottom
    let shift := shifts.getD i 0
    let dy := if shift > 0 || (a.rowSpan == 1 && gridBaselineSelf is.align.alignSelf s.align.alignItems) then gridPx shift
      else match autoCrossOffset is.autoMarginTop is.autoMarginBottom (areaH-outerH) with
      | some d => d
      | none => LU.toPx (Grid.selfOffset align (gridUnits areaH) (gridUnits outerH))
    let y := box.y+LU.toPx extent.1+dy
    let done ← if kids.heightSensitive item then
        if (height-natural).abs < 0.01 then pure (r.shift 0 (y-box.y))
        else kids.layout item x y {available := areaW, width := some width, height := some height}
      else pure (kids.frame item x y width height (r.shift 0 (y-box.y)))
    out := out.over done
  return {out with height := contentH,
                   grid := some {x := box.x, y := box.y, width := box.width, height := contentH, rtl,
                                 colNames := plan.colNames, rowNames := plan.rowNames,
                                 colLead := plan.colLead, rowLead := plan.rowLead,
                                 colStarts, rowStarts, colSizes, rowSizes}}

/-- The min-content and max-content widths of a grid container's content box (§12.1):
the columns sized under a min-content and under a max-content constraint, with their
gaps. A percentage track or gap counts as `auto` or 0 here (its container is not sized
yet). -/
def gridIntrinsic (kids : Children) (s : Computed) (items0 : Array Item) : Except String (Float × Float) := do
  let items := orderItems kids items0
  let colGap := gridUnits (match s.align.columnGap with | .px v => max 0 v | _ => 0)
  let plan := gridPlan kids s items none none colGap 0
  let colFns := gridTrackFns plan.colAxis s.grid.autoColumns plan.colLead plan.cols none
  let collapsed := gridCollapsed plan.colAxis plan.colLead plan.cols (plan.areas.map fun a => (a.col, a.colSpan))
  let mut colItems : Array Grid.Contribution := #[]
  for i in [0:items.size] do
    let a := plan.areas.getD i default
    colItems := colItems.push (← gridInlineContribution kids items[i]! (kids.style items[i]!) a.col a.colSpan)
  let lo := gridSizes colFns collapsed colGap colItems .minContent false
  let hi := gridSizes colFns collapsed colGap colItems .maxContent false
  return (gridPx (gridExtent lo collapsed colGap),gridPx (gridExtent hi collapsed colGap))

/-- §9.1: the containing block (x, y, width, height) that a grid container whose grid is
`f` and whose padding box is `(cx,cy,cw,ch)` gives an absolutely positioned box with the
grid values `g`: the area between the lines its grid-placement properties name, a padding
edge for each `auto` line. -/
def gridAbsBlock (f : GridFrame) (cx cy cw ch : Float) (g : GridStyle) : Float × Float × Float × Float :=
  let cols := Grid.absLines f.colNames f.colLead f.colSizes.size g.columnStart g.columnEnd
  let rows := Grid.absLines f.rowNames f.rowLead f.rowSizes.size g.rowStart g.rowEnd
  -- the padding edges from the content box's start edges, in units
  let padLeft := LU.ofPx (f.x-cx)
  let padRight := LU.ofPx (cx+cw-(f.x+f.width))
  let (padStart, padEnd) := if f.rtl then (padRight, padLeft) else (padLeft, padRight)
  let w := LU.ofPx f.width
  let (s, e) := Grid.absSpan f.colStarts f.colSizes (-padStart) (w+padEnd) cols
  let (t, b) := Grid.absSpan f.rowStarts f.rowSizes (-(LU.ofPx (f.y-cy))) (LU.ofPx (cy+ch-f.y)) rows
  let x := if f.rtl then f.x+f.width-LU.toPx e else f.x+LU.toPx s
  (x, f.y+LU.toPx t, max 0 (LU.toPx (e-s)), max 0 (LU.toPx (b-t)))

/-- The absolutely positioned children of a grid container are not grid items (CSS Grid 2
§9.2). Their static position is that of a box which is the only item of an area whose edges
are the container's content edges, at the start of both axes: `fx = fy = 0`. -/
def gridAbsolutes (dom : Dom) (styles : Array Computed) (container : Nat) (x y width height : Float) : Array Pending :=
  (dom.get container).kids.filterMap fun k =>
    let cs := styles[k]!
    if (dom.get k).type == .element && cs.display != .none && cs.pos.isAbsolute then
      some {id := k, x, y, width, height}
    else none

end L4Factoidal.Rendering.Layout
