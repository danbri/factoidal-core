import L4Factoidal.Rendering.Fragment
import L4Factoidal.Rendering.Flex

/-! Flex layout (CSS Flexible Box Layout 1 §9) of a container's items: this module reads
the computed values, asks `Rendering/Flex.lean` for sizes and positions in layout units,
and lays the items out through the `Children` callbacks (`Rendering/Fragment.lean`).

What this layer does: containers in the four directions, single-line and multi-line
(`flex-wrap`, `align-content`); `order`, flex base sizes from `flex-basis`, `width`/`height` or content,
automatic minimum sizes (§4.5), the flexible lengths of §9.7, `gap`, auto margins,
`justify-content`, `align-items`/`align-self` (baseline is read as start), stretch, and
definite or content-sized containers with `min-height`/`max-height`.

Cost: an item that is not a flex or grid container has its content laid out once
(`Children.content`), then framed at its final height. An item that is such a container
is laid out a second time only when its final height differs from its natural height. -/
namespace L4Factoidal.Rendering.Layout
open DOM CSS

/-- A flex factor in millionths (`Flex.one`). -/
def flexFactor (x : Float) : Nat :=
  if x.isNaN || x <= 0 then 0 else (min x 1000000 * 1000000).round.toUInt64.toNat

/-- A length on a basis that may be indefinite: a percentage of no basis is `none`. -/
def resolveOpt (basis : Option Float) : CSS.Length → Option Float
  | .px v => some v
  | .percent p => basis.map (· * p)
  | .calc p v => basis.map (· * p + v)
  | _ => none

/-- `align-self` of an item (its own, or the container's `align-items`) as the cross-axis
alignment of the algorithm. `normal` is `stretch` in a flex container. -/
def itemAlign (container item : Computed) : Flex.Align :=
  let a := if item.align.alignSelf == .auto then container.align.alignItems else item.align.alignSelf
  match a with
  | .auto | .normal | .stretch => .stretch
  | .start | .flexStart | .selfStart | .left => .start
  | .end_ | .flexEnd | .selfEnd | .right => .end_
  | .center => .center
  | .baseline | .lastBaseline => .baseline

/-- `justify-content` as distribution from the main-start side. `reverse`: the direction
is `row-reverse` or `column-reverse` (main-start is the writing mode's end side);
`mainStartLeft`: main-start is the physical left (rows only; `none` for a column, where
`left` and `right` are `start`). -/
def mainJustify (c : ContentAlign) (reverse : Bool) (mainStartLeft : Option Bool) : Flex.Justify :=
  match c with
  | .normal | .flexStart | .stretch | .baseline => .start
  | .flexEnd => .end_
  | .start => if reverse then .end_ else .start
  | .end_ => if reverse then .start else .end_
  | .left => match mainStartLeft with
    | some l => if l then .start else .end_
    | none => if reverse then .end_ else .start
  | .right => match mainStartLeft with
    | some l => if l then .end_ else .start
    | none => if reverse then .end_ else .start
  | .center => .center
  | .spaceBetween => .spaceBetween
  | .spaceAround => .spaceAround
  | .spaceEvenly => .spaceEvenly

/-- The items in order-modified document order (§5.4): by `order`, then document order.
With no `order` in use (the usual case) the array is returned as it is. -/
def orderItems (kids : Children) (items : Array Item) : Array Item :=
  let keyed := items.map fun item => ((kids.style item).align.order, item)
  if keyed.all (fun k => k.1 == 0) then items
  else ((keyed.toList.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)).toArray

/-- Kind: structure. Says: ordering by `order` only rearranges the items: each item of
the container is laid out exactly once. Does not say: that the order is the one of §5.4
(a stable sort by `order`; tested). -/
theorem orderItems_perm (kids : Children) (items : Array Item) :
    (orderItems kids items).toList.Perm items.toList := by
  unfold orderItems
  simp only
  split
  · exact List.Perm.refl _
  · have h := (List.mergeSort_perm (items.map fun item => ((kids.style item).align.order, item)).toList
      (fun a b => decide (a.1 ≤ b.1))).map (·.2)
    simpa [List.map_map, Function.comp_def] using h

/-- A cross-axis offset from auto margins: `none` when the item has none on that axis. -/
def autoCrossOffset (startAuto endAuto : Bool) (free : Float) : Option Float :=
  if !startAuto && !endAuto then none
  else if free <= 0 then some 0
  else if startAuto && endAuto then some (free / 2)
  else if startAuto then some free else some 0

/-- A size within optional limits; the minimum wins. -/
def clampOpt (lo : Float) (hi : Option Float) (v : Float) : Float :=
  max lo (match hi with | some h => min h v | none => v)

/-- The main-axis positions of a line: for each item its margin box as `(offset, size)`
from the main-start edge, in layout units, with the share of free space that each of its
auto margins takes. §9.5: free space goes to auto margins first, else to `justify-content`. -/
def mainPositions (justify : Flex.Justify) (room gap : Int) (outers : List Int) (autos : List Nat) :
    List (Int × Int) × Int :=
  let free := room - outers.sum
  let autoCount := LU.total autos
  let autoShare : Int := if 0 < free && 0 < autoCount then free / (autoCount : Int) else 0
  let grown := (outers.zip autos).map fun (o, a) => o + autoShare * (a : Int)
  -- `Flex.spread`: each item's place is a share of the whole free space, so the last item
  -- of `space-between` ends exactly at the line's end (`Flex.lead_between_last`).
  (if 0 < autoShare then Flex.place 0 gap grown else Flex.spread justify free gap grown, autoShare)

/-- `align-content` as distribution of the lines from the cross-start side; `none` for
`stretch` (and `normal`, which is `stretch` in a flex container). `reverse`: `wrap-reverse`
(cross-start is the writing mode's end side). -/
def crossJustify (c : ContentAlign) (reverse : Bool) : Option Flex.Justify :=
  match c with
  | .normal | .stretch => none
  | .flexStart | .baseline | .left | .right => some .start
  | .flexEnd => some .end_
  | .start => some (if reverse then .end_ else .start)
  | .end_ => some (if reverse then .start else .end_)
  | .center => some .center
  | .spaceBetween => some .spaceBetween
  | .spaceAround => some .spaceAround
  | .spaceEvenly => some .spaceEvenly

/-- A row or row-reverse flex container, single-line or multi-line. -/
def flexRow (kids : Children) (s : Computed) (items : Array Item) (box : ContentBox) : Except String Result := do
  let gap := max 0 ((CSS.resolve box.width s.align.columnGap).getD 0)
  -- §9.2: flex base sizes, minimum and maximum main sizes.
  let mut cores : Array Flex.Item := #[]
  let mut styles : Array Computed := #[]
  for item in items do
    let is := kids.style item
    let m := is.margin
    let b := is.borderEdges
    let p := is.padding
    let pad := b.left+b.right+p.left+p.right
    let edges := m.left+m.right+pad
    let specified := CSS.resolve box.width is.width
    let basis := match is.flex.basis with
      | .length l => CSS.resolve box.width l
      | .auto => specified
      | .content => none
    let minSpecified := CSS.resolve box.width is.minWidth
    let hi := CSS.resolve box.width is.maxWidth
    let needContent := basis.isNone || (minSpecified.isNone && !is.clipOverflow)
    let (minContent,maxContent) ← if needContent then kids.contentIntrinsic item else pure (0,0)
    -- §4.5: the automatic minimum is the content size, no more than a specified size or the maximum.
    let lo := match minSpecified with
      | some v => v
      | none => if is.clipOverflow then 0 else
        let c := match specified with | some w => min w minContent | none => minContent
        match hi with | some h => min c h | none => c
    cores := cores.push {base := LU.ofPx (basis.getD maxContent), lo := LU.ofPx (max 0 lo), hi := hi.map LU.ofPx,
                         grow := flexFactor is.flex.grow, shrink := flexFactor is.flex.shrink, edges := LU.ofPx edges}
    styles := styles.push is
  let n := items.size
  let inner := LU.ofPx box.width
  let gapU := LU.ofPx gap
  let rtl := s.direction == .rtl
  let mainRight := rtl != s.flex.reverse
  let justify := mainJustify s.align.justifyContent s.flex.reverse (some !mainRight)
  -- §9.3: the lines. A single-line container has one, whatever its items' sizes.
  let multi := s.flex.wrap != .nowrap
  let lines : Array Nat := if multi then (Flex.breakLines inner gapU (cores.toList.map fun c => c.hyp+c.edges)).toArray else #[n]
  -- §9.7 and §9.5, line by line: used main sizes and positions.
  let mut main : Array (Float × Float) := #[]   -- x of the margin box, border-box width
  let mut first := 0
  for count in lines do
    let lineCores := (cores.extract first (first+count)).toList
    let lineStyles := (styles.extract first (first+count)).toList
    let room := inner - gapU * ((count : Int) - 1)
    let resolved := Flex.resolve room lineCores
    let autos := lineStyles.map fun is => (if is.autoMarginLeft then 1 else 0) + (if is.autoMarginRight then 1 else 0)
    let (placed,autoShare) := mainPositions justify room gapU (resolved.items.map Flex.St.outer) autos
    for ((pos,outer),(size,is)) in placed.zip (resolved.sizes.zip lineStyles) do
      let left := if mainRight then inner-pos-outer else pos
      let x := box.x+LU.toPx left+(if is.autoMarginLeft then LU.toPx autoShare else 0)
      main := main.push (x,LU.toPx size+is.borderEdges.left+is.borderEdges.right+is.padding.left+is.padding.right)
    first := first+count
  -- §9.4: each item at its main size; a line is as high as its highest item.
  let mut laid : Array (Result × Float) := #[]   -- content, natural border-box height
  for i in [0:n] do
    let item := items[i]!
    let is := styles[i]!
    let m := is.margin
    let (x,width) := main.getD i (box.x,0)
    let padV := is.borderEdges.top+is.borderEdges.bottom+is.padding.top+is.padding.bottom
    let minH := (resolveOpt box.height is.minHeight).getD 0
    let maxH := resolveOpt box.height is.maxHeight
    let fixed := (resolveOpt box.height is.height).map fun h => clampOpt minH maxH h+padV
    let r ← if kids.heightSensitive item then
        kids.layout item x box.y {available := box.width, width := some width, height := fixed}
      else kids.content item x box.y width
    let natural := if kids.heightSensitive item then r.height-m.top-m.bottom
      else fixed.getD (clampOpt minH maxH r.height+padV)
    laid := laid.push (r,natural)
  let mut lineSizes : Array Float := #[]
  first := 0
  for count in lines do
    let mut highest : Float := 0
    for i in [first:first+count] do
      let m := (styles[i]!).margin
      highest := max highest ((laid[i]!).2+m.top+m.bottom)
    lineSizes := lineSizes.push highest
    first := first+count
  -- §9.4 step 8 and §9.6: the cross size of the container and the place of each line
  -- (`align-content`); a single line fills a definite cross size.
  let crossGap := if multi then max 0 ((resolveOpt box.height s.align.rowGap).getD 0) else 0
  let gaps := crossGap*Float.ofNat (lines.size-1)
  let total := lineSizes.foldl (·+·) 0+gaps
  let innerCross := match box.height with
    | some h => h
    | none => clampOpt box.minHeight box.maxHeight total
  let reverseCross := s.flex.wrap == .wrapReverse
  let (lineHeights,lineTops) : Array Float × Array Float :=
    if !multi then (#[innerCross],#[0])
    else
      let free := innerCross-total
      let distribution := crossJustify s.align.alignContent reverseCross
      let extra := if distribution.isNone && free > 0 && lines.size > 0 then free/Float.ofNat lines.size else 0
      let sizes := lineSizes.map (·+extra)
      let (start,between) := match distribution with
        | some j => Flex.justify j (LU.ofPx free) lines.size
        | none => (0,0)
      let placed := Flex.place start (between+LU.ofPx crossGap) (sizes.toList.map LU.ofPx)
      (sizes,(placed.map fun (pos,size) =>
        if reverseCross then innerCross-LU.toPx pos-LU.toPx size else LU.toPx pos).toArray)
  -- §9.4 step 11 and §9.6: stretch, then align each item in its line.
  let mut out : Result := {}
  let mut line := 0
  first := 0
  for i in [0:n] do
    if i >= first+lines.getD line 0 then
      first := first+lines.getD line 0
      line := line+1
    let item := items[i]!
    let is := styles[i]!
    let m := is.margin
    let (r,natural) := laid[i]!
    let (x,width) := main.getD i (box.x,0)
    let lineCross := lineHeights.getD line 0
    let padV := is.borderEdges.top+is.borderEdges.bottom+is.padding.top+is.padding.bottom
    let align := itemAlign s is
    let autoCross := is.autoMarginTop || is.autoMarginBottom
    let definite := (resolveOpt box.height is.height).isSome
    let height := if align == .stretch && !definite && !autoCross then
        let minH := (resolveOpt box.height is.minHeight).getD 0
        let maxH := resolveOpt box.height is.maxHeight
        max padV (clampOpt (minH+padV) (maxH.map (·+padV)) (lineCross-m.top-m.bottom))
      else natural
    let outerCross := height+m.top+m.bottom
    let offset := match autoCrossOffset is.autoMarginTop is.autoMarginBottom (lineCross-outerCross) with
      | some d => d
      | none =>
        let d := LU.toPx (Flex.alignOffset align (LU.ofPx lineCross) (LU.ofPx outerCross))
        -- with `wrap-reverse` the cross-start side of a line is its bottom
        if reverseCross then lineCross-outerCross-d else d
    let dy := lineTops.getD line 0+offset
    let done ← if kids.heightSensitive item then
        if (height-natural).abs < 0.01 then pure (r.shift 0 dy)
        else kids.layout item x (box.y+dy) {available := box.width, width := some width, height := some height}
      else pure (kids.frame item x (box.y+dy) width height (r.shift 0 dy))
    out := out.over done
  return {out with height := innerCross}

/-- A column or column-reverse flex container (single line). -/
def flexColumn (kids : Children) (s : Computed) (items : Array Item) (box : ContentBox) : Except String Result := do
  let gap := max 0 ((resolveOpt box.height s.align.rowGap).getD 0)
  let rtl := s.direction == .rtl
  let n := items.size
  -- The cross size (width) of each item, then its content at that width: the natural height
  -- is its flex base size when `flex-basis` and `height` give none (§9.2 step 3).
  let mut cores : Array Flex.Item := #[]
  let mut styles : Array Computed := #[]
  let mut laid : Array (Option Result × Float × Float × Float) := #[]   -- measured, x, y it was measured at, border-box width
  let mut y := box.y
  for item in items do
    let is := kids.style item
    let m := is.margin
    let b := is.borderEdges
    let p := is.padding
    let padH := b.left+b.right+p.left+p.right
    let padV := b.top+b.bottom+p.top+p.bottom
    let align := itemAlign s is
    let autoCross := is.autoMarginLeft || is.autoMarginRight
    let roomW := box.width-m.left-m.right-padH
    let widthC ← match CSS.resolve box.width is.width with
      | some w => pure w
      | none =>
        if align == .stretch && !autoCross then pure roomW
        else do
          -- fit-content (CSS Sizing 3 §5.1): the max-content width, no more than the room,
          -- no less than the min-content width
          let (a,c) ← kids.contentIntrinsic item
          pure (min c (max a roomW))
    let widthC := max 0 (clampOpt ((CSS.resolve box.width is.minWidth).getD 0) (CSS.resolve box.width is.maxWidth) widthC)
    let width := widthC+padH
    let outerW := width+m.left+m.right
    let freeW := box.width-outerW
    let dx := match autoCrossOffset is.autoMarginLeft is.autoMarginRight freeW with
      | some d => d
      | none =>
        let d := LU.toPx (Flex.alignOffset align (LU.ofPx box.width) (LU.ofPx outerW))
        -- the cross-start side is the right in a right-to-left container
        if rtl then freeW-d else d
    let x := box.x+dx
    let definite := resolveOpt box.height is.height
    let basis := match is.flex.basis with
      | .length l => resolveOpt box.height l
      | .auto => definite
      | .content => none
    let minSpecified := resolveOpt box.height is.minHeight
    let hi := resolveOpt box.height is.maxHeight
    let sensitive := kids.heightSensitive item
    let needContent := basis.isNone || (minSpecified.isNone && !is.clipOverflow)
    let measured ← if sensitive then
        if needContent then some <$> kids.layout item x y {available := box.width, width := some width}
        else pure none
      else some <$> kids.content item x y width
    let contentH := match measured with
      | some r => if sensitive then max 0 (r.height-m.top-m.bottom-padV) else r.height
      | none => 0
    let lo := match minSpecified with
      | some v => v
      | none => if is.clipOverflow then 0 else
        let c := match definite with | some h => min h contentH | none => contentH
        match hi with | some h => min c h | none => c
    let core : Flex.Item := {base := LU.ofPx (basis.getD contentH), lo := LU.ofPx (max 0 lo), hi := hi.map LU.ofPx,
                             grow := flexFactor is.flex.grow, shrink := flexFactor is.flex.shrink,
                             edges := LU.ofPx (m.top+m.bottom+padV)}
    cores := cores.push core
    styles := styles.push is
    laid := laid.push (measured,x,y,width)
    y := y+LU.toPx (core.hyp+core.edges)+gap
  -- §9.2 step 2 and §9.7: the main size of the container, then of the items.
  let gapU := LU.ofPx gap
  let gaps := gapU * ((n : Int) - 1)
  let inner : Int := match box.height with
    | some h => LU.ofPx h
    | none => LU.clamp (LU.ofPx box.minHeight) (box.maxHeight.map LU.ofPx)
        ((cores.toList.map fun c => c.hyp+c.edges).sum+gaps)
  let room := inner-gaps
  let resolved := Flex.resolve room cores.toList
  let sizes := resolved.sizes.toArray
  let autos := styles.toList.map fun is => (if is.autoMarginTop then 1 else 0) + (if is.autoMarginBottom then 1 else 0)
  let (placed,autoShare) := mainPositions (mainJustify s.align.justifyContent s.flex.reverse none)
    room gapU (resolved.items.map Flex.St.outer) autos
  let placed := placed.toArray
  let mut out : Result := {}
  for i in [0:n] do
    let item := items[i]!
    let is := styles[i]!
    let m := is.margin
    let (measured,x,measuredY,width) := laid[i]!
    let padV := is.borderEdges.top+is.borderEdges.bottom+is.padding.top+is.padding.bottom
    let (pos,outer) := placed.getD i (0,0)
    let top := if s.flex.reverse then inner-pos-outer else pos
    let itemY := box.y+LU.toPx top+(if is.autoMarginTop then LU.toPx autoShare else 0)
    let height := LU.toPx (sizes.getD i 0)+padV
    let constraints : Constraints := {available := box.width, width := some width, height := some height}
    let done ← match measured with
      | none => kids.layout item x itemY constraints
      | some r =>
        if kids.heightSensitive item then
          if (height-(r.height-m.top-m.bottom)).abs < 0.01 then pure (r.shift 0 (itemY-measuredY))
          else kids.layout item x itemY constraints
        else pure (kids.frame item x itemY width height (r.shift 0 (itemY-measuredY)))
    out := out.over done
  return {out with height := LU.toPx inner}

/-- A multi-line column or column-reverse flex container (`flex-wrap: wrap` or
`wrap-reverse`): the items break into columns at the container's height (§9.3), the
flexible lengths of each column are resolved on their own (§9.7), a column is as wide as
its widest item (§9.4 step 8) and the columns are distributed across the container's
width by `align-content` (§9.6). Cost: an item that `stretch` makes wider than its own
content has that content laid out a second time, at the column's width. -/
def flexColumnWrap (kids : Children) (s : Computed) (items : Array Item) (box : ContentBox) : Except String Result := do
  let gap := max 0 ((resolveOpt box.height s.align.rowGap).getD 0)
  let crossGap := max 0 ((CSS.resolve box.width s.align.columnGap).getD 0)
  let rtl := s.direction == .rtl
  let n := items.size
  -- §9.4 step 7: the hypothetical cross size (width) of each item is its `width` or its
  -- fit-content width; its content at that width gives the flex base size when
  -- `flex-basis` and `height` give none (§9.2 step 3).
  let mut cores : Array Flex.Item := #[]
  let mut styles : Array Computed := #[]
  let mut laid : Array (Option Result × Float) := #[]   -- measured at the content box's corner, border-box width
  for item in items do
    let is := kids.style item
    let m := is.margin
    let b := is.borderEdges
    let p := is.padding
    let padH := b.left+b.right+p.left+p.right
    let padV := b.top+b.bottom+p.top+p.bottom
    let roomW := box.width-m.left-m.right-padH
    let widthC ← match CSS.resolve box.width is.width with
      | some w => pure w
      | none => do
        let (a,c) ← kids.contentIntrinsic item
        pure (min c (max a roomW))
    let widthC := max 0 (clampOpt ((CSS.resolve box.width is.minWidth).getD 0) (CSS.resolve box.width is.maxWidth) widthC)
    let width := widthC+padH
    let definite := resolveOpt box.height is.height
    let basis := match is.flex.basis with
      | .length l => resolveOpt box.height l
      | .auto => definite
      | .content => none
    let minSpecified := resolveOpt box.height is.minHeight
    let hi := resolveOpt box.height is.maxHeight
    let sensitive := kids.heightSensitive item
    let needContent := basis.isNone || (minSpecified.isNone && !is.clipOverflow)
    let measured ← if sensitive then
        if needContent then some <$> kids.layout item box.x box.y {available := box.width, width := some width}
        else pure none
      else some <$> kids.content item box.x box.y width
    let contentH := match measured with
      | some r => if sensitive then max 0 (r.height-m.top-m.bottom-padV) else r.height
      | none => 0
    let lo := match minSpecified with
      | some v => v
      | none => if is.clipOverflow then 0 else
        let c := match definite with | some h => min h contentH | none => contentH
        match hi with | some h => min c h | none => c
    let core : Flex.Item := {base := LU.ofPx (basis.getD contentH), lo := LU.ofPx (max 0 lo), hi := hi.map LU.ofPx,
                             grow := flexFactor is.flex.grow, shrink := flexFactor is.flex.shrink,
                             edges := LU.ofPx (m.top+m.bottom+padV)}
    cores := cores.push core
    styles := styles.push is
    laid := laid.push (measured,width)
  -- §9.3: the columns. The container breaks at its height, or at its `max-height` when
  -- its height is the content's; with neither there is one column.
  let gapU := LU.ofPx gap
  let hyps := cores.toList.map fun c => c.hyp+c.edges
  let limit : Option Int := match box.height with
    | some h => some (LU.ofPx h)
    | none => box.maxHeight.map LU.ofPx
  let lines : Array Nat := match limit with
    | some l => (Flex.breakLines l gapU hyps).toArray
    | none => if n == 0 then #[] else #[n]
  -- The main size of the container: its height, or that of the longest column.
  let mut longest : Int := 0
  let mut first := 0
  for count in lines do
    let lineHyps := (hyps.drop first).take count
    longest := max longest (lineHyps.sum+gapU*((count : Int)-1))
    first := first+count
  let inner : Int := match box.height with
    | some h => LU.ofPx h
    | none => LU.clamp (LU.ofPx box.minHeight) (box.maxHeight.map LU.ofPx) longest
  -- §9.7 and §9.5, column by column: used heights and positions.
  let justify := mainJustify s.align.justifyContent s.flex.reverse none
  let mut main : Array (Float × Float) := #[]   -- top of the margin box from the content box's top, border-box height
  first := 0
  for count in lines do
    let lineCores := (cores.extract first (first+count)).toList
    let lineStyles := (styles.extract first (first+count)).toList
    let room := inner - gapU * ((count : Int) - 1)
    let resolved := Flex.resolve room lineCores
    let autos := lineStyles.map fun is => (if is.autoMarginTop then 1 else 0) + (if is.autoMarginBottom then 1 else 0)
    let (placed,autoShare) := mainPositions justify room gapU (resolved.items.map Flex.St.outer) autos
    for ((pos,outer),(size,is)) in placed.zip (resolved.sizes.zip lineStyles) do
      let top := if s.flex.reverse then inner-pos-outer else pos
      let dy := LU.toPx top+(if is.autoMarginTop then LU.toPx autoShare else 0)
      main := main.push (dy,LU.toPx size+is.borderEdges.top+is.borderEdges.bottom+is.padding.top+is.padding.bottom)
    first := first+count
  -- §9.4 step 8: a column is as wide as the widest margin box in it.
  let mut lineSizes : Array Float := #[]
  first := 0
  for count in lines do
    let mut widest : Float := 0
    for i in [first:first+count] do
      let m := (styles[i]!).margin
      widest := max widest ((laid[i]!).2+m.left+m.right)
    lineSizes := lineSizes.push widest
    first := first+count
  -- §9.6: the columns across the container's width (`align-content`); `stretch` shares
  -- the free width between them. The cross-start side is the left, or the right in a
  -- right-to-left container; `wrap-reverse` swaps the two.
  let reverseCross := s.flex.wrap == .wrapReverse
  let fromRight := rtl != reverseCross
  let total := lineSizes.foldl (·+·) 0+crossGap*Float.ofNat (lines.size-1)
  let free := box.width-total
  let distribution : Option Flex.Justify := match s.align.alignContent with
    | .left => some (if fromRight then .end_ else .start)
    | .right => some (if fromRight then .start else .end_)
    | other => crossJustify other reverseCross
  let extra := if distribution.isNone && free > 0 && lines.size > 0 then free/Float.ofNat lines.size else 0
  let sizes := lineSizes.map (·+extra)
  let (start,between) := match distribution with
    | some j => Flex.justify j (LU.ofPx free) lines.size
    | none => (0,0)
  let placed := Flex.place start (between+LU.ofPx crossGap) (sizes.toList.map LU.ofPx)
  let lineLefts : Array Float := (placed.map fun (pos,size) =>
    if fromRight then box.width-LU.toPx pos-LU.toPx size else LU.toPx pos).toArray
  -- §9.4 step 11 and §9.6: stretch, then align each item in its column.
  let mut out : Result := {}
  let mut line := 0
  first := 0
  for i in [0:n] do
    if i >= first+lines.getD line 0 then
      first := first+lines.getD line 0
      line := line+1
    let item := items[i]!
    let is := styles[i]!
    let m := is.margin
    let (measured,hypWidth) := laid[i]!
    let (dy,height) := main.getD i (0,0)
    let lineCross := sizes.getD line 0
    let padH := is.borderEdges.left+is.borderEdges.right+is.padding.left+is.padding.right
    let align := itemAlign s is
    let autoCross := is.autoMarginLeft || is.autoMarginRight
    let stretched := align == .stretch && (CSS.resolve box.width is.width).isNone && !autoCross
    let width := if stretched then
        max padH (clampOpt ((CSS.resolve box.width is.minWidth).getD 0+padH)
          ((CSS.resolve box.width is.maxWidth).map (·+padH)) (lineCross-m.left-m.right))
      else hypWidth
    let outerW := width+m.left+m.right
    let offset := match autoCrossOffset is.autoMarginLeft is.autoMarginRight (lineCross-outerW) with
      | some d => d
      | none =>
        let d := LU.toPx (Flex.alignOffset align (LU.ofPx lineCross) (LU.ofPx outerW))
        if fromRight then lineCross-outerW-d else d
    let x := box.x+lineLefts.getD line 0+offset
    let itemY := box.y+dy
    let constraints : Constraints := {available := box.width, width := some width, height := some height}
    let done ← match measured with
      | none => kids.layout item x itemY constraints
      | some r =>
        if kids.heightSensitive item then kids.layout item x itemY constraints
        else if (width-hypWidth).abs < 0.01 then
          pure (kids.frame item x itemY width height (r.shift (x-box.x) (itemY-box.y)))
        else do
          let again ← kids.content item x itemY width
          pure (kids.frame item x itemY width height again)
    out := out.over done
  return {out with height := LU.toPx inner}

/-- The contents of a flex container in its content box `box`: the flex formatting
context. The result's `height` is the height of the content box. -/
def flexLayout (kids : Children) (s : Computed) (items : Array Item) (box : ContentBox) : Except String Result :=
  let items := orderItems kids items
  if s.flex.column then
    if s.flex.wrap != .nowrap then flexColumnWrap kids s items box else flexColumn kids s items box
  else flexRow kids s items box

/-- The min-content and max-content widths of a flex container's content box (§9.9.1,
simplified): a row is the sum of its items' contributions and gaps, a column the largest. -/
def flexIntrinsic (kids : Children) (s : Computed) (items : Array Item) : Except String (Float × Float) := do
  let mut lo : Float := 0
  let mut hi : Float := 0
  for item in items do
    let (a,b) ← kids.intrinsic item
    if s.flex.column then
      lo := max lo a
      hi := max hi b
    else
      lo := lo+a
      hi := hi+b
  if !s.flex.column && items.size > 1 then
    let gap := match s.align.columnGap with | .px v => max 0 v | _ => 0
    let gaps := gap*Float.ofNat (items.size-1)
    lo := lo+gaps
    hi := hi+gaps
  return (lo,hi)

/-- The absolutely positioned children of a flex container, pending at their static
positions (§4.1): each as if it were the only item, aligned in the content box
`(x,y,width,height)` by `justify-content` on the main axis and its `align-self` on the
cross axis. `space-between` is `start` and the other distributions are centred, as for
one item. -/
def flexAbsolutes (dom : Dom) (styles : Array Computed) (container : Nat) (x y width height : Float) : Array Pending :=
  let s := styles[container]!
  let rtl := s.direction == .rtl
  (dom.get container).kids.filterMap fun k =>
    let cs := styles[k]!
    if (dom.get k).type == .element && cs.display != .none && cs.pos.isAbsolute then
      let mainEnd := if s.flex.column then s.flex.reverse else rtl != s.flex.reverse
      let main : Float := match mainJustify s.align.justifyContent s.flex.reverse (if s.flex.column then none else some !mainEnd) with
        | .start | .spaceBetween => 0
        | .end_ => 1
        | .center | .spaceAround | .spaceEvenly => 0.5
      let main := if mainEnd then 1-main else main
      let crossEnd := if s.flex.column then rtl else s.flex.wrap == .wrapReverse
      let cross : Float := match itemAlign s cs with
        | .start | .stretch | .baseline => 0
        | .end_ => 1
        | .center => 0.5
      let cross := if crossEnd then 1-cross else cross
      some {id := k, x, y, width, height,
            fx := if s.flex.column then cross else main, fy := if s.flex.column then main else cross}
    else none

/-- Viewport lengths of the flex, alignment and inset values, once the viewport is known. -/
def flexAtViewport (width height : Float) (s : Computed) : Computed :=
  {s with align := {s.align with rowGap := s.align.rowGap.atViewport width height,
                                 columnGap := s.align.columnGap.atViewport width height},
          pos := {s.pos with top := s.pos.top.atViewport width height, right := s.pos.right.atViewport width height,
                             bottom := s.pos.bottom.atViewport width height, left := s.pos.left.atViewport width height},
          flex := match s.flex.basis with
            | .length l => {s.flex with basis := .length (l.atViewport width height)}
            | _ => s.flex}

end L4Factoidal.Rendering.Layout
