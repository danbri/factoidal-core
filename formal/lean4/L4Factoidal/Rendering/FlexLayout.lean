import L4Factoidal.Rendering.Fragment
import L4Factoidal.Rendering.Flex

/-! Flex layout (CSS Flexible Box Layout 1 §9) of a container's items: this module reads
the computed values, asks `Rendering/Flex.lean` for sizes and positions in layout units,
and lays the items out through the `Children` callbacks (`Rendering/Fragment.lean`).

What this layer does: single-line containers in the four directions (`flex-wrap` is read
as `nowrap`), `order`, flex base sizes from `flex-basis`, `width`/`height` or content,
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
  let keyed := items.mapIdx fun i item => ((kids.style item).align.order, i, item)
  if keyed.all (fun k => k.1 == 0) then items
  else (keyed.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).map (·.2.2)

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
  let autoCount := autos.sum
  let autoShare : Int := if 0 < free && 0 < autoCount then free / (autoCount : Int) else 0
  let (start, between) := if 0 < autoShare then (0, 0) else Flex.justify justify free outers.length
  let grown := (outers.zip autos).map fun (o, a) => o + autoShare * (a : Int)
  (Flex.place start (between + gap) grown, autoShare)

/-- A row or row-reverse flex container (single line). -/
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
  -- §9.7 and §9.5: used main sizes and positions.
  let n := items.size
  let inner := LU.ofPx box.width
  let gapU := LU.ofPx gap
  let room := inner - gapU * ((n : Int) - 1)
  let resolved := Flex.resolve room cores.toList
  let sizes := resolved.sizes.toArray
  let rtl := s.direction == .rtl
  let mainRight := rtl != s.flex.reverse
  let autos := styles.toList.map fun is => (if is.autoMarginLeft then 1 else 0) + (if is.autoMarginRight then 1 else 0)
  let (placed,autoShare) := mainPositions (mainJustify s.align.justifyContent s.flex.reverse (some !mainRight))
    room gapU (resolved.items.map Flex.St.outer) autos
  let placed := placed.toArray
  -- §9.4: each item at its main size; the line is as high as its highest item.
  let mut laid : Array (Result × Float × Float × Float) := #[]   -- content, x, natural border-box height, border-box width
  let mut highest : Float := 0
  for i in [0:n] do
    let item := items[i]!
    let is := styles[i]!
    let m := is.margin
    let b := is.borderEdges
    let p := is.padding
    let (pos,outer) := placed.getD i (0,0)
    let left := if mainRight then inner-pos-outer else pos
    let x := box.x+LU.toPx left+(if is.autoMarginLeft then LU.toPx autoShare else 0)
    let width := LU.toPx (sizes.getD i 0)+b.left+b.right+p.left+p.right
    let padV := b.top+b.bottom+p.top+p.bottom
    let minH := (resolveOpt box.height is.minHeight).getD 0
    let maxH := resolveOpt box.height is.maxHeight
    let fixed := (resolveOpt box.height is.height).map fun h => clampOpt minH maxH h+padV
    let r ← if kids.heightSensitive item then
        kids.layout item x box.y {available := box.width, width := some width, height := fixed}
      else kids.content item x box.y width
    let natural := if kids.heightSensitive item then r.height-m.top-m.bottom
      else fixed.getD (clampOpt minH maxH r.height+padV)
    highest := max highest (natural+m.top+m.bottom)
    laid := laid.push (r,x,natural,width)
  let lineCross := match box.height with
    | some h => h
    | none => clampOpt box.minHeight box.maxHeight highest
  -- §9.4 step 11 and §9.6: stretch, then align each item in the line.
  let mut out : Result := {}
  for i in [0:n] do
    let item := items[i]!
    let is := styles[i]!
    let m := is.margin
    let (r,x,natural,width) := laid[i]!
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
    let dy := match autoCrossOffset is.autoMarginTop is.autoMarginBottom (lineCross-outerCross) with
      | some d => d
      | none => LU.toPx (Flex.alignOffset align (LU.ofPx lineCross) (LU.ofPx outerCross))
    let done ← if kids.heightSensitive item then
        if (height-natural).abs < 0.01 then pure (r.shift 0 dy)
        else kids.layout item x (box.y+dy) {available := box.width, width := some width, height := some height}
      else pure (kids.frame item x (box.y+dy) width height (r.shift 0 dy))
    out := out.over done
  return {out with height := lineCross}

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

/-- The contents of a flex container in its content box `box`: the flex formatting
context. The result's `height` is the height of the content box. -/
def flexLayout (kids : Children) (s : Computed) (items : Array Item) (box : ContentBox) : Except String Result :=
  let items := orderItems kids items
  if s.flex.column then flexColumn kids s items box else flexRow kids s items box

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

/-- Viewport lengths of the flex and alignment values, once the viewport is known. -/
def flexAtViewport (width height : Float) (s : Computed) : Computed :=
  {s with align := {s.align with rowGap := s.align.rowGap.atViewport width height,
                                 columnGap := s.align.columnGap.atViewport width height},
          flex := match s.flex.basis with
            | .length l => {s.flex with basis := .length (l.atViewport width height)}
            | _ => s.flex}

end L4Factoidal.Rendering.Layout
