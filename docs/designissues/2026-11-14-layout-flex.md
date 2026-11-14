# Layout: formatting contexts, flexbox and positioning (2026-11-14)

State of `Rendering/Layout.lean` before this work: block flow, inline lines and tables, in `Float` px, with
no flex, grid, positioning, floats, `box-sizing` or height limits. `display: flex` was dropped by the cascade, so
a flex container was a block and its items stacked. This record covers the interface that lets formatting
contexts nest, flex layout, positioning, and what is proved.

## 1. The interface between formatting contexts

One rule: **constraints in, fragment out**, and a context never recurses by itself.

- **Fragment** (`Rendering/Fragment.lean`): `Result {nodes, boxes, runs, height, pending}`. Paint nodes, the border
  box of each element (`boxes[0]` is the box's own), glyph runs, the margin-box height, and the absolutely
  positioned descendants that an ancestor still has to lay out. Coordinates are absolute; `Result.shift` moves a
  fragment, `Result.over` puts one over another.
- **Constraints**: `Constraints {available, width?, height?}`. `available` is the containing block's width;
  `width` and `height` are border-box sizes that the parent context imposes (a flex item's main size, a
  stretched item, an absolutely positioned box, later a grid area).
- **Tasks** of `layoutTask` (the one recursive function, on fuel): `box id` (size yourself in `available`),
  `sized id width height?` (an imposed border box), `inner id width` (contents only), `contents container kids`
  (an anonymous box), `table ...`, `positioned pending cx cy cw ch` (the root's absolutely positioned boxes).
- **Items and callbacks**: `Item` is `element id` or `anonymous container kids` (a run of text).
  `Children {style, intrinsic, contentIntrinsic, layout, content, frame, heightSensitive}` is what a context may
  ask about its items. `layoutTask` builds the record from itself with the smaller fuel, so flex layout
  (`Rendering/FlexLayout.lean`) and grid layout are ordinary functions:
  `layout : Children → Computed → Array Item → ContentBox → Except String Result` and
  `intrinsic : Children → Computed → Array Item → Except String (Float × Float)`.
- **Dispatch**: in `layoutTask`'s box case, after the box's own width, edges and height limits are resolved as for
  any box, the contents come from `flexLayout` when `display` is `flex`/`inline-flex`, else from block flow;
  the same in `intrinsic` (`boxWidths`). Grid adds its branch at the same two places. Block in flex, flex in
  block, flex in flex, table in flex and flex in table go through the one function.
- **Computed values**: one sub-structure of `Computed` per concern, each in a module that imports only the
  property table: `Computed.align` (`BoxAlign.lean`: content and self alignment, gaps, `order`), `Computed.flex`
  (`FlexStyle.lean`), `Computed.pos` (`BoxPosition.lean`: `position`, insets, `z-index`, `float`, `clear`,
  `box-sizing`). `Style.apply` tries each reader after its own properties; a reader checks the property name
  before it parses anything. Every value is validated and made canonical by `CssValues.specified` /
  `computed` / `expand`: there is no second parser of CSS values. Shorthands that layout reads (`flex`,
  `flex-flow`, `gap`, `place-*`, `inset`) become longhands in a declaration block, so the cascade orders them.
- **Units for proofs**: `Rendering/LayoutUnit.lean`. Space is divided on `Int` in 1/64 px (`LU.ofPx`, `LU.toPx`),
  because nothing can be proved about `Float`. `LU.distribute` splits a space by weights with a running
  remainder, so the shares sum to exactly the space.

Cost rule built into the interface: an item that is not a flex or grid container has its contents laid out once
(`Children.content`) and is then framed at its final height (`Children.frame`, `frameBox`): stretching does not
lay it out again. An item whose contents depend on its height (`heightSensitive`: a flex or grid container, a
table, a replaced element, a positioned box) is laid out a second time only when its final height differs from
its natural height.

## 2. Flex layout (CSS Flexible Box Layout 1 §9)

`Rendering/Flex.lean` is the algorithm as pure functions on layout units; `Rendering/FlexLayout.lean` reads the
computed values, calls it, and lays the items out.

Done: row, row-reverse, column, column-reverse; right-to-left; `order`; flex base size from `flex-basis`,
`width`/`height` or content; automatic minimum size (§4.5); hypothetical sizes; lines (`flex-wrap`,
`wrap-reverse`) for rows; flexible lengths with the freeze loop (§9.7), including factors that sum to less than
1; `gap`; auto margins on both axes; `justify-content`; `align-items`/`align-self`; `align-content`; stretch;
definite and content-sized containers with `min-height`/`max-height`; nested containers; `inline-flex` as an
atomic inline box; anonymous items for text; blockified items; absolutely positioned children with the static
position of §4.1; intrinsic widths of a container (sum for a row, largest for a column).

Added in the second round (section 6): wrapping columns (`flexColumnWrap`), main-axis distribution with no
lost remainder (`Flex.lead`, `Flex.spread`), the min-content width of a wrapping row.

Not done: baseline alignment (read as start; it waits for a first-baseline field of `Result` that the grid
work adds); `visibility: collapse`; aspect ratio of replaced items; intrinsic widths of wrapping columns;
vertical writing modes; fragmentation.

## 3. Positioning, box sizing, lengths

- `position: relative`: the laid-out box is shifted (`left` over `right`, `top` over `bottom`).
- `position: absolute` and `fixed`: the box is `pending` in its fragment with its static position until the
  nearest positioned ancestor knows its height; that ancestor lays it out in its padding box (CSS 2.1 §10.3.7,
  §10.6.4: insets, fill between two insets, shrink-to-fit, auto margins). The root does the same with the
  viewport (`layoutRoot`). `z-index` orders them under or over the in-flow content; this is not the whole of
  the stacking order (CSS 2.1 Appendix E).
- `offsetParent`, `offsetLeft`, `offsetTop`: decided by `Rendering/OffsetParent.lean` (CSSOM View §7) and
  answered with the layout read (op 17). The host wraps the node.
- `box-sizing: border-box`: taken out of a style before layout (`contentBoxed`), so the layout reads
  content-box sizes only.
- `Length` gains `calc (percent) (px)`: `calc(100% - 2rem)` and border-box percentages.
- Blocks honour `min-height` and `max-height` (px).

Added in the second round (section 6): margin collapse, floats and `clear`, percentage heights against a
height that the styles make definite.

Not done: `position: sticky` offsets (laid out as relative with no offset), fixed boxes that stay put on
scroll (they are laid out once in the first viewport), percentage heights against a height known only in
layout (a stretched flex item, the root), overflow scroll containers, multi-column, self-alignment of
absolutely positioned boxes (CSS Align 3 §6.1.2), the sizing keywords (`min-content`, `max-content`,
`fit-content`, `stretch`) as values of `width` and `height`.

## 4. Proved, tested, open

Proved (Lean theorems; axioms `propext`, `Classical.choice`, `Quot.sound` only):

| Theorem | Says |
|---|---|
| `LU.distribute_sum` | shares of a space sum to exactly the space when a weight is not zero |
| `LU.distribute_length`, `distribute_zero`, `distribute_sum_zero`, `distribute_eq_spec` | one share per weight; a zero weight gets nothing; the loop equals the plain recursion |
| `LU.le_clamp`, `clamp_le`, `clamp_idem`, `clamp_of_within` | a clamped size is within its limits, a minimum wins |
| `Flex.resolve_frozen` (`round_decreases`) | flexible lengths of n items are final within n rounds |
| `Flex.resolve_bounds` | no item is smaller than its minimum or larger than its maximum (a minimum wins) |
| `Flex.resolve_exact`, `resolve_exact_sizes` | when the last round flexed with no violation, the outer sizes sum to exactly the room: with the gaps, the container's inner main size |
| `Flex.resolve_items` | the result has the items it was given, in order |
| `Flex.place_pairwise`, `place_snd` | boxes placed along a line do not overlap; sizes are kept |
| `Flex.justify_between_nonneg`, `justify_fits` | content distribution never pulls items together; with free space the items stay inside the line |
| `Flex.breakLines_sum`, `breakLines_pos` | every item is on exactly one line; no line is empty |
| `Flex.alignOffset_within` | an item no larger than its line lies inside it |
| `Layout.offsetParent_sound`, `offsetAncestor_sound` | an offset parent is positioned, or the body, or a table cell or table |
| `LinkTheorems.render_links`, `render_link_complete` | restated on `layoutRoot` (the root with its positioned boxes); proofs unchanged |
| `Floats.leftEdge_ge`, `rightEdge_le`, `leftEdge_clears`, `rightEdge_clears` | the room beside floats is inside the container and beside every float that meets the range |
| `Floats.clearY_ge`, `clearY_clears` | clearance never moves a box up; a cleared box is below every float of the sides it clears |
| `Floats.place_disjoint` | a float placed by `place` shares no point with a float placed before it |
| `Flex.lead_nonneg`, `lead_mono`, `lead_le` | distribution never pulls an item before the line's start or towards the item before it; the last item ends inside the line |
| `Flex.lead_between_last` | with `space-between`, free space and two or more items, the last item ends exactly at the line's end, whatever the remainder of the division |
| `Flex.spread_pairwise`, `spread_snd` | boxes placed by `spread` do not overlap; sizes are kept |
| `Layout.percentHeights_size`, `percentHeights_get` | resolving percentage heights keeps one style per node |
| `Layout.percentHeight_rest`, `percentHeight_px`, `percentHeight_auto`, `percentHeight_absolute` | the pass changes nothing of a style but its height; a length, `auto` and the style of an absolutely positioned box are left as they are |
| `Ratio.autoSize_min`, `autoSize_max`, `fromWidth_min`, `fromHeight_min` | a size from a preferred aspect ratio is within `min-width`/`min-height`, and within the maximums unless a minimum is larger |
| `Ratio.autoSize_ratio` | when the height that the ratio gives the used width is within the height's own limits it is the used height: the box has the ratio |
| `Ratio.autoSize_natural`, `heightFor_widthFor_le` | with no limits the natural width stands; a maximum carried to the other axis and back is not exceeded |
| `Layout.keywordWidth_isSome`, `resolve_keyword` | a width is taken from the contents or the fill width exactly when it is a sizing keyword; `CSS.resolve` answers `none` for a keyword, so code that does not know them lays the box out as `auto` |
| `Layout.shrinkWidth_minContent`, `_maxContent`, `_auto` | a box that shrinks to fit takes its min-content or max-content width when its `width` says so, fit-content otherwise |
| `ScrollExtent.extent_ge_client`, `extent_ge_kid`, `extent_inside` | the scroll size is never less than the client size; every box inside is within it; with no overflow it is the client size |

Tested only (`#guard` through `Layout.render`, original fixtures): `FlexLayoutTests.lean` (90 cases),
`PositionLayoutTests.lean` (47 cases), and the readers' guards in `BoxAlign.lean`, `FlexStyle.lean`,
`BoxPosition.lean`. The glue in `FlexLayout.lean` and the positioned layout in `Layout.lean` are tested, not
proved: what they pass to the proved functions (base sizes, minimums, reversal, auto margins, stretch) is where
an error would be.

Open:

- The theorems are about layout units. Px values are units/64, exact in `Float` below 2^46 units; the conversion
  is not a theorem.
- "Layout is deterministic" holds by construction (pure functions, no state). Idempotence of a second layout
  with the same constraints is the same statement; there is no cache whose validity would need a proof.
- Cost: no theorem yet that an unchanged subtree is not laid out again. `intrinsic` is recomputed at each
  nesting level of flex containers (an item's content is measured once per flex ancestor); a cache of intrinsic
  sizes by node is the fix. Layout times of the eight pages are not measured yet (no macOS engine of this
  branch); the cloud check's WPT durations are the only timing so far.
- Grid: separate record by agent `grid`.

## 5. Measured

**First round (flex, positioning; merged as main 5cfcaf872)** (run 43563338346, core 558b4eab0, baseline main 19fb349c1):

| Directory | Chrome subtests | Baseline | This | Difference |
|---|---:|---:|---:|---:|
| css/css-flexbox | 4813 | 573 | 1093 | +520 |
| css/css-grid | 16015 | 2846 | 3081 | +235 |
| css/css-sizing | 6523 | 2077 | 2160 | +83 |
| css/css-align | 5435 | 2928 | 2874 | -54 |
| editing/other | 41 | 2 | 32 | +30 |
| css/css-position | 1553 | 574 | 589 | +15 |
| content-security-policy/embedded-enforcement | 13 | 0 | 7 | +7 |
| html/syntax | 14 | 8 | 13 | +5 |
| css/cssom-view | 2 | 1 | 0 | -1 |
| css/CSS2 | 2566 | 1826 | 1826 | +0 |
| css/css-box | 5 | 5 | 5 | +0 |
| css/css-overflow | 4 | 0 | 0 | +0 |

All names of the check: {"names": 2469, "run": 2469, "chrome": 48660, "passed": 21585, "baseline": 20734}. 39 tests worse, 196 better.

Worse: `/css/CSS2/abspos/abspos-in-block-in-inline-in-relpos-inline-002.html` 1 -> 0; `/css/CSS2/positioning/inline-static-position-001.html` 1 -> 0; `/css/css-align/abspos/align-self-default-overflow-htb-ltr-htb.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-htb-ltr-vrl.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-htb-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-htb-rtl-vrl.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-ltr-htb.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-ltr-vrl.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-rtl-vrl.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-htb-ltr-htb.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-htb-ltr-vrl.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-htb-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-htb-rtl-vrl.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-vrl-ltr-htb.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-vrl-ltr-vrl.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-vrl-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-vrl-rtl-vrl.html` 2 -> 0; `/css/css-align/abspos/safe-align-self-vrl.html` 12 -> 0; `/css/css-align/abspos/safe-justify-self-htb.html` 6 -> 0; `/css/css-align/abspos/safe-justify-self-vlr.html` 6 -> 0; `/css/css-align/abspos/safe-justify-self-vrl.html` 6 -> 0; `/css/css-flexbox/align-self-014.html` 1 -> 0; `/css/css-flexbox/balance/balance-negative-margin-002.html` 2 -> 1; `/css/css-flexbox/flexbox-baseline-wrap-reverse-unequal-lines.html` 1 -> 0; `/css/css-flexbox/flexbox-ignores-first-letter.html` 12 -> 6; `/css/css-flexbox/getcomputedstyle/flexbox_computedstyle_flex-shorthand-invalid.html` 1 -> 0; `/css/css-flexbox/intrinsic-size/row-use-cases-001.html` 5 -> 2; `/css/css-flexbox/justify-content-rounding.html` 1 -> 0; `/css/css-flexbox/main-axis-margin-rounding.html` 1 -> 0; `/css/css-flexbox/percentage-size-quirks-004.html` 3 -> 1; `/css/css-grid/alignment/grid-align-baseline.html` 1 -> 0; `/css/css-grid/grid-lanes/grid-lanes-container-minimum-size-single-axis-scroll-container.html` 4 -> 2; `/css/css-position/position-absolute-in-inline-dynamic.html` 8 -> 1; `/css/css-position/position-absolute-in-inline-vertical-lr.html` 8 -> 0; `/css/css-sizing/abspos-intrinsic-height-inset-percentage-child.html` 4 -> 1; `/css/css-sizing/stretch/abspos-inline-containing-block.html` 2 -> 0; `/css/css-sizing/stretch/flex-basis-1.html` 4 -> 1; `/css/cssom-view/elementFromPoint-visibility-hidden-resizer.html` 1 -> 0.

The 39 tests that got worse in the first round are of three kinds: tests of self-alignment of absolutely
positioned boxes and of absolute boxes in inline containing blocks that passed while absolute boxes stayed in
the flow (css-align/abspos, css-position/position-absolute-in-inline-*); tests whose rules use a child
combinator, which the render cascade of that commit dropped, so items had no width (rounding tests,
align-self-014); and features not done yet (first-letter, quirks-mode percentages, `stretch`).

**Second round (margin collapse, floats, inline-blocks, wrapping columns, percentage heights)** (run 43578643617, core fe0f14576, baseline main d799500c7):

| Directory | Chrome subtests | Baseline | This | Difference |
|---|---:|---:|---:|---:|
| css/css-flexbox | 4813 | 573 | 1457 | +884 |
| html/semantics | 598 | 196 | 369 | +173 |
| css/css-sizing | 6523 | 2077 | 2180 | +103 |
| trusted-types | 166 | 0 | 93 | +93 |
| css/css-align | 5435 | 2928 | 3013 | +85 |
| css/cssom-view | 2696 | 694 | 743 | +49 |
| content-security-policy/securitypolicyviolation | 34 | 2 | 34 | +32 |
| css/css-position | 1553 | 576 | 595 | +19 |
| html/rendering | 92 | 53 | 36 | -17 |
| css/css-overflow | 1209 | 476 | 488 | +12 |
| sanitizer-api | 271 | 18 | 28 | +10 |
| webcodecs | 47 | 0 | 9 | +9 |
| domxpath | 7 | 0 | 7 | +7 |
| css/CSS2 | 2566 | 1826 | 1831 | +5 |
| css/css-box | 982 | 375 | 375 | +0 |
| css/css-display | 576 | 379 | 379 | +0 |
| css/css-grid | 480 | 23 | 23 | +0 |

All names of the check: {"names": 3967, "run": 3967, "chrome": 85186, "passed": 63330, "baseline": 61862}. 33 tests worse, 242 better.

Worse: `/content-security-policy/reporting/report-frame-ancestors-no-parent-cookies.sub.html` 1 -> 0; `/css/CSS2/abspos/abspos-in-block-in-inline-in-relpos-inline-002.html` 1 -> 0; `/css/CSS2/linebox/vertical-align-top-bottom-001.html` 5 -> 0; `/css/CSS2/positioning/inline-static-position-001.html` 1 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-ltr-htb.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-ltr-vrl.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/align-self-default-overflow-vrl-rtl-vrl.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-htb-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-htb-rtl-vrl.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-vrl-rtl-htb.html` 2 -> 0; `/css/css-align/abspos/justify-self-default-overflow-vrl-rtl-vrl.html` 2 -> 0; `/css/css-flexbox/align-self-014.html` 1 -> 0; `/css/css-flexbox/balance/balance-negative-margin-002.html` 2 -> 1; `/css/css-flexbox/flexbox-baseline-wrap-reverse-unequal-lines.html` 1 -> 0; `/css/css-flexbox/flexbox-ignores-first-letter.html` 12 -> 6; `/css/css-flexbox/getcomputedstyle/flexbox_computedstyle_flex-shorthand-invalid.html` 1 -> 0; `/css/css-flexbox/intrinsic-size/row-use-cases-001.html` 5 -> 2; `/css/css-flexbox/justify-content-rounding.html` 1 -> 0; `/css/css-flexbox/main-axis-margin-rounding.html` 1 -> 0; `/css/css-flexbox/percentage-size-quirks-004.html` 3 -> 1; `/css/css-position/position-absolute-in-inline-dynamic.html` 8 -> 1; `/css/css-position/position-absolute-in-inline-vertical-lr.html` 8 -> 0; `/css/css-position/sticky/position-sticky-margins.html` 2 -> 1; `/css/css-sizing/abspos-intrinsic-height-inset-percentage-child.html` 4 -> 1; `/css/css-sizing/stretch/abspos-inline-containing-block.html` 2 -> 0; `/css/css-sizing/stretch/flex-basis-1.html` 4 -> 1; `/css/css-sizing/stretch/flex-line-003.html` 3 -> 0; `/css/css-sizing/stretch/flex-line-004.html` 1 -> 0; `/css/cssom-view/elementFromPoint-visibility-hidden-resizer.html` 1 -> 0; `/html/rendering/non-replaced-elements/the-fieldset-and-legend-elements/legend-display.html` 52 -> 36; `/html/rendering/replaced-elements/embedded-content/video-controls-stacking-hit-test.html` 1 -> 0; `/html/semantics/scripting-1/the-script-element/module/charset-01.html` 6 -> 0.

The baseline of the second check is the full run of main d799500c7, which is before the first round was
merged: the differences above are both rounds together (css-flexbox 573, then 1,093, then 1,457). Other
directories of the table moved by main's own commits. New among the worse tests, each a pass that did not
come from the feature: `legend-display` (a legend with `display: flex` and the like now has a box, and the
test compares its width with a legend that is still laid out inline), `vertical-align-top-bottom-001`
(inline-blocks with blocks inside are real boxes now and `vertical-align: top`/`bottom` is not read for
them yet), `stretch/flex-line-003` and `-004` (`width: stretch` is not read, and a wrapping column no longer
lays out as one column), `justify-content-rounding` (passes at whole px now; at 40.1px the container's edge
is not on the 1/64 px grid that its items are on).

Cost, measured in the interpreter on rows nested 8, 10, 12 and 14 deep where each nested container is
shorter than a sibling: 204, 775, 2749, 12028 ms as first merged (each level laid the nested container out
twice); 42, 63, 93, 138 ms with the stretched height known before layout.

## 6. Second round: block flow, inline-blocks, wrapping columns

**Margin collapse (CSS 2.1 §8.3.1).** In `flow`, the margin after a block and the margin before the next
collapse to the larger (`previous`, `Result.marginBottom`). A block with no border, padding, clearance or
formatting context of its own shows the top margin of its first block child and the bottom margin of its last
(`collapsesTop`, `collapsesBottom`, `leadMargin`: a loop down the first blocks). White space between blocks
does not separate margins; text does. The root, flex items and positioned boxes are not collapsed through.
Margins are not negative in this profile.

**Floats (CSS 2.1 §9.5).** `Rendering/Floats.lean` is the geometry on layout units, with no engine import:
`band` (the room beside the floats for a range of y), `clearY`, `place` (the first of the flow's y and the
bottom edges of the floats where the new float fits, against its side; below all when it fits nowhere). In
`flow` a floated child is laid out at its given or shrink-to-fit width (`Task.sized`), placed, and recorded in
`floats`; lines take the band (`inlineLayout`'s `band`), a box with a formatting context of its own (a table,
a flex container, a box that clips) is laid out in the band, and a plain block is laid out under the floats
with its lines beside them (`Task.flowed id floats`: the floats travel down and back up in `Result.floats`).
A box laid out with no floats around it is the root of its formatting context: it is as high as its floats
(§10.6.7). `clear` adds the clearance before a block or a float. Intrinsic widths count uncleared floats side
by side, so a box that shrinks to fit around floated children is as wide as their row. A flow with no float
computes none of this (`floats.isEmpty`).

A plain block child of a flow (display block, not clipping, not replaced) is part of the flow's formatting
context whether or not a float came before it (`Task.flowed`, `box ... participates`): it is not as high as its
floats, and they stay beside the lines of the blocks after it (a floated image in a paragraph). Any other task
lays a box out as the root of a context, which holds its floats.

Simplifications to know: a float inside an inline box is laid out inline; a line too narrow for its first word
still takes it; `shape-outside` is not read; with no `::after` box a "clearfix" container has no height.

**Inline-blocks with blocks inside (CSS 2.1 §9.2.2).** An inline-block that has a block-level or floated
child, or is positioned and has element children (`Layout.blockInside`), is one atomic box in its line whose
contents are laid out by `layoutTask` (as an inline flex container is): blocks in it have their widths, its
floats are contained, and it is the containing block of its absolutely positioned descendants. An inline-block
with inline content only is laid out as before (`atomicBox`). Its bottom margin edge sits on the baseline
in both cases, which is not CSS 2.1 §10.8.1 for a box with lines in it (open).

**Percentage heights (CSS 2.1 §10.5).** `definiteHeight` walks up from a box with a percentage `height`
while the ancestors' heights are percentages, to a length; `percentHeights` (in `layoutRoot`, so the theorems
about `render` are untouched) turns each such percentage into px before layout. A percentage of a height that
depends on content stays and is read as `auto`. The root's own percentage is not resolved (the page would
lose its length: a fixed-height root does not yet scroll its overflow). Cost: one match per node, and a walk
only from nodes that have a percentage height.

**Wrapping columns (§9.3).** `flexColumnWrap`: items break into columns at the container's height or
`max-height` (`Flex.breakLines`), each column resolves its flexible lengths (`Flex.resolve`), a column is as
wide as its widest margin box, and `align-content` distributes the columns across the width (`stretch` shares
the free width). `wrap-reverse` and a right-to-left container start from the right. An item that `stretch`
makes wider than its content has its content laid out a second time.

**Distribution with no lost remainder.** `Flex.justify` gave an offset and a gap, both rounded down, so the
last item of `space-between` could end up to n−2 units before the line's end. `Flex.lead j free n k` is the
space before item k as a share of the whole free space, and `Flex.spread` places a line with it:
`lead_between_last` proves the last item ends exactly at the end.

Tested only in this round: the wiring of all of the above in `Layout.lean` and `FlexLayout.lean`
(`PositionLayoutTests.lean`: floats, clear, inline-blocks, percentage heights, margin collapse;
`FlexLayoutTests.lean`: 20 cases of wrapping columns, wrapping-row min-content). The expected numbers are by
hand from the specifications.

**Cost of nested rows.** A row laid a nested container out once to measure it and again to stretch it to
the line, so N nested rows, each shorter than a sibling, cost 2^N layouts. In a single-line container with a
definite cross size the stretched height is known before the item's contents are laid out (§9.4 step 11), and
an item whose contents depend on its height is now laid out once at that height. The re-layout of a stretched
item is then a single pass, so nested auto-height rows are polynomial (timings in section 5). Still two
passes: a stretched container in a multi-line row, and a column item whose flexed height differs from its
content's; a cache of layouts by node and constraints is the general fix.

Open after this round: the same list as section 4, and: negative margins in collapse; floats that leave a
block which is not a formatting context root when no float preceded it; the baseline of an inline-block;
a theorem that a flow with no float lays out as it did before floats (it is true by `floats.isEmpty`, and is
tested by the fixtures of the first round, which did not change).

## 7. Third round: aspect ratio, canvas boxes, sizing keywords, scroll sizes, vertical flex, list markers

**`aspect-ratio` (CSS Sizing 4 §5).** `Rendering/AspectRatio.lean` (no engine import, layout units):
`heightFor`, `widthFor`, `fromWidth`, `fromHeight` and `autoSize`, which takes the natural width within the
limits carried over from the height, then within the width's own, and gives the height by the ratio within its
own limits: a limit of an axis wins over one carried from the other, a minimum over a maximum. The property is
read into `Computed.pos` (`ratio : Option (Nat × Nat)`, `ratioAuto`) by `BoxPosition.lean` through the
property table, with no change to `Style.apply`. `replacedSize` uses it for replaced elements
(`aspect-ratio: auto <ratio>` keeps the ratio of content that has one). A box with `height: auto` takes the
height of its width (of its border box with `box-sizing: border-box`): as its least height (§5.2, the
automatic minimum is the content), or as its height when it clips or has a `min-height`. Flex items and
grid items do not read it yet.

**Canvas boxes.** A `canvas` is a replaced box of its natural size (its `width` and `height` attributes, 300
by 150 without them), empty: `Layout.blankReplaced`. Its fallback content is not laid out.

**Sizing keywords (CSS Sizing 3 §3.2).** `CSS.Length` gains `minContent`, `maxContent`, `fitContent` and
`stretch` (also under `-webkit-fill-available` and `-moz-available`). `CSS.resolve` answers `none` for them,
so every place that asks for a number reads them as `auto` (`resolve_keyword`). `width`, `min-width` and
`max-width` of a box take the widths of its contents (`intrinsic`, asked only when a keyword is used) or the
fill width (`keywordWidth`); a float, an inline-block and an absolutely positioned box take the keyword in
place of shrink-to-fit (`shrinkWidth`). `height: stretch` fills a containing height that the styles make
definite (`resolvedHeight`); `min-content`, `max-content` and `fit-content` heights are the content height.
A flex item whose `flex-basis` (or, with `flex-basis: auto`, its `width`) is a keyword takes that width of its
content as its flex base size, and in a column as its cross size. Not done: `fit-content(<length>)`, `stretch`
against a height known only in layout.

**Scroll sizes (CSSOM View §6.1).** `Rendering/ScrollExtent.lean`: `extent` is the padding box extended to the
right and bottom edges of the boxes inside it (proved: never less than the client size, every box inside is
within it, the client size when nothing overflows). `Layout.scrollSize` (`ScrollGeometry.lean`) finds the boxes
of an element's descendants in a layout; the root element scrolls the viewport over the whole page. The engine
answers `node_query` 38 with it and the `scrollWidth` and `scrollHeight` getters read the answer. Nothing is
computed until a script asks. Not done: the padding after in-flow content, margins of flex and grid items,
transforms, right-to-left and vertical scrolling origins, scroll positions (`scrollTop` stays 0).

**Flex containers in vertical writing modes.** `writing-mode` is read into `Computed.pos` and inherited.
`Layout.flexAxes` gives a container its physical axes (`column`, `mainFlip`, `crossFlip`): in a vertical writing
mode a row runs down the inline axis (up with `row-reverse` or right-to-left), its lines stack along the block
axis (from the right in `vertical-rl`), and a column runs along the block axis. `flexRow`, `flexColumn` and
`flexColumnWrap` take their directions from the axes, and `column-gap`/`row-gap` are the gaps of the inline
and block axes (`flexGaps`). The contents of the items, and block layout in general, stay horizontal: a
vertical block container still stacks its children downwards, and text is not set vertically.

**Cost of nested flex containers.** A row laid out a nested container once to measure it and again to stretch
it, so N nested rows, each shorter than a sibling, cost 2^N layouts: 204, 775, 2749 and 12028 ms for 8, 10, 12
and 14 levels in the interpreter. In a single-line container with a definite cross size the stretched height is
known before the item's contents are laid out, and an item whose contents depend on its height is now laid
out once at that height: 42, 63, 93 and 138 ms for the same pages (the re-layout of a stretched item is itself
a single pass, so the whole is polynomial). Still two passes: a stretched container in a multi-line row, and a
column item whose flexed height differs from its content's. A cache of layouts by node and constraints is the
general fix (open).

**List markers (CSS Lists 3 §3).** `list-style-type` (none, the bullet, a numbering style) and
`list-style-position` are read into `Computed.pos` and inherited; `list-style` expands to them. A marker is
outside the item's box by default, beside its first line and half an em before the content edge, and takes no
room in the line; `inside` keeps it as the first thing in the line. The bullet is still drawn as `*`, and the
numbering styles all draw decimal numbers.

**Aspect ratio, sizing keywords, scroll extents, flex in vertical writing modes, list markers, percentage heights** (run 43581862867, core 68bdcc958, baseline main 6ecf053c7):

| Directory | Chrome subtests | Baseline | This | Difference |
|---|---:|---:|---:|---:|
| css/css-flexbox | 4813 | 573 | 2503 | +1930 |
| css/css-sizing | 6523 | 2077 | 2667 | +590 |
| css/css-align | 5435 | 2928 | 3031 | +103 |
| css/css-position | 1553 | 576 | 616 | +40 |
| css/cssom-view | 2696 | 703 | 735 | +32 |
| css/css-overflow | 1209 | 476 | 506 | +30 |
| html/rendering | 92 | 53 | 29 | -24 |
| css/css-box | 982 | 375 | 389 | +14 |
| css/css-display | 576 | 379 | 386 | +7 |
| css/css-lists | 974 | 568 | 575 | +7 |
| css/css-writing-modes | 421 | 212 | 219 | +7 |
| css/CSS2 | 2566 | 1826 | 1825 | -1 |

The baseline of this check is the full run of main 6ecf053c7, from before the first layout merge, so these
rows are the three rounds together (the other directories of the check moved with other merges to main and are
left out). Test by test against the check of the second round (43578643617, the same names): 2,545 more
subtests pass and 246 fewer, in 37 tests:

- `css-sizing/animation/*-interpolation` and `min-width-composition` (-70): the sizing keywords are now values of `min-width`, `max-height` and the others, and this base had no
  animation engine, so "from none to max-content at 0" answered the end value where an invalid end value used to
  leave the start value. The animation engine on main interpolates these by steps.
- `css-flexbox/alignment/flex-align-baseline-*-002`, `-004` (-67): flex containers in a vertical writing mode,
  now laid out vertically; baseline alignment is not done yet in either axis (it passed where a start-aligned
  horizontal row happened to give the same offsets).
- `cssom-view/scrollWidthHeight-overflow-visible-margin-collapsing` (-20): the `inline-flex` case; the items'
  `min-width` was not part of their intrinsic contribution, so the container was narrower than its items and the
  scroll width, now measured, says so. Fixed in the next step (`boxWidths` clamps by `min-width`/`max-width`).
- `css-mixins/functions/function-conditionals` (-22): not layout; passes that came from an unread `if()`.
- `CSS2/linebox/animations/line-height-interpolation` (-18): not traced. The test reads only `line-height`, which
  this round does not touch; the two checks were built on different commits of main.
- `legend-display` (-8), `contain-intrinsic-size-logical-003` (-6), `intrinsic-percent-replaced-028` (-8, a canvas
  now has a box: a replaced element with a percentage width contributes 0 to min-content, next step),
  `overflow-empty-child-box` (-4, a box of no area is not scrollable overflow, next step), and 22 tests that lose
  one to three subtests where `scrollWidth` used to equal `clientWidth` for want of a measurement (transforms,
  relative inline boxes, scrollbars).
