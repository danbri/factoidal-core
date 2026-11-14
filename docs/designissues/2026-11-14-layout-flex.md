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

Not done: wrapping columns; baseline alignment (read as start); `visibility: collapse`; aspect ratio of
replaced items; intrinsic widths of wrapping containers; vertical writing modes; fragmentation.

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

Not done: floats and `clear` (the values are read), margin collapse, `position: sticky` offsets (laid out as
relative with no offset), fixed boxes that stay put on scroll (they are laid out once in the first viewport),
percentage heights against a definite containing block, overflow scroll containers, multi-column.

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

To be filled from the cloud checks (run ids, subtests before and after per directory).
