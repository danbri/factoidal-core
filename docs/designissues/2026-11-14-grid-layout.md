# CSS Grid Layout in BubblePopKit

Date: 2026-11-14. Branch `wip/grid`. Specification: CSS Grid Layout Module Level 2
(https://drafts.csswg.org/css-grid-2/), CSS Box Alignment 3, CSSOM View §7.

## Why

Before this work `display: grid` was laid out as block flow: a page that uses grid came
out as one column. css/css-grid passed 2,846 of Chrome's 15,868 subtests (full run of
main 19fb349c1, Linux), almost all of them parsing tests.

## Counts before (main 19fb349c1, Chrome's subtests)

| kind of test | Chrome | pass | tests |
|---|---|---|---|
| `checkLayout` (offsets and sizes of boxes) | 4,896 | 78 | 483 |
| other testharness (3,200 are positioned descendants in orthogonal writing modes) | 4,293 | 283 | 182 |
| interpolation of track lists | 3,776 | 1,350 | 8 |
| parsing and computed values | 1,667 | 895 | 69 |
| resolved track lists through `getComputedStyle` | 1,236 | 240 | 24 |

Reftests carry no subtests in the denominator. Of the 4,896 `checkLayout` subtests,
3,205 are in pages whose grid sits in a `position: relative` container, so they need
`offsetParent`; 2,248 use vertical writing modes, which the engine does not have.

## Design

The formatting-context interface is that of `Rendering/Fragment.lean` (flex layout uses
the same): a context is a function from the container's style, its items and its content
box to a fragment, and asks about its items through callbacks (`Children`). Grid is in
its own modules:

| module | what | imports |
|---|---|---|
| `Rendering/Grid/Placement.lean` | §8.5 placement: areas, sparse and dense packing, implicit tracks | Std |
| `Rendering/Grid/Sizing.lean` | §12 track sizing | Std |
| `Rendering/Grid/Template.lean` | §7 explicit grid: `repeat()`, auto-repeat counts, named areas; §8.3 line resolution | the two above |
| `Rendering/Grid/Align.lean` | §11: distribution of free space among tracks, self alignment | Std |
| `Rendering/GridStyle.lean` | `Computed.grid`: the grid values read through the property table | BoxAlign, Template |
| `Rendering/GridLayout.lean` | the glue: `gridLayout`, `gridIntrinsic` | Fragment, FlexLayout, Align |
| `Rendering/GridResolved.lean` | resolved `grid-template-columns` / `-rows` from a laid-out scene | GridLayout, ComputedGeneric |

Decisions:

- **Whole layout units.** Track sizes, gaps and contributions are natural numbers of
  1/64 px (the unit of `Rendering/LayoutUnit.lean`). Nothing can be proved about `Float`,
  and with whole units a row of `1fr` tracks adds up to the container exactly. Floats
  appear only where the glue talks to the rest of layout.
- **One source of values.** Grid values are declarations read by the property table
  (`CssValues.specified`, `CssValues.computed`); `GridStyle` turns the components of the
  computed value into track lists and grid lines. The grid shorthands are split at their
  top-level `/` after the table has accepted the value.
- **Each step of track sizing can only raise a track** (`Sizing.raise`), and only tracks
  the step is about. The steps compute candidates with ordinary code; the bounds are
  proved once, for `raise`.
- **Flexible tracks share space by cuts.** The share of a track is the difference of two
  whole-number cuts of the space, at the sum of the factors up to and before the track.
  The cuts telescope, so the shares add up exactly, and each is within one unit of the
  exact proportional part.
- **Collapsed `auto-fit` tracks** are left out of track sizing and put back with size 0;
  no gap is counted for them.
- **Resolved values.** Grid layout leaves the used track sizes of a container in its
  fragment as an empty group named `grid-tracks <node>` with the two resolved lists.
  `getComputedStyle` finds it in the scene of the layout it already has. No second
  layout, no new field through every fragment constructor.
- **`offsetParent`**, `offsetLeft` and `offsetTop`, which most of the layout tests read,
  come from the shared layout (`Rendering/OffsetParent.lean`, layout read op 17), not from
  this module.
- **Positioned children** of a grid container are not items (§9.2): they go to the
  pending list with the container's content box as their static position, as a flex
  container's do.

## Proved, tested, open

Proved (no `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`; each
theorem's doc comment states its kind, what it says and what it does not say):

- Placement: every item is placed exactly once (`placeAll_indices`); a definite start
  track and every span are kept (`placeAll_honoured`); of two placed items of which at
  least one had an automatic position, the areas share no cell (`placeAll_disjoint`), so
  auto-placement never covers an explicitly placed item; with sparse packing the cursor
  never moves backwards (`step_cursor_le`, `foldl_step_cursor_le`); every area lies
  inside the grid the placement reports (`placeRows_inside`); one area for each item
  (`place_size`); the column or row found for an item is the earliest free one
  (`firstFreeCol_earliest`, `firstFreeRow_earliest`, `fitInRow_earliest`); placing the
  placed areas again as definite positions gives the same areas (`placeAll_idem`).
- Track sizing: the shares of flexible tracks add up to the space exactly
  (`frRound_sum`, `expandFlexible_sum`, `expandFlexible_sum_of_zero_base`); each share is
  proportional to its factor to within one unit (`share_proportional`); a track with a
  fixed min sizing function is at least that size (`sizeTracks_ge_min`); a track with
  fixed min and max, min ≤ max, is at most its max (`sizeTracks_le_max`); one size for
  each track (`sizeTracks_size`, `expandFlexible_size`). Termination: every loop is
  structural or has a fuel; the definitions are total (no `partial`).
- Explicit grid: an automatic repetition repeats at least once (`repeatCount_pos`) and,
  when one repetition fits, the tracks and gaps do not overflow the container
  (`repeatCount_fits`); two definite lines give a span of at least 1
  (`resolveAxis_span_pos`).
- Alignment: the space given to the start offset and the gaps is at most the free space
  (`contentOffsets_within`); an item no larger than its area lies inside it under every
  alignment (`selfOffset_inside`).
- The sums of the inflexible base sizes and of the flex factors run as loops with an
  accumulator, proved equal to their list definitions (`inflexSum_eq_loop`,
  `flexSum_eq_loop`, used by the compiler through `@[csimp]`).
- Positioned boxes in a grid (§9.1, `Grid/Abspos.lean`): the lines found are lines of the
  implicit grid or the padding edge (`absLines_inside`, `inImplicit_le`); `auto` on both
  sides is the padding box (`absSpan_auto`); two numbered lines come out in order
  (`absRaw_ordered`).
- Baseline alignment (§11.6, `Grid/Baseline.lean`): an aligned item's baseline ends at
  its row's largest (`baselineShift_spec`), so two aligned items of a row end aligned
  (`baselineShift_aligned`).
- A track size with no percentage has the same sizing functions for every container size
  (`TrackSize.toFn_of_not_hasPercent`): rows are sized a second time only when one has a
  percentage.
- Logical axes (`Rendering/LogicalAxes.lean`, shared with block and flex layout): the
  mapping from logical to physical rectangles and back are inverse in every writing mode
  and direction (`toLogical_toPhysical`, `toPhysical_toLogical`); a rectangle inside the
  container stays inside (`toPhysical_inside`); sizes are kept, exchanged in a vertical
  frame (`toPhysical_size`). A vertical grid is laid out with its axes exchanged
  (`gridTranspose_twice`: exchanging twice gives the values back).
- Track sizing, more: stretched auto tracks and the gaps fill a definite space exactly
  (`stretchCand_sum`, with `bonusSum_all`: the shares sum to the free space); the shares of
  §12.5/§12.6 never exceed the space shared (`distribute_sum_le`) and, with no growth
  limits, hand out all of it (`distribute_exact`); an auto-repeated track counts at least its
  min (`fixedSize_ge_min`).
- Alignment, more: a `safe` item never starts before its area (`gridSelfOffset_safe`).
- Resource bounds (local-lean-rules §11): lines and spans are clamped to ±10000 lines
  (`clamp_bounds`, `clampSpan_none`), so the implicit tracks before the explicit grid are at
  most 10000 (`leading_le`) and no page can ask for an unbounded grid.
- Determinism: every function here is a pure function of its arguments; the same grid
  gives the same layout.

Tested only (`#guard`): the distribution of extra space across spanning items
(§12.5.1), intrinsic track sizes, line names and areas, the cascade of grid values, and
the layout glue (`GridLayoutTests.lean`, original fixtures on a monospace test face).

Open:

- The exact-sum theorem at the level of `sizeTracks` as a whole (it is proved for its
  flexible step, `expandFlexible`, and its stretch step, `stretchCand_sum`),
  and the sum when a flexible track is frozen at its base size in an earlier round (it
  holds for the last round, `frRound_sum`).
- That the dense cursor restarts at the start of the grid for every item (tested).
- A cost theorem. The layout of a document is kept by its key
  (`FrameCost.layout_once_per_distinct_key`), so an unchanged document, and the grids in
  it, are not laid out again; there is no cache below the document.

## Not done

Baseline alignment in columns (`justify-self: baseline`); subgrid tracks (a subgrid is
laid out as a nested grid that stretches in its subgridded axes: the parent has no channel
to hand it its tracks yet); items whose own writing mode is orthogonal to the grid's (the
engine lays text out horizontally); masonry (`grid-lanes`).

## Measured

To be filled from the cloud branch checks (`/css/css-grid/,/css/css-align/,sample:150`).
