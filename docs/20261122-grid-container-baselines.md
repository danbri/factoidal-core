# Horizontal grid container baselines

Foafnaut propagated the first and last line baselines from the child-fragment
append order. An inline grid with an empty baseline-aligned item instead fell
back to the grid's bottom edge. This positions neighboring inline text and
atomic boxes against the wrong baseline.

Horizontal grids select the first and last occupied rows and prefer the
baseline alignment group in that row. Other items are ordered by their grid
position. A missing horizontal baseline, including that of an orthogonal
item, is synthesized from the bottom border edge. Existing vertical container
baseline handling is outside this change. See [CSS Grid 2 §11.6](https://www.w3.org/TR/css-grid-2/#grid-baselines).

The three extracted Lean selection guards compile with warnings as errors.
The first three cases in the pinned grid container baseline fixture exercise
horizontal inline grids. The full selected native comparisons are pending.
