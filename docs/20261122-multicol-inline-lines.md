# Fragment inline lines into CSS columns

The existing multicolumn layout finds column breaks only between child
boxes. A run of text is one DOM child even if it wraps over many lines,
so the height balancer can leave the other columns empty.

The inline formatter can now return each completed line. A horizontal
multicolumn box with a single inline formatting context lays out the
lines once at the used column width. It distributes them using cumulative
line heights, the available height, column-fill, orphans and widows.
Moving a line moves its paint, text runs, hit boxes and pending positions
together. The direction chooses which side gets the first column.

The integer partition planner compiled under Lean 4.33.1 with warnings
treated as errors. Six guards cover balancing, default line minimums,
constrained sequential fill and an overfilled column row.
Separate block fragmentation, nested column sets and vertical text need
additional work. The native WPT and pixel comparisons are tracked in the PR.

[CSS Multi-column Layout Level 2](https://drafts.csswg.org/css-multicol-2/#filling-columns)
[CSS Fragmentation Level 3](https://drafts.csswg.org/css-break-3/#unforced-breaks)
