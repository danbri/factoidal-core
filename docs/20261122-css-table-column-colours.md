# CSS table column colours

The layout grid previously retained one element per declared column for width
calculations. A column inside a column group replaced the group's ID, so the
paint stage had no sources for either of the column layers. Keep the group
separately and draw the two solid colours in the originating cell's rectangle,
before its existing row-group, row and cell backgrounds. A column group's own
span uses the group for sizing and emits its colour once. No grid dimensions
change. See [CSS 2.2 §17.5.1](https://www.w3.org/TR/CSS22/tables.html#table-layers).

This covers solid colours. Column gradient and raster positioning need the
group and track rectangles as separate positioning areas. Collapsed border
conflict handling remains separate.

Local Lean 4.33.1 compiled the changed table grid module with warnings treated
as errors against the available compiled Style module. Native compilation and
paired pixel checks will exercise the complete engine at WPT commit
`4b26db8978f6024d3184ca483d74afbc354b35de`.
