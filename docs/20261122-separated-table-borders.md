# Separated table borders

The renderer drew cell borders inside the allocated cell but omitted them from
track width, row height and content placement. It also omitted the table's own
borders when placing the grid. Use the same insets during intrinsic sizing and
placement. The table wrapper paints its own border, and its declared width and
height follow `box-sizing`. An HTML table uses the HTML user-agent border-box
default, while a CSS table box may have the content-box default.

[CSS 2.2 separated borders](https://www.w3.org/TR/CSS22/tables.html#separated-borders)
and [HTML table rendering](https://html.spec.whatwg.org/multipage/rendering.html#tables-2).

An extracted Lean check confirmed the four cell insets and preservation of the
existing collapsed-model insets. Collapsed border conflict resolution remains
separate. The native table check and the full selected border pixel comparison
are pending at WPT commit `4b26db8978f6024d3184ca483d74afbc354b35de`.

The stretch follow-up retained both visual gains on the original baseline. This branch now includes the merged root stacking and transparent border changes. The paired follow-up isolates the table geometry against that main revision.
