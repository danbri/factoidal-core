# Empty inline wrappers around out-of-flow media

The [BBC-style fixture comparison](https://github.com/danbri/factoidal-builds/actions/runs/45626809614) measured a 180-pixel image in Chrome and about 200 pixels in Foafnaut for a 320-pixel card. The excess stayed constant across block, column flex, percentage heights and grid placement.

The inline picture wrapper contains only collapsible whitespace and an absolute child. Its horizontal boundaries are layout bookkeeping and do not establish an in-flow line by themselves. Apply the empty line rule when the remaining participants are zero-edge inline boundaries, bidi controls or static positions. Preserve inline geometry and static positioning data. Text, preserved whitespace, atomic boxes, line breaks and any nonzero inline edges retain the usual line strut. [CSS 2.2 §9.4.2](https://www.w3.org/TR/CSS22/visuren.html#inline-formatting)
