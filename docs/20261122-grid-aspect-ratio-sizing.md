# Grid aspect-ratio sizing

A grid item with auto width, an explicit aspect ratio and a definite height can
derive its fit-content width from the height. The first layout uses the height
when its row tracks already make it definite. Otherwise final placement resolves
the height against the sized row area, then reflows the item when the transfer
changes its width. Measuring a nested grid retains the existing bound on
repeated child layout. The transfer operates in layout units and applies both
dimensions' min and max sizes and the preferred box-sizing edges.

[Grid item sizing](https://www.w3.org/TR/css-grid-2/#grid-item-sizing)
and [preferred ratio sizing](https://www.w3.org/TR/css-sizing-4/#aspect-ratio).

The [baseline](https://github.com/danbri/factoidal-builds/actions/runs/45057393069)
failed all 40 subtests across the two `grid-item-aspect-ratio-justify-self`
fixtures. In the ordinary item fixture, the non-stretching 32 px tall panels
should be 16 px wide and currently have no width. The table fixture also
exercises the independent table sizing path.

Scope covers own definite-height and resolved percentage-height transfer for
non-table, non-stretching items with an explicit preferred ratio. This change
does not rerun intrinsic track sizing after the final transfer. It leaves the
special table sizing algorithm and natural image ratio precedence alone.
Candidate measurements and compilation are pending.
