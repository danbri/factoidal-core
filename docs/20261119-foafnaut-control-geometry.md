# Form control border boxes in Foafnaut

The macOS package check reported a 23 px script rectangle and a 21 px render box for
the same input on both integration pages. Both requests used the native engine,
the bitmap font and an 800 by 600 CSS-pixel viewport at 100% scale.
[Mac package check](https://github.com/danbri/factoidal-builds/actions/runs/44421244654/job/135233291433)

The form-control text added in `9bc7b4a6c` gave its word and space fragments the
input's source node. The text line was 20 px high and started 3 px below the top
of the input. The input was 21 px high, including its padding and borders.
`WebDocument.readAnswer` took the union of both rectangles for
`getBoundingClientRect`. The frame reported the input's border box first.

`Rendering.Layout` gives the anonymous fragments an index outside the layout
arena. Their dimensions still contribute to intrinsic sizing and their glyphs
retain the control's node as their paint source. `Layout.pageBoxes` projects the
same geometry for script reads and frames. Link regions use only fragments with
a source node in the layout arena.

`L4Factoidal.Rendering.Layout.controlText_geometry_excluded` states that
projection excludes a fragment assigned the first index outside the layout
arena, provided the original page is no larger than that arena. The source
requests an axiom report. This lemma concerns the projection. Script and frame
equality, control glyph attribution and intrinsic button sizing are checked by
`host_parity_test.ts`. A build of the change and the macOS package check are
pending.
