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

## Nested inline-block review

The earlier native Mac run passed the direct control and anonymous-text tests,
then failed the real-clock pacing test described in
[the pacing worknote](20261119-foafnaut-gpu-pacing-clock.md). That result does
not cover the following additional layout fix.

Independent review reproduced a missing border box for both a filled and an
empty input nested in a static inline-block. The verified official Wasm engine
at `4b330942d28e93d0a58a437a22ed546b0ff63d31` returned no input frame box,
a zero script rectangle and a hit on its wrapper. Giving the otherwise same
wrapper `position:relative` routed it through the existing container layout
and passed the new regression. This is differential runtime evidence.

`atomize` now closes each nested inline-block as one item in its parent's line.
The item retains its border box, positioned child boxes and glyph runs. Nested
percentages resolve against the parent's first-pass content width. The new
`framedAtomic_preserves` and `framedAtomic_lineWidth` declarations state the
structural frame and line-width properties; their compilation and axiom reports
are pending. They do not prove browser layout conformance.

The native/Wasm regression checks filled and empty inputs, exact script/frame
rectangles, own-node pointer hits, the enclosing 324 by 27 px wrapper and a
108 px border box for a 50% input in a 200 px content width. The focused test
typechecked. The patched Lean engine and all runtime expectations await a fresh
exact-source package build. No timing or allocation improvement is claimed;
the existing anonymous text-source metadata cost is still unmeasured.

## Validated checkpoint

The [complete exact-source Linux and macOS run](https://github.com/danbri/factoidal-builds/actions/runs/44456094827) at
`e089543af9d390626ffd62809f4cd7c6b94c830b` passed, including the new nested
control geometry/hit tests in both Wasm and native. The two framing theorem
reports use only the permitted axioms. Native package/relocation, unchanged
size budget and offscreen pixel gates pass. The dylib is61,477,280 bytes.
Two physical-window parity tests remain explicitly ignored; no physical-display
or allocation/timing claim follows. [PR606](https://github.com/danbri/factoidal-core/pull/606)
merged as182c86e477a823864c00f69c0bebdc3f9d6aeb18. Public main-bundle
publication is tracked separately from the successful candidate package.
