# Shared clipping for HTML and embedded SVG

Tracking: https://github.com/danbri/factoidal/issues/1230 .

HTML block overflow and embedded SVG viewports now construct the same typed
Float clip nodes used by SVG symbol instances. A retained clipped node has
separate content and clip transforms: viewBox scaling changes child geometry,
while the viewport clip stays in the parent coordinate frame. Primitive clip
stacks, their complete affine frames and painter order survive the explicit
SVG/common-scene roundtrip. No producer payload or serialized SVG is involved.

The Lean HTML frontend supports `overflow:hidden` and `overflow:clip` for
ordinary block boxes. Embedded SVG defaults to viewport clipping and accepts
an explicit visible overflow override. HTML CSS dimensions and inherited
currentColor/visibility are resolved before entering the existing SVG reader.
SVG presentation attributes have lower priority than inline and stylesheet
CSS; root declarations consumed by HTML are removed from the direct DOM
transfer so the SVG reader cannot accidentally override the computed value.
Native SVG paint declarations remain owned by the SVG reader.

Link hit regions intersect the actual clipping ancestor boxes before the
viewport intersection. A link on a wrapped second line beyond a fixed-height
clip no longer paints or picks there. The browser still calls the Lean picker.

## Checked source checkpoint

The targeted `Rendering.Tests` build passed 44 style/layout guards and the
four imported picker guards. Three new checks distinguish parent, content and
clip affine frames while retaining source IDs and group order. Eleven lab
runtime guards in `WebRenderTests.lean` exercise actual CPU samples for CSS
SVG sizes, viewBox, viewport background, currentColor cascade, important
visibility override, block overflow and clipped symbol instances.

Fresh adapter compilation checked `clip_roundtrip` with no axioms.
`geometry_roundtrip`, `style_roundtrip`, `primitive_roundtrip` and
`node_roundtrip` use only `propext` and `Quot.sound`; `scene_roundtrip`
additionally uses `Classical.choice`. The common retained traversal's exact
fast twins still compile. These theorems preserve binary64 fields and order;
they do not prove binary32/WGSL/driver raster equivalence.

`web-render/check-embedding.mjs` compares untouched
pinned `svg/render/reftests/overflow-clip.html` and `rect-ref.html` separately
against original-browser whole images, compares CPU and GPU output, and
checks local CSS dimension/color and clipped-link controls. The combined fresh
native/WASM engine passed all five groups. Both unchanged upstream HTML files
matched their independently rendered Chrome originals exactly over 16,384
pixels, with maximum channel difference zero, and their candidate images
matched each other. All five diagnostic images matched CPU/GPU and original
Chrome pixels exactly. Clipped link picking and explicit descendant-CSS
refusal also passed. These selected diagnostics do not update the full
601-case corpus score or turn the reference file into another WPT test pass.

The renderer WASM SHA-256 is
`a32b0dd97c3d2902e28c2c9dae546637e232cfa676001e02ed948cd2713ceeed`;
the fresh native executable SHA-256 is
`3e8c87ac25eb7705cdc56a1180db34b2a61288a1d750909c8058beb2076679de`.
The combined source checkpoint is `61e2522c4`, including the independent
proved CPU sampling optimization. GPU-only evidence is
`/tmp/factoidal-web-shared-clips-gpu/report.json`; the later full CPU/GPU
comparison is `/tmp/factoidal-web-prepared-embedding/report.json`.

## Remaining boundaries

Root/body overflow propagation, decorated inline boxes, SVG margin/padding,
percentage SVG heights without a definite containing height, and external
HTML stylesheet rules targeting embedded SVG descendants are explicit
unsupported results. Native inline SVG painting and SVG-owned styles still
use their existing strict profile. General HTML/SVG cascade unification is
not complete.

The original whole-HTML `visibility-collapse-001.html` corpus mismatch stays
a failure. Its paragraph uses the temporary ASCII bitmap profile and lacks
browser default paragraph/font layout; removing that paragraph or comparing
only the SVG would not fix the test. Real font-data consumption, UA paragraph
metrics, line boxes and margin collapse form the next visible text milestone.
The checked [HarfBuzz/FreeType data adapter](../labs/demos/foafnaut/tools/FONT_DATA.md)
and `Rendering.FontData` decoder are available but are not yet consumed by
this layout profile. Ahem is still refused rather than mislabeled bitmap text.

## Box-edge cascade follow-up, 2026-11-03

All eight margin/padding longhands now accept finite nonnegative px values.
The margin/padding shorthand expands into its four longhands before cascade,
so a later shorthand can override an earlier longhand and importance/specificity
still win before source order. This fixes the real RDF view's unsupported
`padding-bottom` declaration. Negative edges remain a named profile refusal;
nonzero vertical block margins still require the unimplemented collapse rules.
HTML style admission and embedded-root declaration filtering now share one
property list, including the new longhands.

The targeted core checks now pass 58 style/layout guards plus four picker
guards. Twelve fresh lab CPU guards pass, including zero-valued SVG box
longhands, actual text origin changes and following-block flow from bottom
padding. These source checks precede the next fresh RDF/native/WASM image gate.
