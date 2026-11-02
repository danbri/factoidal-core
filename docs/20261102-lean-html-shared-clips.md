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

`web-render/check-embedding.mjs` is the next image gate: it compares untouched
pinned `svg/render/reftests/overflow-clip.html` and `rect-ref.html` separately
against original-browser whole images, compares CPU and GPU output, and
checks local CSS dimension/color and clipped-link controls. At this source
checkpoint that gate awaits the combined fresh native/WASM engine build; no
new official WPT pass is claimed here.

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
