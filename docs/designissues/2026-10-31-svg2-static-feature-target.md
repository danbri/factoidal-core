# Project target for a useful SVG 2 static renderer

Tracking: <https://github.com/danbri/factoidal/issues/1209>.
This project wants complete coverage of a declared useful feature set, then
broader modern static SVG. The 38 pinned WPT cases are a regression slice,
not that feature set, not SVG Tiny 1.1 and not a conformance denominator for
all SVG. Secure-static mode disables scripts/animation/interaction/external
fetch; it is a capability restriction, not a graphics feature profile.

## First complete target: a Tiny-sized SVG 2 feature set

This is a project checklist, not a W3C-defined profile. A row is complete only
when its declared semantics, error cases, CPU implementation and real full-image
upstream comparisons are covered. Local samples and successful compilation
cannot close a visual-coverage row. Every row below remains open.

| Required feature | Current boundary / remaining work |
| --- | --- |
| XML and document structure | Actual Factoidal XML namespace view; metadata support is partial. Complete allowed descriptive/foreign metadata, processing rules and relevant limits. |
| Root and nested viewports | Root viewBox/meet/slice/none works for explicit numeric/px sizes. Percentage/intrinsic sizing, root-transform ordering, nested SVG, overflow/clipping and unit resolution remain. |
| Affine transforms | Group/primitive matrix/translate/scale/rotate/skew with ordered composition is the current implementation slice. Root/CSS transform-origin/transform-box and viewport interactions remain separate obligations. |
| Basic geometry | Rect/circle/ellipse/line/polygon partial. Rounded corners, auto radii, polyline and all associated fill/stroke behavior remain. |
| Paths | All M/m Z/z L/l H/h V/v C/c S/s Q/q T/t A/a forms; implicit/repeated arguments, multiple subpaths, close/open behavior, arc conversion and defined error handling. Filled retained linear/compound M/L/H/V/Z paths now work, including relative/repeated arguments, winding and implicit closure. Curves/arcs, strokes and partial-prefix error recovery remain. |
| Fills and strokes | Solid/currentColor/inheritance, polygon winding, primitive strokes and butt/round line caps partial. All shape/path strokes, square caps, miter/round/bevel joins, miter limits, dashes, pathLength, vector effects and paint order remain. |
| CSS presentation | Presentation attributes partial. Inline style, style elements, cascade/specificity/inheritance, supported selectors and CSS color/length syntax need explicit coverage. |
| Definitions and reuse | defs, symbol, use, same-document references, recursion/cycle bounds, instance style and viewport semantics remain. |
| Paint servers | Linear/radial gradients, stops, units, transforms, spread and fallback; patterns remain. Only missing simple local fragment fallback currently works. |
| Clipping and images | clipPath with units/transforms, same-document/data-URL raster images, intrinsic sizing/aspect/color policy remain. External fetching stays disabled. |
| Text | Actual Unicode/font selection, shaping, bidi, positions/anchoring and text layout remain; temporary bitmap graph labels do not implement SVG text. Declare a font/input contract and measure against independent raster output. |
| Compositing and rasterization | Element fill/stroke opacity works for current primitives; isolated group opacity, antialiasing, color/interpolation behavior and shared edge coverage remain. |
| Processing mode | Verify disabled animation/script/external fetch, permitted same-document/data references and explicit unsupported/resource-failure results. Current strict refusal is not full mode conformance. |

After that first target, complete the broader static SVG requirements, including
markers, masks, filters, richer text (including textPath), extended paint and
foreignObject/document layout. These remain tracked work, not silently excluded
from the long-term goal. Interactive DOM, scripting and animation execution
belong to different processing-mode targets.

## Implementation and measurement sequence

1. Finish affine group/primitive transforms, with inverse local-space stroke
   evaluation, singular CTMs, composition, reflection, finite budgets and tests.
2. Implement a real typed path parser and retained path geometry. Start with
   linear/close/multiple subpaths, then quadratic/cubic/smooth and elliptical
   arcs; do not rename fixed polyline approximation as exact curve semantics.
3. Complete viewport, fill and stroke semantics, then inline/style cascade and
   definitions/reuse. Add gradients, clipping and data images, then text.
4. Expand pinned upstream inventories per feature area without trimming the
   existing 38. Bind each feature row to actual source cases, independent image
   captures, candidate GPU output and unchanged upstream fuzzy limits. Cases
   incompatible with the chosen mode keep original and mode-specific results
   separate. Record unsupported/unavailable/disagreement outcomes explicitly.

The browser-host raw WebGPU track now reports **2 matches, 23 unsupported and
13 unavailable** in the unchanged 38-case slice, with no mismatch/rejection.
The candidate uses Lean-generated WGSL and the Lean render-plan bridge on
installed Chrome 156.0.8078.76 / Apple `metal-3` non-fallback hardware. The two
matches are pixel-exact against independently rendered SVG references. Native
Deno remains adapter-unavailable; this does not establish native presentation.
The independent Chrome track has 29 captured pairs, 25 agreeing relations and
four disagreements requiring triage; nine original runtime/resource cases remain
unavailable. See the [affine/GPU worknote](../20261031-svg-affine-gpu.md).

Primary semantics: [SVG 2 coordinates](https://www.w3.org/TR/SVG2/coords.html),
[paths](https://www.w3.org/TR/SVG2/paths.html),
[painting](https://www.w3.org/TR/SVG2/painting.html), and
[processing modes](https://www.w3.org/TR/SVG2/conform.html#secure-static-mode).
