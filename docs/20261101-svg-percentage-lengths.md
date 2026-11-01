# SVG viewport-relative percentage lengths

Implemented in the Lean lab parser `labs/demos/foafnaut/SVG.lean`.
This is source-checked compatibility work, not a new published renderer.

## Contract

[SVG 2 §8.9 Units](https://www.w3.org/TR/SVG2/coords.html#Units)
defines horizontal percentages against viewport width, vertical percentages
against height, and other lengths against the normalized diagonal
`sqrt((width² + height²)/2)`. When a viewBox is present, its width and height
supply these references. ViewBox origin, meet/slice letterboxing and child
transforms do not change those references.

The parser now resolves x/y, x1/y1/x2/y2, width/height, cx/cy, ellipse rx/ry,
circle r and stroke-width accordingly. The resolved values feed the existing
geometry, CPU sampler and generated GPU buffers/shader. No TypeScript geometry
implementation was added. Circle r and stroke-width use the normalized diagonal;
ellipse rx/ry use the appropriate axis. Negative positions and positions above
100% remain legal; existing negative-size/radius/stroke refusals remain.
Rectangle rounded-corner rx/ry are still outside the supported profile.

The host contract is deliberately narrower than CSS layout. Explicit
`parse(xml, outputWidth, outputHeight)` dimensions are the **final viewport**.
They override root width/height attributes, including percentages. Thus root
width="50%" with an explicit output width of 800 still yields an 800-pixel
viewport: the API input is not a parent containing-block size. Root percentage
values are syntax/negativity checked, not used to perform CSS sizing. Without
both explicit output dimensions, root percentage dimensions are refused because
there is no supplied containing block. Omitted/numeric root sizing preserves the
existing behavior. Full intrinsic sizing, nested SVG viewports, CSS layout,
relative font units and percentage path-data operands are not implemented.

The reftest host also accepts XHTML link rel="help" as inert metadata alongside
rel="match". Neither causes any fetch. Stylesheet relations remain refused;
metadata acceptance does not establish stylesheet support.

## Validation

`SVGPercentageTests.lean` passes against newly compiled current SVG source with
existing `.build/olean` dependencies and an isolated `/private/tmp` output.
Checks cover all supported geometry axes, numeric diagonal expectations,
viewBox meet/slice/none with a nonzero origin, transformed groups, inherited
stroke width, explicit host viewport, negative dimensions, malformed units,
unresolved root percentages, signed positions, ordinary px/unitless lengths,
inert help/match metadata and refusal of active stylesheet metadata.
`SVGTransformTests.lean` and `SVGPathTests.lean` also pass. These are executable
Lean tests over Float calculations, not mathematical real-number proofs.

The percentage module is now invoked by `build-engines.sh`. Coordinator replay
of percentage, transform and prerequisite checks passed against refreshed SVG
source. The WASM test now expects hosted percentages to compile, while
unresolved root percentages remain an explicit refusal.
No heavy WASM rebuild, GPU replay or browser conformance run was performed here.

## Unchanged official fixture admission

Replayed all 38 selected SVG test inputs from the existing manifest/baseline,
WPT revision `70dae60789ef6220d9b4e60c92c5b2107b4e2b93`, at the suite's 800×600
host viewport. All fixtures were unchanged. Result after this change:
**2 accepted, 36 refused**. This is admission only, not visual agreement;
accepted files remain `fallback-001.svg` and `fallback-002.svg`.

`percentage-attribute.svg` and `percentage.svg` now reach the real next blocker:
`<style>` support. Both use a rect selector for fill:none and stroke:blue.
The attribute variant also requires stroke-dasharray="20% 30%" and
stroke-dashoffset="-10%"; the CSS variant puts those properties and stroke-width
inside its stylesheet. Percentage lengths alone therefore do not increase the
official visual pass count.

Other revealed blockers: external paint URLs, marker-start/marker dimensions,
group style and root class attributes. Numerous marker fixtures link a real
stylesheet and still explicitly refuse it. Do not bypass those dependencies to
increase counts. `disabled-shapes-01.svg` still refuses negative rectangle
sizes instead of disabling just that element. The current subset is not SVG
Tiny or full static SVG 2 conformance.
