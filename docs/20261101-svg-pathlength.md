# SVG pathLength calibration for rectangle and line dashes

`SVG.lean` accepts the numeric pathLength attribute on rect and line. Positive
values calibrate nonpercentage dash and offset distances by computed geometric
length / author length. Rectangles use their full perimeter; lines use Euclidean
length. The existing retained stroke union and single element compositing remain
unchanged. Stroke width and child affine transforms are not rescaled by this
attribute. No additional CSS selectors/properties are implemented.

[SVG 2 §9.6.1](https://www.w3.org/TR/SVG2/paths.html#PathLengthAttribute)
and [stroke dashing](https://www.w3.org/TR/SVG2/painting.html#StrokeDashing)
establish the calibration contract. Percentage distances are exempt. The parser
now retains a percentage flag for each normalized dash and for the offset,
including through inheritance and odd-pattern duplication. An explicit length
check prevents parallel value/flag lists being silently truncated by zip.
The [paired-record follow-up](20261101-svg-dash-unit-provenance.md) replaces
these parallel lists and their guard with one typed list, with kernel-checked
normalization provenance.

Zero pathLength is valid in the specification. This implementation accepts it
when calibration is irrelevant (solid stroke or percentage-only distances).
Active nonpercentage distances that need infinite scaling refuse explicitly;
this remains a coverage gap, not a claim that zero is invalid. Negative values,
units/percent suffixes on pathLength itself, nonfinite numbers and calibration
outside numeric limits refuse. Other shape kinds and the CSS path-length
property remain unsupported.

## Checked source and actual GPU result

`SVGPathLengthTests.lean` compares complete generated artifacts with independently
written equivalent numeric dash patterns: signed offsets, px units, mixed and
all-percentage patterns, odd duplication, inherited flags and rectangle perimeter.
It also checks zero behavior, negative/invalid input and admission of unchanged
WPT svg/shapes/reftests/pathlength-001.svg. The named lab build invokes it, and
svg_test.ts has corresponding public artifact regressions for a rebuilt engine.
The public WASM tests have not been run against a new binary in this step.

Current source compilation and focused pathLength, dash, percentage and CSS
integration checks use existing dependencies with an isolated temporary SVG
olean. The artifact was exported through SVGArtifact.lean to
/private/tmp/solving-pathlength-001.json at 800×600 (the fixture root is 100%).

The coordinator ran the real GPU against independently captured browser test and
reference images. Their browser images match each other exactly, and fixture and
image hashes were verified. Our candidate **fails exact comparison: 1,512 different
pixels, maximum channel difference 64**. Difference pairs are all grayscale edge
coverage: 1,320 candidate black/reference 64; 112 candidate 128/reference 64;
64 candidate 128/reference 191;8 candidate 191/reference 128;8 candidate 191/reference 255.
At the horizontal edge y = 229.1667 (viewBox scale 5/3), the current 2×2 coverage
sampler paints black while the browser paints 64. This is a measured sampling
limitation, not a visual conformance pass. No tolerance or oracle was changed.
Reports: /private/tmp/solving-pathlength-001-gpu/comparison.json and candidate.json.

The source tests establish this bounded implementation's calibration behavior;
they are not general mathematical proofs or evidence of a published WASM.
No heavy build, binary commit, fixture edit or CSS scope expansion was made.
