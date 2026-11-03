# SVG edge coverage: geometric accuracy and browser comparison

The pathlength-001 source artifact exposes a limitation of the current 2×2
coverage sampler. Two temporary diagnostic copies of its generated WGSL changed
only the final sample grid to 4×4 and 8×8. They are edited shader experiments,
not fresh Lean exports or product builds. Geometry, paint and viewport data were
unchanged. Chrome 156 on Apple metal-3 executed each shader at 800×600.

The browser's independently captured test and reference match exactly. Our
source-generated 2×2 candidate still fails that external comparison. Increasing
sample density does not monotonically improve agreement with this browser:

| Grid | Pixels differing from browser | Maximum channel difference from browser | Maximum channel difference from exact area |
| --- | ---: | ---: | ---: |
| 2×2 (current) | 1,512 | 64 | 56 |
| 4×4 (diagnostic) | 48 | 32 | 23 |
| 8×8 (diagnostic) | 1,536 | 48 | 13 |

The exact-area column uses rational intersection and union area of the decoded
scene's axis-aligned, opaque black dash rectangles, then rounds the resulting
white-background channel to the nearest byte. The browser differs from this
model by up to 43 channel levels. This model is an independent area calculation,
**not an independent SVG parser**: it does not establish that SVG lowering chose
all the right rectangles. It admits only the fixture's constrained scene, with
explicit assertions for paint, shape, transform and viewport assumptions.

`tests/external/svg/pathlength_coverage_probe.py` reproduces the area comparison
without Pillow. It records artifact and image hashes and writes the exact-area
PPM and JSON metrics. Example:

```sh
python3 tests/external/svg/pathlength_coverage_probe.py \
  --artifact /private/tmp/solving-pathlength-001.json \
  --browser-reference /private/tmp/foafnaut-svg-oracle/01-reference.png \
  --candidate 2x2=/private/tmp/solving-pathlength-001-gpu/00-actual.ppm \
  --candidate 4x4=/private/tmp/solving-pathlength-diagnostic-4-gpu/00-actual.ppm \
  --candidate 8x8=/private/tmp/solving-pathlength-diagnostic-8-gpu/00-actual.ppm \
  --output /private/tmp/solving-coverage-probe
```

Source artifact SHA256:
`07edb2b27eac7d518321c495d2bf3af6c7d29044c178882d87f34973a4f5a16a`.
The unchanged fixture/reference and independent image hashes were checked in
the preceding pathLength comparison. The diagnostic copies are not coverage
passes, and no original tolerance or image has been changed.

## Consequence for Solving

Keep three claims separate: the official test/reference relation within one
renderer, differential agreement with a browser rasterizer, and geometric area
accuracy. The original reference uses stroked paths, which Solving cannot yet
render; the complete same-renderer reftest remains unavailable. SVG 2's
[viewer conformance requirements](https://www.w3.org/TR/SVG2/conform.html#ConformingSVGViewers)
state geometric accuracy and recommend antialiasing; they do not select this
particular Chrome sampling implementation as the mathematical reference.

Do not select a global grid merely to reduce one screenshot's mismatch count.
Next work should provide bounded sampling choices or analytic coverage for
admitted geometry, shared by CPU and GPU, with explicit numeric error and cost
claims. A rational area model can support tests for such a fast path. Extending
it to transparency requires integrating ordered scene composition, not summing
independent primitive coverage (which breaks overlapping geometry). The current
production sampler remains 2×2; these diagnostics neither fix that limitation
nor claim full SVG conformance.
