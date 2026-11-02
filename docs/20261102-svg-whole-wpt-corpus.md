# Whole SVG standards corpus and actual browser measurements

The harness now inventories the entire pinned WPT SVG subtree, rather than a
pair of selected directories. Its 2,452 original files include 1,327 SVG and
1,042 HTML documents. Forty original external dependencies/license files bring
the byte-verified transport to 2,492 files. WPT commit is
`70dae60789ef6220d9b4e60c92c5b2107b4e2b93`, SVG tree
`e719d1b7247635648362bbbe8611e713db30f3f0`.

This is an inventory, not 2,452 passes. The fixed executable relation table has
601 entries (595 match, 6 mismatch), of which 462 are classified static and 139
dynamic. The table includes all original HTML-embedded SVG relations. Script
tests, manual cases, resource dependencies, fonts, unresolved base contexts and
animation requirements remain visible. The separate older 38-case baseline is
unchanged; its overlap is labeled diagnostic in the broad report.

The first complete corrected baseline is
`/tmp/factoidal-overnight-corpus-baseline-root/run.json`, with details and PNGs
in its `capture/` directory:

| Scope | Match | Mismatch | Unsupported | Rejected | Unavailable |
|---|---:|---:|---:|---:|---:|
| All 601 original relations | 15 | 3 | 310 | 16 | 257 |
| Static 462 subset | 15 | 3 | 310 | 16 | 118 |

These are engine/profile limitations, not excluded tests. Capture command exit
was 0, comparison and wrapper exit were 1 (incomplete conformance). All three
controls passed for each of the 15 exact independent-test baselines: unchanged
replay, real magenta shader injection and an altered unsampled readback pixel.
The remaining control states are unavailable, not passed. No negative relation
was promoted to a qualified image match.

The stable SVG candidate WASM was
`cc304ebc359a29da36657fbe462f983b3a32cfeb27a9900b016b915ccbaa03fb`.
Original HTML was sent directly to the frozen native Lean HTML/CSS/common-scene
CLI, SHA-256
`0e5e98e05e456ba5f5f3bda5884d6437d2c38e79f46db58add5d2b9dbf69944b`,
with its b814d09c7 source witness. Native artifacts were rendered through the
same raw WebGPU bridge. The browser was installed Chrome 156.0.8078.80,
executable SHA-256
`3f0acaf1e585195596d73ffa1824baa72c3c3ac115b5cfc43d789030a3f23d93`,
Apple Metal WebGPU adapter, fallback false. Each capture records exact runtime,
source, input, artifact, submitted shader, browser and screenshot identities.

The three actual baseline mismatches are
`svg/painting/reftests/visibility-collapse-001.html` (9,363 pixels, maximum
channel difference 255), and `svg/shapes/reftests/pathlength-001.svg` and
`pathlength-004a.svg` (1,512 pixels each, maximum 64). These are whole-image
differences; sample pixels do not establish raster equivalence.

Two separate feature diagnostics demonstrate real progress without changing
that baseline. Five precomputed Lean clipped-scene artifacts match independent
analytic 64x64 RGBA controls exactly (rotated half-plane, content frame, parent
frame, nested intersection and singular clip). They are math/backend controls,
not parsed SVG or WPT passes; evidence is
`/tmp/factoidal-overnight-corpus-clip-math/report.json`.

The ten original use/symbol reftests listed in
`tests/external/svg-wpt/diagnostics/use-symbol.json` all match their independent
browser references exactly, with zero differing pixels, on the new URL-aware
SVG engine. Each fault control passes for all ten. Evidence:
`/tmp/factoidal-overnight-corpus-use-symbol/run.json`. This is a selected
diagnostic with the other 591 rows explicit, not a full-suite feature score.
That SVG WASM SHA-256 is
`6e1de3a3fbf8bb2b215fcd53e272a35978c2def46223c90848f5069db816c58d`,
glue `4716f7b83cb27c462d3223f2761e00e3177bfa5b017204699fc281665d6f3607`,
and TypeScript host
`38511f26402f218874db4090d090314f582dd720fd92bec44473df4e46b6f370`.

Harness integrity is independently exercised by corrupting a relation, fuzzy
limit, reference, resource hash and whole inventory; all must fail. The
comparator also tests that an incorrect blank negative-relation candidate
cannot qualify as an image match, that upstream fuzzy lower bounds matter,
and that the final pixel remains in the comparison.

Earlier captures are preserved as historical harness failures. Headless macOS
`requestAnimationFrame` readiness timed out; the corrected static transport
uses fonts readiness and screenshot paint flushing. A `/wpt/` prefix mount
broke original root-absolute resource paths; the corrected run serves original
paths `/svg/`, `/fonts/`, etc. The earlier `baseline-ready` report is not the
final baseline. No fixtures, fuzzy values or success expectations changed.

Step zero ran `tools/ensure-test-env.sh --check` and attempted restoration.
Unrelated RDF, XSD, Xalan, Wycheproof and Solid fixture/binary gaps remained
because nested network access failed. This isolated SVG run does not claim
those suites passed. No renderer/runtime was built in this lane. Reproduction,
transport boundaries and third-party notices are in
[`tests/external/svg-wpt/README.md`](../tests/external/svg-wpt/README.md).
