# Original SVG/HTML corpus through browser-shipped Lean WASM

The runner now supports a frozen browser HTML producer as an alternative to
the native CLI. It passes original HTML and the fixed 800x600 viewport directly
to the existing Lean WASM entry point. It performs no DOM extraction, attribute
stripping or font fallback. All three HTML runtime files and the exact source
witness are archived. Engine MJS/WASM hashes must agree with the witness before
browser execution. Native hashes receive the same check when the witness
declares them.

The complete frozen run is
`/tmp/factoidal-overnight-corpus-curves-web-wasm-ready/run.json`:

| Scope | Match | Mismatch | Unsupported | Rejected | Unavailable |
|---|---:|---:|---:|---:|---:|
| All 601 original relations | 29 | 21 | 264 | 30 | 257 |
| SVG 322 | 28 | 15 | 161 | 17 | 101 |
| HTML 279 | 1 | 6 | 103 | 13 | 156 |

The static subset contains 462 relations and has the same aggregate counts
with 118 unavailable. Each of the three independent fault controls passes all
29 exact baselines, with zero failures. Capture exits 0; comparison/wrapper
exit 1 for incomplete conformance. The original pin, all references and upstream
fuzzy limits remain unchanged. The older 38-case baseline remains separate.

SVG WASM SHA-256:
`9aaacedafaa880d27acfcb70f8902049a380ee3955393f0608334d6ef9bacfc1`,
from source checkpoint `82dbeb417bc497df5bc9bc55a4eea167cf73b763`.
HTML WASM:
`2cc861f917d5ee8bd1097b8569cacbbdc8e5be0bf97658c217b3906b8bf32e2e`;
generated MJS:
`5a7a12b0abdb68b88a81635799d65bd89b305b208d8326ff83081894f7a080d4`;
entry wrapper:
`81df58ecb197d8c1b97474f3376f3e77a20dbfdf2df2e83ffa061574a1727f6f`.
Its build witness names source `af1c1dd87033ab1f2ac2763efe390ae302c9027e`;
later test/doc commits are not described as rebuilds. This is the default HTML
profile, whose emitted metadata explicitly names ASCII bitmap text; the new
supplied-font API is not used by this corpus run.

Attribution matters: every SVG case has the same status as the preceding
use/symbol engine, and all 44 accepted SVG candidate PNGs are byte-identical.
The new exact WPT image match is HTML `svg/render/reftests/overflow-clip.html`.
Curves are separately demonstrated by five native-reader and five fresh
WASM-reader analytic controls. In each group four full 64x64 RGBA images match
exactly; arc stroke differs at four diagonal pixels, maximum channel delta 64,
despite all six embedded Lean checks passing. All five native/WASM GPU images
are byte-identical, including that failure. Evidence:
`/tmp/factoidal-overnight-corpus-curve-math/report.json` and
`/tmp/factoidal-overnight-corpus-curve-wasm-math-ready/report.json`. These controls
do not add WPT passes, and no marker/textPath support is inferred from them.

Two original HTML cases were also paired against the same-source native CLI:
overflow clip is exact and visibility-collapse still mismatches the original
browser image. Both native/WASM artifacts and PNGs are byte-identical. Native
executable SHA-256:
`ec95971ab8130ae1d59a841c26b5e541d957b7ba0ea20f9f2be16fc5c874840c`.
Evidence: `/tmp/factoidal-overnight-corpus-html-wasm-smoke/run.json` and
`/tmp/factoidal-overnight-corpus-html-native-paired/run.json`. This pair is a
diagnostic, not a second full native score.

Newly admitted HTML failures are retained. `viewBox-fractional-valid.html`
assigns the SVG a 300x200 layout box although its height 200 and viewBox ratio
100.5/100 imply width 201. Candidate ink bounds are [57,8,258,208]; original
test/reference bounds are [8,8,208,208]. The 20,100-pixel discrepancy is a
layout-sizing difference, not an oracle viewport change. `href-use-element.html`
defines IDs in one hidden SVG root and references them from another; its
expected red 100x100 rectangle is missing. Document-wide reference context is
a concrete interoperability target. Other evaluated refusals include missing
host URL context; rejection counts describe producer outcomes, not invalidity
of the original standards fixtures.

A later SVG-only diagnostic uses WASM
`830431a9c2344ad0963d113a60629738c6daa851c496632ed46c2360e90f9704`,
source `767c51a87ec4c8762ce81f573ba33913ca43320d`. The three original zero-viewBox
cases and `circle-006.svg` all match exactly; all controls pass four checks.
The other 597 rows are explicitly unselected. Evidence:
`/tmp/factoidal-overnight-corpus-zero-viewport-radius/run.json`. These four results
are not added to the earlier full-suite score without another complete run.

Fifteen integrity/provenance/scoring controls pass. New transport mutations
prove that mismatched WASM/native witnesses fail before any browser access,
and that two HTML producer selectors cannot silently choose one. The full run
initially stopped below the 3 GiB disk floor, preserving exit 2 and all 601 rows
unavailable. Only a redundant own WPT fetch cache was reclaimed after verifying
the committed originals/proofs. An early own UI-check overlay was compressed
with all bytes retained; authoritative Lake outputs and baseline evidence were
preserved. The successful full run has its separate `-ready` directory.

Reproduction and profile selection:
[`tests/external/svg-wpt/README.md`](../tests/external/svg-wpt/README.md).
Draft: https://github.com/danbri/factoidal-core/pull/310 (whole original corpus
and actual image transport). Tracker:
https://github.com/danbri/factoidal/issues/1209#issuecomment-6591712565.
