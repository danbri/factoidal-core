# Browser SVG and WebGPU harness, 2026-11-02

The browser harness now records the bytes it serves and tests its ability to
detect changed GPU output. The official WPT slice remains 38 cases. No new
feature filter, tolerance or success override was added.
The final corrected run gives 4 matches, 2 mismatches, 1 rejected, 18 unsupported
and 13 unavailable, out of 38. The patched viewer smoke passes. The two remaining
WPT mismatches and the local scene's raster differences remain visible.

## Measurement boundary

`tests/external/svg/browser_gpu.mjs` runs the existing Lean WASM SVG producer and
Lean render plan through raw WebGPU. The browser SVG implementation only draws
the independent oracle. Candidate/oracle comparison requires the same browser
version and executable hash. Each candidate case records its original input
hash, compiled artifact hash, shader hash and output-image hash.

The runner freezes all served runtime bytes before browser launch and verifies
that they did not change during the snapshot. Source and served hashes differ
for stripped TypeScript and are reported separately. Source metadata includes
the local Lean import closure, toolchain pin, Git HEAD, dirty filenames and
tracked-diff hash. These facts identify inputs. They do not attest that a warm
WASM artifact was built from the current checkout. Standard-library imports
outside the repository are listed separately.

The optional `--controls` run adds an unchanged GPU replay, a real magenta GPU
shader fault, and a one-pixel readback fault outside every Lean sample position.
The last fault still passes the original sample checks. All three controls use
separate images. The comparator requires a matching unmodified baseline before
scoring sensitivity. Control counts never enter the 38-case WPT score. A setup
failure is unavailable, not a successful detection.

## Existing-artifact measurements

Installed Chrome is 156.0.8078.76. The browser uses Apple `metal-3`, with
`isFallbackAdapter=false`. Node is 22.22.2 at
`/opt/homebrew/opt/node@22/bin/node`; Playwright Core was already installed at
`/Users/danbri/.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright-core/index.mjs`.
No package or browser was downloaded.

The October 31 SVG WASM hash is
`efe7aa153159b6431283dc17211c2d48470b2033e6f4c97180bfdc7a1cea3087`.
The render-plan WASM hash is
`c8aff3e34270dd1130f513ec5275fca1cbcf2a2dbd35636cc0fae03fcf9e753f`.
The current source includes later changes; this run is an existing-artifact
baseline, not a measurement of those source changes.

Independent capture retained 29 original test/reference pairs and nine
unavailable runtime/resource cases. The existing WASM producer accepted two,
reported 27 unsupported and retained those nine unavailable cases. The full
independent comparison gives 2 matches, 23 unsupported and 13 unavailable, out
of 38. The latter includes four independent-browser reftest disagreements.

The layered local viewer rendered 46 primitives at 640×420. Its two raw images
differed at 676 of 268,800 pixels, with maximum channel difference 106. This is
a mismatch, despite all six Lean sample checks passing. GPU RGBA SHA-256:
`bcbe486739806700b3d3767d88cfcad855ec5ef7b79d1e10c0e8f59cf099850c`.
Browser RGBA SHA-256:
`5560775924bdc886788ff0a1bb1f820a328ab6fb2a5e96fead273a8980322cf8`.
The warm artifact has no retained-tree field, so that check is unavailable.
The actual manual shader fault, invalid WGSL cleanup and restoration of the
original full-image hash passed.
All 676 differing pixels are adjacent to a color change in the browser image's
3×3 pixel neighborhood; zero occur in a flat browser-color region. Their bounds
are x=14..617, y=18..363. This localizes the disagreement to raster edges; it
does not prove that anti-aliasing is the only cause.

The page also had a 12.86 CSS-pixel vertical offset between the two previews:
the GPU title row includes the Save PNG button. A common 64-pixel minimum title-row
height fixes this host layout issue. The smoke now checks desktop viewport
alignment and one-column narrow-screen layout separately from raw image metrics.
The measured 60-pixel intermediate rule aligned both viewport tops exactly and
passed narrow-screen stacking; the final 64-pixel rule gives the button more room.

All three sensitivity controls passed for each of the two matching WPT inputs:
2 pass, 0 fail, 36 unavailable per control, separately from the WPT score.

## Provisional rebuild caught a runtime defect

The first November 2 source rebuild used an official toolchain cache whose
runtime `object.o` predated the wasm32 string/list repair. Its browser result
was 0 matches, 7 rejected, 18 unsupported and 13 unavailable, out of 38. Six
admitted inputs threw a bare WASM exception before GPU adapter creation; the
seventh rejection was the negative rectangle in `disabled-shapes-01`. The
viewer initially rendered the three retained groups, but its affine fixture
switch failed. The complete viewer smoke did not pass.

This failing snapshot remains in `/tmp/factoidal-svg-20261102-fresh/`, with the
partial viewer report at `/tmp/factoidal-svg-20261102-viewer-fresh.json`.
The wrapper preserved command exit statuses 0/0/1 and returned 1 for the
incomplete WPT result. Its runtime bytes were frozen before capture; later
relinking cannot change the recorded identities. These are provisional failing
results, not the final rebuilt-engine result.

## Patched runtime and viewport diagnosis

After the runtime repair, the viewer smoke passed, including the affine fixture
which failed before. It required the three retained groups and 46 paint nodes,
checked exact preview source and submitted shader bytes, tested manual GPU and
invalid-WGSL faults, and restored the identical original full-image hash.
The final 64-pixel title rule aligns both desktop viewport tops at CSS
y=396.71875. The narrow-screen outputs remain one column. The screenshot was
visually inspected.

The current SVG WASM SHA-256 is
`cc304ebc359a29da36657fbe462f983b3a32cfeb27a9900b016b915ccbaa03fb`;
render-plan WASM is
`eed9715dc12ba25e4a13d958a26dd2de649c724087a487b118cbdc05fb116f96`.
The measured `SVG.lean` hash is
`1a0e9f745bc4cd7c6feca3b1e4fe2b390e3c8b081687accf28e3e22f885521bf`.
Exact source/runtime identities are also in
`/tmp/factoidal-svg-20261102-build-manifest.json` and the browser reports.

The default scene still differs from the browser at 668 of 268,800 pixels,
with maximum channel difference 47. All differences are adjacent to browser
color edges; none occur in a flat browser-color region. This is not pixel
equivalence. The GPU RGBA hash is
`b232e78eeb48b202b66dd1d52bbe3a1d4d18e042cdfa87759c75e0fd11b0c471`;
the browser hash remains the value recorded above. Final viewer evidence is
`/tmp/factoidal-svg-20261102-viewer-posttraversal.json` and its `.png` screenshot.

The first patched WPT run retained 2 matches, 4 mismatches, 1 rejected,
18 unsupported and 13 unavailable, out of 38, in
`/tmp/factoidal-svg-20261102-patched/`. It removed all six bare-WASM failures.
However, the transport forced an 800×600 output over each declared root size.
For the original percentage SVG's 310×170 viewport and 620×340 viewBox, this
gave scale 1.29032258 and y-offset 80.64516129 instead of scale 0.5 and no offset.
The resulting 48,552 differing pixels were a harness error. A separate intrinsic-
size GPU artifact matched both unchanged original browser test and reference
exactly, with zero differing pixels and maximum difference zero. The renderer
and fixtures did not need a change.

The corrected transport first compiles with intrinsic dimensions. For this
verified WPT pin only, it retries 800×600 on the exact Lean errors for percentage
root dimensions or omitted root width. The complete 38-root inventory has
22 `100%`/`100%`, 13 omitted-both, two 310×170 and one 200×200; there are no
partial dimensions or other percentages. No JavaScript SVG geometry or sizing
parser was added. Arbitrary local/future-pin inputs without an intrinsic viewport
remain unavailable. The capture records each viewport policy and actual output
dimensions, and the one-command runner includes a separate regression over the
two original 310×170 inputs. This does not change the WPT denominator.

## Final corrected full-slice result

`/tmp/factoidal-svg-20261102-posttraversal/run.json` records the final one-command run. Oracle
capture and candidate capture each exited 0; the comparator and wrapper exited
1 for the incomplete conformance score. There are no failed control or viewport
checks. The full image score is 4 matches, 2 mismatches, 1 rejected,
18 unsupported and 13 unavailable, out of 38.

This repeat uses the final engine after the stack-safe retained-tree traversal
repair. All six accepted cases have exactly the same generated artifact/WGSL
identities and GPU image hashes as the earlier intrinsic-viewport corrected run
in `/tmp/factoidal-svg-20261102-final/`. The complete required-tree viewer smoke
also passes on the final engine, with the same scene RGBA hash. The earlier
reports remain unchanged.

Both fallback inputs and both percentage inputs match the independent browser
test and upstream reference exactly. The percentage cases retain their declared
310×170 viewport; the dedicated transport regression passes with zero differing
pixels and maximum channel difference zero. The two `pathlength` cases each
still differ at 1,512 pixels, with maximum channel difference 64.
`disabled-shapes-01` remains rejected for negative rectangle dimensions. Nine
original runtime/resource requirements and four independent-browser relation
disagreements remain unavailable.

Each sensitivity control reports 4 pass, 0 fail and 34 unavailable. The four
unchanged replays match exactly; the four real GPU shader faults and four
unsampled readback-byte faults are detected. The two mismatching baselines do
not establish independent-oracle sensitivity, so their controls remain
unavailable rather than increasing the control pass count.

All ten existing Python harness tests passed after the final transport and
metadata changes. The new viewport regression uses the two original SVG files
and real image comparison above; it does not add synthetic WPT cases. The viewer
server remains at <http://127.0.0.1:8097/> (exec session 58359) for local review.

## Evidence and rerun commands

Generated images and JSON are artifacts under `/tmp`, not source fixtures:

- `/tmp/factoidal-svg-20261102-oracle/oracle.json`
- `/tmp/factoidal-svg-20261102-warm-candidate-v3/candidate.json`
- `/tmp/factoidal-svg-20261102-warm-comparison-v3/report.json`
- `/tmp/factoidal-svg-20261102-viewer-warm.json`
- `/tmp/factoidal-svg-20261102-viewer-aligned-warm.json`
- `/tmp/factoidal-svg-20261102-final/run.json`
- `/tmp/factoidal-svg-20261102-final/comparison/report.json`
- `/tmp/factoidal-svg-20261102-viewer-patched.json`
- `/tmp/factoidal-svg-20261102-viewer-patched.png`
- `/tmp/factoidal-svg-20261102-posttraversal/run.json`
- `/tmp/factoidal-svg-20261102-posttraversal/comparison/report.json`
- `/tmp/factoidal-svg-20261102-viewer-posttraversal.json`
- `/tmp/factoidal-svg-20261102-viewer-posttraversal.png`

Use the installed browser and Playwright paths above:

```sh
node tests/external/svg/run_browser.mjs --output /tmp/svg-browser-run \
  --browser /path/to/chrome --playwright /path/to/playwright-core/index.mjs
```

This wrapper requires an empty output directory. It retains exact commands and
their exit statuses in `run.json`. Exit 1 reports an incomplete 38-case WPT run;
exit 2 reports capture/runtime failure or a failed/unavailable control on a
matching baseline. Separate steps remain available:

```sh
node tests/external/svg/capture_reference.mjs --output /tmp/svg-oracle \
  --browser /path/to/chrome --playwright /path/to/playwright-core/index.mjs
node tests/external/svg/browser_gpu.mjs --controls --output /tmp/svg-candidate \
  --browser /path/to/chrome --playwright /path/to/playwright-core/index.mjs
python3 tests/external/svg/oracle.py --oracle /tmp/svg-oracle \
  --candidate /tmp/svg-candidate --output /tmp/svg-comparison
node labs/demos/foafnaut/browser-webgpu/server.mjs 8097
node labs/demos/foafnaut/browser-webgpu/smoke.mjs http://127.0.0.1:8097/ \
  /path/to/playwright-core/index.mjs /path/to/chrome /tmp/viewer.png \
  --report /tmp/viewer.json --require-tree
```

The comparator exits 1 for an incomplete WPT run. A changed-browser metadata
control was rejected before candidate scoring. All ten existing Python harness
tests passed; the four independent-oracle tests also passed after decoder
performance changes. The decoder retains bounded input, CRC, PNG filter and
white-background alpha checks. It avoids computing predictors for unused filter
types, caches repeated independent images, and takes an exact equality shortcut
without changing the upstream fuzzy ranges.
