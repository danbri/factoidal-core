# Proved formatting cache in the Lean renderer

The editable renderer at http://127.0.0.1:8099/ compiled its initial page
in roughly1.7–1.9s in warm Chrome calls. GPU drawing took roughly0.17s;
device/pipeline setup took8ms. These are local measurements under concurrent
build load, not stable benchmark limits.

Tracker: https://github.com/danbri/factoidal/issues/1230 .
Source draft: https://github.com/danbri/factoidal-core/pull/308 .
SVG semantics: https://github.com/danbri/factoidal/issues/1209 .

## The measured cost and exact replacement

A native phase probe of the frozen initial input found DOM/style/layout
at3–8ms, shared-scene adaptation at1ms and packed data at6–11ms.
Six four-quarter CPU probes cost238–355ms. Number formatting alone cost
601–656ms in that probe. Formatting repeatedly computed the exact
`Tdb2.javaDoubleString` representation of identical noninteger colors and
transform coefficients.

`Rendering.FloatFormat` now memoizes only that bit-keyed decimal operation.
The integer branch remains unchanged. Its cache invariant says every stored
string equals `javaDoubleString` of its key. The step and tail-recursive
list proofs establish `formatList xs = xs.map format` for every Float list.
No theorem equating Float arithmetic with real arithmetic is assumed.
The proof uses only the standard Lean axioms.

The SVG source retains its reference list formatter. A checked `@[csimp]`
equivalence selects the memoized implementation in compiled code. Inspection
of generated C confirms that `Scene.json` calls `FloatFormat.formatList`;
the proof does not merely exist beside an unchanged slow caller.

On44,212 scene numbers, three native trials measured the formatter at
599/787/1,348ms before and9/8/30ms after, with every output string identical.
These phase timings do not establish a matching whole-page speedup.

## Compiled WASM and rendering checks

Five alternating reference/candidate WASM rounds in one Node process used
the same frozen HTML, viewport and raw-output check. Reference/candidate
times were2,850/1,589ms;2,493/1,395ms;2,420/1,265ms;2,075/1,218ms;
and2,245/1,122ms. Ratios were1.70–2.00. Concurrency creates timing noise;
the paired measurement avoids comparing unrelated cold and warm runs.

Full raw artifacts are byte-for-byte identical on default, boxes, flow and
links inputs. This checks tree metadata, every packed float, shader text,
reference samples, layout boxes, glyph runs and link regions together.
The actual WASM/WebGPU link tests also pass all six groups, including
wrapped links, author color, non-links, embedded SVG and four click records.

The portable paired runner is:

```sh
node labs/demos/foafnaut/web-render/bench-compile.mjs \
  /path/to/reference/web-render.mjs /path/to/candidate/web-render.mjs \
  /path/to/original.html /tmp/new-paired-report.json
```

It records source/engine hashes, alternating timings and exact raw artifact
hashes, and refuses to overwrite a report. Local first-measurement evidence:
`/tmp/factoidal-web-paired-perf.json`,
`/tmp/factoidal-web-format-exact-output.json`,
`/tmp/factoidal-web-format-perf-native.json` and
`/tmp/factoidal-web-format-links-gpu-20261102/`.

## Next costs

CPU reference sampling still reconstructs coverage expression trees and
resolved paint repeatedly. Preparing them once per scene while proving the
same sample result is the next candidate. The GPU still scans every paint
item at every pixel; spatial indexing and glyph batching need their own
order/coverage arguments. No samples, bounds, pixel checks or tolerances were
removed for this change. Real fonts, incremental layout and resource reuse
remain separate work; this is not a full browser-performance claim.

## Prepared CPU sampler: proof checkpoint

`GraphicsPrepared.Expr.prepare_correct` establishes typed interpreter equivalence
for all expressions, arrays and environments. It folds scene constants without
using algebraic Float rewrites. Invalid array parameters remain delayed, including
inside short-circuit branches; explicit guards exercise this behavior.

The SVG coverage, primitive composition, paint-order fold and four-quarter sample
proofs connect preparation back to the existing CPU reference implementation.
A tail-recursive list builder has its own equivalence proof. The compiled batch
sampler selects the proved replacement through `@[csimp]`; it shares preparation
across all requested coordinates. Clipped, dashed and complex path primitives
retain their reference coverage implementation.

This checkpoint is source-checked. A fresh combined engine, emitted-call inspection,
byte comparisons and paired timings are pending; no second speedup is claimed yet.
The proofs preserve Lean CPU Float operations. They do not establish equivalence
to GPU Float32 evaluation or resolve the rotated-edge GPU numerical disagreement.
