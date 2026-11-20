# Paralliverse Studio: programs, evidence and actual readback

19 November 2026. [Work item 647](https://github.com/danbri/factoidal-core/issues/647),
[GPU work item 646](https://github.com/danbri/factoidal-core/issues/646),
[combined PR 648](https://github.com/danbri/factoidal-core/pull/648).

The Studio turns the existing packing demo into an editable program playground.
It keeps the packing experiment and adds flat word pipelines, visual CPU/GPU
views, an inspected source/fused tree, complete GPU plans, a bounded signal
animation, keyboard/manual/live controls, sharing and export of actual Lean
source. The [developer guide](20261119-paralliverse-studio-guide.md) includes
complete examples of the library API and a separate primitive language.

## One source, independent execution paths

Lean parses commands such as `map multiply 3` followed by `map add 1`. The
browser editor accepts this bounded Paralliverse language, rather than compiling
arbitrary Lean source. The resulting typed `Program` is the source for both
interpretations. CPU execution uses the actual fused `Par.mapChunks` interpreter.
GPU selection inspects the original syntax, preserving the current backend's
explicit refusal of unsupported source trees. More than two commands remain
available on the CPU, up to the sixteen-command admission limit.

The runtime returns the original and actual fused IR, a copyable Lean term, the
CPU words and every word/identifier in the selected execution plan. JavaScript
does not parse commands, compute reference results, select kernels or reconstruct
the intermediate payload. It presents the returned data, copies buffers, submits
the selected shaders and compares readback. GPU devices initialise on demand.

The complete buffer plan includes each input header, payload and spare sentinel;
pass selectors and source/destination IDs; dispatch geometry; and the expected
entire final destination. In a two-pass program, the first destination is the
second source. Separate ordered command passes provide the physical visibility
assumption. [GPU model and exact fifteen-name inventory](20261119-paralliverse-word-map-gpu.md)

## Interaction and bounded motion

CPU and GPU visual views have separate result caches. A GPU view remains empty
until actual GPU readback arrives. Colour and cell placement are presentation
choices; the complete numeric result is also shown. Input edits invalidate the
previous result and exported source. Pausing stops future automatic requests
while allowing an already-submitted current request to finish.

Signal playback requests at most 32 phases. The UI changes only the requested
coefficient. Each next phase waits for the current request's actual CPU/GPU byte
match, including the full header/tail comparison. A mismatch, refusal, failure,
edit, mode change or explicit Stop ends playback. Step requests one acknowledged
frame. Playback starts only on request and has no unbounded animation loop.

Experiment links hold bounded local fragment state, with UTF-8/version/type
checks before use. Both initial loading and same-document `hashchange` restore
the source and input, which are still checked by Lean. Copy and download use the
runtime's `leanSource`; the page does not synthesise another implementation.

## Byte interface and limits

Existing operations 0 (prepare packing), 1 (CPU packing), and shader selectors
0–2 retain their meaning. Operation 2 also exports selectors 3 (add) and 4
(multiply). Operation 3 takes program UTF-8, a NUL byte and a flat JSON input.
Operation 4 accepts an empty request and reports the Lean-owned capabilities.
Old runtimes without operation 3 keep packing available and disable the Studio.

| Admission | Bound |
| --- | --- |
| Program bytes | 512 |
| Nonempty map commands | 1–16 |
| Flat input bytes | 16,382 |
| Combined request bytes | 16,895 |
| Input words | 0–1,024 |
| GPU source maps | 1 or 2 |
| Workgroup size / maximum groups | 64 / 16 |
| Share state before base64 | 16 KiB |
| Playback / host submission deadline | 32 frames / 15 seconds per submission |

The byte-refusal and admitted-script results below are kernel checked. A complete
text-grammar roundtrip, general heap/time bounds, host deadline enforcement and
physical scheduling are separate properties; tests do not establish them as
theorems.

## Compiled theorem evidence

All twelve new Studio declarations compiled at
`d499e3be2f158278adc544dc1089cebc8443c5be`, Lean 4.33.1, in
[strict job 135839543303](https://github.com/danbri/factoidal-core/actions/runs/44603117138/job/135839543303).
Its complete 21-module source closure returned zero. Mandatory individual axiom
reports and hygiene passed. Root independently read the raw log. Only `propext`,
`Classical.choice` and `Quot.sound` occur; `pipeline_affine` needs no axioms and
`report_refused_plan` needs only `propext`.

Within `L4Factoidal.Paralliverse`:

| Namespace | Checked declaration |
| --- | --- |
| `Studio` | `runCPU_eq_source` |
| `Studio` | `pipeline_affine` |
| `Studio` | `three_maps_refused` |
| `Studio` | `Script.command_count` |
| `Studio` | `parseProgram_over_limit` |
| `Studio` | `parseRequest_over_limit` |
| `Studio` | `evaluate_correct` |
| `Studio` | `report_source_fields` |
| `Studio` | `report_selected_plan` |
| `Studio` | `report_refused_plan` |
| `Hub` | `studio_exports` |
| `Hub` | `capability_exports` |

The five GPU proof lanes in the same run passed their fifteen new declarations
and eleven executable model guards. These 27 declarations are additional to
the earlier eight typed-program and five ordered-partition results incorporated
by PR 648. The separate theorem-only draft PR 609 remains for human review.

## Executable and device evidence

The native Studio fixtures exercise real report JSON, modular arithmetic,
operation order, seeded buffers, malformed source/input, exact byte/word/command
limits and GPU refusal. CI also emits the actual copy/export source and compiles
it. At `ad76d6043`, all three developer-guide Lean code blocks also compiled.

[Physical run 44605819693](https://github.com/danbri/factoidal-core/actions/runs/44605819693)
at `ac601b4e45298c21c528c7b01427d408c9345815` passed:

- Linked Wasm C/byte-interface fixtures, including all five shader source hashes.
- Nine native-Lean versus actual Deno/Mesa Vulkan comparisons, using llvmpipe
  LLVM 20.1.2, with payload and complete destination equality. Cases include
  0, 1, 64, 65, 129 and 1,024 words, wrapping values, duplicates and both pass orders.
- Seventeen Chrome 157/SwiftShader browser scenarios, including 32 matched
  signal frames, actual GPU visual selection, keyboard execution while live
  updates are paused, refusal, malformed-input recovery, copy/share,
  same-document fragment restoration and a fresh 390-pixel mobile load.
- Six applicable premerge groups, zero failures, 23.7 seconds on that runner.

Browser and worker exceptions and failed network requests were empty. Root
inspected the desktop, signal and mobile screenshots. The earlier sharing
acceptance failure is retained in run 44604522509 and was fixed rather than
counted as a pass. A deliberately withheld-WebGPU API scenario is an additional
UX test; its final result and subsequent landing/publication are recorded in
the issue so this source record does not claim an unrun gate.

A later independent review reproduced an initialization race where device loss
could be followed by an incorrect ready event. The initializer now rejects that
loss, the worker checks loss again before publishing readiness, and neither
backend publishes a completed result after its loss callback. Five isolated
event-ordering tests exercise the real initializer/worker code with synthetic
device timing. Before repair only the ordinary initialization case passed;
after repair all five pass. These tests check host state publication, not GPU
numerical correctness. The repaired exact-source physical and Linux results are
recorded in the issue before landing.

The standalone CPU Wasm is 1,535,005 bytes, compared with 1,459,362 bytes in the
live source-7005 module before this change: 75,643 additional bytes, about 5.2%.
No comparative latency benchmark is established. The page reports actual
worker-clock samples and includes different transport work in CPU and GPU
times; it infers no speedup. The Lean compiler/runtime, C glue, serializer
transport, browser compiler/driver/hardware and physical command ordering remain
explicit trust or separately tested boundaries.
