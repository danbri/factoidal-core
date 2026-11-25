# Paralliverse: checked model and Hub implementation

[Issue 604](https://github.com/danbri/factoidal-core/issues/604) tracks the component and static DSL. [PR 607](https://github.com/danbri/factoidal-core/pull/607) carries the implementation. The [v0.1 handoff](../formal/lean4/L4Factoidal/GpuKernel/STATIC_COMPUTE_V0_1.md) remains the scope agreement. The first public delivery is a worked realtime Factoidal Hub example of the same Lean packing function on CPU and GPU.

## What has actually compiled

The [fresh strict check at76c1ec9ea5c30a63357fc5cc68d9c2635367f934](https://github.com/danbri/factoidal-core/actions/runs/44456102217) passed all66 required individual reports, every owned module, hygiene and both ordinary CPU and bounded Hub protocol fixture groups. Dependencies and generated C came from the recorded source, with explicit package setup and positive compiled-definition anchors. No local Lean cache or copied olean is evidence for these results.

- `PipelineTarget.decoded_pipeline` and `decoded_pipeline_eq_packSpec` connect the accepted byte packet, arbitrary adequate initial arrays and independent valid padded lane orders to the actual finite Count, Scan and Scatter executions. Readback uses the executed terminal offset and equals the original sequential `StaticPack.packSpec`. The theorem retains count/offset memory, sizes and every untouched payload-tail cell. It does not assume the desired intermediate outputs.
- Count expression and Loop expression/statement continuation machines have universal equality theorems covering their original instruction semantics. Those theorems compiled before enabling their compiler replacements. The full Linux build must still establish the complete executable recursion gate.
- `WGSL.parse_count_text`, `count_text_launch` and `decoded_count_text_lane` connect the actual333-byte Count source to its independent byte parser and finite u32 execution. The active invocation writes only its own count address; padding has an empty store trace.
- `WGSL.parse_scan_text`, `scan_text_launch` and `decoded_count_scan_text` connect the actual570-byte Scan source to its independently parsed loop, carry, bound snapshot, guard and terminal assignment. For every accepted input and real Count result, the whole offset array agrees with the finite Scan target, includes the mathematical terminal total and preserves the tail. The actual chronological store footprint is exactly addresses0 through n, including the zero-row case. The host must dispatch this shader once.

Both shader parse/launch pairs report `[propext]`. The Scan accepted-packet equivalence and both pipeline results report `[propext, Classical.choice, Quot.sound]`. All reports stay within those three permitted axioms. Earlier rejected proof attempts and elaborator-recovery `sorryAx` reports do not establish results. The Count source was rechecked unchanged after sharing the parser helpers with Scan. Scatter source and trace equivalence are still under construction.

The generated-C component diagnostic checks real `lp_l4factoidal_` definitions. Its five remaining input-proportional rows are four derived `Repr` functions and `GpuKernel.lastWrite`, covered by existing reviewed allowances. The earlier full build at2cdd1538e had rejected the expression evaluator and right-fold sum before linking CPU Wasm. Those executed paths now use the checked continuation replacements and a proved foldl sum. The focused diagnostic is not a full-library gate or a runtime speed measurement.

Five ordinary CPU fixtures and bounded Hub protocol fixtures exercise empty/mixed rows, duplicates, maximum u32, padded/reordered storage, malformed packets and exact/one-off limits. These runtime tests are separate from universal theorems. A fresh integrated-main full Linux build and the actual linked CPU Wasm/Node smoke are the next gates.

## Integrated build and remaining proof gates

The integrated688bac00a Linux build compiled the full library but stopped at
the C recursion gate before CPU Wasm. Its sole new report is the unchanged
`Dataflow.Pipeline.toStage` helper. The classifier's global short-name set
now treats the nonrecursive indexed `Paralliverse.DSL.Stage` as recursive and
classifies the distinct Dataflow Stage result as depth-sensitive. The helper
is genuinely non-tail if executed; source review found only its own recursive
call and proof uses. Source inspection is not a complete emitted-C reach audit,
so no specification-only allowance was added.

Instead a direct Stage constructor uses the existing tail-recursive
`Pipeline.run`, its contract and the existing soundness theorem. A universal
whole-function equality candidate `Pipeline.toStage_eq_direct` is submitted
to a separate fresh dependency-closure check. The [fresh strict check at ae9c130fa](https://github.com/danbri/factoidal-core/actions/runs/44458557948) compiled `Pipeline.toStage_eq_direct` with `[propext, Quot.sound]`. Compiler substitution is now enabled after that result. The next full C and caller-reach gate remains required.

The first Scatter text proof check rejected elaboration errors and a concrete
parse reduction at the 2 GiB kernel limit. The repaired second check rejected
only the lexer/parser reductions at that limit; no recovery self-axiom report
is accepted. The next check gives only Scatter a 4 GiB Lean cap inside a 6 GiB
OS ceiling, retaining one worker, the fixed stack and180-second deadline. All
other new modules keep the earlier limits. The [resulting ae9c130fa check](https://github.com/danbri/factoidal-core/actions/runs/44458557901) passed all71 required reports, including Scatter source parsing, actual whole-buffer lane equality and disjoint actual store traces. No recovery axioms occur in the accepted reports.

## Model and physical boundary

`packSpec` is ordinary row flattening. The DSL computes count memory, reads it in a completed serial scan, writes n+1 offsets including the terminal, then scatters using the completed offset memory. It reads the final output length from the actual terminal slot. Its evaluator does not return a reference answer in place of executing those stages. A canonical valid schedule exists even for zero rows.

The mathematical DSL uses total natural-addressed memories. Stage completion, immutable inputs and separate memory roles are part of that model. It does not model physical aliases or arbitrary instruction interleavings. `CountTarget` separately models finite reads/stores with faults and unsigned arithmetic. Its generic instruction interpreter never calls the DSL. Packet facts concern only input descriptors, not the desired count output; the byte-decoder theorems discharge them.

The version-1 input packet is little-endian: version, row count and bank size, then logical `(start,length)` descriptors and a distinct word bank. The encoder reverses physical row storage and inserts nonzero padding, so GPU input cannot simply be the packed output. The decoder checks the whole header, extent, all source spans and combined output count before materialising rows. A proof-oriented descriptor traversal replaces the former mutable loops. Existing CPU fixtures exercise that change; a universal equality to the former implementation is not claimed. The decoder properties proved above concern the current executable implementation and arbitrary accepted producers.

The bounded demo accepts 128 rows, 1,024 output words and 16 KiB editor input. These are demo limits, not the mathematical library's throughput or generality limit. Accepted-packet source/count/scan/scatter composition is checked in the finite instruction model. Count and Scan emitted-text semantics are checked independently; Scatter text semantics, whole-pipeline emitted-text composition and real GPU execution remain required work. No physical GPU correctness or speed gain follows from the current proofs.

## Whole-text composition and individual-store candidates

The next snapshot adds an actual parsed-text Count→Scan→Scatter program,
chronological per-lane store logs and terminal readback. Its proof candidates
connect that program to packSpec without putting a target interpreter into
the program itself. Generic unique-address individual-store permutation and
prefix theorems, plus an adapter to the actual recorded scatter events, address
the gap between completed-lane schedules and arbitrary individual stores.
These new scripts still await strict checking. The Race module's prose now
explicitly avoids claiming that arbitrary racy interleavings equal whole lanes.

The three byte-identical shader literals now live in dependency-light
`WGSL/ShaderText.lean`, shared by the proof modules and CPU ABI. Operation2
returns a source selected by one request byte; an ABI equality theorem and
actual linked smoke are pending. The worker has a strict UTF-8 source reader.
The new GPU transport uses fixed positive buffers, ordered passes, an actual
terminal copy to aligned staging and bounded payload readback. Strongest-model
independent review checked buffer roles, zero/odd rows, allocation errors and
device loss. It is connected in the unpublished page but has not yet executed on a device. That source review does not establish GPU execution.

## Browser CPU and release path

`Wasm/ParalliverseHub.lean` exposes a narrow byte ABI. Operation 0 validates the editor input and prepares the packet; operation 1 decodes it and calls `StaticPack.packSpec` directly. JavaScript converts and transports bytes; it contains no packing algorithm or CPU imitation. A C shim owns the Lean input/result and returns an explicitly freed output region. The worker refreshes heap views after calls that may grow Wasm memory.

`Wasm/build-paralliverse.sh` uses the existing pinned, patched Wasm runtime and only the small CPU closure. It checks the runtime patch witness, applies the existing wasm32 Nat-literal rewrite/check, rejects unexpected linker signatures and runs the actual linked ABI in Node before installing assets. It captures source inputs from one Git commit and refuses mismatching working-tree inputs. The manifest records input and binary hashes, toolchain and runtime witness. The browser verifies both Wasm and glue bytes before importing the glue.

The separate products live under ignored `docs/web/hub/assets/l4/paralliverse/`, already carried by the web release and Eleventy pass-through. Existing browser/npm runtimes retain their own link closures. The Paralliverse page and its runtime use the service worker's network-only path. The page source has `permalink: false` until the real GPU and matching release gates pass. CPU execution remains available when WebGPU is absent, while the GPU state explicitly reports absence or an unavailable program.

## Independent review and remaining acceptance

Independent semantic review accepted the staged model and finite count statements with their stated boundaries. Independent host review found no confirmed ABI blocker and checked heap growth with a synthetic WebAssembly memory. It found dirty-source provenance and stale service-worker risks, which were repaired. Those source controls and syntax checks are test evidence.

The linked Wasm smoke, a real-browser digest-loader/tamper test, staged GPU readback, device-loss/absence handling, timing provenance and reachable deployment still need execution. Report initialisation, CPU call, upload/readback, device compute when available and comparable end-to-end samples separately. A software WebGPU run is distinct from identified hardware. Open the normal desktop Chrome tab only after the deployed demo is confirmed live.

## Device execution check submitted

The local pinned Deno2.9.4 request returned no adapter. This is not a device
validation pass. A separate bounded CI job uses the proven Linux Mesa lavapipe
Vulkan environment and the actual Hub GPU transport. Fresh native Lean produces
the three shader strings, encoded packets and sequential packSpec byte outputs.
Eight cases exercise one reused buffer session: changed equal-sized data, zero
rows followed by prior data, active empty rows,65 padded rows,128 rows/1024 words
and one maximal-width row. The checker requires an adapter and compares every
returned byte and length, recording source, shader hashes, driver, timings and
output digests. A missing adapter fails that check. Actual CI execution is pending.

This native Lean differential is separate from the linked CPU Wasm/Node ABI,
the browser worker and live Hub acceptance. The new scripts are under
Harness/ParalliverseDeviceFixtures.lean and tools/paralliverse-device-smoke.mjs;
they do not replace any kernel proof or claim hardware performance.

## Checked complete text and device checkpoint

[Strict6a1fd7842](https://github.com/danbri/factoidal-core/actions/runs/44462235622)
passes the combined parsed-text pipeline and both individual-store adapters,
all three generic permutation/prefix results and the actual shader-export ABI
theorem. The complete text readback and concrete interleaving results report
`[propext, Classical.choice, Quot.sound]`; generic store results and the ABI
result use `[propext, Quot.sound]`. All owned modules return zero, with clean
hygiene and both CPU fixture groups. Earlier resource-recovery reports are
not counted.

The [same-source actual WebGPU execution check](https://github.com/danbri/factoidal-core/actions/runs/44462235672)
passes all8 native-Lean differential fixtures on Mesa llvmpipe LLVM20.1.2,
reported fallback=true. Every prefix byte and actual output length matched,
including reuse and both1024-word cases. This is software Vulkan execution,
not a hardware correctness proof or a browser-Wasm result.

The first full6a build still stopped at the Dataflow recursion audit because
its source scanner recognises inline `@[csimp]` annotations but not the
standalone attribute command used for the checked constructor equality. The
same already-proved replacement now uses the existing inline style. The
unchanged scanner positively resolves the exact full name to toStageDirect;
no allowance or audit rule changed. Fresh complete C/caller gates remain.

The manual browser acceptance workflow waits for an official matching web
release. It builds the actual Pages source with the route enabled only in
disposable CI, drives compiled Wasm CPU and Chrome software WebGPU through
the actual controls, and saves diagnostics and a screenshot. It has not run.
The public route remains disabled.

## Full build checkpoint — 2026-11-19 06:10 UTC

The [ac55 full build](https://github.com/danbri/factoidal-builds/actions/runs/44465276144) passed the unchanged C/caller gates, native Linux, browser-host tests and relocated Linux browser GUI checks. Its Wasm stage reached the new linked module and failed the actual Node ABI smoke: Emscripten rejected the supplied `wasmBinary` because it was absent from `INCOMING_MODULE_JS_API`. The linker now explicitly accepts `wasmBinary` and `locateFile`, the two inputs used by the smoke and digest-verified worker. Bash syntax and whitespace checks pass; linked execution remains pending a fresh exact-source build. The public route remains disabled.

## Checked runtime publication and browser workflow

[All a458 Linux gates](https://github.com/danbri/factoidal-builds/actions/runs/44469930225) passed, including actual linked CPU Wasm/Node fixtures,53 host checks with0 failures, web gates and relocated Linux GUI. PR607 merged as c9b4e07358437579427f580ae7b40d079d590ca5 with the public route disabled. The existing publisher's fresh current-main comparison accepted a458 as an ancestor and published [the exact checked web release](https://github.com/danbri/factoidal-builds/releases/tag/build-a458a3fa48d6-web), without rebuilding it.

The release's build-info lists the Paralliverse manifest,88,428-byte glue and1,459,362-byte Wasm. Its Wasm SHA-256 is b42f549e9781463589722e34447931530d5fb616a04c6003858757749f10ff5c. The first browser dispatch was rejected before execution: GitHub does not allow runner.temp in job-level env. Evidence setup now uses that expression only at step scope and passes its value to subsequent steps through GITHUB_ENV. No runtime or proof changes are made. Actual browser acceptance remains pending and the public route remains disabled.

## Actual browser acceptance and public Hub entry

[Chrome acceptance44475690694](https://github.com/danbri/factoidal-core/actions/runs/44475690694) passed against frozen page source c9b4e07358437579427f580ae7b40d079d590ca5 and the official a458 runtime release, using the repaired workflow control at978dc00fe. Chrome157.0.8103.50 reports Google SwiftShader, fallback=true. All four mixed/changed/zero/changed-after-zero cases show the actual compiled-Wasm CPU and actual WebGPU readback bytes equal, with no page errors or failed requests. All three reported shader hashes match the checked Lean constants. The preserved screenshot was inspected: editor, result cards, exact match, costs and proof/trust boundaries are legible. A single console warning calls zero workgroups unusual; there is no validation failure. This remains software-device differential evidence, not a physical-GPU benchmark or proof of the driver.

The route and Hub entry are enabled in source after that acceptance. A final-source browser check and canonical deployment are next. Normal desktop Chrome opening waits for confirmed live deployment. The wider604 library, hardware CI and benchmark obligations remain open. Runtime/proof files and published bytes do not change in this publication step.
