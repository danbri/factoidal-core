# Paralliverse: checked model and Hub implementation

[Issue 604](https://github.com/danbri/factoidal-core/issues/604) tracks the component and static DSL. [PR 607](https://github.com/danbri/factoidal-core/pull/607) carries the implementation. The [v0.1 handoff](../formal/lean4/L4Factoidal/GpuKernel/STATIC_COMPUTE_V0_1.md) remains the scope agreement. The first public delivery is a worked realtime Factoidal Hub example of the same Lean packing function on CPU and GPU.

## What has actually compiled

At `9b01b038096add11f62e57768b186510aee28b5e`, the [focused Lean 4.33.1 check](https://github.com/danbri/factoidal-core/actions/runs/44428608515) compiled fresh dependencies and these four modules with strict warnings, bounded resources and individual axiom reports:

- `Paralliverse.StaticPack`: 15 results, including exact staged/scatter equality with independent `packSpec`, stable positions, unchanged surrounding memory and checked fallback.
- `Paralliverse.DSL`: eight results, including `eval_packProgram_memory` and `eval_packProgram_eq_packSpec` for every valid invocation order and arbitrary initial count, offset and payload memories.
- `Paralliverse.PackWireTheorems`: six results connecting accepted bytes to finite little-endian words, exact packet extent, row count and each descriptor's decoded row length.
- `Paralliverse.CountTarget`: six results for unsigned, checked finite-buffer instructions, culminating in `count_grid_eq_dsl`. Padded lanes are inert; all permitted physical lane permutations finish without a buffer fault, preserve destination size and agree with the whole DSL count memory, including its initial tail.

Only `propext`, `Classical.choice` and `Quot.sound` occur in the reports. The workflow requires every expected fully qualified name; a nonempty compiler log is insufficient. Earlier failed proof attempts and Lean's error-recovery `sorryAx` output are not evidence. The subsequent `CountPacketTheorems` adapter composes byte acceptance with count execution; its two new statements require their own fresh check.

Five ordinary CPU fixtures and the bounded Hub protocol fixtures passed in [run 44426385728](https://github.com/danbri/factoidal-core/actions/runs/44426385728). These are runtime tests, separately from the universal theorems. The protocol tests cover empty and mixed rows, duplicates, maximum u32, padded/reordered source storage, malformed packets and exact/one-off limits. They do not replace an encoder round-trip or a complete physical packing proof.

## Model and physical boundary

`packSpec` is ordinary row flattening. The DSL computes count memory, reads it in a completed serial scan, writes n+1 offsets including the terminal, then scatters using the completed offset memory. It reads the final output length from the actual terminal slot. Its evaluator does not return a reference answer in place of executing those stages. A canonical valid schedule exists even for zero rows.

The mathematical DSL uses total natural-addressed memories. Stage completion, immutable inputs and separate memory roles are part of that model. It does not model physical aliases or arbitrary instruction interleavings. `CountTarget` separately models finite reads/stores with faults and unsigned arithmetic. Its generic instruction interpreter never calls the DSL. Packet facts concern only input descriptors, not the desired count output; the byte-decoder theorems discharge them.

The version-1 input packet is little-endian: version, row count and bank size, then logical `(start,length)` descriptors and a distinct word bank. The encoder reverses physical row storage and inserts nonzero padding, so GPU input cannot simply be the packed output. The decoder checks the whole header, extent, all source spans and combined output count before materialising rows. A proof-oriented descriptor traversal replaces the former mutable loops. Existing CPU fixtures exercise that change; a universal equality to the former implementation is not claimed. The decoder properties proved above concern the current executable implementation and arbitrary accepted producers.

The bounded demo accepts 128 rows, 1,024 output words and 16 KiB editor input. These are demo limits, not the mathematical library's throughput or generality limit. Complete source-word correspondence, physical scan/scatter safety and simulation, target lowering, emitted-text semantics and real GPU execution remain required work. No physical GPU correctness or speed gain follows from the current proofs.

## Browser CPU and release path

`Wasm/ParalliverseHub.lean` exposes a narrow byte ABI. Operation 0 validates the editor input and prepares the packet; operation 1 decodes it and calls `StaticPack.packSpec` directly. JavaScript converts and transports bytes; it contains no packing algorithm or CPU imitation. A C shim owns the Lean input/result and returns an explicitly freed output region. The worker refreshes heap views after calls that may grow Wasm memory.

`Wasm/build-paralliverse.sh` uses the existing pinned, patched Wasm runtime and only the small CPU closure. It checks the runtime patch witness, applies the existing wasm32 Nat-literal rewrite/check, rejects unexpected linker signatures and runs the actual linked ABI in Node before installing assets. It captures source inputs from one Git commit and refuses mismatching working-tree inputs. The manifest records input and binary hashes, toolchain and runtime witness. The browser verifies both Wasm and glue bytes before importing the glue.

The separate products live under ignored `docs/web/hub/assets/l4/paralliverse/`, already carried by the web release and Eleventy pass-through. Existing browser/npm runtimes retain their own link closures. The Paralliverse page and its runtime use the service worker's network-only path. The page source has `permalink: false` until the real GPU and matching release gates pass. CPU execution remains available when WebGPU is absent, while the GPU state explicitly reports absence or an unavailable program.

## Independent review and remaining acceptance

Independent semantic review accepted the staged model and finite count statements with their stated boundaries. Independent host review found no confirmed ABI blocker and checked heap growth with a synthetic WebAssembly memory. It found dirty-source provenance and stale service-worker risks, which were repaired. Those source controls and syntax checks are test evidence.

The linked Wasm smoke, a real-browser digest-loader/tamper test, staged GPU readback, device-loss/absence handling, timing provenance and reachable deployment still need execution. Report initialisation, CPU call, upload/readback, device compute when available and comparable end-to-end samples separately. A software WebGPU run is distinct from identified hardware. Open the normal desktop Chrome tab only after the deployed demo is confirmed live.
