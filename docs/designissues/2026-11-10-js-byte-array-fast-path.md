# Direct byte-array conversions in BubblePopJS

`JS/Interp.lean` specializes unsigned byte reads and the three byte-sized numeric
writes. Other element types retain the reference path. Two universal `@[csimp]`
equalities preserve the exact values and bytes, including every fallback case.
These are refinement proofs, not claims of ECMAScript conformance or speed.

A native Pako 2.1.0 profile put 7.4% of main-thread samples inside `typedRead` and
10.8% inside `typedBytes`. The byte cases now avoid the one-element range/fold/map
and power calculations. Generated C confirms the replacements reach `getV`,
`ownDesc`, `typedWrite`, `typedWriteV` and the native built-in dispatchers.

Before/after: base `7b4af1e1c`, macOS 15.6.1 arm64, Lean 4.33.1, native `leanjs`.
The six existing realworld drivers ran at 0, N and 4N, three times each, alternating
engine order. CPU milliseconds below are the minimum at 4N minus the minimum at 0,
as in `bubblepop_perf/realworld.py`. All 108 engine results matched Node 22.

| Workload | Before ms | After ms | Change |
|---|---:|---:|---:|
| Lodash 4.17.21 | 452.14 | 459.35 | +1.6% |
| Acorn 8.11.3 | 974.92 | 973.34 | -0.2% |
| Pako 2.1.0 | 2732.11 | 2352.40 | -13.9% |
| Marked 4.3.0 | 223.68 | 224.46 | +0.3% |
| Immutable 4.3.5 | 905.63 | 890.05 | -1.7% |
| F* SPARQL | 2639.30 | 2640.49 | +0.05% |

Pako's paired 4N reductions were 11.3–13.7%; the small changes elsewhere are not
evidence of improvement or regression on this shared machine. Library versions
match the manifest; JavaScript files came from upstream GitHub, cdnjs and installed
packages, rather than hash-checked npm tarballs. The F* bundle matches the manifest's
file hash exactly. A macOS memory watchdog bounded every run at 512 MiB.

Both `leanjs` builds and the JS test modules passed. The hygiene, import and compiled
replacement gates passed. Wrong-offset and wrong-modulus mutations failed the proofs.
No browser, renderer, QuickJS comparison or wasm32 performance result is claimed.
