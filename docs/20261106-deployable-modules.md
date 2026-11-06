# Deployable modules: the mechanism, by measurement

Status: PARTIAL, pushed after a machine restart so that the results are not lost. Work continues.
Scope: how a module decision reaches JS/wasm and other targets. It is not a list of topic groups.

## Results so far

Engine: `web-render.wasm`, the XSLT 4 build. Main at `dfd3d077b` unless a row says "older objects"
(objects of `factoidal-zoom-copy`, same shape, before the perf merge).

1. **Lean 4.33 already makes closed terms lazy.** Generated C reads them through `lean_obj_once`.
   In the web-render closure about 4,185 closed terms are lazy. Only 1,764 top-level constants
   and boxed constants are eager, and only 2 initialisers do IO. So "initialize computes every
   closed term" is no longer true. The eager residue is what costs.
2. **Start cost is a few constants, not `Init`.** Native, older objects, 215 M instructions in all:
   `XPath4.Core` 59 M, `Unicode.Normalization` 54 M, `XPath4.Ixml` 44 M, `XSD11.Load` 15 M,
   `HTML.Entities` 14 M, `Init` 6.4 M, runtime 0.5 M.
3. **Function reach is far below the shipped engine.** Raw link, older objects, 15.0 MB code:
   `web_render_call` reaches 1,952 functions and 1.8 MB; `web_document_call` 9,215 and 11.1 MB
   (XSLT 4); `web_render_hit` 0.34 MB.
4. **The runtime floor is mainly init code.** `render-plan`: of 1.55 MB code, 0.75 MB is
   `initialize_*`, 0.30 MB is `_init_*`, 0.46 MB is the C/C++ runtime, 38 KB is its own Lean code.
5. **Linker and Binaryen tools do not fix this.** On the 14.5 MB engine: `wasm-metadce` 14.28 MB,
   `wasm-opt -Oz` 13.93 MB, `-O3` 14.72 MB. The roots are the problem, not the tools.
6. **Post-pass over generated C** (`tools/deploy/lean-c-shake.py --mode lazy`): removes eager
   constants that no root reaches, and turns the rest into once cells. Older objects: first call
   in Node 640 ms to 39 ms; 31 of 31 fixture cases byte-identical.
7. **`wasm-split --multi-split` works on the Lean engine.** One memory, one table, one Lean heap;
   closures cross as plain pointers. Older objects: primary 4.07 MB (952 KB gzip), `xslt` unit
   9.1 MB (1.8 MB gzip), against 14.5 MB (2.9 MB gzip) in one file. The unit loads on demand.
   Split before `wasm-opt`: otherwise Binaryen inlines the gate and merges identical functions.

Main baseline: 14,683,426 bytes, 2,976,917 gzip, first call about 700 ms in Node under load.
`status.html`: call 2.4 to 3.5 s, `UTF8ToString` 3 to 27 ms, `JSON.parse` 15 to 45 ms; of the 1.87 MB
artifact, `data` is 1.23 MB. The JS side is under 3% of the call.

## Tools

`deploy/units/*.json` (manifest), `tools/deploy/build-units.py` (driver), `lean-c-shake.py`,
`wasm-refgraph.mjs`, `plan-units.mjs`, `unit-loader.mjs`, `check-units.mjs`, `entry-report.mjs`,
`web-render-corpus.mjs`. Nothing here changes the shipped engine or its build.

## Not finished

Main rerun of the split, entry-point table for SPARQL, SHACL and OWL, dynamic linking test,
native and rv32 notes, ABI cost, browser check, recommendation.
