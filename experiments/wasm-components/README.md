# Wasm build experiments: the Lean engine as a WebAssembly component

Milestone 1 of https://github.com/danbri/factoidal/issues/1167 (modular wasm
with the Component Model; track C). Nothing here changes the shipped build,
the npm package or a `danbri/factoidal-builds` workflow.

Results and the measurements table: [`RESULTS.md`](RESULTS.md).
Design record and recommendation:
[`docs/designissues/2026-10-29-wasm-components.md`](../../docs/designissues/2026-10-29-wasm-components.md).

## What is built

`lean/WcCore.lean` is a small Factoidal subset over existing library code:
the RDF 1.1 Turtle reader (`L4Factoidal.Syntax.parseTurtle`) and the query op
of the shipped wasm (`L4Wasm.Ops.queryParsedDataset`, SPARQL 1.1 Query). Its
import closure is 334 repository modules and 811 toolchain modules
(`tools/closure.py`).

| Path | What |
| --- | --- |
| `wit/factoidal.wit` | WIT package `factoidal:core@0.1.0`: interface `rdf`, worlds `engine` (exports `rdf`) and `client` (imports it) |
| `c/wc_shim.c` | initialise Lean, convert strings; no RDF logic |
| `c/wc_component.c` | the `engine` exports over the shim, for wit-bindgen's C bindings |
| `wasi-port/` | what Lean's runtime needs under WASI and does not get from wasi-libc (see RESULTS.md, blockers) |
| `tools/patch-runtime-wasi.py` | anchored, `__wasi__`-guarded patches of Lean v4.33.1's runtime sources |
| `rust-client/` | a Rust command component (`wasm32-wasip2`) that imports `factoidal:core/rdf` |
| `rust-static/` | the same driver as a Rust static library, linked into one core module with the Lean objects |
| `build.sh` | all builds (`c`, `p1`, `p2`, `emcc`, `static`, `compose`) and the variant switches |
| `bench/` | input generator, query, `measure.py` (wasmtime and Node), `node-bench.mjs` |

## Reproduce

```sh
experiments/wasm-components/tools/install.sh        # toolchains into /opt/wc
cd experiments/wasm-components
./build.sh c && ./build.sh p1 && ./build.sh p2 && ./build.sh emcc
WC_EH=trap ./build.sh p1                            # the jco / browser variant
./build.sh static
./build.sh compose /opt/wc/out/wasm32-wasip1-o3.component.wasm
/opt/wc/bin/wasmtime run -W exceptions=y /opt/wc/out/wasm32-wasip1-o3.composed.wasm
```

`bench/gen-data.py 1000 > /opt/wc/p1000.ttl` and `... 10000 > /opt/wc/p10000.ttl`
make the inputs; `bench/measure.py` runs the table.
