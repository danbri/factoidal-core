# Wasm component experiments (track C, milestone 1)

Plan: https://github.com/danbri/factoidal/issues/1167 (modular wasm with the
Component Model; measured build strategies). Results: [RESULTS.md](RESULTS.md).
Design record and recommendation:
[`docs/designissues/2026-10-29-wasm-components.md`](../../docs/designissues/2026-10-29-wasm-components.md).

These files change nothing in the shipped build (`formal/lean4/Wasm/build-wasm.sh`),
the npm package or any `danbri/factoidal-builds` workflow.

## What is built

A small Factoidal subset, [`lean/FxSubset.lean`](lean/FxSubset.lean): one RDF
parse entry (the reader of the shipped `parseToDatasetJson` op, then the
canonical N-Quads writer) and one SPARQL entry (the shipped `queryDataset` op).
Its import closure is 337 Lean modules of `formal/lean4`.

| Directory or file | Content |
| --- | --- |
| `wit/factoidal.wit` | the WIT world `factoidal:subset/subset`: `parse` and `query` |
| `build.sh` | Lean C plus the Lean v4.33.1 runtime with wasi-sdk 30, for `wasm32-wasip1` or `wasm32-wasip2`, wit-bindgen C bindings, `wasm-tools component new` |
| `gen-core.sh` | the C of Lean's core library, regenerated with the native `lean` (as `build-wasm.sh` step 3) |
| `closure.py` | the generated C files of the import closure of `FxSubset.lean` |
| `component/fx_component.c` | the glue between the wit-bindgen exports and the Lean exports |
| `runtime-wasi/` | 5 patches to the Lean runtime, shim headers and stubs for WASI |
| `driver-rs/` | a Rust component (wasi:cli command) that imports `factoidal:subset/rdf`; composed with `wac plug` |
| `driver-static/` | strategy 3: the same driver as a Rust static library, linked by `wasm-ld` with the Lean C into one core module |
| `baseline-emcc/` | the same subset built with Emscripten and the flags of the shipped build |
| `bench/` | inputs (`gen-data.py`), the Node harness, the variant builds and the measurement run |

## Reproduce

```bash
experiments/wasm-components/setup-tools.sh            # wasi-sdk 30, wasmtime 37, wasm-tools, wit-bindgen, wac, jco
# Lean 4.33.1 (elan) and, for the baseline only, emsdk (skills/lean4-wasm-export)
(cd formal/lean4 && lake build Wasm.Ops.Query Wasm.Ops.Parse)
python3 experiments/wasm-components/bench/gen-data.py 2000 10000
(cd experiments/wasm-components/driver-rs && cargo build --release --target wasm32-wasip2)
bash experiments/wasm-components/bench/build-variants.sh
bash experiments/wasm-components/driver-static/build.sh
N=5 bash experiments/wasm-components/bench/run-all.sh > results.jsonl
python3 experiments/wasm-components/bench/summarize.py results.jsonl
```

Run one composed component by hand:

```bash
T=/opt/tc/bin; O=/opt/wc/out/p2-opt
$T/wac plug driver-rs/target/wasm32-wasip2/release/fx-driver.wasm --plug $O/subset.wasm -o $O/composed.wasm
$T/wasmtime run --dir bench/data::/data $O/composed.wasm /data/people-2000.ttl turtle /data/q1.rq 3
/opt/jco/node_modules/.bin/jco run $O/composed.wasm $PWD/bench/data/people-2000.ttl turtle $PWD/bench/data/q1.rq 3
```
