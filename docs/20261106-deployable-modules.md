# Deployable modules: the mechanism, by measurement

Date: 6 November 2026. Owner's question, 5 November: what mechanisms make a module decision
deployable in JS/wasm and in other extraction workflows, on the call graph and not on files.
This is not a list of topic groups. Nothing here changes the shipped engine, its build or npm.

## Result

Use **one manifest and two mechanisms**:

1. **A post-pass over the C that Lean emits** (`tools/deploy/lean-c-shake.py`). It keeps only the
   constants that the declared entry points reach, and makes them lazy. It is plain C in and plain
   C out, so it serves wasm, native and rv32. It removes almost all start cost.
2. **`wasm-split --multi-split`, by function, after the link and before `wasm-opt`.** One primary
   wasm holds the Lean runtime and heap. Each unit is a wasm that imports the primary's memory,
   table and functions. Lean objects and closures cross as plain pointers. JS loads a unit when
   the manifest says a call needs it. No Lean source changes and no recompile with `-fPIC`.

On the real case (`web-render`, XSLT 4 linked, main at `dfd3d077b`):

| | Shipped form | Manifest build |
|---|---|---|
| First download | 14,683,426 B (2,976,917 gzip) | primary 4,213,864 B (988,992 gzip) |
| On demand | none | `xslt` unit 9,364,868 B (1,847,971 gzip) |
| Native start, instructions | 186 to 213 M | 0.4 to 1.6 M |
| Native memory after start | 6.5 to 7.4 MB | 1.4 MB |
| Node: load, then first call | 52 ms, 200 ms | 40 ms, 29 ms |
| Node: load unit, first XSLT | none | 30 ms, 173 ms |
| `status.html` in wasm, 800x600 | 555 to 631 ms | 574 to 590 ms (no change) |
| Output, 31 fixture cases | reference | byte-identical, unit not loaded until needed |

Medians of 7 processes, Node 22, machine lightly loaded. Output hashes also match in Chrome 156
and Safari 18.6 (2 cases each), under a CSP with `wasm-unsafe-eval` and no `unsafe-eval`.

## Corrections to the brief

- **`web-render.wasm` is 14.7 MB, not 3.5 MB.** XSLT 4 made the change; 2.98 MB is its gzip size.
- **Lean 4.33 does not compute every closed term at start.** The code generator already reads
  `___closed__` terms through `lean_obj_once`. What stays eager is top-level constants and boxed
  constants: 1,764 in this link, and 3,466 in the full engine.
- **`Init` is not the main start cost.** Native, older objects: 215 M in all. `XPath4.Core` 59 M,
  `Unicode.Normalization` 54 M, `XPath4.Ixml` 44 M, `XSD11.Load` 15 M, `HTML.Entities` 14 M, `Init`
  6.4 M, runtime 0.5 M. ("Older objects" means the same engine before PRs 363 and 364.)
- **The 1.4 MB "runtime floor" is mostly init code.** Measured floor below: 435 KB.

## 1. Call graph

Tools: `wasm-refgraph.mjs` reads a `wasm-ld --emit-relocs` link. Its edges are relocations, so a
Lean closure (an address taken) is an edge. `wasm-opt --print-call-graph` shows direct calls only
and would miss closures. `lean-c-shake.py` does the same over the generated C, and it also sees
which constant needs which initialiser. `entry-report.mjs` prints the table below. Bytes are raw
link code before `wasm-opt`, Lean runtime functions included. The file columns are the object code
of the import closure, without `Init` and the runtime.

| Entry point | Functions | Code bytes | Data bytes | Files | File-closure code |
|---|---:|---:|---:|---:|---:|
| parse Turtle (`parseTurtleFast`) | 721 | 560,977 | 69,988 | 10 | 496,433 |
| parse HTML | 769 | 814,461 | 121,130 | 7 | 634,193 |
| layout (`Layout.render`) | 941 | 541,944 | 73,962 | 18 | 1,076,697 |
| SPARQL (`queryDataset`) | 4,543 | 3,407,066 | 226,977 | 334 | 7,155,577 |
| SHACL validate | 3,909 | 2,922,540 | 221,872 | 113 | 4,039,930 |
| OWL closure, with RL | 1,472 | 727,142 | 84,792 | 149 | 3,584,338 |
| `web_render_call` | 2,421 | 1,963,768 | 189,987 | | |
| `web_document_call` (all ops) | 13,203 | 13,435,067 | 1,509,617 | | |
| `l4_call_c`, the one dispatch export | 31,124 | 30,837,044 | 2,336,905 | 873 | 30,790,403 |

Findings:

- The function closure is 72% of the file closure for SHACL, 48% for SPARQL, 20% for OWL. For small
  parsers the two are near, because the function column counts runtime and `Init` code and the
  file column does not.
- **The export is the wrong unit.** A string-keyed dispatch reaches 97% of the 31.8 MB engine from
  one export, and `web_document_call` reaches 97% of `web-render` for one `op` value. The linker can
  never remove this. Parse, SPARQL, SHACL and OWL together reach 4.88 MB, 15% of that code.
- **`initialize_*` kept alive:** in `web-render` 1,280 of 1,764 eager constants have no reader
  from the exports, and raw link code falls from 15.0 MB to 13.8 MB (19,557 to 14,480 functions).
  So most of that engine is really reachable; there the gain is start cost and the split. In
  `render-plan`, which reaches little, 68% of the bytes went: 1,375,073 to 435,246.

## 2. Dead code

| Step on the engine | Result |
|---|---|
| `wasm-ld --gc-sections` | on by default; every module init is a root |
| `wasm-metadce`, exports as roots | 14.53 MB to 14.28 MB (older objects) |
| `wasm-opt -Oz`, `-O3` | 13.93 MB, 14.72 MB (older objects) |
| LTO, `render-plan` | 1,375,073 to 1,362,419 (0.9%) |
| C post-pass, `render-plan` | 1,375,073 to 435,246; gzip 258,936 to 137,908; first call 28 ms to 3 ms |
| C post-pass, `web-render`, one file | 14,683,426 to 13,456,673; gzip 2,976,917 to 2,815,742 |
| C post-pass, native arm64, `web-render` | 22.7 MB to 4.3 MB binary |

These tools cannot do this because the roots are wrong, not because they are weak. After the
post-pass, `render-plan` has 3.9 KB of init code left, against 1.05 MB.

**What the pass does.** Each eager `G = _init_G();` becomes a once cell and an accessor, and
each read of `G` calls the accessor: 484 constants and 1,097 reads here. Constants that no root
reaches are deleted from the init function. Empty init chains go too. Two `initialize` declarations
with IO stay eager here (36 in the full engine); their functions are roots.

**Cost.** Native, same-compiled `Init`, `status.html`: 2.925 G instructions before, 2.915 G after,
so the accessors cost nothing measurable. The toolchain's own `libInit` is 9% faster than our `-O3`
rebuild (2.66 G). That is a separate result, and it says the wasm `Init` may also leave speed behind.
Native output hashes match on 3 fixtures.

**Lean module system.** No help here. Only 77 of 1,468 files use `module`. It splits
`runtime_initialize_` from `meta_initialize_` (446 eager terms in `meta`, Lean parser descriptors),
and the post-pass removes those anyway. Laziness of closed terms does not depend on `module`.
A `Thunk` by hand (as for HTML entities) works for one table, but it changes each type and each
author must remember it. The post-pass needs no source change.

**Trust.** The post-pass is outside the Lean proofs. It changes when a pure constant is evaluated,
not what it is. One visible change: a `panic` in a constant comes at first use, not at start. It
reads compiler output, so a new Lean version can change the form. An unknown statement form is kept
as it is, so that constant stays eager; the tool does not stop on it. A check for this is still to do.

## 3. Composition at load time

Same engine and same 31 cases where a row says so.

| | (a) static engines | (b) `MAIN_MODULE=2` + side | (c) components | (d) `wasm-split` units |
|---|---|---|---|---|
| Status | shipped | prototype, 31 of 31, with a stub | 2-function subset, 2026-10-29 | prototype, 31 of 31 |
| First download | 14.68 MB (2.98 gzip) | 5.94 MB (1.26 gzip) | not built here | 4.21 MB (0.99 gzip) |
| Second part | none | 10.92 MB (1.95 gzip) | not built here | 9.36 MB (1.85 gzip) |
| JS glue, gzip | 27 KB | 76 KB | 49 KB | 46 KB (`-O1` link; see limits) |
| Load, first call | 52, 200 ms | 33, 20 ms | jco load 2x Emscripten | 40, 29 ms |
| Load second part | none | 85 to 118 ms | not measured | 23 to 40 ms |
| Lean objects across parts | no: JSON strings | yes | no: separate memory, copy | yes |
| Heap and runtime | one each per engine | one | one each per component | one |
| Split granularity | engine | object file | component | function |
| Recompile | none | all 1,043 objects with `-fPIC` | wasi-sdk, 5 runtime patches | none |
| Hot path, `status.html` | 555 to 631 ms | 573 to 581 ms | equal in 2026-10-29 data | 574 to 590 ms |
| Exceptions | fine | fine | jco refuses wasm exceptions | fine; unit needs no tag |
| Browser | all | Chrome/Safari not tested | jco output, not tested | Chrome 156, Safari 18.6 |
| Node | yes | yes | yes | yes |
| CSP | `wasm-unsafe-eval` | same | same | same |

Why (d) and not (b), although (b) ran:

- **Granularity.** With objects, 2.2 MB of XSLT-only code stays in main, because a file holds both
  kinds of function. Unit code in (b) is also larger: 10.92 MB against 9.36 MB.
- **`GOT` entries must resolve at start.** A main object that names a side global or a side
  closure (`___boxed`) aborts the load. A fix-point moved 12 objects to main.
- **Init chains.** Main needs the `initialize_` of side modules. I stubbed 103 of them. With the
  stubs, IO initialisers in the side module do not run, so this prototype is not correct in general:
  no fixture touches `schemaCache`. A function split does not have this problem.
- **Cost of (b):** a second compile of every object, and a second set of system libraries.

(a) stays right for a small independent tool: after the post-pass an engine costs 435 KB (138 KB
gzip), so `render-plan` can stay separate. (c) stays right at a coarse boundary with another language
or a server host. The 2026-10-29 data show the copy across a coarse boundary is cheap. It cannot share
Lean objects. That experiment is on main in `experiments/wasm-components/`.

**wasm-split notes.** The `xslt` unit imports 212 functions, 1 global, memory and table. The primary
exports 239 names and imports 4,232 placeholders, about 100 KB. A closure in the table points at a
placeholder until the unit loads. In Node or a worker the placeholder can load the unit
synchronously. The test with `--no-sync` shows that the declared route never reaches a placeholder.
Chrome limits synchronous compile on the main thread, so a page must use `ensure()`.

Two traps, both found by test:

1. Split **before** `wasm-opt`. At `-O2` it inlines the gate and merges identical functions, and
   a primary function then calls into the unit at start. The link is `-O1`; each part gets
   `wasm-opt -O2` after the split. Total size stays near: 13.58 MB against 13.46 MB in one file.
2. Static inline helpers have one name in many objects, so a name is not an address. A function
   whose name is not unique stays in the primary (171 here).

## 4. ABI

`status.html`: 1.87 MB of JSON; `data` is 1.23 MB, `tree` 357 KB, `webRender` 107 KB, `tiles` 84 KB.

Wasm in Node: the call is about 570 ms; `UTF8ToString` 3 to 27 ms; `JSON.parse` 15 to 45 ms. So the JS
side is under 10% of the call. Most of the cost is in Lean, before the boundary. Native profile, share
of `web_render_compile`: `Scene.json` 83%, of which CPU check samples 33% (no relation to the ABI);
`FloatFormat` 16%, string `quote` 10%, `DisplayNode.json` 8%, `Float.ofScientific` 12%. Layout 9%.

Estimate, not measured: a binary boundary removes about 25 to 35% of the Lean call and most of the
JS cost. The check samples are a larger target and need no ABI change: leave them out of the
production artifact.

The shape: one result with a JSON head and one byte region. The fat engine already has this form,
`l4_call_blob_io_c`. With one memory (mechanism d), JS can view the region in place,
`new Float32Array(memory.buffer, ptr, n)`, and pass it to `writeBuffer` with no copy. The view breaks
when the memory grows, so JS must use it before the next call. Lean `FloatArray` holds doubles, so
Float32 needs a pack step. Components cannot do this: they copy.

Between units there is no ABI question: a unit call is a wasm call with Lean objects.

## 5. Other targets

| Target | Post-pass | Units | Tested |
|---|---|---|---|
| wasm, browser and Node | yes | `wasm-split` | yes |
| Native C | yes | one link for each manifest root set | arm64: 186 to 213 M to 0.4 to 1.6 M at start, identical hashes |
| rv32, ESP32-P4 | yes, it is plain C | one static link; flash holds it all, so laziness is the gain | no: no toolchain, no board |
| WASI component | yes, same C | a component for each coarse boundary | no: not combined yet |
| F\*/KaRaMeL C, JS | no: not Lean output | manifest entries still apply | no |

For rv32, start memory matters more than bytes: 1.4 MB against 6.5 MB of 32 MB. Reach gives a size
guide: `web_render_call` is 1.96 MB code and 0.19 MB data in wasm. wasm32 shows that 32-bit and no
GMP work; GMP is absent from the wasm runtime and present in native. The pass does nothing about
64-bit floats.

## 6. Architecture

```
deploy/units/<engine>.json      entries, gates, which call needs which unit, budgets
   |
lean-c-shake.py  ---> C, for all targets
   |
cached compile, one link with relocations (-O1)
   |
plan-units.mjs   ---> function to unit; refuses a missing gate or a gate that is an export
   |
wasm-split, wasm-opt each part, strip  --->  primary.wasm, <unit>.wasm, glue
   |
units.json       ---> sizes, sha256, which call needs which unit
   |
unit-loader.mjs, check-units.mjs (byte equality against the shipped form)
```

A unit in `deploy/units/web-render.json`:

```json
"xslt": { "gate": ["l_WebXslt_transform"], "needed-by": [{ "export": "web_document_call", "op": "xslt" }] }
```

A gate is a function where the primary stops. The unit is the closure of its gates less what the
primary reaches. What two units share moves to the primary. A gate needs no Lean change, so a
dispatch arm can be a gate.

**Proved by the prototype.** One added line, `"rdf": {"gate": ["web_render_rdf_compile"]}`, gave a
third unit with no compile: primary 4,106,913 B, `rdf` 106,524 B (22,045 gzip), 3 shared functions
moved to the primary, 31 of 31 identical. Build time from cached objects: about 1 minute. The build
is deterministic: two runs gave the same sizes and hashes.

`units.json` fits the npm code. `browser-engine.mjs` already has the `instantiateWasm` hook,
`engine-integrity.mjs` already checks sha256, and `lib/lean-entry.mjs` already has a refusal for ops
that the core engine lacks.

## Limits

- Not tested: Firefox, Deno, a phone, any rv32 toolchain or board, the post-pass with wasi-sdk, and a
  browser with variant (b). Chrome's times were virtual time, so only Safari's are real:
  98 ms load, 92 ms render, 121 ms unit, 64 ms XSLT (local server).
- The full engine was linked and graphed, but not split and not run. No gate list exists for it.
- Rows marked older objects were not repeated on main. The shape is the same.
- All data stays in the primary: 1.27 MB belongs to the `xslt` unit. Moving it is a next step, and it
  needs an address-preserving post-pass.
- Glue comes from the `-O1` link: 46 KB gzip, not 27 KB. Taking it from an `-O2` link is not tried.
- A unit cannot be unloaded.
- Not tried: a build-time heap snapshot (Wizer style). First XSLT use still pays for its tables.
- Wasm instruction counts were not measured; wasm times are wall time, so small differences mean nothing.

## Reproduce

```bash
labs/demos/foafnaut/build-web-render.sh --source-only
EM_CACHE=<copy of the emscripten cache> tools/deploy/build-units.py deploy/units/web-render.json \
  --build labs/demos/foafnaut/.build/web-render --runtime <l4wasm-work> --out <dir> --jobs 4
node tools/deploy/web-render-corpus.mjs <shipped engine>.mjs > base.json
node tools/deploy/check-units.mjs <dir>/dist <dir>/dist/web-render.mjs --no-sync --expect base.json
```

The `shake` and `compile` steps took 11 s and 205 s; a cold full run is about 5 minutes.
