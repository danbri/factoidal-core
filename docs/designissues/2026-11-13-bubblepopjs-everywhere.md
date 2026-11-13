# BubblePopJS everywhere; QuickJS-NG as a marked exception

Date: 2026-11-13. Branch `wip/bp-default`.

## Decision

BubblePopJS, the JavaScript engine written in Lean (`formal/lean4/L4Factoidal/JS/`), is the page
script engine of every build of BubblePopKit and every browser on it: the macOS window, the native
libraries for macOS, Linux and Windows, the Wasm build, the Hub, Textnaut, the command line tools and
the test and score runners. It is where the work on security, speed and conformance goes.

QuickJS-NG, compiled to WebAssembly and run in WasmVM, stays for two uses only: differential tests
against BubblePopJS, and the guest API (the WasmVM host imports that both engines share). It runs only
when it is asked for by name. Using it is an unusual exception, and each place that chooses it says so.

## What changed

- `WebRenderScript.defaultEngine` is `"bubblepop"` for every host. Before, `"hub"` and `"wasm"` gave
  `"quickjs"` (no host asked for them any more, since the Hub and the desktop both asked as `"native"`).
- `scriptSession` `start` with no `engine` runs BubblePopJS. `engine:"quickjs"` runs QuickJS-NG; any other
  value is refused. Before, no `engine` meant QuickJS-NG. `info` lists `engines` with `bubblepop` first,
  `engine:"BubblePopJS"` and `default:"bubblepop"`.
- The hosts (`run_html.ts`, `docs/web/hub/foafnaut/browser-worker.mjs`) send `engine:plan.engine`, the
  engine of Lean's plan, always. An explicit name works on engines from before and after this change.
- An engine too old to answer `scriptPlan` gets no page scripts, with a notice ("Page scripts are off:
  this engine is too old to choose a script engine"). Before, both hosts then ran QuickJS-NG silently.
- The desktop window reads the QuickJS-NG guest file only when the setting names `quickjs` (or the
  engine has no BubblePopJS). Before, it read and loaded the guest at every start.
- Tests and benches choose by `SCRIPT_ENGINE` / `--script-engine`, default BubblePopJS; `quickjs` runs
  the same checks on QuickJS-NG. The QuickJS-NG runs in `labs/demos/foafnaut/test.sh` set
  `SCRIPT_ENGINE=quickjs`. `tests/crypto/webcrypto_engine.ts` defaulted to QuickJS-NG; it now defaults to
  BubblePopJS.

## The check

`tools/quickjs-exception-check.py` fails when a tracked code file chooses QuickJS-NG (the quoted engine
id `quickjs`, `SCRIPT_ENGINE=quickjs`, `--script-engine quickjs`, `--quickjs-wasm`,
`--script-setting quickjs`) and has no `QUICKJS-EXCEPTION` comment. It runs in `test.sh` and in
`verify-lean4.yml`. It is per file: a second choice in a file that already has a marker is not caught.
The QuickJS-NG implementation itself (`tools/wasmvm/quickjs/`, `tools/wasmvm/build-quickjs.sh`,
`WasmVM/Bench/`, the older lab server's `web-render/script-engine/`, `tests/browser-wpt/quickjs-probe.mjs`)
is out of scope: it is QuickJS-NG, not a choice of it.

## The exceptions (`git grep QUICKJS-EXCEPTION`)

| Where | Why |
|---|---|
| `WebRenderScript.engines`, `WebScripts` `start`, `WebState.Settings.scripts` | the named `quickjs` setting and request field: differential runs, the guest API; a saved user choice is kept |
| `WebRenderScriptTests.lean` | guards that the named QuickJS-NG choice still works |
| `run_html.ts` (guest load) | reads the guest only for the named setting |
| `browser-worker.mjs` (engines of an old engine) | an engine older than the `engines` list had QuickJS-NG only; it still runs only by name |
| `native_html_scripts_test.ts`, `native_html_pointer_test.ts`, `page_gpu_test.ts`, `shader_gallery_test.ts`, `canvas2d_test.ts`, `dom_breadth_test.ts`, `bubblepop_pages_test.ts`, `native_liberal_test.ts`, `script_reads_holds_test.ts`, `test.sh` | differential tests: the same checks on both engines |
| `bubblepop_bench.ts`, `shader_gallery_bench.ts`, `wasm/check_bench.ts`, `hub_scripts_speed.mjs`, `hub_page_gpu_check.mjs` | speed comparisons with BubblePopJS |
| `tests/browser-wpt/testharness-run.ts`, `tests/crypto/webcrypto_engine.ts` | `--script-engine quickjs` for differential WPT and Web Crypto runs |
| `npm/factoidal/bin/foafnaut.mjs` | `--quickjs-wasm` passes a guest through for the named setting |
| `tools/package-web-render.py` | the older lab web-render development bundle has no BubblePopJS path (not Foafnaut) |

Shipping the guest is allowed where an explicit QuickJS-NG option exists: the Hub deploy puts
`docs/web/hub/wasm-guests/qjs-wasmvm.wasm` beside the engine (`factoidal-builds`, `build.yml`, "Build the
WasmVM guest modules"), and the Hub loads it only when the setting is `quickjs`.

## Builds and packaging, checked 2026-11-13

- `build-web-render.sh` (native and Wasm): builds BubblePopKit with BubblePopJS; it reads
  `tools/wasmvm/quickjs/prelude.js`, which is the shared page prelude of both engines (the name is
  historical), not the QuickJS-NG guest.
- `build-executables.sh`, the single-file app: the window (`run_html.ts`) defaults to BubblePopJS.
- Textnaut: BubblePopJS only (`engine:"bubblepop"`); no QuickJS-NG path.
- `factoidal-builds` (read, not changed): `wpt-score-job.py` needs `--script-engine` given; the nightly
  `wpt-score.yml` matrix runs both `bubblepop` and `quickjs` (the second is a differential run and
  should be named so in its summary; a change there is for the owner of that repository).
  `build.yml` builds the guest for the Hub deploy (above).

## Open

- The marker check is per file, not per choice.
- The older lab web-render server and its npm development bundle run page scripts in a host-run
  QuickJS WASI reactor. It is not Foafnaut; retiring it or moving it to BubblePopJS is separate work.
