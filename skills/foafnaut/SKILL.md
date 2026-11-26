---
name: foafnaut
description: Contribute to Foafnaut, the web browser with its own rendering engine (labs/demos/foafnaut, formal/lean4/L4Factoidal/Rendering, docs/web/hub/foafnaut). The code map (window, worker, engines, page generator, Hub host, Lean modules, page script engines BubblePopJS and QuickJS-NG in WasmVM, the text terminal front end Textnaut), what the owner says Foafnaut is and where each part is in the tree, how to build, test, run and measure (on the Mac, and the engine and BubblePopJS on a Linux cloud machine), the shared-machine rules (coordination log, one Lean build at a time, disk limits), the traps that cost time, and how to land work. Use before any Foafnaut change, build, sweep, Hub deploy or status report.
---

# Foafnaut

Foafnaut is a web browser. Its engine parses HTML, computes CSS, lays out text and boxes,
and makes the GPU commands. The engine is written in Lean 4. It runs in a macOS window
and on the Hub (https://danbri.github.io/factoidal/web/hub/foafnaut/). "foafnaut2525" is
the name of the engine in the status note, the release records and older files.

Names for new text and docs: **Foafnaut** is the browser and **Textnaut** the text-mode browser. **BubblePopKit** is
the rendering engine as a whole, by analogy with WebKit: every build of it (macOS and Linux native libraries, Wasm
binaries). Browsers built on it: Foafnaut, Textnaut and the WWW harness (the Hub page). **BubblePopJS** its JavaScript engine, and **BubblePopWASM** its WebAssembly engine
(WasmVM), which runs Wasm modules. BubblePopWASM is not a build: BubblePopKit compiled to Wasm is the Wasm build of
BubblePopKit. Code identifiers keep their existing names.

State at the last handoff, what is in flight, and what to do next:
[docs/designissues/2026-11-09-foafnaut-handoff.md](../../docs/designissues/2026-11-09-foafnaut-handoff.md).
This skill changes slowly. The handoff record goes stale first: check it against
`git log origin/main` and the coordination log (below).

Agents: read [AGENT-BRIEF.md](AGENT-BRIEF.md) first; it is the standard brief.

Every command here was read from the scripts at commit `6f08a9824` (2026-11-09). When a
command and a script disagree, the script is correct. Fix this file.

## What Foafnaut is (owner, 2026-11-09)

Owner, 2026-11-09, verbatim, to a cloud session: "In the last ~10 days we have (using Lean)
implemented some SVG on top of our XML stack and created a brand new browser, with builds
including native OSX, and a wasm web-based version exposed in Factoidal hub. It is called
FOAFNaut, and will touch on ideas explored 20 years ago under that name." "We have
whatwg-based html parsing, an. Implementation of web assembly that permits us to safely run
some legacy code when needed, our own new JS engine called BubblePopJS, font rendering, html
layout, css, networking, tls and much more. We have beginnings of protocol support for chrome
debugger, headless control and mcp. Also a text terminal frontend, Textnaut. The goal is to be
competitive as a real browser, measured against the official Web Platform Tests, and to be
efficient, performant, fast, private, accessible, international, and secure."

Rules from it:

- The measure of the browser is the Web Platform Tests (`tests/browser-wpt/`; batch 2 KR 1.1),
  measured by full runs as [`wpt-runs`](../wpt-runs/SKILL.md) sets out: every name run, never a
  sample, on BubblePopJS, quoted with and without `encoding/`. A score needs its suite,
  denominator, engine commit, WPT commit and date.
- Real pages next to the number: [`realpages-survey`](../realpages-survey/SKILL.md) measures everyday
  pages live on each release (speed, memory, crashes, layout against Chrome) and keeps the trend.
- Seven qualities have equal standing with standards: efficient, performant, fast, private,
  accessible, international, secure. A change that helps one and harms another says so.
- Factoidal's first product line (the W3C data standards in `@factoidal/core`) continues. The
  browser is built on the same Lean tree (XML, URL, encodings, RDF, SPARQL, XSLT).

Where each part is in the tree. Checked on `origin/main` at `489d5cd3a` (2026-11-09, 22:41
UTC) by file name and by text search. "Not found" means the search found no file on `main` or,
by file name, on the `wip/` branches that were on origin at that time; the work may be in a
local clone that is not pushed. Check again before you write that a part is missing.

- HTML parsing after the WHATWG standard: `formal/lean4/L4Factoidal/HTML/` (`Tokenizer`,
  `TreeBuilder`), DOM in `L4Factoidal/DOM/`; URL and encodings in `L4Factoidal/WHATWG/`.
- SVG over the XML stack: `labs/demos/foafnaut/SVG*.lean`, `L4Factoidal/XML/`.
- BubblePopWASM, the WebAssembly engine (it runs QuickJS-NG and other guests in a sandbox):
  `L4Factoidal/WasmVM/`.
- BubblePopJS: `L4Factoidal/JS/`; its page host `L4Factoidal/WasmVM/Hosts/LeanJS.lean`; its
  command line `lake exe leanjs` (`run FILE`, `eval SRC`, `test262 ROOT DIR...`, `bench`).
- Fonts: `L4Factoidal/Rendering/Sfnt*.lean`, `FontPolicy`, `FontProvider`; fonts in
  `third_party/fonts/`.
- Layout and CSS: `L4Factoidal/Rendering/Style.lean`, `Layout.lean`, `TableLayout.lean`.
- Networking: the desktop host loads pages with the host's `fetch`
  (`labs/demos/foafnaut/native_html_document.ts`), so TLS is the host's (Deno). Page scripts
  have no network access yet: https://github.com/danbri/factoidal-core/issues/374 (`fetch`,
  `XMLHttpRequest`, CORS in the engine). Record and replay proxy: `tools/devproxy/`. HTTP
  code of the library: `L4Factoidal/HTTP/`, `L4Factoidal/Net/`.
- A TLS implementation in BubblePopKit: not found.
- Chrome debugger protocol, headless control, MCP served by the browser: not found. The
  `labs/demos/foafnaut/hub_*_check.mjs` files use the Chrome debugger protocol as a client, to
  drive headless Chrome against the Hub: that is test tooling. The WPT runner on
  `wip/wptserve` classifies WebDriver tests. The work is tracked in
  https://github.com/danbri/factoidal-core/issues/372 (developer tools: console input, an MCP
  server for agents, WebDriver BiDi, Chrome DevTools Protocol). MCP for the data tools is
  https://github.com/danbri/factoidal/issues/1121 (MCP over XMPP, and MCP controls for the
  command line tools).
- Textnaut, the browser in a text terminal: `labs/demos/foafnaut/textnaut/` (`README.md`,
  `TUI-CATALOGUE.md`, the launcher `textnaut`). On Linux it runs on the native engine:
  `foafnaut-linux.yml` releases a self-contained `libweb-render.so` (Lean runtime linked in, with
  initial-exec TLS, by `build-leanrt-no-gmp.sh`; the build fails if it needs more than libc),
  `textnaut --install-native` installs it, and `textnaut-native.yml` (builds) checks it against
  the Wasm engine on a runner with no Lean (`textnaut/engine_parity.py`).
- Names, parts and the state of each build: `labs/demos/foafnaut/README.md`, "Names and parts".
- macOS app and window: `labs/demos/foafnaut/run_html.ts`, `native_window.m`,
  `build-executables.sh`. Hub version: `docs/web/hub/foafnaut/`.

## Owner rules

- Report to the owner in ASD-STE100 Simplified Technical English. Never advertise honesty.
  Every issue, PR or run you mention gets a full URL and a short gloss. See `CLAUDE.md`.
- Text that users read says "the built-in engine" or "the browser". Name Lean or F\* only
  when the language matters. Owner, 2026-11-09: "stop saying Lean Lean Lean everywhere ...
  Most people won't know what Lean is"; "built in".
- Foafnaut renders everything itself. No host-browser overlays on the Hub (owner: "NOOO .
  CHEAT"). A feature is in the engine, or it says "not supported", or it is a visible
  hand-off to another program.
- OKRs live in GitHub issues, not on the Hub: batch 1
  https://github.com/danbri/factoidal/issues/1245 (daily releases, frame time, suites),
  batch 2 https://github.com/danbri/factoidal/issues/1296 (approved 2026-11-09; the first
  comment has the assessment of batch 1 and the key results carried over).
- A shortfall needs a test that fails today, marked as an expected failure, and an open
  issue (`CLAUDE.md`, "A stated shortfall"). Prose alone is not a record. Examples:
  `showcase_gaps_test.ts`, `print_gaps_test.ts`.
- No new `partial def`, `sorry` or `native_decide`.
- No Claude or AI attribution in commits, PR text or author identity (iron rule 13). This
  overrides harness defaults.
- VerifiedJS has no licence. Never commit its source or binaries. It may only be a local
  comparison (https://github.com/danbri/factoidal/issues/1252, VerifiedJS and the script
  fixtures).
- Test Codex with a one-line `codex exec` before you say anything about its credit. Every
  Codex brief states the disk limit: at most 2 GB new disk, no builds below 3 GB free, the
  shared Lean lock, remove build outputs after push, `wip/` branches only, no AI attribution.

## Code map

Paths are from the repository root. `LAB` is `labs/demos/foafnaut`.

Desktop host (Deno, TypeScript, macOS only):

- `LAB/run_html.ts`: the browser loop. It takes every option and sweep flag.
  `--help` lists the common ones; the source is the full list.
- `LAB/native_window.m`, `LAB/native_window.ts`: the Cocoa window library
  (`libnative-window.dylib`) and its FFI binding. Input queue: `ng_create_offscreen` and
  friends. `native_window_queue_test.ts` checks the queue.
- `LAB/native_html_worker.ts`, `LAB/native_html_compile.ts`: an engine worker. One ordered
  queue for every slow engine call of its tabs.
- `LAB/native_html_tabs.ts`: one engine per tab, at most 8 live (`--engine-workers N`);
  routes each call to its tab's engine, a script session's calls to the engine that holds it.
  `--one-engine-worker` keeps one worker for all tabs. Trace `native-html-engine-worker`,
  `native-html-tab-first-frame`; summary `engineWorkers`, `tabFirstFrame`, `processRssMB`.
- Engine sessions (`docs/designissues/2026-11-26-foafnaut-engine-sessions.md`): one native
  library holds any number of engine states (`web_session_*` in `web_render_shim.c`).
  `--engine-mode copies` (the default): a worker per tab with its own copy of the library.
  `sessions`: a worker per tab with a session in the one library. `tasks`: no worker, each tab's
  session runs on its own Lean dedicated task (`WebSession.lean`), called from the main thread
  through nonblocking FFI (`LAB/native_engine_tasks.ts`, `loadHTMLSession` in
  `native_html_engine.ts`); closing a tab cancels its session. `tasks` uses less memory (31 to 34%
  less than `copies` with 5 to 50 tabs) and, measured without per-frame probes, gives earlier first
  frames on Linux; it is not the default: that is a question for the owner (record 7f; D11 rested on
  numbers with the probes). Tests: `engine_sessions_test.ts`;
  measurement: `LAB/tools/engine_sessions_bench.py` (Linux rig). The remote engine calls are
  written once over a kernel (`remoteMethods`), for the engine on this thread and the session.
  `pooled` (a prototype, record section 7): the sessions of `tasks`, served by one or two host
  workers (`--host-workers 1|2`, `LAB/native_engine_pool.ts`) that make the requests and read
  the answers; the main thread keeps each tab's lanes (`laneClient`, `native_engine_tasks.ts`).
- Tabs not shown (`--hidden-tabs`, record section 7): `stopped` (the default) gives their pages
  no timer turn; `throttled` at most one a second; `running` as the shown page (a load for
  measurement). With the last two a hidden page's canvas commands are held and replayed when its
  tab is shown, coalesced by rectangle. Summary `hiddenTabs`.
- Steady state with many tabs: `engine_sessions_bench.py --scenario steady5|steady20|steady50`
  (configurations take more host flags: `NAME=LAB:ENGINE:MODE:--hidden-tabs=running`), read with
  `LAB/tools/engine_sessions_report.py`. Where the CPU of a window went: `perf record -k
  CLOCK_REALTIME` and `LAB/tools/perf_window_report.py` (the steps start with `mark`). On this
  VM `/usr/bin/perf` fails for its kernel: use `/usr/lib/linux-tools-6.8.0-151/perf` with `-e
  cpu-clock`. Whether a WebGPU device can go to another worker: `LAB/tools/webgpu_share_check.ts`.
- `LAB/native_html_engine.ts`, `LAB/native_html_document.ts`: engine ABI and page loading.
- `LAB/native_html_session.ts`, `LAB/layer_compositor.ts`, `LAB/scroll_prefetch.ts`,
  `LAB/gpu_transport.ts`, `LAB/render_plan.ts`: GPU. The two-layer scroll and the prefetch
  rule are in the frame pipeline record.
- `LAB/native_state.ts` (bookmarks, history, settings through LWS), `LAB/native_console.ts`,
  `LAB/native_print.ts`, `LAB/native_html_fonts.ts`.

Engine in the lab, Lean modules at the top of `LAB`:

- `WebDocument.lean` (document ops, layout, two-layer answers), `WebRender.lean`,
  `WebRenderSVG.lean`, `WebShell.lean` (browser chrome), `WebRoute.lean` (where a link goes),
  `WebHit.lean`, `WebHistory.lean`, `WebGesture.lean`, `WebSelection.lean`, `WebRepaint.lean`
  (hover and `:active` with no layout), `WebAccept.lean` (liberal mode), `WebConsole.lean`,
  `WebPrint.lean`, `WebState.lean`, `WebSparql.lean`, `WebXslt.lean`, `WebWasm.lean`,
  `WebGraph.lean`, `WebEventLoop.lean`.
- `WebRenderScript.lean` chooses the page script engine (`defaultEngine`).
  `WebScripts.lean` runs page scripts.
- `SVG*.lean`, `Image*.lean`, `RenderPlan.lean`, `Font.lean`, `Graphics.lean`.
- `web_render_shim.c` is the C ABI of the engine: engine sessions (`web_session_new`,
  `web_session_new_task`, `web_session_cancel`, `web_session_free`) and the calls on them; the
  calls with no session use a default session. `WebSession.lean` is a session on a Lean task.

Engine in the library, under `formal/lean4/L4Factoidal/`:

- `Rendering/` (style, layout, tables, scene, fonts, `Sfnt*` shaping, `FontPolicy`,
  `MediaQuery`, `ComputedValues`, `CssSupports`), `HTML/`, `DOM/`, `FrameCost/`,
  `PageCanvas/`, `PageGpu/`.
- `JS/`: BubblePopJS, the JavaScript engine written in Lean.
- `WasmVM/`: the WebAssembly engine written in Lean. `WasmVM/Hosts/` connects page scripts:
  `Page.lean`, `PageEvents.lean`, `PageWasm.lean`, `PageAot.lean`, `Dom.lean`, `DomOps.lean`,
  `WebApi.lean`, and `LeanJS.lean` + `LeanJSRealm.lean` for BubblePopJS.

Page scripts run in the engine. No host JavaScript engine runs a page script.
`WebRenderScript.defaultEngine` gives BubblePopJS for every host (`defaultEngine_eq`); QuickJS-NG
in WasmVM runs a page only when the setting names it. The QuickJS-NG guest is `tools/wasmvm/build-quickjs.sh` with
`tools/wasmvm/quickjs/prelude.js`. BubblePopJS uses the same prelude.

Hub host, `docs/web/hub/foafnaut/`:

- `index.njk` (the page), `browser.mjs` (page thread: forwards input, shows frames),
  `browser-worker.mjs` (the browser loop, the counterpart of `run_html.ts`), `layers.mjs`
  (two-layer view), `page-gpu.mjs`, `browser-state.mjs`, `link-route.mjs`, `font-coverage.mjs`.
  `fallback-fonts.mjs` is generated by `LAB/fallback_fonts.py`.
- At deploy the workflow puts the engine in `docs/web/hub/html-webgpu/runtime/` and the
  QuickJS guest in `docs/web/hub/wasm-guests/qjs-wasmvm.wasm`. Neither is in git.
  Both come from one `factoidal-builds` release (`tools/fetch-builds.sh --set foafnaut-web`).

Pages and generators (do not edit generated files by hand):

- `LAB/pages/`: demo pages and `manifest.json`. `LAB/pages/README.md` gives the rules.
- `tools/build-demo-pages.py` writes the pages from `source/`, writes `index.html` from
  `START`, `GROUPS` and `BLURBS` in that script, and writes `feed.xml` from the Foafnaut
  notes. `--check` is in `test.sh`.
- `tools/status-to-html.py` makes the status page from `docs/web/hub/foafnaut2525-status.md`.
- `LAB/tools/showcase-pages.mjs` writes pages with a `generator` in the manifest.
  `LAB/tools/combination-pages.py` and `LAB/tools/image-pages.py` write the others that say so.

Other programs in `LAB`, older than the browser: `run_ui.ts` (springs, layout, vectors, the
FOAF graph as a window), `run_lean.ts`, `run_svg.ts`, `web-render/server.mjs` (a local lab
server with its own QuickJS worker path), `browser-webgpu/`. `LAB/README.md` covers them.

## Build

Toolchain pins: `LAB/toolchain-versions.env`. `test.sh` and `build-executables.sh` stop
unless `deno --version` equals the pin. Run each `bash` line below from `LAB`.

Lean builds on the shared machine go through the lock. See "Shared machine" first.

```sh
bash build-engines.sh --runtime-cache <dir>        # .build/engines/ (render-plan and others)
bash build-web-render.sh --native                  # .build/web-render/web-render-native, engines/libweb-render.dylib
FACTOIDAL_WASM_RUNTIME_CACHE=<cache>/l4wasm-cache/l4wasm-work bash build-web-render.sh --wasm
```

- `--wasm` with no `FACTOIDAL_WASM_RUNTIME_CACHE` stops with a message.
- `build-web-render.sh` refuses with less than 3 GiB free, and refuses when its own
  `.build/web-render/lock` exists.
- Native and Wasm can not share a build tree in parallel because of that lock.

After a Wasm build, for direct runs of `run_html.ts` or `sweeps.sh`:

```sh
mkdir -p .build/native-html/runtime && cp .build/web-render/engines/web-render.{mjs,wasm} .build/native-html/runtime/
```

(`test.sh` and `build-executables.sh` make this copy too.)

The window library is separate. On a clean checkout `test.sh` skips everything that needs
it, so build it first:

```sh
mkdir -p .build/native && xcrun clang -dynamiclib -fobjc-arc -O2 -Wall -Wextra -Werror -framework Cocoa -framework QuartzCore -Wl,-install_name,@rpath/libnative-window.dylib native_window.m -o .build/native/libnative-window.dylib
```

The local QuickJS guest. A stale guest makes page-script tests fail ("no canvas command",
`getContext` missing):

```sh
EMCC=$(command -v emcc) bash tools/wasmvm/build-quickjs.sh ~/working/qjs-wasm   # from the repository root
```

`test.sh` reads `$QUICKJS_WASM`, then `~/working/qjs-wasm/qjs-wasmvm.wasm`, then
`docs/web/hub/wasm-guests/qjs-wasmvm.wasm`.

The app: `bash labs/demos/foafnaut/build-executables.sh <outdir>` from the repository root.
It runs `build-engines.sh --source-only` (a Lean build, so it needs the lock) and
`test.sh --skip-build`, compiles the window program with `deno compile --include` (so an
app has the pages of its build commit), starts the compiled program for one off-screen
graph sweep, and writes `BUILD-INFO.json` (commit, dirty flag, build time). With no
`web-render.wasm` the package has no browser window, and the script says so.

## Test

```sh
bash test.sh --skip-build
bash sweeps.sh [--only NAME]... [--wasm-only]
```

- `test.sh` runs every check, even after one fails, and ends with a summary: each check, its
  time, and the failed ones (exit 1 if any failed). `--fail-fast` (or `FOAFNAUT_FAIL_FAST=1`)
  stops at the first failure.
- Read every `NOT RUN` line. `test.sh` exits 0 with `NOT RUN` lines. A `NOT RUN` is a
  check that did not happen. Do not report it as a pass.
- `sweeps.sh` runs each sweep of `run_html.ts` with `--offscreen`: a hidden window, the
  real event queue, frames into a GPU texture. It works with the screen locked. Exit code 4
  from a sweep means the engine is older than the sweep.
- Latency printed by `sweeps.sh` includes a pixel check of every frame, which adds 100 ms
  or more. For input latency, run the sweep directly with `--idle-checks-only`.
- CI does less than a local run. In `danbri/factoidal-builds` (`.github/workflows/build.yml`,
  `scripts/build-foafnaut.sh`) the `test.sh` step runs before the window library exists and
  with no QuickJS guest. The run of 2026-11-09
  https://github.com/danbri/factoidal-builds/actions/runs/42620085179 (build of the
  foafnaut job) printed `NOT RUN` for the sweeps, `native_window_queue_test.ts`,
  `native_html_scripts_test.ts` and `print_document_check.ts`. The only sweep in CI is the
  start check of `build-executables.sh`. Run `test.sh` and `sweeps.sh` locally before you land an
  engine or window change.
- `build.yml` also runs `test.sh --skip-build` in the job `foafnaut-host-tests` (Linux) as soon as
  `foafnaut-engines` is done, on its Wasm engines: about 35 minutes after dispatch, not after the
  macOS bundle. Checks that need `web-render-native`, `libweb-render.dylib` or macOS
  print `NOT RUN` there and still run in the macOS bundle job. Jobs, caches, cold builds and the
  per-run timing record: [`ci-caching.md`](ci-caching.md).
- Hub checks, from the repository root, Chrome needed: `node labs/demos/foafnaut/hub_links_check.mjs`
  (before every Pages deploy; `--only published`, `--runtime DIR`), and the other
  `LAB/hub_*_check.mjs` files. See `docs/web/hub/README.md`.
- Suite scores (`tests/browser-wpt/`, W3C SVG, html5lib, HarfBuzz): `LAB/releases/` holds the
  scored record of each named release, written by `tools/foafnaut-scoreboard.py`. A score
  needs its suite, denominator and date. Do not copy one from an old note without those.

## Run and measure

From source, from `LAB` (the flags are the ones `sweeps.sh` uses):

```sh
deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi -A \
  run_html.ts --html pages/index.html --native-engine .build/web-render/engines/libweb-render.dylib
```

Use `--wasm-engine` for the Wasm engine. `--be-liberal-in-what-we-accept` draws a page and lists
what was skipped; `WebAccept.Skip` is the list. Strict is the default at `6f08a9824`.

The launcher `npm/factoidal/bin/foafnaut.mjs` (installed at `~/.local/bin/foafnaut`):
plain `foafnaut` starts the installed build (`~/.foafnaut/current`, no network use);
`--update` (old name `--install-latest`) installs the newest macOS build of main and says what it
replaced; `--latest` updates, then starts; `--bleeding-edge` starts the local build and prints its
commit and age; `--which` shows what runs, the newest build of main and how far behind, and the local
build. `~/.foafnaut/config.json` key `bleedingEdge` gives the local app path. The lookup
(`bin/foafnaut-releases.mjs`, copied as Textnaut's `lib/releases.mjs`) reads every page of the
release list, then asks `danbri/factoidal-core`'s compare API which candidates are on main and picks
the one nearest main's head; branch builds are skipped. The lane pointer
`latest/darwin-status.json` (`mac_release`) is only a fallback: it can lag the newest release.

Measuring:

- `--perf-summary`: frame and input latency when the run ends.
- `--idle-checks-only`: the normal-use pixel-check rule in a sweep.
- `--single-frame`: the path before two-layer scroll, for comparison.
- Idle loop: with nothing to draw and nothing in flight for 200 ms, `run_html.ts` waits in the
  window library (`ng_wait_event`) for the next event, up to the next deadline and 100 ms at
  most, instead of an 8 ms poll. `--poll-idle` keeps the poll, for comparison. The perf summary's
  `idle` field counts it; `idle_loop_check.ts` (test.sh) holds the wakeups per second against
  the `window` section of `fixtures/spinal-bisect/budgets.json`. New async work in the loop must
  be counted in its `busy` test, or it waits up to 100 ms after an idle wait.
  Inside those 200 ms the loop waits only for the page's own next timer, for at most 34 ms
  (`TIMER_WAIT_CAP_MS`): a page with a 16 ms timer is never quiet, and pumped between its turns.
- Engine op `frameWork`: counts layouts, kept layouts used, repaints on a kept layout,
  `pagesMade` and `pagesKept`.
  `frame_work_test.ts` and `frame_cost_test.ts` hold the ratchets; the model is
  `formal/lean4/L4Factoidal/FrameCost/`.
- Profiling: macOS `sample` against a Deno loop over `engine.compileLayers`. No script for
  this is in the repository.
- A real page as a budgeted test: the Spinal Tap page (issue 450). `spinal_perf.ts` loads it on
  the native engine, lays it out, runs 600 animation ticks and writes JSON (per tick: engine ms,
  `frameWork` deltas, whole-page or paint-only, RSS, heap); `spinal_perf_check.ts` (in `test.sh`,
  about 15 s) checks it against `fixtures/spinal-perf/budgets.json`, which may only tighten, and
  prints the known failures. `node hub_spinal_perf.mjs [--live]` measures the Hub in headless
  Chrome with WebGPU for 45 s (frame path, draw ms, heap, RSS, GPU errors) against the same file.
  Times with the CPU probe (`checks` on, the default of `compile`) are about five times those
  without it on this page: say which one a number is.
- Which features of a page cost what: `spinal_variants.ts` makes about 25 variants of the Spinal
  Tap page at test time (none committed): its DOM after load with no scripts, then one feature
  taken away (SVG, strokes, gradients, the web font, clip, borders, half the DOM, ...) or added
  (shadows, fixed and sticky boxes, a CSS animation, filters, a 16 ms timer, images), down to
  plain text and an empty page. `spinal_bisect.ts` measures each on the native engine (load,
  first and kept frames, the CPU probe, ticks, scroll bands, RSS) and, with `--app DIR`, in the
  desktop browser off screen (first frame, frame and GPU ms, the longest pump gap, the idle
  check, idle CPU %, scroll input latency), and ranks feature against added cost.
  `spinal_bisect_check.ts` (test.sh, about 20 s) is the fast mode against
  `fixtures/spinal-bisect/budgets.json`; `sh spinal_bisect_full.sh` is the full mode (25 to 40
  minutes). Every timed run holds `flock /tmp/foafnaut-timing.lock`.

### Measure BubblePopKit and BubblePopJS with no Mac

A Linux cloud session can build and measure everything that is CPU work: the native build of
BubblePopKit (`web-render-native`) and BubblePopJS (`leanjs`). Record of the first such session,
with every number and command:
[docs/designissues/2026-11-09-foafnaut-perf-exploration.md](../../docs/designissues/2026-11-09-foafnaut-perf-exploration.md).

Since 2026-11-25 it can also run the window and the Deno host from source, under Xvfb with Mesa
software Vulkan and the newest released engine of main:
`tools/foafnaut-linux-rig/setup.sh` (apt packages, the two release sets checked by sha256,
`libnative-window.so` built from this checkout), then
`tools/foafnaut-linux-rig/run.sh --html FILE --scroll-sweep --perf-summary` (use a sweep so the run
exits). Host changes (input, queues, workers, network) are measured as they are. GPU times are
software Vulkan times: do not compare them with a Mac. A Lean engine change needs an engine build
first. Before this, the cost of having no rig: on 2026-11-25 the gesture work of issue 1031 was
pushed with only a type check, because the window could not run here.

A page that animates by script (a canvas game) is paced by its timer turns. `--perf-summary`
prints a "timer turns" line (each `native-html-script` line of cause `timers` has the same
fields): the engine's own time of a turn, `callMs` (the ask to the answer minus the engine's
time: worker messages, FFI, the answer's wire form such as `PageCanvas.rle`) and `waitMs` (the
answer to the next ask). Frame time is about their sum. Example, Particle Rex on the rig,
2026-11-26: engine 32 ms, call 4.5 ms, wait 0.2 ms, 26.7 fps. To split the engine's time by Lean
function, drive the page with no window (a Deno script that calls `scriptSession` with
`action:"advance"`) under `perf record --call-graph dwarf`; the frame-pointer call graph of a
window run does not reach into the Lean library. Issue
https://github.com/danbri/factoidal-core/issues/1098 (Particle Rex frame costs).

```sh
# tools (Ubuntu 24.04): elan and the pinned Lean (skills/session-restore), then
apt-get install -y --no-install-recommends time linux-tools-generic valgrind libc++-dev libc++abi-dev
# (libc++: the native link needs it; without it the build stops at the link, after about 22
# minutes on 4 vCPUs, with "clang++ can not compile against libc++". Seen 2026-11-22.)
# BubblePopJS command line: about 3 minutes on 4 vCPUs. From formal/lean4:
lake build leanjs && .lake/build/bin/leanjs bench
# BubblePopKit, native: 16 to 20 minutes on 4 vCPUs, 1.1 GB of build output. From the repository root:
bash labs/demos/foafnaut/build-web-render.sh --native
```

- One page, timed (font loaded, first compile, then COUNT frames, microseconds each). From
  `labs/demos/foafnaut`, with `REQ` a file that holds
  `{"op":"render","url":"https://example.invalid/","resources":[],"commands":[],"checks":false}`:
  `.build/web-render/web-render-native pages/index.html 1600 1000 --document-bin REQ ../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf OUT.bin 8`.
  With no `"checks":false` each frame also computes the probe pixels (two to three times the time).
- Exact cost by function: `valgrind --tool=callgrind` on that command at COUNT 1 and COUNT 4;
  the difference, divided by 3, is one frame. COUNT 0 is start, font load and first compile.
- That request has no `layers` and no `shell`: it measures the path with no layers, which neither
  host uses for frames. A browser frame is `"layers":true,"binary":true` with a `shell` object (see
  `spinal_perf.ts`). Cost of not saying so: the 249 M instructions of the 2026-11-25 briefing were
  of that path; the browser's frame on a kept layout was 12-15 M (issue 1124).
- Hover, press and scroll-band frames: `--document-bin-seq SEQ.json FONT OUT COUNT` (call `i`
  sends element `i` mod the array's length). `--document-bin-check SEQ.json FONT COUNT` checks the
  page answers kept or patched by `have` against whole answers.
- The native host tests of `test.sh` (64 checks, against 12 without) run on Linux when
  `.build/web-render/engines/libweb-render.dylib` exists and `web-render.wasm` is in that
  directory: `ln -sf libweb-render.so libweb-render.dylib`, and copy `web-render.{mjs,wasm}` from
  `.build/native-html/runtime` (the rig's release). The Wasm engine is then the release, not this
  checkout.
  `perf` on this kind of VM has only `-e cpu-clock` (no hardware counters); the binary is
  `/usr/lib/linux-tools/*/perf`.
- Canvas 2D cost: µs per canvas call and pixel bytes uploaded per frame,
  `labs/demos/foafnaut/canvas_cost_bench.ts` (header has the command); Particle Rex in play on
  the rig with `--steps fixtures/particle-rex-play.json`. How the pixels reach the GPU and what
  each call costs: [docs/designissues/2026-11-26-canvas-upload-and-call-cost.md](../../docs/designissues/2026-11-26-canvas-upload-and-call-cost.md).
- Real-world libraries on each engine (right answer, CPU time, memory), under a memory
  watchdog: `labs/demos/foafnaut/bubblepop_perf/realworld.py`. Run every BubblePopJS test of
  unknown code under a memory limit: `new Array(4294967295)` takes all memory, and on
  2026-11-09 the kernel then killed a build on the same machine.
- A change to `formal/lean4/L4Factoidal/JS/Interp.lean` (above all to the arguments of a
  function of the interpreter's mutual block) is checked with `lake build L4Factoidal.JS.FuelMonoAll`
  as well (from `formal/lean4`; about 20 minutes): the fuel-monotonicity statements name each
  function's arguments, and neither the engine build nor `JS.RegressionTests` imports them. Cost:
  on 2026-11-26 068b8b4b0 gave `callBody` one more argument; the engine built and the tests passed,
  and `FuelMonoIH` on main did not compile for about four hours (repair 861c0f1ad).
- A repaired defect of BubblePopJS gets its scripts in
  `formal/lean4/L4Factoidal/JS/RegressionTests.lean`: `#guard out "<script>" == [lines]`, with
  the lines that QuickJS-NG and Node both print. `lake build L4Factoidal.JS` runs them. When a
  library of `realworld.py` fails, repair and run it again: `marked` had three more defects
  behind the first one (2026-11-10), and the last gave a wrong answer with no error.
- The cost of one JavaScript operation, for each engine, and its instructions, allocations
  and big-number calls: `labs/demos/foafnaut/bubblepop_perf/opcost.py` (its header has the
  commands). Comparison engines: QuickJS-NG `v0.18.0` built natively (`git clone --depth 1
  --branch v0.18.0 https://github.com/quickjs-ng/quickjs`, then `cc -O2 -D_GNU_SOURCE
  -funsigned-char -I. quickjs.c libregexp.c libunicode.c dtoa.c quickjs-libc.c qjs.c
  gen/repl.c gen/standalone.c -lm -lpthread -ldl -o qjs`) and `node --jitless`.
- Number::toString and toFixed, toPrecision, toExponential (Ryū and 64-bit fast paths, exact
  path behind them): `leanjs numfmt-diff N SEED` against the exact reference,
  `tools/ryu-differential.sh LEANJS N SEED [QJS]` against Node (QuickJS-NG is wrong at some
  powers of two), `leanjs numfmt-bench` for the time. Record:
  `docs/designissues/2026-11-25-number-tostring-ryu.md`.
- What BubblePopJS allocates, by constructor shape and by function, its reference-count operations and
  copied bytes, with no Lean build: `labs/demos/foafnaut/bubblepop_perf/alloc/build-count.sh` makes a
  counting `leanjs` from the generated C; `leancount.py` and `opcount.py` read the counts (per run, per
  JavaScript operation); `sampleprof.py` reads a macOS `sample` profile by memory-management class.
  Baseline and method: `docs/bubblepopjs-heap.md`.
- Literals and conversions that the generated C evaluates at each call:
  `python3 tools/lean-literal-parse-audit.py` (a `Nat` literal of 2^32 or more read from text),
  `--float-literals` (a `Float` literal left in a function body, with its case) and
  `--conversions` (`Float.ofNat`, `Float.ofInt`). Its positive control, to run after a
  toolchain change: `python3 tools/test_lean_literal_parse_audit.py`.
- Machine speed differs between cloud machines and from the Mac. Compare engines and builds
  in one run on one machine; never compare a number from here with a number from a record.
- A before and after comparison needs two builds of one base commit. `main` moved 3 times in
  2 hours on 2026-11-09; build the unchanged base in a second worktree (`git worktree add`,
  with a copy of `formal/lean4/.lake` and of `labs/demos/foafnaut/.build` to save the first
  build; delete the stale files of modules that the base does not have), and name the base in
  the report.

Frame costs and design: [docs/designissues/2026-11-07-foafnaut-frame-pipeline.md](../../docs/designissues/2026-11-07-foafnaut-frame-pipeline.md).

## Shared machine

Several sessions work on the owner's laptop at once.

- Coordination log: `/Users/danbri/working/foafnaut/fncg/coordination.log` (with `status.md` beside it; older paths are symlinks).
  Append only. One line, under 500 bytes. Format: `YYYY-MM-DD HH:MM UTC, session, TYPE: text`,
  TYPE one of CLAIM, RELEASE, DONE, NOTE, ASK. Read the CLAIM lines before you touch a
  shared resource (a file another session changes, a build tree, the bleeding-edge app).
- One Lean build at a time, through `leanlock.sh <dir> <command>`. At 2026-11-09 it is at
  `/private/tmp/claude-501/-Users-danbri-working-sandbox-october-tpac-depmap/c7798ecd-041f-428f-92ea-0a6389b033c2/scratchpad/wasmvm/leanlock.sh`.
  That path is temporary and can vanish. The script: each waiter writes a ticket in
  `/tmp/foafnaut-lean-build.queue` named by its arrival time (`0-` first for
  `LEANLOCK_PRIORITY=1`); only the oldest live ticket may take the lock, and only when no
  `lake`, `lean` or `leanc` process runs; the lock is the directory
  `/tmp/foafnaut-lean-build.lock` with an `owner` file; a lock whose owner process is dead
  and with no Lean process running is removed. `LEANLOCK_PRIORITY=1` is only for the
  owner's bleeding-edge build and the one build an approved branch needs just before it
  goes to main.
- Edit `leanlock.sh` only by writing a new copy and `mv` over the old one. Bash reads a
  running script as it goes. An edit in place killed the waiting builds on 2026-11-09.
- Disk: nobody builds below 2.5 GB free. `build-web-render.sh` refuses below 3 GiB. Check
  `df -h /` first. Delete `.lake` and `.wasm-work` from a worktree after pushing
  (`CLAUDE.md`). At 2026-11-09 some sessions' private build wrappers (not in the repository)
  also wait for 5 GB free.
- The bleeding-edge app is in `cache/bleeding/foafnaut`. Build it with `build-executables.sh`
  into a new directory and swap it in only if the build passes. One owner per shared
  resource: read the log for the current owner.
- Releases: `danbri/factoidal-builds` builds them (the `foafnaut` and `foafnaut-engines` jobs of
  `build.yml`). One owner per release (`skills/npm-release/SKILL.md`). A Hub deploy takes the
  engine and the QuickJS guest from one release.

## Traps, each with its cost

- A run with `--steps`, `--resize-sweep` or a sweep that is a list of steps (`--gesture-sweep`,
  `--scroll-sweep`, `--command-sweep` and the others that set `commands`) sets `everyFrame` in
  `run_html.ts` (`--watch-sweep` does not): every frame asks Lean for CPU probes
  (`Scene.checks`, the scene drawn on the CPU at six points). A window in use asks for none in an
  interactive frame (`checks:false`) and for one probe frame once it is idle. So the frame times
  of such a run are not those of the window in use. 2026-11-26, 5 tabs, `tasks`, one run each:
  Lean frame p50 591 ms with the probes, 70 ms with `--idle-checks-only`; new tab first frame
  p50 1,300 and 299 ms. In a profile of a tab's first frame, 95% of the spare engine's samples
  were in `Scene.checks`. The first-frame numbers on which D11 of the engine sessions record was
  decided include the probes. Measure frames of the window in use with `--idle-checks-only`; keep
  the probes for correctness runs.

- A new tab (`showTab`) stops the load in progress in the tab that was shown, and that tab keeps
  its old page. 2026-11-26: the first steady-state trial opened the next tab 2 s after sending
  tab 2 to `particle-rex.html`, which needs about 3.7 s; tab 2 kept the new tab page, so the "load
  in one background tab" ran no script. Let each step wait for a settled frame, and check
  `pagesLoaded` in the bench output.
- In Deno 2.9.4, `structuredClone` or `postMessage` of a `GPUDevice`, `GPUBuffer` or `GPUTexture`
  does not fail: it gives an empty object with no methods. A check that only looks for an error
  reads this as a device that moved. `tools/webgpu_share_check.ts` checks the prototype and a
  call on the copy.
- `--engine-mode copies` loads each engine from a copy of the library and deletes the file, so
  `perf` names none of the engine's functions in those workers (`[unknown]`). Make the script with
  `--show-mmap-events` and give `perf_window_report.py --library` the original.

- `tabFirstFrame` counts only the tabs that drew before the next tab was shown: `run_html.ts`
  times one shown tab (`tabShown`), and a newer tab replaces it. A sweep that opens tabs faster
  than they draw drops the slow ones, so the mode with more slow tabs reports a better p95.
  2026-11-26: the first report of the engine sessions work said "new tab first frame p95 874
  against 984 ms"; with tabs 1 s apart the counted tabs were 27 and 19 of 35. Open tabs far
  enough apart that each one draws (`engine_sessions_bench.py --scenario tabs-spaced`, 3 s), and
  report the count next to the percentiles.
- A native library whose Lean code runs on threads of its own (a task session's dedicated task,
  pool workers with work) must not be unloaded while they run. Deno closes its library handles
  when its runtime ends, and the last `dlclose` unloads the code. 2026-11-26:
  `engine_sessions_test.ts` passed its 8 tests and then ended with a segmentation fault on every
  run (gdb: a session task thread in `lean_dec_ref_cold`, a Deno thread in `_dl_close_worker`).
  `web_session_new_task` now pins the library (`RTLD_NODELETE`; record D12). Read a test's exit
  code, not only its pass count.
- A port check with `ss` passes silently where `ss` is not installed (the cloud container). Check
  a port by connecting to it (`(exec 3<>/dev/tcp/127.0.0.1/PORT)`). C tor relays take up to 30 s
  to exit after SIGTERM, so a chutney network that was just stopped can still hold its ports.
  2026-11-25: `tor-wasm/chutney/run.sh` ran a new network on ports still held by the last one and
  failed after 5 minutes (Tor record, section 12.5).
- While `build-web-render.sh --native` runs, do not run `lake build` and do not edit a Lean file
  that the build has not compiled yet, in `formal/lean4` or in `labs/demos/foafnaut`. The build
  reads `.lake` oleans and the lab sources as it goes, so the library it makes can mix old and
  new code. A Lean file is safe to edit only after `WEB_RENDER_BUILD_RC=` is in its log. Check
  the log before you edit. 2026-11-24, in one session: an edit of `Layout.lean` and then a
  `lake build` of `WasmVM.Hosts` were each made during the Lean stage. Each time, the session
  stopped the build and started it again: about 25 minutes lost each time. No mixed library
  was used for a measurement.
- A proof module that imports `Lean.Elab.*` or `Lean.Meta.*` (tactics, `elab`, `MetaM`) must not be in the
  import closure of an executable or engine. 2026-11-16: `L4Factoidal.JS` imported `JS/FuelMono` (tactics),
  so `leanjs` linked Lean's elaborator and grew from 11 MB to 111 MB unnoticed (issue 551). Make such a
  module a lib root of its own; `tools/binary-budget.py` (premerge, build-web-render.sh, the CI lean job)
  fails on the import, on Lean-library symbols in the binary, and on growth over 2 % of
  `tools/binary-budget.json`.
- A compiled host needs every permission its source uses. 2026-11-08: `deno compile`
  had no `--allow-env`, `run_html.ts` read `HOME`, and the app died at start while all
  source tests passed. Fixed by `--allow-env=HOME` and the start check of
  `build-executables.sh`.
- macOS has no `timeout` unless coreutils is installed. Use
  `perl -e 'alarm shift; exec @ARGV' SECONDS CMD`, as `test.sh` does. `sweeps.sh` still
  calls `timeout`; it will fail on a runner without it (see the handoff).
- Page code must probe engine capability before it uses a new ABI. A Hub page called the
  font export with 5 arguments on a published engine whose export takes 4, and the engine
  aborted; the page fell back to the bitmap font. Fixes `34a00e5a7`, `463c07016`.
- A commit made from an older file blob silently reverts other sessions' work.
  `56fcb3002` removed 935 lines of the Hub worker; `5b79ae85d` reverted it. Check
  `git diff --stat origin/main HEAD` before you push, and push only after
  `git merge-base --is-ancestor origin/main HEAD`.
- Two scripts compile the lab modules, each with its own list: `build-web-render.sh` (the
  browser engine) and `build-engines.sh` (the smaller engines; `CORE_MODULES` and explicit link
  lists). A new `import L4Factoidal...` in a lab module (`SVG.lean`, `Graphics.lean`, ...) must
  be added to `build-engines.sh` too. 2026-11-10: PR 382 added `import L4Factoidal.Prim.FloatOfNat`
  to `SVG.lean` and was checked with `build-web-render.sh --native` only; the `foafnaut-engines`
  job of the build repository then failed on `main` and no Foafnaut release was made for about
  two hours of commits. A cloud VM with no Emscripten can not run `build-engines.sh`: search it
  for the module list by hand, and say in the PR that it was not run.
- Lake does not track `include_str`. `build-web-render.sh` removes the `LeanJS` outputs when
  `prelude.js` is newer. A direct `lake build` does not, and the prelude stays old.
- The GPU commands of the script's start turn must be replayed. The start turn's commands
  were dropped, so every later turn failed and the canvas stayed blank. Fixed by `25ced320b`;
  `test.sh` checks it (webgpu-triangle, webgl-triangle, canvas-chart).
- HiDPI: the Hub scaled text but not CSS pixels. Fix in progress at 2026-11-09 (see the handoff).
- An empty block inside an inline-block is not painted:
  https://github.com/danbri/factoidal-core/issues/369 (the empty block has a size and a background).
- Lean: a new doc comment directly under an existing doc comment is a syntax error. Cost: a
  queued build on 2026-11-09. Module-level `#guard`s run on every build: keep them small.
- In Lean 4.33.1 every `Float.ofNat`, `Float.ofInt` and `Nat.toFloat` call reads the number
  2^53 from decimal text through GMP (45 ns), and a Lean `Int` outside the signed 32-bit range
  is a GMP number. Found 2026-11-09: 359,009 such parses in the font load and first compile of
  the status page (10% of its instructions), and three GMP remainders for one JavaScript `|`.
  A module with a hot conversion or with `Float` literals in hot functions imports
  `L4Factoidal.Prim.FloatOfNat` (the specification is the core function; the fast version is
  proved equal to it; `csimp` puts it in the compiled code). On two builds of `489d5cd3a` the
  first compile of five pages took 12 to 23% less time with it. Rules and the other forms of
  this cost: `skills/lean4-performance`, "Integers through GMP".
- A `Float` literal that the compiler leaves in a function body is converted at each call. With
  an exponent above 22 or a mantissa of 2^53 or more the conversion is big number arithmetic.
  Two finds on 2026-11-09, by two sessions: `1e300` in `WebPaint.cullCurve` was 85% of a frame
  (commit `57fe3531d`), and `9007199254740991.0` in `Number.isSafeInteger` costs 16,800
  instructions a call. `python3 tools/lean-literal-parse-audit.py --float-literals` lists them.
- A Lean definition with no argument is computed when the engine starts, in every program
  that links its module. `LeanJS.snapshotData` runs the whole page prelude at each start (740 M
  of 1,109 M start instructions on Linux at `036198f2`) and only a build tool reads it. The
  branch `wip/bootstack` makes it a function (not on `main` at `489d5cd3a`). Before you add a
  table or a constant that needs real work, give it an argument or measure the start
  (`valgrind --tool=callgrind web-render-native` with no argument; list the `_init_` functions).
- A speed result for BubblePopJS names the branch and commit it was measured on. On 2026-11-09
  `main`, `wip/bpperf` (stage A) and `wip/bpperf-vm` (stage B) took 926, 267 and 81 ms for one
  loop (`for (let ...)` in a function), and six operations are quadratic on `main` only.

## The Hub and other sites

The Hub runs in the visitor's browser, so its reads of other sites obey that browser's
cross-origin rules (CORS). There is no open proxy, and none is to be added: a Hub proxy may only
ever serve URLs matched by an approved allow regex, and none is approved today. A link to another
site never leaves Foafnaut by itself (owner, 2026-11-16). In order
(`docs/web/hub/foafnaut/copies.mjs` `fetchOutside`, `browser-worker.mjs` `outsideGo`):

1. A Hub copy (`labs/demos/foafnaut/realpages/hub-copies.json`; openly licensed pages only,
   snapshots in factoidal-builds `third_party/realpages/*/hub-*.zip`).
2. A direct read the site allows, without credentials. Wikimedia articles
   (`https://LANG[.m].PROJECT.org/wiki/TITLE`) are read from
   `https://LANG.PROJECT.org/api/rest_v1/page/html/TITLE` (`Access-Control-Allow-Origin: *`; its
   `<base>` makes links and images resolve to the real site; `upload.wikimedia.org` and
   `/w/load.php` allow it too). Other sites are tried as they are; on 2026-11-16 W3C TR, WHATWG,
   RFC Editor, peps.python.org, spec.commonmark.org, danluu.com, lite.cnn.com and wttr.in
   allowed it, and Gutenberg, NPR text, Hacker News, MDN, GOV.UK, arXiv, Python docs, SQLite,
   LWN, Rust, Go and Lua did not. An origin that refuses is not asked again in that page.
3. Else the tab shows the "Another site" page; only its "Open in a new browser tab" button calls
   `window.open`. `tests/hub/hub_no_silent_open_test.mjs` and `hub_links_check.mjs` check this.

## Land work

- Branch from `origin/main`: `wip/<issue>-<topic>`. Push after each step that passes.
- Before you push to `main`: `git fetch origin main`, rebase, then
  `git merge-base --is-ancestor origin/main HEAD` and `git diff --stat origin/main HEAD`.
  Touch only the files you meant. Remove `.lake` and `.wasm-work` after the push.
- Page-only change: `tools/hub-quick-ship.sh` (no engine build; it refuses other paths,
  prints the deploy command).

### A/B gate for engine changes (`tools/foafnaut-ab.py`)

Before an engine change goes to `main`, run it against its base commit:
`python3 tools/foafnaut-ab.py gate BASE BRANCH --first /css/css-backgrounds/`, with
`FOAFNAUT_AB_MANIFEST`, `FOAFNAUT_AB_WPT` (the WPT checkout of `skills/wpt-runs`, "Locally")
and `FOAFNAUT_AB_REALPAGES` (factoidal-builds `third_party/realpages`).

- It takes main's library from its factoidal-builds release when there is one (checked by
  sha256), else makes a native build; it builds the branch. It runs the WPT reftests of 9
  directories on both (CSS2, css-lists, css-backgrounds, css-transitions, css-animations,
  cssom, selectors, svg, html), then the real-page snapshots (status, picture hash, time).
  Baseline on main da564916, 2026-11-25: svg 295 pass of 636 (2 min), html 835 of 1,517
  (7 min).
- Libraries and suite results are kept by commit under `~/.cache/foafnaut-ab`, so `main`
  is built and measured once per commit. A gate takes about 1.5 hours on a 4-core cloud
  machine when neither side is kept: about 35 minutes for the two builds, which run at the
  same time, then about 1 hour for the suites.
- The gate passes with 0 tests lost and every page with the same status. Look at each page
  whose picture changed. A lost test that the owner accepts goes in
  `--accept TEST=ISSUE` with the issue that records it.
- When `main` moves before you push: `python3 tools/foafnaut-ab.py overlap BASE NEWMAIN
  BRANCH`. If no file changed on both sides, the result still holds; rebase and push. If a
  file did (`Layout.lean` often), read the new diff, and gate again when the two changes
  can meet.
- Time numbers are wall-clock. Compare them only from runs on a machine where no build runs.

Cost of not having this (2026-11-25): the gate was a set of scripts in one session's `/tmp`,
and a new container deletes them. `main` was built 4 times in one day only because it moved.
PR https://github.com/danbri/factoidal-core/pull/994 went to `main` without a gate and lost 4
css-backgrounds tests (2 fixed in 42fdbc10; the others are
https://github.com/danbri/factoidal-core/issues/1038).
- A new server, protocol or security surface carries the experimental code notice
  (`CLAUDE.md`).

## Records

- [Frozen document base URLs](../../docs/designissues/2026-11-16-frozen-base-url.md): live script DOM cache, mutation hooks, URL reflection and its proof/test boundary.

- [Architecture briefing](../../docs/designissues/2026-11-25-foafnaut-architecture-briefing.md) for an
  outside engineer: design rules, numbers, why WPT is high and pages are slow, where help pays off.
- [Frame pipeline](../../docs/designissues/2026-11-07-foafnaut-frame-pipeline.md), the design
  and measurements of frames, scroll and press.
- [Kept answers, layout sections, page patches](../../docs/designissues/2026-11-25-foafnaut-display-list.md)
  (issue 1124): the chrome and no-layers answers kept by key, `layoutSections`, `have` with
  `{"kept":id}` and byte patches, `--document-bin-seq` and `--document-bin-check`, the band change
  profile.
- [Page scripts](../../docs/designissues/2026-11-08-page-scripts.md),
  [BubblePopJS](../../docs/designissues/2026-11-08-lean-js-engine.md),
  [event loop](../../docs/designissues/2026-11-08-event-loop.md),
  [WasmVM](../../docs/designissues/2026-11-07-wasmvm-engine.md).
- [Performance exploration of 2026-11-09](../../docs/designissues/2026-11-09-foafnaut-perf-exploration.md):
  BubblePopJS (`main`, stage A, stage B) against QuickJS-NG and V8 by operation and on
  real-world libraries, where the instructions go, defects found by differential runs, the
  engine's start, first compile and frame by phase.
- [BubblePopJS plan of 2026-11-09](../../docs/designissues/2026-11-09-bubblepopjs-plan.md):
  the data layout (value words, flat heap, shapes, inline caches), the tiers, the theorems,
  the profiles, key results and stages; with a Lean model that measures the layout. Its
  tracking issue, with the decisions it needs: https://github.com/danbri/factoidal-core/issues/378.
- [Liberal mode and console](../../docs/designissues/2026-11-08-liberal-mode-and-console.md),
  [browser state](../../docs/designissues/2026-11-08-browser-state-lws.md),
  [CPU backend](../../docs/designissues/2026-11-08-cpu-render-backend.md),
  [cost theorems](../../docs/designissues/2026-11-08-cost-theorems.md),
  [page GPU](../../docs/designissues/2026-11-08-page-gpu.md).
- [Safety map of 2026-11-13](../../docs/designissues/2026-11-13-foafnaut-safety-map.md): which
  modules can reach I/O (`io-free`, `reaches-hatch`, `effect-typed`), from the compiled
  environment. Run `python3 tools/safety-scan/safety-scan.py --self-test`, then the scan,
  before and after a change that adds an `@[extern]`, `unsafe`, `@[implemented_by]`,
  `initialize` or `dbgTrace`. Tracking: https://github.com/danbri/factoidal-core/issues/427.
- [Threads, tabs, processes, DNS and HTTP connections, 2026-11-24](../../docs/designissues/2026-11-24-foafnaut-concurrency-and-network.md):
  what runs on which thread today, one engine worker per tab, processes per site, the connection
  pool and HTTP/2, the DNS cache and speculative resolution, the Veil models to add first.
- [Tor and onion services, 2026-11-25](../../docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md):
  three routes (local SOCKS port, embedded Arti, a Lean client), the conflict with Egress DNS
  pinning, what the pool key and any substrate must allow, and the fingerprint limit; section 10:
  Arti 2.8.0 built for wasm and run in a page (`labs/demos/foafnaut/tor-wasm`), with its security review.
- Records dated before 2026-11-08 describe earlier stages. Most carry a dated note that says what changed.
- Status for readers: `docs/web/hub/foafnaut2525-status.md`, dated. Notes:
  `docs/web/hub/web-platform/foafnaut/notes/posts/` (do not rewrite old notes).
