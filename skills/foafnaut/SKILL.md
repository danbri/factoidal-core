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
  `TUI-CATALOGUE.md`, the launcher `textnaut`).
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
- `LAB/native_html_worker.ts`, `LAB/native_html_compile.ts`: the engine worker. One ordered
  queue for every slow engine call.
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
- `web_render_shim.c` is the C ABI of the engine.

Engine in the library, under `formal/lean4/L4Factoidal/`:

- `Rendering/` (style, layout, tables, scene, fonts, `Sfnt*` shaping, `FontPolicy`,
  `MediaQuery`, `ComputedValues`, `CssSupports`), `HTML/`, `DOM/`, `FrameCost/`,
  `PageCanvas/`, `PageGpu/`.
- `JS/`: BubblePopJS, the JavaScript engine written in Lean.
- `WasmVM/`: the WebAssembly engine written in Lean. `WasmVM/Hosts/` connects page scripts:
  `Page.lean`, `PageEvents.lean`, `PageWasm.lean`, `PageAot.lean`, `Dom.lean`, `DomOps.lean`,
  `WebApi.lean`, and `LeanJS.lean` + `LeanJSRealm.lean` for BubblePopJS.

Page scripts run in the engine. No host JavaScript engine runs a page script.
`WebRenderScript.defaultEngine` gives BubblePopJS on the desktop and QuickJS-NG in WasmVM
on the Hub. The QuickJS-NG guest is `tools/wasmvm/build-quickjs.sh` with
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
plain `foafnaut` starts the newer of the installed release and the bleeding-edge build;
`--bleeding-edge` also prints the build commit and age; `--latest` and `--install-latest`
install from `danbri/factoidal-builds`. `~/.foafnaut/config.json` key `bleedingEdge` gives the app path.

Measuring:

- `--perf-summary`: frame and input latency when the run ends.
- `--idle-checks-only`: the normal-use pixel-check rule in a sweep.
- `--single-frame`: the path before two-layer scroll, for comparison.
- Engine op `frameWork`: counts layouts, kept layouts used, repaints on a kept layout,
  `pagesMade` and `pagesKept`.
  `frame_work_test.ts` and `frame_cost_test.ts` hold the ratchets; the model is
  `formal/lean4/L4Factoidal/FrameCost/`.
- Profiling: macOS `sample` against a Deno loop over `engine.compileLayers`. No script for
  this is in the repository.

### Measure BubblePopKit and BubblePopJS with no Mac

A Linux cloud session can build and measure everything that is CPU work: the native build of
BubblePopKit (`web-render-native`) and BubblePopJS (`leanjs`). It can not run the window, the
GPU or the Deno host. Record of the first such session, with every number and command:
[docs/designissues/2026-11-09-foafnaut-perf-exploration.md](../../docs/designissues/2026-11-09-foafnaut-perf-exploration.md).

```sh
# tools (Ubuntu 24.04): elan and the pinned Lean (skills/session-restore), then
apt-get install -y --no-install-recommends time linux-tools-generic valgrind
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
  `perf` on this kind of VM has only `-e cpu-clock` (no hardware counters); the binary is
  `/usr/lib/linux-tools/*/perf`.
- Real-world libraries on each engine (right answer, CPU time, memory), under a memory
  watchdog: `labs/demos/foafnaut/bubblepop_perf/realworld.py`. Run every BubblePopJS test of
  unknown code under a memory limit: `new Array(4294967295)` takes all memory, and on
  2026-11-09 the kernel then killed a build on the same machine.
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

- Coordination log: `/Users/danbri/working/sandbox/october/tpac/depmap/cache/foafnaut-coordination.log`.
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

## Land work

- Branch from `origin/main`: `wip/<issue>-<topic>`. Push after each step that passes.
- Before you push to `main`: `git fetch origin main`, rebase, then
  `git merge-base --is-ancestor origin/main HEAD` and `git diff --stat origin/main HEAD`.
  Touch only the files you meant. Remove `.lake` and `.wasm-work` after the push.
- Page-only change: `tools/hub-quick-ship.sh` (no engine build; it refuses other paths,
  prints the deploy command).
- A new server, protocol or security surface carries the experimental code notice
  (`CLAUDE.md`).

## Records

- [Frame pipeline](../../docs/designissues/2026-11-07-foafnaut-frame-pipeline.md), the design
  and measurements of frames, scroll and press.
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
- Records dated before 2026-11-08 describe earlier stages. Most carry a dated note that says what changed.
- Status for readers: `docs/web/hub/foafnaut2525-status.md`, dated. Notes:
  `docs/web/hub/web-platform/foafnaut/notes/posts/` (do not rewrite old notes).
