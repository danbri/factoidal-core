---
name: foafnaut
description: Contribute to Foafnaut, the web browser with its own rendering engine (labs/demos/foafnaut, formal/lean4/L4Factoidal/Rendering, docs/web/hub/foafnaut). The code map (window, worker, engines, page generator, Hub host, Lean modules, page script engines BubblePopJS and QuickJS-NG in WasmVM), how to build, test, run and measure, the shared-machine rules (coordination log, one Lean build at a time, disk limits), the traps that cost time, and how to land work. Use before any Foafnaut change, build, sweep, Hub deploy or status report.
---

# Foafnaut

Foafnaut is a web browser. Its engine parses HTML, computes CSS, lays out text and boxes,
and makes the GPU commands. The engine is written in Lean 4. It runs in a macOS window
and on the Hub (https://danbri.github.io/factoidal/web/hub/foafnaut/). "foafnaut2525" is
the name of the engine in the status note, the release records and older files.

Names for new text and docs: **Foafnaut** is the browser and **Textnaut** the text-mode browser. **BubblePopKit** is
the rendering engine as a whole, **BubblePopJS** its JavaScript engine, and **BubblePopWASM** its WebAssembly. Code
identifiers keep their existing names.

State at the last handoff, what is in flight, and what to do next:
[docs/designissues/2026-11-09-foafnaut-handoff.md](../../docs/designissues/2026-11-09-foafnaut-handoff.md).
This skill changes slowly. The handoff record goes stale first: check it against
`git log origin/main` and the coordination log (below).

Every command here was read from the scripts at commit `6f08a9824` (2026-11-09). When a
command and a script disagree, the script is correct. Fix this file.

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
- [Liberal mode and console](../../docs/designissues/2026-11-08-liberal-mode-and-console.md),
  [browser state](../../docs/designissues/2026-11-08-browser-state-lws.md),
  [CPU backend](../../docs/designissues/2026-11-08-cpu-render-backend.md),
  [cost theorems](../../docs/designissues/2026-11-08-cost-theorems.md),
  [page GPU](../../docs/designissues/2026-11-08-page-gpu.md).
- Records dated before 2026-11-08 describe earlier stages. Most carry a dated note that says what changed.
- Status for readers: `docs/web/hub/foafnaut2525-status.md`, dated. Notes:
  `docs/web/hub/web-platform/foafnaut/notes/posts/` (do not rewrite old notes).
