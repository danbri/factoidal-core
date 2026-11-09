# Browser WPT probes

These commands measure the existing Lean renderer, HTML parser, DOM arena
and actual QuickJS WASM guest against pinned upstream files. They preserve
unsupported, unavailable, timeout and failing rows. They currently exit 1
because the implementation is incomplete; do not mask that exit as a pass.

The [3 November baseline](baseline-20261103.json) records artifact hashes,
denominators and report hashes. The
[worknote](../../docs/20261103-browser-wpt-baseline.md) explains the results
and the boundary between native engine evidence and browser expectations.
This is a local probe suite, not yet a CI or release gate.

## Requirements and inputs

- Run from the repository root with Python 3, NumPy, Pillow, Node 22+ and
  the repository's Lean toolchain installed.
- Supply an already-built `web-render-native` and its source witness. No
  renderer, WASM runtime, browser or Lake package is downloaded or rebuilt.
- `parser-probe.py` needs the existing production Lean module cache under
  `formal/lean4/.lake/build/lib/lean`. It records its hashes and compiles
  harness and code-point adapter modules into a new output directory. This is a cached-module
  interpreter test, not a fresh native parser executable build.
- Parser fixtures are the unchanged `third_party/testing` trees documented
  by [parser-fixtures.json](parser-fixtures.json). Their complete file lists
  and Git blob hashes are checked before the test starts.
- The SVG corpus is `tests/external/svg-wpt` in the corpus checkout. Its
  `source.json`, `inventory.json` and `upstream/` must be present. Run its
  `corpus.py --check` independently to verify the complete corpus.
- Native image tests additionally require the existing `capture.json` and
  original browser PNGs from a qualified pinned capture. Those are cached
  expectations. Candidate pixels are produced freshly by the native CLI.

Use a fresh result directory. The examples match the sibling checkouts on
the development laptop; adjust paths elsewhere. Run all commands even when
one reports conformance failures. Do not connect them with `&&`.

```sh
RUN_DIR=$(mktemp -d /tmp/factoidal-browser-wpt.XXXXXX)
NATIVE=labs/demos/foafnaut/.build/web-render/web-render-native
CORPUS=../factoidal-svg-corpus-overnight/tests/external/svg-wpt
ORACLE=/private/tmp/factoidal-overnight-corpus-curves-web-wasm-ready/capture

python3 tests/browser-wpt/parser-probe.py \
  --fixtures ../factoidal-core/third_party/testing \
  --output "$RUN_DIR/parser"

node tests/browser-wpt/quickjs-probe.mjs \
  --corpus "$CORPUS" --native "$NATIVE" --output "$RUN_DIR/quickjs"

python3 tests/browser-wpt/native-reftests.py \
  --corpus "$CORPUS" --oracle "$ORACLE" --native "$NATIVE" \
  --output "$RUN_DIR/native" --timeout 5

python3 tests/browser-wpt/native-provenance.py \
  --native "$NATIVE" \
  --witness labs/demos/foafnaut/.build/web-render/source-witness.json \
  --input "$CORPUS/upstream/svg/render/reftests/overflow-clip.html" \
  --output "$RUN_DIR/provenance"
```

The provenance command currently uses macOS `otool` and `dyld` diagnostics.
The parser runner starts Lean from `formal/lean4`, as required by this repo.
Use `--lean /absolute/path/to/lean` if it is not on the command path.

## Original SVG Tiny 1.2 admission

`svg-tiny-admission.py` takes the official W3C archive as a local input,
checks its pinned SHA256, and sends all 496 original `svg/` documents to
the Lean SVG compiler. The archive contains 496 metadata-approved cases,
including a UTF-16 case; the overview page's 495 summary is not the runner's
denominator. No labels, metadata, attributes or unsupported content are
removed. `svggen/` derived files are not substituted.

```sh
python3 tests/browser-wpt/svg-tiny-admission.py \
  --archive /path/to/W3C_SVG_12_TinyTestSuite.tar.gz \
  --output /tmp/factoidal-tiny-new-run
```

This uses the existing `labs/demos/foafnaut/.build/web-render/olean` and
production Lean caches. It records every input's SHA256 and every refusal.
`ADMITTED` would only mean a scene compiled; **visual conformance is
NOT_RUN**, never inferred from admission. The
[initial inventory and admission](svg-tiny-admission-20261103.json) has
495 unsupported cases, one unavailable UTF-16 input and zero admitted
scenes. Most stop at the unsupported `baseProfile` attribute. This is a
baseline for SVG work, not a passing Tiny implementation.

## SVG Tiny 1.2 pixel comparison

`svg-tiny-pixels.py` sends each original `svg/` file to `web-render-native
--svg`, draws the Lean WebGPU artifact on a real GPU with `svg_tiny_gpu.ts`, and
compares the pixels with the `png/` file from the same archive. All 496 take
about 40 seconds. It needs Python with Pillow and NumPy, and Deno.

```sh
python3 tests/browser-wpt/svg-tiny-pixels.py \
  --archive /path/to/W3C_SVG_12_TinyTestSuite.tar.gz \
  --native labs/demos/foafnaut/.build/web-render/web-render-native \
  --output /tmp/factoidal-tiny-pixels
```

A pixel differs when a channel differs by more than 32. MATCH means at most 0.5%
of pixels differ, and at least 95% of the reference's non-white pixels agree.
CLOSE means at most 5% and 70%. These bands were fixed before the first run.
They are ours, not a W3C verdict. A blank white image goes through the same
bands as a control.

`SVGForgiving.lean` removes what the strict reader can not draw and logs each
removal. `filesAffectedByDrop` in the report is the ranked to-do list. Only the
first frame is drawn, so animated tests can not match yet. Results are in
[the dated report](svg-tiny-pixels-20261107.json).

## Whole-WPT score

`wpt-score.py` measures Foafnaut's score over all of WPT the way wpt.fyi and
Apple's EU browser-engine rule count it: subtests passed divided by the most
subtests any browser runs on wpt.fyi (Chrome's count at the pinned WPT commit).
It uses `testharness-run.ts --wpt-root DIR --list FILE`, which runs tests by
their wpt.fyi names from any WPT checkout. Since 2026-11-09 it runs them through
WPT's own server, `wptserve` (see "Running through wptserve" below); the older
path (`wpt-score.py run --files`) reads the checkout's files and makes
wptserve's `.any.html`, `.window.html` and `.test262.html` wrappers and the
common `.sub.` substitutions in the runner. Pages without testharness.js
(reftests, crashtests) are counted as not testharness. Run without `--list`, the
runner's defaults and output are as before.

```sh
SCRATCH=$(mktemp -d)
# 1. Chrome's wpt.fyi summary for the commit (summary_v2: name -> {s, c: [passed, total]}).
#    Find the run at https://wpt.fyi/api/runs?sha=<commit>&product=chrome&label=master
#    and save its summary_v2.json.gz, unzipped, as $SCRATCH/chrome.json.
# 2. Draw the stratified sample (fixed seed; 25 names a stratum, the 5 largest always).
#    --variants all (the default) also draws the worker, shared worker, service worker,
#    ShadowRealm and module variants, as strata of their own; --variants window draws
#    the window sample of the 2026-11-09 score, which `all` keeps unchanged.
python3 tests/browser-wpt/wpt-score.py sample --chrome $SCRATCH/chrome.json \
  --out $SCRATCH/sample.json --list $SCRATCH/sample.list
# 3. The part of WPT those tests need, from GitHub's tarball of the commit, streamed
#    (no git, no full checkout): tools/ (wptserve itself), resources/, common/, fonts/,
#    images/, interfaces/, the Test262 harness, each test's directory with its
#    resources/ and support/, and what the pages load from elsewhere (about 380 MB).
python3 tests/browser-wpt/wpt-score.py tree --wpt-root $SCRATCH/wpt --list $SCRATCH/sample.list
# 4. Run (3 processes under nice; a test stalled for 300 s is recorded and skipped).
#    One wptserve serves all three; it stops at the end. Add `-- --script-engine bubblepop`
#    for BubblePopJS.
python3 tests/browser-wpt/wpt-score.py run --list $SCRATCH/sample.list --dir $SCRATCH/run \
  --wpt-root $SCRATCH/wpt --native-engine labs/demos/foafnaut/.build/web-render/engines/libweb-render.dylib
# 5. Optionally run whole directories (a list of all their names) into another --dir,
#    then score everything together.
python3 tests/browser-wpt/wpt-score.py score --chrome $SCRATCH/chrome.json --sample $SCRATCH/sample.json \
  --results $SCRATCH/run $SCRATCH/run-full --out tests/browser-wpt/wpt-score-$(date +%Y%m%d).json
```

The `sparse` command (a blobless sparse git checkout of the test files and the
scripts they load) still works for the `--files` path; wptserve needs `tree`.

[wpt-score-20261109.json](wpt-score-20261109.json) is the first such score, at
WPT fea36e49dd with the release-equivalent native engine: 31,202 subtests
measured (1.38% of 2,267,658), about 39,600 by extrapolation (95% range
36,600 to 42,700, 1.61% to 1.88%). The sample of 5,898 names took 2 h 18 min
in 3 processes. Its `notes` list the whole strata run, and two diagnostics that
are not counted: Test262 run at top level, and the iframe documents and fuel
bound that hold back dom/nodes and the html/dom reflection tests.

The score file gives each test run (our passed and reported subtests, and
Chrome's count), each stratum (measured, extrapolated and Chrome's subtests)
and the totals: the measured lower bound, the extrapolated estimate with a 95%
range, and their share of the denominator. Passed subtests are capped at
Chrome's count for the same name. The method is described at the top of
`wpt-score.py`.

## Running through wptserve

`testharness-run.ts --wptserve --wpt-root DIR --list FILE` is WPT test mode.
The runner loads every test from a local wptserve, as a browser run does:

- **Pages and scripts over HTTP.** A name such as `/url/a.any.html?include=x`
  loads `http://web-platform.test:8000/url/a.any.html?include=x`; a `.https.`
  name loads `https://web-platform.test:8443/...`, a `.www.` name the www
  subdomain. The host (the runner, in place of run_html.ts) fetches the page,
  then each `<script src>` the engine lists (`inspect`), on any WPT origin,
  and gives the sources to the engine's script session. Lean decodes the page
  bytes with the HTTP Content-Type. So wptserve's own wrappers, `.sub.`
  substitution, `.headers` files, pipes (`?pipe=`), Python handlers,
  redirects and the other origins (www1, www2, the IDN subdomains,
  not-web-platform.test, port 8001) behave as they do for a browser.
- **The server.** `wpt-score.py serve --wpt-root DIR` runs WPT's
  `tools/serve` with WPT's vendored libraries, so it needs no virtualenv and no
  network. It binds to 127.0.0.1 only, with HTTP on 8000-8003, HTTPS on
  8443-8446 (WPT's pregenerated certificates), HTTP/2 on 9000 and WebSockets on
  8888/8889. There is no WebTransport and no DNS server. `wpt-score.py run`
  starts one server for all its processes. The runner starts its own when none
  answers. SIGTERM or SIGINT stops it with its server processes.
- **The test-mode resolver** (`wpt-hosts.ts`). WPT's hostnames are
  web-platform.test and not-web-platform.test, each with www, www1, www2 and the
  two IDN subdomains. They reach 127.0.0.1 only inside this runner process, and
  only with `--wptserve`, on the ports above. HTTP goes through Deno's fetch
  with a `tcp` transport to 127.0.0.1, keeping the URL's host. HTTPS goes
  through a small HTTP/1.1 client: TCP to 127.0.0.1, then TLS with the URL's
  host for SNI and the certificate check. Redirects are followed one hop at a
  time, and each hop is checked again. Any other host, port or scheme is
  refused, including `nonexistent.web-platform.test`, which WPT means to fail.
  So this mode never reaches a real network host, and it is not a proxy.
  Nothing is written to /etc/hosts.
  `deno test tests/browser-wpt/wpt-hosts_test.ts` checks the refusals.
- **Trust.** HTTPS trusts WPT's test CA (`tools/certs/cacert.pem` in the
  checkout) as an extra root for this client only. No certificate is installed
  and no system setting changes.
- **testharnessreport.js** is the one file the runner still supplies itself:
  ours reports results as console lines. wptrunner does the same for each
  browser.
- **Variants.** Once a process, the runner asks the engine which APIs it has
  (`info.features` in `--out`): Worker, SharedWorker, navigator.serviceWorker,
  ShadowRealm, fetch, XMLHttpRequest and module scripts. A variant whose API is
  missing is `SKIP` "not supported by engine: Worker (dedicated worker
  variant)", kind `engine`, and scores 0. That is kept apart from runner gaps
  (kind `runner`, for example `.h2.` names, which need the HTTP/2 server). A
  worker variant runs as soon as the engine defines `Worker`. Then wptserve
  serves its `fetch_tests_from_worker` page and the worker script, and the
  runner answers each script the worker asks for (`fetches` in a turn, action
  `fetched` in reply) over the same HTTP path.

What stays out of scope or is still missing:

- **Engine features.** The runner serves what a browser would get. Whether the
  engine follows the same-origin policy is the engine's business. Its
  scriptSession has no host fetch for page `fetch()`/XHR, iframe documents,
  Worker scripts or importScripts yet. Tests that need these fail in the
  engine, not in the runner.
- **The url/ data shim.** The url/ tests load their data with
  `fetch("resources/x.json")`. Until page scripts have `fetch`, the runner's
  shim answers those files. With `--wptserve` it gets them from wptserve over
  HTTP. It goes away when the engine has fetch.
- **Not run.** The HTTP/2 tests (`.h2.`, kind `runner`), because the HTTPS
  client speaks HTTP/1.1; WebTransport; and the `.py` names (kind `wdspec`), which
  are pytest tests driving a browser over WebDriver or reading its accessibility
  tree, not pages. Browser extension tests are kind `engine`. Reftests and
  crashtests weigh 0 in wpt.fyi's subtest counts.
- **Provenance.** The WPT tree is BSD-3-Clause and stays in scratch. `tree`
  writes a PROVENANCE file with the commit. Nothing from it is committed.

### wptserve against the file path

The 5,898 window names of the scorer's sample, on BubblePopJS with the native
engine at 0f89690b6, capped at Chrome's count for each name, three processes
each. The file path took 2,173 s of wall time and wptserve took 2,211 s (+1.7%).

| Directory | Names | File path | wptserve | Change |
| --- | ---: | ---: | ---: | ---: |
| html/infrastructure | 21 | 100 | 143 | +43 |
| encoding-detection | 23 | 0 | 6 | +6 |
| html/dom | 16 | 51,070 | 51,068 | -2 |
| All other directories | 5,838 | 135,223 | 135,223 | 0 |
| **Total** | **5,898** | **186,393** | **186,440** | **+47** |

- The gains are the HTTP charset of the served pages (query-encoding, encoding
  detection) and the UTF-16 pages, which the runner now recognises as tests.
- The two losses are `html/dom/reflection-forms.html` and
  `reflection-embedded.html`. Both stop at the engine's fixed step budget in both
  paths ("halted: step budget exhausted"), and the longer URL (`:8000`) reaches it
  one subtest sooner.
- The small gain says where the limit is: the engine. Most tests that need the
  server also need `fetch`/XHR, iframe documents or Workers. wptserve removes the
  runner as a cause of failure. It does not add those APIs.

## History and dashboard

`tools/render-dashboard/run.py` runs these probes and the font suites, adds one
record per suite to `tools/render-dashboard/history.jsonl`, and writes the Hub
page `docs/web/hub/render-scores/index.njk`. See its `--help`. A record is
`measured` (this tool ran it), `copied` (a number from a named report) or
`not-run` (with the reason and no counts). Do not edit the page.

## What is evaluated

`parser-probe.py` runs all original tree fixtures directly and through
`DOM.ofTreeBuilder`, then all html5lib tokenizer fixtures. It does not pass
an expected-failure/exclusion file. Tree equality and parse-error counts
are distinct measurements. The code-point adapter preserves lone surrogates
in character tokens; unsupported String-valued token buffers remain explicit
refusals. The four original character-output surrogate cases now run.

Every parser run also saves `error-counts.jsonl` with all document inputs,
original diagnostic descriptions, actual tokenizer/tree-builder errors and
independent tree equality. `parser-error-audit.py` produces
`error-counts-audit.json`, retaining every mismatch and separating overlapping
old/new descriptions, empty expectations and algorithm-review cases. These
categories never change the raw score. See the
[diagnostic audit](../../docs/20261103-html-parser-error-count-audit.md).

`quickjs-probe.mjs` asks the native Lean `--document inspect` operation to
parse each original HTML document and extract connected nodes and ordered
classic scripts. It then loads the original `testharness.js` into the
actual pinned QuickJS WASM reactor in shell mode and installs the production
guest DOM binding and its synchronous capability into a separate Lean WASM
engine. The probe reuses that stateless Lean instance between cases, with
separate document command histories and QuickJS heaps. Page code is never evaluated in Node's
JavaScript realm; host `eval` and `Function` are trapped. Node still hosts
the transport and WebAssembly runtime. JSON callbacks replace the reporting
UI; synchronous harness completion status is recorded as well as assertions.

This adapter has no browser task queue, promise-job draining, full Window,
SVG/XML document loading or complete DOM APIs. Async and
incomplete documents cannot count as passes. It is not the upstream `wpt
run` browser product integration, and it is not a JS language-conformance
suite or a claim that QuickJS is implemented or verified in Lean.

`native-reftests.py` retains all HTML relations from the SVG inventory. It
runs the native compiler and CPU pixel sampler with a five-second budget
per operation, original source and an 800×600 viewport. The original
browser's test/reference pair must satisfy the upstream relation before it
can qualify an expectation. Original fuzzy bounds are preserved. A
negative relation alone cannot pass without an exact original-test match.
The profile uses the renderer's default bitmap font; there is no fresh
Chrome or WebGPU candidate run. Standalone SVG/XML relations are outside
this HTML runner's denominator and remain in the separate full corpus.

## Failure controls

The QuickJS runner checks one passing and one deliberately failing WPT
assertion and checks that host globals are absent before installing the
guest. Exact native image matches receive a one-pixel corruption check.
Source and image hashes are checked, and a truncated oracle inventory is
rejected. The provenance runner requires the binary and current source/C
files to match the witness and records actual loaded libraries.

The baseline also records successful rejection of deliberately wrong
native and fixture hashes and a truncated oracle. These checks improve
auditability; they are not a formal binary correctness proof.
