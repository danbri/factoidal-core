---
name: wpt-runs
description: How Foafnaut's Web Platform Tests score, its WPT reftest scores (rendering, svg/ and css/) and BubblePopJS's full Test262 score are measured, recorded and reported, and the other conformance suites with them. Full measured runs only (no sampled scores), BubblePopJS only, cloud runs on every release and four times a day, validity rules, runs.csv and per-run metadata. Use before running WPT or Test262, quoting a WPT or Test262 number, comparing with other browsers, planning WPT work, or changing the test workflows.
---

# WPT and Test262 runs: the testing regime

WPT is sections 1 to 8, WPT reftests section 10; Test262, the whole tc39/test262 suite on BubblePopJS, is section 9 (same
regime: full runs only, validity rules, the same `runs.csv`).

Since 2026-11-13, decisions are made on **full measured runs**, never on samples: a sampled estimate
is too uncertain to plan from.

## 1. What a score is

- **Full**: every WPT name Chrome runs at the WPT commit (94,406 names at fea36e49dd), each one run. No
  sampling, no extrapolation.
- **Scale**: Chrome's subtest count at that WPT commit is the denominator (2,267,658 at fea36e49dd). Each
  engine's passes in a test are capped at Chrome's count for that test (`tests/browser-wpt/wpt-full.py`).
  Rival browsers are scored the same way from wpt.fyi.
- **Two numbers, always together**: the share, and the share without `encoding/`. `encoding/` is half the
  denominator: one subtest per character of five legacy East Asian encodings. A headline without the
  second number misleads.
- **Engine**: page scripts on BubblePopJS. A number with no engine named means BubblePopJS. QuickJS runs
  are a differential check only: run them on request, mark them `differential`, never show them as the
  browser's score.
- Every number names its engine commit, WPT commit, date and platform.

First record: `tests/browser-wpt/wpt-full-20261113.json`. Foafnaut 63.14%, 25.2% without encoding.
Chrome 97.28% on the same scale.

## 2. Valid runs only

A run is shown or quoted as a score only if all of these hold:

- every name was run (names_run = names_total) and no shard is missing;
- test-server failures ("fetch failed", "Connection refused") are under 0.5% of names;
- its wptserve stayed up for the whole run;
- the engine commit and release (or local build) are recorded.

Invalid runs are kept, with `valid=false` and the reason, and never plotted or quoted.

### When shards or whole runs produce nothing

Infrastructure failures are never turned into test failures that lower a score. The rules:

- **Every run is recorded**, valid or not: a `runs.csv` row and `runs/<run_id>/meta.json`.
- **Per shard** (`meta.json` `shard_table`, one row per planned shard, present or not): shard index,
  status (`complete`, `partial`, `no-results`, `missing`), names planned and run, tool exit, start
  and finish times, wall seconds, runner (OS, machine, CPUs, image), start-check tries, the cause
  in words, and the last lines of its log. `shards_missing_reasons` gives each missing shard's
  reason: its own error, "no artifact" (the job failed, was cancelled or its runner was lost), or
  no shard-meta. The job summary lists every shard that is not complete, and each missing shard
  is a GitHub error annotation on the run.
- **Completeness** (`meta.json` `completeness`): `complete`, `partial` (some shards or names have
  no results) or `none`. The first validity reason says it: "partial run: 7 of 12 shards gave
  results, ...". A partial run's share counts the missing names as not passed, so it is never a
  score and the Hub shows no share for it.
- **Bounded retries**: a shard tries its one-test start check up to 3 times before giving up
  (`--start-tries`). When a run ends with some, not all, shard jobs failed,
  `release-tests-retry.yml` re-runs its failed jobs once (attempt 2, recorded under its own run id
  `...a2`; attempt 1 stays recorded as partial). No third attempt. A run where every shard failed
  is a setup fault and is not retried: its record names the cause shard by shard.
- **Headline**: only complete valid runs (`valid=true`, `kind=full`). The Hub's Conformance page
  lists the newest runs that are not counted ("Runs not counted": suite, engine, platform,
  completeness, names run, reason, link to the workflow run), so a gap in the history is
  explained.
- The same applies to full Test262 runs (`test262.py score`) and WPT reftests (`reftests.py
  score`): per-shard reasons, completeness, the same retry workflow. The real-page survey is not
  a sharded full run; it adopts the pattern if it becomes one.
- Known bound: in a valid run, names with test-server failures (under 0.5%) count as not passed.
  They are listed (`server_failures`) and retried once in the shard first.
- A setup fault seen on 2026-11-16: the shard jobs' sparse checkout lacked
  `docs/web/hub/foafnaut`, which the engine host imports; every shard of three runs gave no
  results. When the engine host imports from a new directory, add it to the sparse checkout of
  the WPT jobs in `release-tests.yml` and `branch-wpt.yml` (a test in factoidal-builds checks it). A rival run that
reports only part of WPT (Ladybird on wpt.fyi: 35,966 of 94,406 names) is left out of comparisons.

## 3. When runs happen (cloud, `danbri/factoidal-builds`)

- **Every Factoidal release on main**: when `build.yml` publishes a commit's releases.
- **Every browser release**: a daily wpt.fyi check. A new stable version, or a new aligned WPT commit,
  records the rivals and runs Foafnaut's latest release at that WPT commit.
- **At least four times a day** on a schedule. Each run picks the newest main commit whose releases are
  complete, and may wait up to about an hour for one that is finishing. It pushes a snapshot branch
  `wpt-snap/<YYYYMMDD-HHMM>-<sha12>` in factoidal-core first, so the source and tool used stay fixed. A
  run on an unchanged commit is a repeat (`repeat_of`): repeats measure flakiness.
- **Platforms**: scored runs on Linux, sharded wide (12 runners, 20 to 25 minutes). macOS arm64, the
  shipping platform, runs once a day (13:41 UTC) and on each `build.yml` release as a cross-check (4
  runners, about 45 minutes). Differences between the two on one commit are bugs to find (fonts, timing,
  platform code). On 6dde36491 they agree to 0.01 points (Linux 71.2202%, macOS 71.2245%).
- **A valid Linux row is the score of a commit while that commit has no valid macOS row.** Report the
  platform with the number.
- **Main on Linux, automatically**: every 20 minutes `foafnaut-linux.yml` builds the Linux engine of the
  newest main commit when that commit changes engine code (`formal/lean4/`, `labs/demos/foafnaut/`,
  `tools/wasmvm/`, the WPT runner) and has no Linux engine yet. Docs-only commits are skipped: they have
  the engine of the commit before. One build at a time, and the newest commit wins. The build takes
  about 12 minutes (the Lake cache and a C object cache serve what did not change) and starts the Linux
  full run as soon as the engine is published. The end of each branch check also runs this step, since
  GitHub starts scheduled runs late. Only x86_64 is built automatically (arm64: a dispatch with
  `arm64=true`). So a main commit that changes the engine has a full-run row about an hour
  after the push, with no macOS runner. The same step starts `build.yml` for main when the hourly poll
  missed the commit.
- **Main on macOS, the engine alone**: `foafnaut-macos.yml` ("Foafnaut macOS engine") builds
  `libweb-render.dylib` for each main commit whose Linux engine was published (one build at a time, the
  newest commit wins; also every three hours) and publishes `build-<sha12>-foafnaut-engine-darwin-arm64`
  (the tarball holds `foafnaut/libweb-render.dylib`; static Lean runtime). Its gate is the engine build
  and one WPT page, none of `build.yml`'s other gates, so a main commit has a macOS engine for drawing
  pages and for a macOS WPT run also while `build.yml` publishes no `foafnaut-darwin-arm64` set. The
  macOS full run takes the full set when the commit has one, else this one. A branch or any commit on
  request: `gh workflow run foafnaut-macos.yml -R danbri/factoidal-builds -f core_ref=wip/x -f branch=true`,
  then `gh run download RUN_ID -R danbri/factoidal-builds -n foafnaut-engine-darwin-arm64 -D out/` (no
  release for a branch; the artifact is kept 5 days). The account runs 5 macOS jobs at once.
- **What changed since the previous run**: every valid full run is compared with the previous valid one
  of the same platform and WPT commit: subtests and points, the directories that fell and rose, where
  subtests were lost, the tests that lost most, and the core commits between the two. It is in the job
  summary, in `meta.json` (`since_previous`), in `runs/<run_id>/changes.md` on `wpt-scores`, and, with
  every changed test, in `<run_id>.wpt-changes.json.gz` on the release `test-results`. A fall of more
  than 0.2 points is marked DROP. Two result files by hand:
  `release-tests/release-tests.py wpt-changes --prev A.wpt-full.json.gz --cur B.wpt-full.json.gz --out DIR`.
- The other Factoidal conformance suites that have runners run on the same triggers, in parallel.
- No scheduled sampled job. The old daily sample (`wpt-score.yml`) was disabled and its schedule removed
  on 2026-11-13. Sampling remains only as a manual smoke check, never recorded as a score.

Where it lives (`danbri/factoidal-builds`):

- `release-tests.yml` ("Release tests"): the release, browser-release and scheduled full runs, and the
  other suites. `foafnaut-linux.yml` ("Foafnaut Linux engine"): the Linux engine build.
- `wpt-score.yml`: the old sampled job, disabled, schedule deleted (8adb27c); manual smoke runs only,
  never recorded.
- `build.yml` concurrency is one group per ref (7ab6de8): branch dispatches no longer evict each other,
  and the hourly poll can't evict them.

## 4. Records

- `runs.csv`: one row per run, append-only. Run id, times, trigger, suite, engine, platform, factoidal
  commit and its dates, snapshot branch, release tag, WPT commit, names run and total, passed,
  denominator, share, share without encoding, outcome counts, server failures, valid and reason, kind
  (full / sample / differential), shards, wall minutes, workflow run URL.
- `rivals.csv`: WPT commit, browser, version, wpt.fyi run id, passed, share, names reported, partial,
  status, reason. A rival that wpt.fyi cannot give (no run at the WPT commit, or no answer after three
  tries a few seconds apart) never fails the job: it is a row with `status=unavailable` and the reason
  (once per WPT commit and browser), listed in the job summary, so the dashboard can say "Servo: no run
  at this WPT commit". Rows before 2026-11-15 have empty status (= ok).
- `runs/<run_id>/meta.json`: everything above plus build-info, runner and tool versions, list hashes,
  why that build was chosen, the per-directory table, and a link to the full result JSON.
- `runs/<run_id>/incidents.json` and `incidents.md` (every full run since 2026-11-14 0907Z): the names
  that ended in `CRASH` (with the reason when the result says it: the step budget, the script heap
  limit, a script error before the harness completed, the test process killed with its signal and the
  memory guard's kills), in `STALL` (no result in the runner's 300 s) and in `TIMEOUT` (the harness's
  own), and the new and gone names of each against the previous valid full run. `meta.json` has the
  crash and stall lists and the differences under `incidents`. By hand from a run's shard artifacts:
  `gh run download RUN -p 'wpt-shard-*' -D DIR` then `release-tests.py wpt-incidents --shards-dir DIR
  --prefix wpt-shard- --out OUT [--prev PREVIOUS/incidents.json]`. A branch check's report lists the
  same for its names against the baseline run.
- Location: branch `wpt-scores` of `danbri/factoidal-builds` holds `runs.csv`, `rivals.csv`,
  `differential.csv` (QuickJS, kept apart from scores) and `runs/<run_id>/meta.json`. The full WPT
  result of each run is the asset `<run_id>.wpt-full.json.gz` of the release `test-results`.
- Dashboard: the WPT Pass Map artifact is refreshed from these records and shows valid full runs only.

## 5. Running WPT locally

- `tests/browser-wpt/wpt-score.py run --list <list> --dir <dir> --wpt-root <wpt> --native-engine
  <libweb-render> --jobs 3 -- --script-engine bubblepop`, then `wpt-full.py` to score a full run.
- **One WPT run per machine.** The runner refuses to start when port 8000 is taken, and stops if its
  wptserve dies (6af85600a). A second run sharing the ports once cost 21,411 names of a full run. Never
  kill another session's run: wait for it.
- Use a release build from the cloud (`build-<sha12>-foafnaut-darwin-arm64`) rather than building locally
  when disk is short.
- Local runs are for development: before and after a change, on the names it affects, plus a regression
  sample. A local full run counts as a score only if it meets section 2 and is recorded in `runs.csv`
  as `trigger=manual`.

## 6. Planning from the numbers

- Rank work by Chrome subtests regained per unit of work, with real-site impact as the tie-break. Find
  causes from the failure messages of every failing name, not from samples. The current plan:
  `docs/designissues/2026-11-13-wpt-plan.md`.
- Every engine change that lands on main gets a full run, and its JSON goes next to the previous one, so
  progress is a measured difference.
- In a hand-back, report subtests before and after on the names affected, the regression check, and
  timings.
- A test that ends in `CRASH`, is killed at the memory limit, or locks up its runner is a defect that
  comes before the subtests around it, not only lost subtests: name it in the report of the run, find the
  cause, and fix it with a stated bound (`local-lean-rules` section 11). Compare the `CRASH` and
  `TIMEOUT` counts of each full run with the run before.

## 7. Cloud builds

- `build.yml` takes `core_ref` (branch, tag or commit) to build a branch. A build takes about 1.5 h.
- Builds of different refs don't cancel each other: the concurrency group is per ref (7ab6de8). Before
  that, a new dispatch or the hourly poll cancelled the one pending build. Check the
  queue before dispatching, batch changes into few builds, and never cancel another agent's run.

- Every engine build (`build.yml`'s Lean Wasm modules, Foafnaut engines and macOS bundle;
  `foafnaut-linux.yml`, `foafnaut-macos.yml`, `branch-wpt.yml`) runs the AES binary gate
  (`tools/aes-gate.py --binary`, `skills/aes-hardware-only`) on what it built: an AES S-box or T-table
  in a library or Wasm module fails the build.

## 8. Checking a branch in the cloud

`branch-wpt.yml` ("Branch WPT check") in `danbri/factoidal-builds` builds the Linux engine library
from any branch or commit of factoidal-core and runs chosen WPT names with it. It is the fast loop for
a feature branch: Linux runners only, no macOS runner, no release, nothing written to `runs.csv`. It
is a development check, not a score.

```bash
gh workflow run branch-wpt.yml --repo danbri/factoidal-builds \
  -f core_ref=wip/my-branch -f names=/css/css-color/,/web-animations/,sample:40
gh run list --repo danbri/factoidal-builds --workflow branch-wpt.yml --limit 3   # the run id
gh run watch --repo danbri/factoidal-builds RUN_ID --interval 300
gh run view --repo danbri/factoidal-builds RUN_ID          # the summary is on the run's page
gh run download --repo danbri/factoidal-builds RUN_ID -n branch-wpt-results -D out/
```

- `core_ref`: any branch, tag or commit (a short commit id too). Push the branch first.
- `names`: a comma list of WPT path prefixes (`/dom/abort/`, `/css/css-color/parsing/`), and/or
  `sample:N` (every Nth name of the full list: a regression check; `sample:20` is about 4,700 names).
  Give the directories your change affects and a sample for regressions in one run.
- `shards` (optional): runners for the tests. Default: one for each 3,000 names, at most 8 (12 when you
  ask). The account runs 40 Linux jobs at a time (39 were seen running at once on 2026-11-14), shared by
  all branch checks and the full runs of main (13 jobs each), so a large sample waits in the queue and
  holds others up: prefer the directories you changed and `sample:40`.
- `wpt_commit` (optional): default is the WPT commit of the newest valid full run, so the baseline is
  at the same commit.
- `dangerously_enable_webdriver_endpoint` (optional, default false): run the wdspec names
  (`webdriver/tests/classic/`) against the engine's WebDriver endpoint. The runner gets
  `--dangerously-enable-webdriver-endpoint`: the engine decides whether the endpoint starts (loopback
  only, a secret in every request path), and `tests/browser-wpt/wdspec-run.py` drives it with pytest
  from the WPT tree. Without it, and in the full runs of main, every wdspec name is SKIP.
- The baseline is the valid full run of the newest scored main commit that your ref contains (same
  names), so the difference is what your ref adds to that commit: your work, and any main commits
  after it that have no score yet. The plan's summary says when that is not main's newest
  scored commit (your ref is older than it: rebase to compare with the newest), and when your ref
  contains no scored commit (then part of a difference is main's).

**Watching runs: the API limit is shared.** Every `gh` call that reads runs (`gh run list/view/watch/
download`, `gh workflow run`, `gh release`) counts against one limit of 5,000 requests an hour for the
whole account, shared by every agent; `gh run watch` asks every 3 seconds by default. On 2026-11-14 it
ran out at 09:04Z (14 agents polling in short loops) and every `gh` call answered HTTP 403 for half an
hour. So:

- one watcher per run, and no faster than every 5 minutes (`gh run watch RUN_ID --interval 300`, or a
  loop with `sleep 300`); one `gh run list` covers several runs, where one `gh run view` each does not;
- `gh api rate_limit` costs nothing: check it before a burst of calls (`--jq .resources.core`);
- read results without the API where they are on a branch: `git fetch` and raw.githubusercontent.com
  are not counted. Full runs: `runs.csv` and `runs/<run_id>/` on `wpt-scores`. Branch checks: every
  check also writes its report to the branch `branch-checks` (`checks.csv`, one row a check;
  `checks/<run id>/report.md` and `report.json`):

```bash
curl -s https://raw.githubusercontent.com/danbri/factoidal-builds/branch-checks/checks.csv | tail -5
curl -s https://raw.githubusercontent.com/danbri/factoidal-builds/branch-checks/checks/RUN_ID/report.md
```

  (raw.githubusercontent.com may serve a copy up to about 5 minutes old; `git fetch origin
  branch-checks` in a clone of factoidal-builds is current.)

What comes back:

- The job summary: subtests passed against the baseline, a table per directory (Chrome subtests,
  passed on this ref, passed on the baseline, difference, page outcomes), the tests that got worse,
  and the largest gains.
- Artifact `branch-wpt-results`: `report.md` (the summary), `report.json` (every directory, every
  test that got worse or better, names with no result) and `results.jsonl` (one line a test, each
  subtest with its status and failure message, as the local runner writes).
- Artifact `build-log`: the whole build log. When the branch does not compile, the run fails in the
  build job and the first errors are in the job summary.
- The build job's summary also gives `build.yml`'s tail-recursion gate
  (`tools/lean-tail-recursion-audit.py --gate`), which the engine build does not run: the declarations
  that are neither tail-recursive nor in `tools/lean-tail-recursion-allow.txt`. It does not fail the
  check, but with such a declaration on main `build.yml` publishes no release: fix it before merging.

Limits: the build is `build-web-render.sh --native` (the summary gives the minutes of each part; the
Lake build directory comes from `build.yml`'s newest Linux cache and the C objects of unchanged modules
from an object cache, so only what the branch changes is compiled again). The lab's `#guard` tests
(`WebDocumentTests.lean` and the others the build script runs) are part of the build: a failing one
fails the build, and the summary shows it. One run per `core_ref` waits at a time: a newer dispatch of the same ref
replaces a waiting one. A test process that grows past the memory limit is killed and its test is
recorded as CRASH.

## 9. Test262: the whole suite on BubblePopJS

The Test262-through-WPT number (`third_party/test262/` pages, Chrome's subtests) is a browser test of
a part of Test262. The **full Test262 run** is the JavaScript engine's own score: the whole upstream
suite, every file, by Test262's rules. Workflow `test262.yml` ("Test262") in
`danbri/factoidal-builds`, script `release-tests/test262.py`.

- **Suite**: tc39/test262 at a pinned commit (`TEST262_PINNED` in `test262.yml`; 2e58f87d83 since
  2026-11-15, the revision test262.fyi ran that day): every `.js` file under `test/` except
  `_FIXTURE` files (53,795 files: annexB, built-ins, harness, intl402, language, staging).
- **Rules** (`INTERPRETING.md`): each file in the modes Test262 runs it in: sloppy and strict;
  `onlyStrict` strict; `noStrict` and `raw` sloppy (`raw`: no harness); `module` once, as a module
  graph loaded from the files it names. 103,533 runs. `includes:` from `harness/`. A negative test
  passes on the named error type in the named phase (`parse`, `resolution` for module loading and
  linking, `runtime`). An async test passes when `$DONE` prints `Test262:AsyncTestComplete`. `$262`
  has `global`, `detachArrayBuffer`, `evalScript`, `gc` (does nothing) and `createRealm` (realms the
  runner makes before the test, two for each place its source names `createRealm`, at most 8; one
  heap, a realm switch at each call of another realm's function); tests that need `agent` or
  `IsHTMLDDA` fail. `import()` is served by the runner after the script's turn (module map per
  test, JSON modules by `with { type: "json" }`); modules with top-level `await` run as async
  generators. One run's heap is 2^22 objects (`runMaxObjs`), so a runaway test halts before the
  driver's 3,000 MB kill.
- **Engine**: core's `bubblepop-test262 test262-files` (`WasmVM/Hosts/Test262Page.lean`), built in
  the workflow from the release's core commit (build.yml's Lake cache, restore only): BubblePopJS on
  the page realm Foafnaut runs page scripts in (`LeanJS.prepareSource`: `prelude.js` on an empty
  document, so Temporal, Intl and the window's globals are there, as on a page). Recorded as
  `engine=bubblepopjs-page`, `script_engine=bubblepop`. `realm=engine` runs `leanjs test262-files`
  (the interpreter alone, no page objects): a diagnostic, never recorded. QuickJS never: its Test262
  numbers are a differential check only. Both runners share `JS/Test262.lean`.
- **Score**: a file passes when all its modes pass (the unit test262.fyi uses, so other engines compare
  on one scale). The headline counts every file. **Two numbers, always together**: the share, and the
  share without the files of the excluded features: `release-tests/test262-excluded-features.txt`
  (host-hook and harness features, each with its reason) plus the stage 3 proposals of `features.txt`
  at the pinned commit. Runs (file x mode) are in `meta.json` as a third, finer number.
- **Valid** when: every shard is present; runs with no result plus harness errors (an include missing)
  are under 0.5% of runs; at least 50,000 files listed. A test that crashes the process (CRASH, with
  the exit or the runner's memory kill at 3,000 MB) or gives no result in 120 s (STALL) counts as a
  failed file and is listed in `meta.json` `incidents`; the rest of its chunk runs in a new process.
- **When**: each successful `build.yml` or "Foafnaut Linux engine" run on main (the newest Linux
  release of main: `build-<sha12>-linux-x86_64` or `-foafnaut-linux-x86_64`; skipped when that commit
  already has a valid run at the pinned commit), six times a day (`11 */4`: repeats show flakiness),
  and `gh workflow run test262.yml -R danbri/factoidal-builds [-f core_ref=wip/x] [-f
  test262_commit=...] [-f shards=8]`. A branch (`core_ref` not on main) is scored in the job summary
  and artifact `test262-result` but not recorded. 8 shards x 4 processes.
- **Records** (branch `wpt-scores`): `runs.csv` row with `suite=test262`; `wpt_commit` holds the
  Test262 commit, `passed`/`denominator` are files, `share_ex_encoding_pct` holds the share without
  the excluded features. `runs/<run_id>/meta.json` (`totals` with `share_ex_features_pct`,
  `excluded_features`, `sections`, `directories` {built-ins/X, language/Y, annexB/Y, intl402/X,
  staging/X, harness: total, passed, runs}, `features`, `top_failures`, `incidents`,
  `since_previous`, `rivals`), `directories.csv`, `features.csv`, `changes.md` (newly passing and
  newly failing files against the previous valid run at the same Test262 commit; a fall over 0.2
  points is DROP). Every run's per-file, per-mode results: `<run_id>.test262.txt.gz` on the release
  `test-results`.
- **Other engines**: `test262-rivals.csv` from test262.fyi (V8, SpiderMonkey, JavaScriptCore,
  QuickJS-NG and the rest, files passed of 53,795): `status=ok` only when test262.fyi ran the same
  Test262 commit, else `other_commit` (not comparable), or `unavailable` with the reason; never fails
  the run. `meta.json` `rivals.directories` has their passes per directory for comparison.
- **Locally**: `lake build bubblepop-test262` (or `leanjs`), a Test262 checkout, then `release-tests/test262.py list --root T
  --out files.json` and `test262.py run --leanjs .lake/build/bin/bubblepop-test262 --root T --files files.json
  --out OUT` (one shard: `--shard k --shards n`), `test262.py score ... --no-rivals`. The core tree
  `third_party/testing/test262` is a 6,301-file subset for tier comparisons (`leanjs test262`), not a
  score.

## 10. Reftests: rendering, scored apart

WPT reftests compare a test page with a reference page as pictures. They are most of WPT's
rendering tests (25,800 under `css/`, 685 under `svg/` at fa649586f3), and the headline score of
sections 1 to 8 gives them **no weight**: wpt.fyi's summaries give a reftest no subtests, and that
score's denominator is Chrome's subtests. So each directory's reftests are a suite of their own,
quoted next to the WPT number, never folded into it: `wpt-reftest-svg` (svg/, first) and
`wpt-reftest-css` (css/). Like wpt.fyi, a reftest is one test: PASS or not.

- **What is run**: every `reftest` item of WPT's manifest at the WPT commit (wpt.fyi
  `/api/manifest?sha=...`) under the directory: HTML, XHTML and standalone SVG/XML documents,
  `==` and `!=` references, reference chains (a reference that is itself a reftest), each test's
  fuzzy annotations and viewport size (800x600 by default). `print-reftest` items are another
  kind and are not run.
- **How a test is judged**: wptrunner's rules (`RefTestImplementation` in
  `tools/wptrunner/wptrunner/executors/base.py`), step for step: references tried in order, a
  chain followed from a reference that holds, PASS when some path reaches a reference with no
  references of its own. Pictures as RGB; per pixel the largest channel difference;
  `maxDifference` and `totalPixels` against the fuzzy ranges (none: identical pixels).
  `reftest-wait` is honoured: the page's time moves in 16 ms steps until a script removes the
  class, for at most 6 s of page time (then TIMEOUT).
- **How a page is drawn**: core's `tests/browser-wpt/reftest-render.ts` on the release's engine
  library: the page loaded as the window and Textnaut load it (`prepareHTML`: sheets, imports,
  images, web fonts), scripts on BubblePopJS, one frame by the engine's CPU raster (op `render`
  with `cpu:true`, `SVGRaster`), Noto Sans and the Hub's fallback fonts from `third_party/fonts`
  (never the bitmap face, which is a diagnostic only: `--bitmap-font`). The pages come from a
  server of the runner on a random port, never wptserve's 8000, so a reftest run can share the
  machine with a WPT run.
- **Rivals**: Chrome, Firefox, Safari and Edge on the same tests at the same WPT commit, from
  wpt.fyi's summaries (`s` = P/F). `reftest-rivals.csv` on `wpt-scores`.
- **Valid**: every shard present, every test has a status, ERROR (the harness: a fetch, the
  runner, a missing picture) under 0.5% of tests. The engine refusing a page is FAIL with its
  message. A CRASH (the drawing process died on a page) or STALL (over 90 s on one page) is the
  engine's defect, as in section 6: listed with its page, never ignored.
- **Records** (`wpt-scores`): `runs.csv` rows with `suite=wpt-reftest-svg` (`passed`/`denominator`
  are tests; `share_ex_encoding_pct` empty; `engine=native-cpu-raster`), `reftest-rivals.csv`,
  `runs/<run_id>/meta.json` (totals, statuses, each rival's share, directories, changes),
  `results.tsv` (every test: status, rivals, maxDifference, totalPixels, ms, message; `.gz` for
  css/), `changes.md` (newly passing and newly not passing against the previous valid run; more
  than 3 newly not passing is DROP), `directories.csv`. Pictures of the tests that do not pass
  (test, reference, and a difference picture: changed pixels red on the faded test) are the
  artifact `reftest-failures-<suite>-<shard>`, kept 5 days.
- **When** (`reftests.yml`, "WPT reftests", in `danbri/factoidal-builds`, script
  `release-tests/reftests.py`): after each "Foafnaut Linux engine" run (skipped when that commit
  has a valid run at the same WPT commit), twice a day, and
  `gh workflow run reftests.yml -R danbri/factoidal-builds [-f suites=svg,css] [-f release=build-<sha12>-foafnaut-linux-x86_64] [-f tools_ref=wip/x] [-f record=false]`.
  The WPT commit is the one of the newest valid full WPT run.
- **Locally**:
  `python3 tests/browser-wpt/wpt-reftests.py run --manifest MANIFEST.json --wpt-root WPT --native-engine libweb-render.dylib --prefix svg/ --out OUT --chrome-summary chrome-summary.json --jobs 3`
  (`--only /svg/painting/` for a directory; OUT/summary.md, OUT/results.json, OUT/failures/).
  A WPT checkout of the directory and its support is enough (a sparse partial clone: `svg/`,
  `css/reference/`, `fonts/`, `common/`, `resources/`, `images/`, `css/support/`).
  `wpt-reftests.py compare --prev A/results.json --cur B/results.json` lists what changed;
  `wpt-reftests.py clusters --results OUT/results.json` groups what does not pass by cause.
- **Planning**: rank failing reftests by root cause (cluster by feature: markers, patterns,
  gradients, text, masking, filters, clipPath, stroke, nested svg and viewBox, use, images,
  animation, scripting), fix the largest clusters, and report before and after per cluster.
  Reftests where Chrome passes and Foafnaut does not come first. Keep the WPT number and the
  Spinal Tap budgets from falling.
  Causes, counts and probes as of 2026-11-22, with the method to repeat them:
  `docs/designissues/2026-11-22-reftest-layout-causes.md`
  (https://github.com/danbri/factoidal-core/issues/747). Before counting a failure as an engine
  defect, check the test picture for the "Partial page" note, and before counting a pass,
  check that the picture is not empty (section 2 of that record).
- **On the Hub**: the Conformance page has a "Rendering (reftests)" section after WPT
  (`passmap-data.py --hub` writes `reftests` into data.json and history.json).

## 11. Semantic-web and data-format suites

The other conformance suites run on the built-in engine (engine `lean`) in `release-tests.yml`'s
suites job, on the same triggers as WPT, and are recorded in `runs.csv` (one row per suite).

- **lean-w3c**: `l4w3c` from the release: `l4w3c-rdf11`, `-rdf12`, `-rdfc10`, `-sparql11`, `-sparql12`.
- **lean-semweb** (since 2026-11-15): the job builds the other Lean runners from the release's
  core commit (build.yml's Lake cache, restore only), runs them through core's
  `tools/lean-scoreboard.sh --only ...` and maps its rows to `l4-*` suites (`SEMWEB_ROWS` in
  `release-tests/release-tests.py`): SHACL 1.0/1.2, ShEx and ShExC, JSON-LD (toRdf, expand,
  compact, flatten, fromRdf, HTML, framing), CSVW, RML modules, RIF Core, RDF 1.2 semantics,
  VC/DID/Data Integrity, xmlconf, XSLT 1.0, Schematron, MathML, JSON Schema, OWL 2 species.
- **lean-xml** (since 2026-11-16; the daily 13:41 run and runs by hand only, about two hours):
  the same way, the scoreboard's XML family jobs (`XML_ROWS`) in two lanes at once: XPath 4.0
  and XQuery 4.0 (`l4qt4` over qt4tests), XSLT 4.0 (`l4xslt4` over xslt40-test), XSD 1.1 Part 1
  (`l4xsd11` over w3c/xsdtests), RELAX NG (spec and compact suites), XInclude, Canonical XML.
  Unsupported dependencies count as other, never as passes. On other runs the job does nothing
  and no row is written.
- **OWL 2 as discrete populations** (`release-tests/owl-populations.py`): the W3C OWL 2 Test
  Cases (`third_party/testing/owl/all.rdf`, 2009-11-18, every case not Rejected: 489 cases, 355
  Approved; W3C Document Licence). One row per population: each of Positive/Negative
  EntailmentTest, ConsistencyTest, InconsistencyTest under the Direct Semantics (`--dl`: RL
  closure, materialisation, tableau refuter) and under the RDF-Based Semantics (`--rdf-based`),
  `l4-owl2-<type>-<direct|rdfbased>`; ProfileIdentificationTest per profile EL, QL, RL
  (`l4-owl2-profile-*`, 418 cases each, since 2026-11-16: the probe's `--profile-id` mode, which
  is the OWL 2 DL species verdict and then the profile's grammar, `OWL/Profiles.lean`, over the
  axioms read back from the RDF graph, `OWL/StructureFromRdf.lean`; a graph the reader cannot
  place is `undecided` and counted as other; a core commit whose probe lacks the mode gives
  `valid=false` with that reason); species (`l4-owl2-species-all|dl|full-only`). The denominator is always
  the population's full official count; `names_run` = units decided (pass + fail); meta.json
  has the split by status (Approved, Proposed, Extracredit, none).
- A row is valid when the scoreboard gave it status `ok` with tests found, or (OWL) the probe
  reported exactly the official count. The F* rows (engine `fstar`) stop at 2026-11-15 15:00Z;
  the Hub's "Semantic web and data formats" section shows a suite with no Lean row from its
  last F* row, marked stale, never as current.
- The F* suites with no Lean row: `rdf12c14n` (covered inside `l4w3c-rdf12`), the three SHACL
  1.2 rules sub-suites `shacl12_rules_syntax`, `_wellformed`, `_stratification` (the Lean
  rules runner reports one total), and the F* RL-closure runs over the OWL profile catalogs
  (`owl2_profile_el`, `owl2_profile_ql`, `owl_rl_positive_entailment`), replaced by the
  populations.
- A check of the workflow without recording: `gh workflow run release-tests.yml -R
  danbri/factoidal-builds --ref BRANCH -f suites=w3c -f force=true -f record=false`.

### 11.1 The Data and documents page and its records

The Hub page `docs/web/hub/specs/` ("Data and documents conformance",
https://danbri.github.io/factoidal/web/hub/specs/) shows these suites: one row per technology family
with its headline, then specification and version, then suite (population, test type), then
sub-manifests and history. Its views: families, every specification and version as one table, and
what needs attention (invalid, partial, stale, runners with no recorded rows).

- **Mapping, never renaming.** `tests/browser-wpt/spec-suites.json` says what each suite id of
  `runs.csv` measures: `family`, `spec`, `specUrl`, `version`, `technology`, `testType`,
  `population`, `manifest`, `source` (with `kind`: official, subset, authored), `engine`, and
  `headline` (counted in the family headline; false for a population inside another headline
  suite, such as `l4-rdf12entail` inside `l4w3c-rdf12`). Lean suites that carry on an F* suite say
  `continues`; every F* suite says `supersededBy`, `coveredBy` or `replacedBy`. History keeps its
  ids. Families whose populations overlap (OWL 2) are `additive: false`: no summed count.
- **Normalised record** (`tests/browser-wpt/specs-data.py`, schema
  `docs/web/hub/specs/data.schema.json`), one per runs.csv row: suite, family, spec, version,
  technology, testType, population, manifest, source, sourceKind, engine, platform, commit, run,
  finished, trigger, total, passed, failed, decided, undecided, status, reason, stale, staleReason,
  current, headline, workflow. **status**: `valid` (valid and every test decided), `partial`
  (valid, fewer decided than the population; reason gives the count), `invalid` (runs.csv
  valid=false; reason is its invalid_reason; the newest valid run is kept as `lastValid`).
  **stale**: every F* row (runners stopped 2026-11-15), and a Lean suite with no row for 36 hours
  before the newest Lean row. Headlines count current, not stale, headline suites; invalid runs
  are never counted.
- **Sub-manifests.** `release-tests.py` keeps l4w3c's score line of each included manifest in
  `meta.json` `parts`; the mapping's `parts` rules classify them (SPARQL Query, Update, result
  formats, protocol, federation, entailment, service description, Graph Store; RDF N-Triples,
  N-Quads, Turtle, TriG, RDF/XML, semantics), so SPARQL 1.1 and 1.2 split by specification.
- **Files** (branch `hub-data` of danbri/factoidal-builds, `specs/`, written by its "Conformance
  data" workflow; copied into the site by danbri/factoidal "Deploy to GitHub Pages"):
  `data.json` (current record per suite, family headlines, sources, measurements not yet
  recorded, unmapped ids), `history.json` (every row per suite as `[finished, commit, passed,
  decided, total, status]`, and each additive family's headline per recording run) and
  `records.csv` (every record, flat). Ad hoc questions: any CSV tool over `records.csv`, for
  example `duckdb -c "select family, spec, version, max(finished) from 'records.csv' where
  status <> 'valid' group by all"`.
- **Adding a suite**: (1) its runner and row in release-tests (`SUITES`, `SEMWEB_ROWS` or the OWL
  populations), with the full official population as the denominator; (2) an entry in
  `spec-suites.json` with every field above, `continues` if it carries on an older id, and a
  `parts` key if it is an l4w3c umbrella manifest; (3) `node --test tests/hub/specs_test.mjs`
  (checks the mapping) and `python3 tests/browser-wpt/specs_data_test.py`. A suite id in runs.csv
  that the mapping lacks is listed in `data.json` `unmapped` and on the page's "Needs attention"
  view. Runners with numbers but no recorded rows (the Xalan corpus run of `l4xslt4 --xslt10`,
  the `xs` family of `l4qt4`) go in `unrecorded`, with the write-up and date, and are never shown
  as a score.
- **Tooling.** Charts are the Conformance page's own SVG line chart; d3 and Observable Plot (ISC,
  vendored in `third_party/observable`) are there if a view needs more. No server-side
  dashboards: Grafana is AGPL-3.0 (relicensed 2021-04-20, grafana/grafana 8db3eb90ae) and needs
  a server; Perses and Superset (Apache-2.0) need servers too. DuckDB-Wasm (MIT) for in-page
  queries is a later option behind a click, since it loads a multi-megabyte Wasm module.
