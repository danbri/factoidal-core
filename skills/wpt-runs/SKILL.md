---
name: wpt-runs
description: How Foafnaut's Web Platform Tests score is measured, recorded and reported, and the other conformance suites with it. Full measured runs only (no sampled scores), BubblePopJS only, cloud runs on every release and four times a day, validity rules, runs.csv and per-run metadata. Use before running WPT, quoting a WPT number, comparing with other browsers, planning WPT work, or changing the test workflows.
---

# WPT runs: the testing regime

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

Invalid runs are kept, with `valid=false` and the reason, and never plotted or quoted. A rival run that
reports only part of WPT (Ladybird on wpt.fyi: 35,966 of 94,406 names) is left out of comparisons.

## 3. When runs happen (cloud, `danbri/factoidal-builds`)

- **Every Factoidal release on main**: when `build.yml` publishes a commit's releases.
- **Every browser release**: a daily wpt.fyi check. A new stable version, or a new aligned WPT commit,
  records the rivals and runs Foafnaut's latest release at that WPT commit.
- **At least four times a day** on a schedule. Each run picks the newest main commit whose releases are
  complete, and may wait up to about an hour for one that is finishing. It pushes a snapshot branch
  `wpt-snap/<YYYYMMDD-HHMM>-<sha12>` in factoidal-core first, so the source and tool used stay fixed. A
  run on an unchanged commit is a repeat (`repeat_of`): repeats measure flakiness.
- **Platforms**: scored runs on Linux, sharded wide (many parallel runners). macOS arm64, the shipping
  platform, runs once a day and on each release as a cross-check. Differences between the two on one
  commit are bugs to find (fonts, timing, platform code).
- The other Factoidal conformance suites that have runners run on the same triggers, in parallel.
- No scheduled sampled job. The old daily sample (`wpt-score.yml`) was disabled and its schedule removed
  on 2026-11-13. Sampling remains only as a manual smoke check, never recorded as a score.

Workflow names, the results branch and file paths: see the README of the results branch in
`danbri/factoidal-builds` (filled in below once the workflows land).

## 4. Records

- `runs.csv`: one row per run, append-only. Run id, times, trigger, suite, engine, platform, factoidal
  commit and its dates, snapshot branch, release tag, WPT commit, names run and total, passed,
  denominator, share, share without encoding, outcome counts, server failures, valid and reason, kind
  (full / sample / differential), shards, wall minutes, workflow run URL.
- `rivals.csv`: WPT commit, browser, version, wpt.fyi run id, passed, share, names reported, partial.
- `runs/<run_id>/meta.json`: everything above plus build-info, runner and tool versions, list hashes,
  why that build was chosen, the per-directory table, and a link to the full result JSON.
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

## 7. Cloud builds

- `build.yml` takes `core_ref` (branch, tag or commit) to build a branch. A build takes about 1.5 h.
- Builds of different refs must not cancel each other. The concurrency group is per ref (fixed
  2026-11-13): before that, a new dispatch or the hourly poll cancelled the one pending build. Check the
  queue before dispatching, batch changes into few builds, and never cancel another agent's run.
