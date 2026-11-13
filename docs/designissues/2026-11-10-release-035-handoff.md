# Handoff: release 0.35.0 and the work of 2026-11-09 and 2026-11-10

For a new session with no memory of this work. Read this file, then
https://github.com/danbri/factoidal-core/issues/389 (release 0.35.0, the nine steps), then
`skills/foafnaut/SKILL.md` and `skills/npm-release/SKILL.md` ("One owner per release").
Written 2026-11-10 about 12:15 UTC. Check each line against `git log origin/main` and the
issue before you act.

## Quick start (10 minutes, no build)

1. `git fetch origin && git log --oneline -8 origin/main`
2. Read issue 389 and its comments. The release manager is whoever the owner names next; the
   session that wrote this file stopped to save credit.
3. Branch for work: `claude/foafnaut-perf-bottlenecks-7hpt38` in `factoidal-core` (one commit
   ahead of `main`: the audit of the lab modules and the corrected status note, plus this
   file and `docs/releases/0.35.0/`). It has no PR yet.
4. Toolchain on a cloud VM: `export PATH="$HOME/.elan/bin:$HOME/.deno/bin:$PATH"`; `lake` only
   from `formal/lean4`. Build one module or one executable, never everything
   (`lake build leanjs L4Factoidal.JS` 3 minutes; `lake build WasmVM wasmvm-spectest` 2 minutes;
   the native engine `bash labs/demos/foafnaut/build-web-render.sh --native` 20 minutes).
5. Cost rules that this session learned late: give a subagent one commit-sized task with the
   files named; do not poll CI, subscribe to the PR; do not paste large tool output; a push to
   a PR branch restarts a 45-minute Lean build, so batch commits.

## On main now (all merged 2026-11-10)

- https://github.com/danbri/factoidal-core/pull/382: BubblePopJS stage B, number conversions
  proved equal to their specifications, five repairs, the corpus harness, the plan.
- https://github.com/danbri/factoidal-core/pull/384: WasmVM fixed-width SIMD; the Hub GPU
  surface keeps its first error.
- https://github.com/danbri/factoidal-core/pull/387: WasmVM GC proposal; `build-engines.sh`
  compiles `Prim/FloatOfNat`; the record on theorems as contributions.
- https://github.com/danbri/factoidal-builds/pull/19: the daily WPT score job (02:47 UTC).
  First manual run passed on macOS: https://github.com/danbri/factoidal-builds/actions/runs/42809587304

Measured: Test262 (6,301 files of `test/language`) 5,633 pass; six library workloads 6 of 6
right, 8.4 times QuickJS-NG (geometric mean, one Linux VM); WebAssembly spec suite 61,698
pass, 0 fail, 3,655 not run. Records: `docs/designissues/2026-11-09-foafnaut-perf-exploration.md`
(section 6.6), `docs/designissues/2026-11-07-wasmvm-engine.md` (sections SIMD and GC).

## Release 0.35.0: state of each step of issue 389

1. Merge PR 387: done (`41a1aaeab`).
   **Open:** confirm that the browser sets build. A build of `41a1aaeab` was dispatched at
   11:56 UTC in `danbri/factoidal-builds` (workflow `build.yml`). Look at its job
   `foafnaut-engines`: it failed on the commit before with a missing `FloatOfNat.olean`; the
   repair was not run anywhere before the merge. If it fails again, read the log tail first.
2. Package Textnaut and the developer proxy: **not started in the tree.** An agent was given
   the task and stopped on a rate limit with nothing saved. The brief: `build-executables.sh`
   also makes a compiled `textnaut` and a `devproxy/` directory, each with a start check; the
   npm launcher gets `foafnaut --text` and `foafnaut --devproxy` with tests; a patch for the
   file list of the set `foafnaut-darwin-arm64` in the build repository. None of it can be run
   to the end on Linux; the owner checks on the Mac.
3. Change log and version: **drafted, not applied.** `docs/releases/0.35.0/changelog-0.35.0.md`
   (three lines, checked against the import closure of `Wasm/Dispatch.lean`),
   `browser-notes.md` (65 lines), `evidence.tsv` (a commit for each line), `not-included.md`.
   To apply: insert the entry at the top of `npm/factoidal/CHANGELOG.md`; set 0.35.0 in
   `npm/factoidal/package.json`, `package-lock.json` (two places), `npm/factoidal/lib/version.mjs`.
4. Browser release record and status note: not started.
5. Release commit: **not chosen.** The owner waits to be told when issue 389 names it; the
   owner then runs the Mac checks (the commands are in a comment of this session's chat and in
   step 6 of the issue).
6. to 9.: not started.

## Other open items

- https://github.com/danbri/factoidal-core/issues/390: 29 `unsafe` definitions and 29
  `@[implemented_by]` in `labs/demos/foafnaut` (the issue text says 30 `unsafe`; 29 is right,
  one match was a comment). The audit baseline is on the branch, not yet on `main`.
- https://github.com/danbri/factoidal-core/issues/388: theorem-only tasks for new contributors.
- https://github.com/danbri/factoidal-core/issues/378: BubblePopJS plan; defects 3 to 7 open
  (a prepared patch for `lastIndexOf` and `toString(radix)` was never applied; `(35).toString(36)`
  prints `*` today).
- https://github.com/danbri/factoidal-core/issues/385 and /386: SIMD and GC limits.
- Spinal Tap page on the Hub: works with no GPU, fails on the GPU path; cause unknown; the
  next Hub deploy shows the first error text.
- Two patches proposed for core, not applied: `docs/releases/0.35.0/0001-*.patch`
  (`wpt-score.py`: stop after three failed starts; `--engine wasm`) and `0002-*.patch`
  (`build-web-render.sh`: a Linux engine library).
- Commits from other sessions on `main` carry assistant attribution trailers (for example
  `226c14a0a`, `996f6f5db`), against iron rule 13. The owner has not decided what to do.
- Owner's order for WasmVM after GC: a speed pass. Not started.

## Added 2026-11-13: items that were only in the chat of the cloud session

**The release part of this record is history.** The release shipped after the handover: npm has
`@factoidal/core` 0.35.1 (2026-11-11; 0.35.0 is not on npm) and 0.36.0 (2026-11-12, `latest`). Main is at
version 0.36.0 (`2fd7fc4d3`). The section "Release 0.35.0: state of each step" above describes
2026-11-10 and is not current. https://github.com/danbri/factoidal-core/issues/389 (release 0.35.0)
was still open on 2026-11-13.

The record above was short of these. Each was said to the owner but not written here.

- **Release role.** The cloud session released the release manager role for 0.35.0 on 2026-11-10:
  https://github.com/danbri/factoidal-core/issues/389#issuecomment-6768338953 (handover comment).
- **WasmVM speed pass.** Owner order, 2026-11-10: "Simd then gc then speed". SIMD and GC are on main
  (https://github.com/danbri/factoidal-core/pull/384, https://github.com/danbri/factoidal-core/pull/387).
  The speed pass is not started. No measurements exist for it.
- **BubblePopJS small defects, prepared and not applied.**
  `docs/releases/0.35.0/0003-bubblepop-lastindexof-and-radix.py` is an edit script for
  `lastIndexOf` with `fromIndex` and `Number.prototype.toString(radix)`. It was written against the
  tree of 2026-11-10 and was not built or tested. Also open: `s += v` on a global in the VM loop, and
  typed array element access with no string key.
- **Wrong text to correct.** https://github.com/danbri/factoidal-core/issues/390 (unsafe in lab
  modules) says 30; the audit baseline is 29. A comment on
  https://github.com/danbri/factoidal-core/issues/378 (BubblePopJS plan) says "07:00 UTC" for a time
  that was wrong.
- **Owner decisions still open.** (1) A full daily WPT run by a job matrix, one job for each WPT
  directory. (2) Commits `226c14a0a` and `996f6f5db` on main carry attribution trailers from other
  sessions, against iron rule 13. (3) Whether the CPU graphics path stays on by default.
- **Deferred by the owner.** https://github.com/danbri/factoidal/issues/1291 ("consider at some
  point"). The Spinal Tap GPU failure needs the next Hub deploy before it can be checked.
- **WPT.** Daily scores: branch `wpt-scores` of `danbri/factoidal-builds`. Ranked causes for `css`
  and `html`: https://github.com/danbri/factoidal-core/issues/429. The treemap of 2026-11-13 is a
  private page of the owner, not in the repository; its data came from the artifact
  `wpt-score-pinned-bubblepop` of https://github.com/danbri/factoidal-builds/actions/runs/43199421148
  and the wpt.fyi summaries at WPT commit `fea36e49ddda`.
- **Linux WPT runs.** Branch `claude/foafnaut-perf-bottlenecks-7hpt38`, commit `3c255e209`, makes
  `libweb-render.so` on Linux. Not yet checked by a run.
