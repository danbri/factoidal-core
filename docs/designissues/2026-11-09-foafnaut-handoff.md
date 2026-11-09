# Foafnaut handoff, 2026-11-09

For the next agents (Codex and Claude) who arrive with no memory of this work. Start with
[skills/foafnaut/SKILL.md](../../skills/foafnaut/SKILL.md), which has the code map, the commands
and the traps. This record holds what changes quickly: state, work in flight, next work.

Everything below is at 2026-11-09, about 14:45 UTC, `main` at `6f08a9824`, unless a line
says otherwise. Check it before you act: `git log origin/main`, the coordination log
`/Users/danbri/working/sandbox/october/tpac/depmap/cache/foafnaut-coordination.log`, and
`git ls-remote origin 'refs/heads/wip/*'`.

Owner, 2026-11-09, verbatim: "put some work into making sure we have skills and docs in the
repo for contributing to foafnaut that are UP TO DATE with the codebase and OKRs and
issues, and not painfully misleading. We may run out of Claude credits before then, so it
could be a handoff for a few days. Documentation is everything."

## Where things stand

- OKRs: batch 1 https://github.com/danbri/factoidal/issues/1245 (daily releases, frame time, suites)
  and batch 2 https://github.com/danbri/factoidal/issues/1296 (approved
  2026-11-09: standards, security, privacy, performance of equal weight; milestones to 90%
  of WPT). The first comment of 1296 assesses batch 1 and lists the carried key results.
- Page scripts: BubblePopJS on the desktop, QuickJS-NG in WasmVM on the Hub
  (`WebRenderScript.defaultEngine`). Strict mode is the default.
- Latest named release record in the repository: `labs/demos/foafnaut/releases/foafnaut2525-2026-11-07-3.md`.
- Latest Pages deploy in the log: engine `build-30f4fe34508d-foafnaut-web`, `main` at
  `6f08a9824` (14:26 UTC).
- Bleeding-edge app (`cache/bleeding/foafnaut`): `BUILD-INFO.json` says `dd0b3ac2f`, built
  06:47 UTC. It is older than `main`.
- Scores are in `docs/web/hub/foafnaut2525-status.md` (8 November) and the scoreboard in
  `labs/demos/foafnaut/releases/`. Read the suite, denominator and date beside each.

Disk is the limit now: 2.8 GB free at the time of writing. Several builds wait for space.

## In flight

Many of these branches are only in local clones at `~/working/factoidal-<name>` and are
not on origin. A lost laptop loses them. `CLAUDE.md` says every agent pushes after each
step that passes; these have not.

Lead session (web-render-overnight):

- Queued bleeding build in `source/factoidal-xslt-pages`, branch `wip/1268-svgtext-geometry`
  at `ec2ceaba3`: SVG text glyph geometry with no path text, splash start page `start.html`,
  Settings filled-box ticks, built-in wording. It lands on `main` when
  `build-executables.sh` passes. Pushed branch: `wip/1268-splash`.
- https://github.com/danbri/factoidal-core/issues/368 (combining marks from a fallback font
  over a base glyph from another font): `wip/showoff` in the merge lane.
- Next speed work (figures from the lead session; not re-measured for this record): a press
  frame costs about 17 ms (scene rebuild), and a page text change lays out the whole
  page again, about 40 ms. Tracking https://github.com/danbri/factoidal/issues/1268
  (responsiveness and frame time).

Other sessions, from the log (branch and clone name, what it does):

- `wip/shaders` (`factoidal-shaders`): frame pacing, shader gallery with ray marcher. Wasm merge
  build waits for disk.
- `wip/emoji` (`factoidal-emoji`): colour glyphs, COLR. https://github.com/danbri/factoidal/issues/1276.
- `wip/liberal-svgcheck` (`factoidal-liberal`): liberal mode as the default (strict for
  tests), console levels. Claimed 14:20 UTC.
- `wip/dprfix` (`factoidal-dprfix`): HiDPI. Layout in CSS pixels at device pixel ratio 2. Single-module
  check passed 14:41 UTC; no build yet.
- `wip/bpwasm` (`factoidal-bpwasm`): BubblePopJS on the Hub. Found that Nat literals over 2^31
  are heap objects on wasm32 (`tools/wasm32-nat-literals.py` on that branch).
- `wip/realperf` (`factoidal-realperf`): real-site layout speed.
- `wip/frames` (`factoidal-shadowframes`, iframe documents), `wip/encoding100` (WPT encoding),
  `wip/workers` (Dedicated Workers), `wip/wptserve` (WPT through the real server, done
  and not pushed), `wip/cryptosec` (crypto boundary review), `wip/foafprove` (verified FOAF
  layout kernel), `wip/haclweb-2` (HACL\* for `crypto.subtle`).
- Open PR: https://github.com/danbri/factoidal-core/pull/370 (Canvas chart status text).

Codex is scheduled for the HTML parser failures (batch 1 KR 3.1, 3.2: tree construction 10
fail, tokenizer 6 fail, numbers in the status note) after its usage limit resets at 2026-11-10
10:07. Test it first with a one-line `codex exec`.

## Do next

**First for real sites: network access from page scripts,**
https://github.com/danbri/factoidal-core/issues/374 (`fetch`, `XMLHttpRequest`, script-inserted
scripts, and CORS enforced by the engine). The prototype and acceptance page is
`labs/demos/foafnaut/pages/search.html` (Open Index Search): in Chrome it answers from seven open
APIs; in Foafnaut its script runs and every source fails. `network_gaps_test.ts` is the expected
failure. When search.html shows results, move it to "Start here" in `tools/build-demo-pages.py`.

1. Read the log and land what passed. Land in the order the merge lane shows.
2. Press frame cost and text-change layout (see above). Use `frameWork` counts and a
   cost test (batch 2 KR 4.3, 4.5).
3. HTML parser KR 3.1, 3.2 (Codex).
4. Whole-suite WPT score on BubblePopJS (batch 2 KR 1.1, `tests/browser-wpt/wpt-score.py`).
5. Make CI run what `test.sh` skips (below).

## Known gaps in the test path

- Performance state and branches in flight: [2026-11-09-bubblepop-perf-handoff.md](2026-11-09-bubblepop-perf-handoff.md).
- Lean on 32-bit Wasm is unsupported upstream; known faults, fixes and our workarounds are in
  [2026-11-09-lean-upstream-wasm32.md](2026-11-09-lean-upstream-wasm32.md).
- CI does not run `sweeps.sh`, the input queue test, QuickJS script tests or the page GPU window
  check. `test.sh` runs before the window library exists and with no guest. Evidence:
  https://github.com/danbri/factoidal-builds/actions/runs/42620085179 (log of the foafnaut job).
  Fix: build the library before `test.sh`, and fetch or build the guest in that job.
- `sweeps.sh` calls `timeout 600`. A macOS runner has no `timeout` unless coreutils is
  installed. The fix above needs `perl -e 'alarm shift; exec @ARGV'` there. Not changed in this landing.
- The Hub link check and the other `hub_*_check.mjs` scripts run by hand, before a deploy.
- `labs/demos/foafnaut/pages/manifest.json` still gives "does not execute scripts" as the `appRefused`
  reason of several pages. The field's only effect is that `native_html_bytes_test.ts`
  skips those pages, because that test has no script host.

## Open decisions for the owner

- Close https://github.com/danbri/factoidal/issues/1271 (desktop window refused page
  scripts)? Scripts now run on the desktop; `bubblepop_pages_test.ts` and
  `native_html_scripts_test.ts` check it.
- Automatic bleeding-edge rebuild: approved by the owner (own checkout, normal queue lane, no
  pushes to main, swap only on pass). Not set up yet.

## Not checked for this record

- The frame cost figures above.
- `labs/demos/foafnaut/SVG_README.md` line by line (only searched for SVG text refusals; none found).
- Codex credit state.
- The dated notes under `docs/web/hub/web-platform/foafnaut/notes/` (left as written).
