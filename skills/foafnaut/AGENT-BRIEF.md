# Foafnaut: the standard agent brief

Every agent working on Foafnaut reads this first, then `skills/foafnaut/SKILL.md` (code map, builds, traps) and
`skills/local-lean-rules/SKILL.md` (Lean soundness rules). A task brief adds only the task.

## What the project is

Foafnaut is a web browser whose engine, BubblePopKit, is written in Lean 4. The point of writing a browser in Lean is
trust: what the browser does with web content, and what it says about itself, is decided by code that can be read,
checked and proved, not by unverified glue. The aim is a browser that is competitive on the Web Platform Tests and
that is fast, efficient, private, accessible, international and secure, with those qualities weighted equally with
standards conformance.

## The core rule: decisions in Lean, the host moves bytes

- Everything that decides something about web content is Lean: parsing, style, layout, text, paint, scripts (BubblePopJS,
  BubblePopWASM), networking policy (origins, CORS, redirects, address checks), isolation (frames, workers, sandbox),
  find in page, accessibility, and anything else a page or a user relies on.
- **The browser's own words are Lean too.** Internal pages (`about:foafnaut`, `foafnaut:` pages, error and refusal pages,
  version answers) are written by Lean. The engine's identity (version, commit, build time, hygiene counts) is compiled
  into the engine. Facts only the host knows (runtime, platform, file hashes) reach Lean as data and are shown labelled as
  reported by the host. If the two disagree, the page says so.
- The hosts (`run_html.ts`, `native_window.m`, the Hub's `.mjs`) open windows, pass input, fetch bytes, run GPU commands
  that Lean emitted and show what Lean drew. They hold no layout, policy or page-writing logic.
- No JavaScript copy of Lean logic, not even a "fallback". A missing engine op turns the feature off.
- No host drawing cheats: never draw page content with host elements (DOM, AppKit, host iframes or video).
- No Foafnaut-only page APIs. Pages see the web platform.

## Proof and hygiene

- No `sorry`, user axioms, `native_decide`, `unsafe`, `@[implemented_by]` or new `partial def`.
  `labs/demos/foafnaut/LabHygiene.lean` (`lab_ratchet`) must still compile: counts may only fall.
- Linux CI runs a tail-recursion gate (`tools/lean-tail-recursion-audit.py --gate`): prefer tail-recursive or structural
  code over allow-list entries.
- Security decisions come with theorems where they are cheap, and the rest is listed as open in the design record.
- Crashes, hangs and resource exhaustion are safety properties: work on page-controlled input has a proved bound and
  a defined refusal at the bound, and a crash in a test run is fixed before the subtests around it
  (`skills/local-lean-rules` section 11).
- Say exactly what is proved, and what is only tested.
- Engine work checks the [theorem pipeline](../theorem-pipeline/SKILL.md): state the theorem first,
  link its item issue, and report theorem names, `#print axioms`, assumptions and tests.
- Text in scripts you cannot read (Arabic, Indic, Thai, CJK, Mongolian, emoji sequences, mixed scripts) is checked
  by machines against independent references, never by eye; where suites are too coarse, write small cases of our
  own: [`i18n-layout-testing`](../i18n-layout-testing/SKILL.md).

## Performance

- A page that doesn't use a feature pays nothing for it. Give before/after timings in every hand-back.
- Hot paths get cost tests that fail if they turn quadratic.
- Speed is judged as a person feels it: report p50, p95, p99, max and the spread over runs, never only a mean, and
  treat a worse tail as a regression. Metrics, targets and workflows:
  [`perceived-performance`](../perceived-performance/SKILL.md).

## Working on the shared Mac

- Commits are authored by Dan Brickley <danbri@danbri.org>, with no Co-Authored-By or session trailers.
- Work in your own worktree on a `wip/` branch. Push it after each passing step. Open a PR; don't merge or push to main
  unless the brief says so.
- Run `tools/premerge.sh` before pushing to main (about 15 s; `--with-lean` adds the lake build, tail-recursion gate and
  dataflow drift test, `--with-engines` the whole test.sh).
- One Lean build at a time: use the build lock (`~/working/foafnaut-tools/leanlock.sh`).
- Cap the memory of every Lean process, proof checks above all: `ulimit -v` (or an equivalent cap) around `lake`/`lean`,
  and check one theorem group per process. On 2026-11-15 one proof file of 116 theorems reached 17 GB and filled swap
  and disk until the Mac rebooted. Tools that may start a build quietly (for example `tools/dataflow-inventory.py`)
  count as Lean builds: take the lock.
- Cloud builds (`danbri/factoidal-builds`, `build.yml`, `core_ref=<branch>`): the first test result (`foafnaut-host-tests`)
  comes about 35 minutes after dispatch, the whole run about 1.5 h, more when macOS runners are busy. Check the queue
  first, batch changes into few builds, never cancel another agent's run, and log each dispatch. Caches, cold builds
  and timing records: [`ci-caching.md`](ci-caching.md).
- **Merge rule** (owner, 2026-11-16): a PR merges when the **Linux jobs** of its `build.yml` run are green (dispatch
  `core_ref=<40-hex PR head>`: a commit not on main runs Linux jobs only, and the run's conclusion is then the Linux
  verdict), `tools/premerge.sh` passes, and the change carries its theorems. The macOS jobs (`lean-macos`, the
  `foafnaut` bundle with the native `test.sh`, `foafnaut-macos.yml`) are not a merge requirement: they run for main's head
  in the Mac release lane (`mac-release.yml`), nightly on main and on request (`-f macos=true`, one at a time). When you
  start waiting on the merge gate of a PR you mean to merge, label it `landing` (remove it when merged or abandoned):
  the Mac release waits up to 30 min for it. A nightly macOS failure on main (issue labelled
  `nightly` in factoidal-builds) is fixed or reverted the next morning. Runner, nightly and the overnight Mac runner:
  [`ci-runner`](../ci-runner/SKILL.md).
- WPT: follow [`wpt-runs`](../wpt-runs/SKILL.md). Full measured runs only, BubblePopJS, one WPT run per machine (the
  runner refuses a taken port 8000; wait, never kill). Report subtests before and after, plus a regression check.
- Coordination lives in `/Users/danbri/working/foafnaut/fncg` (it survives reboots): `coordination.log` (append-only;
  one line per START, DISPATCH, RESULT, MERGED, NOTE or RELEASE, with a prefix naming you) and `status.md` (open work,
  owners, PRs, decisions waiting on the owner). Read the log's tail and `status.md` before each stretch of work and
  every few PRs; obey any OWNER DECISION or pause found there. `/tmp/foafnaut-coordination.log` is only a symlink to
  the log (recreate it after a reboot).
- Timing measurements on the Mac hold the timing lock (`fncg/locks/`, or `flock` on `/tmp/foafnaut-timing.lock`) so two
  agents never measure at once.
- A run that floods the terminal is a failure: the log gate (`docs/web/hub/foafnaut/log-gate.mjs`) names the message;
  fix the cause, never hide it.
- Never kill or signal processes you didn't start. Never touch other agents' worktrees.
- Disk is tight: keep scratch small, delete `.lake`, worktrees and downloaded engines when done, check `df -h /` before
  any build, and stop and report below 4 GiB free. A full disk rebooted the Mac on 2026-11-15.
- After a session ends, an agent stops, or the Mac reboots: check disk and save unpushed work first
  ([`cleanup-and-recovery`](../cleanup-and-recovery/SKILL.md); `tools/disk-audit.sh`, `tools/branch-audit.py`).
- Background waits (watcher loops, `pgrep -f`, `until grep -q`, CI polling) must end: wait on a PID, never a
  `pgrep -f` pattern that is also in the watcher's own command line; add a deadline; stop your own watchers when done
  ([`background-watchers`](../background-watchers/SKILL.md)).
- Codex workers: the recipe and brief rules are in [`codex-claude-interop`](../codex-claude-interop/SKILL.md).
- Releases are never replaced: a published release stays as it is (packaged Textnaut pins its bytes). Publish a new one.
- Don't sit idle. Commit early and often.

## Words

- User-facing text says "the built-in engine", not "Lean". Name Lean only where the language is the subject.
- Names: Foafnaut (browser), Textnaut, BubblePopKit (engine), BubblePopJS, BubblePopWASM.
- Don't use the word "honest". Plain British English.
- Nothing is out of scope: unworked areas are "later", "not yet" or "reported separately", each with a plan issue, and
  headline numbers count everything ([`scope-and-sequencing`](../scope-and-sequencing/SKILL.md)).
- GitHub: technical content only; never quote the owner's chat; no links to upstream Lean issues; never suggest
  contacting people outside the project.
- Real web pages are copyright. Public pages may be vendored as zipped snapshots, as fair use for testing, under
  `third_party/realpages/` in **danbri/factoidal-builds** (not core), each with provenance (URL, fetch time, headers,
  licence or "copyright, vendored as fair use for testing", attribution). Public pages only. Also probe live.
  Minimal repro fixtures in core are original constructs.
- The 90% WPT and 80% Test262 thresholds are Apple's own rules for alternative browser engines in the EU (the
  Commission's DMA enforcement made Apple allow other engines; the criteria are Apple's). Say "Apple's bar", never
  "the EU bar".
- Lean first: F* is not built in CI; don't add F* work without the owner asking.

## Hand-back

What changed (PR, commits), what was verified (tests, counts, timings, cloud build), what wasn't and why, open security
items. Don't claim anything you didn't run.
