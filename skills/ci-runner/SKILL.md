---
name: ci-runner
description: The factoidal-builds merge gate (Linux jobs), the nightly macOS run and its issue, and the overnight self-hosted GitHub Actions runner on the owner's Mac (start, stop, logs, removal, safety rules). Read before dispatching build.yml for a merge, when a nightly issue appears, or when touching the Mac runner.
---

# CI gate, nightly macOS and the Mac runner

Owner decision 2026-11-16: macOS runner starvation held merges for hours (a release waited from 07:41 to about
12:50 UTC), so merges are gated on the Linux jobs and macOS runs on main, nightly and on request, partly on an
overnight runner on the owner's Mac. The code is in `danbri/factoidal-builds`: `.github/workflows/build.yml`,
`foafnaut-macos.yml`, `mac-runner-check.yml`, `scripts/resolve-macos.sh`, `scripts/mac-runs-on.py`,
`scripts/heavy-step.sh`, `scripts/install-elan.sh`, `scripts/nightly-report.sh`, `scripts/mac-runner/`.

## Merge rule

A core PR merges when:

1. its `build.yml` run is green. Dispatch it on the PR head commit:
   `gh workflow run build.yml --repo danbri/factoidal-builds -f core_ref=<40-hex PR head>`.
   A dispatch naming a commit runs the Linux jobs only (`lean`, `lean-wasm`, `foafnaut-engines`,
   `foafnaut-host-tests`, `web-gates`, `publish` (which publishes nothing for a branch), `metrics`); `lean-macos` and
   `foafnaut` show as skipped, so the run's conclusion is the Linux verdict;
2. `tools/premerge.sh` passes on the rebased state;
3. the engine change carries its theorems.

macOS is not a merge requirement. Ask for it with `-f macos=true` when the change is macOS-specific (the native
window, `native_window.m`, `libweb-render.dylib`, Metal paths); `foafnaut-macos.yml -f branch=true` still builds a
branch's macOS engine on request.

What runs macOS:

- **the Mac release lane** (owner rule 2026-11-16: for all tangible progress there is always a Mac build of main
  done or building). `mac-release.yml` checks (every 15 minutes, see "Poll triggers" below) whether main's head
  has a Mac release
  (`build-<12 hex>-foafnaut-darwin-arm64`, what `foafnaut --update` installs). When it has none and no lane run is
  waiting or building it, it dispatches `build.yml` with an empty `core_ref`, into the concurrency group
  `build-factoidal-main` (with the hourly poll): one running run and the newest pending one. A pending run resolves
  main's head when it starts, so a newer main replaces the pending build and never cancels the running one. The runs
  are named `core main (Mac release lane...)` in the run list. If the Mac build of main's head fails, the lane
  waits for a newer main, the nightly run or 6 hours rather than retrying every poll;
- the **nightly** run (cron `41 2 * * *`, 02:41 UTC): main's head with every job, released or not, in its own
  concurrency group;
- `foafnaut-macos.yml` (engine only) every three hours on main, one at a time;
- **on request**: `build.yml -f macos=true` and `foafnaut-macos.yml -f branch=true` share one group,
  `build-factoidal-macos-adhoc`: one ad-hoc macOS build at a time in the repository, and a newer request replaces a
  waiting one (check the queue first; log it).

A dispatch that names a commit runs the Linux jobs only, **also when the commit is on main** (a merge check of a main
commit used to queue two macOS jobs of an older main in front of the release). Runs show their core ref in the run
list (`core <ref>`, `+macOS` when asked).

### The macOS budget

GitHub runs 5 macOS jobs at a time for the account (a concurrent limit, not a daily one), first come first served.
Main's Mac release lane holds 1 slot (its two macOS jobs run one after the other), the nightly run 1 (02:41),
`foafnaut-macos.yml` main 1, ad-hoc requests 1 at most. The macOS WPT run of `release-tests.yml` (4 shards, after
each Mac release and at 13:41) and the `exe.yml` check also queue on the same slots; they come after the release
they test, so they don't hold it up, but a burst of them delays the next one. The owner's Mac runner (below) adds a
sixth slot overnight when it has 12 GiB free.

### Look-ahead before a Mac build ("landing soon")

So that a Mac release does not miss a merge by a few minutes, `mac-release.yml` waits before dispatching onto an
idle lane while a core PR is about to land: an open PR with the label **`landing`**, or one whose `build.yml` run
(`core <PR head>`) is still running with its `lean` job passed, or passed within the last hour. It waits until none
is left (merged, closed, failed, label removed) or 30 minutes, never twice in a row past the cap, and not at all
once main has been ahead of the Mac release for 90 minutes. The wait is a Linux job; no macOS runner is held.

**Landing agents:** add the label when you start waiting on the merge gate of a PR you mean to merge, and remove it
when you merge or give up:
`gh pr edit <n> -R danbri/factoidal-core --add-label landing` / `--remove-label landing`.

### Poll triggers

GitHub drops most scheduled events in danbri/factoidal-builds (2026-11-16: build.yml's hourly poll ran 3 times in
24 h; mac-release.yml's 15-minute cron did not fire once in its first 4 hours). So the poll has three triggers:

- `workflow_run`: the end of a run of build.yml, Branch WPT check, Foafnaut Linux engine or Release tests. Such a poll
  ends at once when another poll was made in the last 10 minutes, except after a main-lane build;
- the Mac runner's `tick.sh` (every 5 minutes, all day) dispatches `mac-release.yml` when no poll was made for 20
  minutes and none is waiting or running;
- the cron, when GitHub sends it.

Don't rely on `schedule:` alone for anything that must run; give it a `workflow_run` or dispatch fallback.

### Status

`latest/darwin-status.json` in factoidal-builds: main's head, the newest Mac release (by commit), `lag_min` (since
main moved past it), the lane's runs and the last decision (with any wait: "waited 12 min for #550, #525"). Read it
with `gh api repos/danbri/factoidal-builds/contents/latest/darwin-status.json -H 'Accept: application/vnd.github.raw'`.
The poll warns in its run when main has been ahead for more than 2 hours, and the Mac runner's `tick.sh` copies each
lane dispatch and that alert (at most hourly) into the coordination log as `macalways-ci:` lines. The alert's lag
is computed fresh from the GitHub API (`ctl/darwin-status.py status`, at most every 10 minutes), not taken from the
committed JSON, whose `lag_min` is only as new as the last poll that changed it (`behind_since` is the field to
compute from).

A nightly failure opens (or comments on) an issue labelled `nightly` in factoidal-builds; a green night comments and
closes it. The `nightly-report` job prints one line for the coordination log. **A nightly macOS failure on main is fixed
or reverted the next morning**: whoever reads the coordinator's morning tick claims it in the log.

## Where macOS jobs run

`resolve` picks `runs-on` for the macOS jobs (`scripts/mac-runs-on.py`); GitHub cannot fall back from a self-hosted
label once a job is queued, so the choice is made before. The owner's Mac (`[self-hosted, macOS, ARM64,
foafnaut-mac]`) is chosen only when:

- the event is `workflow_dispatch` or `schedule` in danbri/factoidal-builds (never `pull_request`);
- the repository variable `MAC_RUNNER` (the Mac's heartbeat, `{"seen","until","free_gib"}`) is under 20 minutes old;
- the overnight window has at least 3 hours left (2 for `foafnaut-macos.yml`, 0.1 for the check workflow);
- the Mac reported enough free disk: 12 GiB for `build.yml`'s macOS jobs, 10 for `foafnaut-macos.yml`, 4 for the check.

Otherwise `macos-15`. Dispatch input `mac_runner`: `auto` (default), `github`, `self-hosted` (forces the Mac; the job
waits for it). Check where jobs land with `gh workflow run mac-runner-check.yml --repo danbri/factoidal-builds`.

## The Mac runner

Installed under `~/actions-runner` (official `actions/runner` release for osx-arm64, sha256 checked against the release
notes by `scripts/mac-runner/install.sh`). The launchd job `org.foafnaut.mac-runner`
(`~/Library/LaunchAgents/org.foafnaut.mac-runner.plist`) runs `~/actions-runner/ctl/tick.sh` every 5 minutes:

- 22:00 to 07:00 local: starts the runner (under `caffeinate -i`) when it is switched on and at least 4 GiB are free;
- outside the window: stops it; a running job may finish until 08:00, then it is stopped (that job fails);
- every tick: sets `MAC_RUNNER` (until = 0 when it should get no new jobs).

Controls (`~/actions-runner/ctl/runner.sh`):

| Command | Effect |
|---|---|
| `runner.sh status` | process, window, disk, GitHub's view, `MAC_RUNNER`, last ticks |
| `runner.sh off` | switch off: no new jobs; stops after the running job (`off --now`: at once) |
| `runner.sh on` | switch back on (runs inside the window) |
| `runner.sh now [hours]` | run now for N hours (default 2), outside the window too |
| `runner.sh logs` | follow `ctl/runner.log` |
| `runner.sh uninstall` | switch off, remove the launchd job, deregister (`./config.sh remove` with a remove token), delete `MAC_RUNNER`; then `rm -rf ~/actions-runner` |

Logs: `ctl/tick.log` (start/stop decisions), `ctl/runner.log` (the runner), `_diag/` (the runner's own logs).
Window and floors: `ctl/config` may set `START_H`, `STOP_H`, `GRACE_MIN`, `MIN_FREE_GIB`.
Removal by hand: `launchctl bootout gui/$(id -u)/org.foafnaut.mac-runner`, then in `~/actions-runner`
`./config.sh remove --token $(gh api -X POST repos/danbri/factoidal-builds/actions/runners/remove-token -q .token)`.

### Safety rules

- **Only the owner's own events.** The job-started hook (`ctl/job-started.sh`, set in `~/actions-runner/.env`, outside
  any workflow's reach) fails every job before its steps unless the repository is danbri/factoidal-builds, the event
  is `workflow_dispatch` or `schedule`, and the actor is `danbri` or `github-actions[bot]`. A fork's pull request can
  edit a workflow to ask for the self-hosted label; the hook refuses it, and the repository requires approval before
  outside contributors' workflows run.
- **Disk:** the hook refuses a job below 4 GiB free; `scripts/heavy-step.sh` checks again before each Lean build.
  The job-completed hook empties the job's workspace and temp directory and removes `~/leanc-cache` and
  `~/leanc-shim`.
- **One Lean build at a time:** `heavy-step.sh` runs the Lean steps (`lake build`, the foafnaut bundle,
  `build-web-render.sh --native`) under `~/working/foafnaut-tools/leanlock.sh`, in the same queue as the agents.
  A job without the lock (no `FOAFNAUT_LEANLOCK`) refuses to build.
- **Owner's tools untouched:** `scripts/install-elan.sh` uses the Mac's own elan (the installer would rewrite the
  shell profile); toolchains are shared with the owner's builds.
- **Daytime is the owner's:** nothing runs on the Mac outside 22:00 to 08:00 unless `runner.sh now` is used.
- Jobs run as the owner's user, so they can read the owner's files and credentials. That is why only the owner's
  own dispatches and schedules are accepted; don't add events or actors to the hook without the owner's decision.

## Troubleshooting

- A macOS job sits "queued" with self-hosted labels: the Mac went to sleep, lost network or was switched off after the
  resolve step chose it. Wake it or run `runner.sh now`; or cancel your own run and dispatch with `-f mac_runner=github`.
- `MAC_RUNNER` stale: `launchctl print gui/$(id -u)/org.foafnaut.mac-runner`, then `ctl/tick.log` and `ctl/launchd.log`.
- The runner updates itself; a failed update shows in `_diag/`. Re-run `install.sh` from a builds checkout to refresh
  the controls; it keeps the registration.
