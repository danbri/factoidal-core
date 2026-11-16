---
name: background-watchers
description: How to wait for something in a background shell without leaving a loop that never ends - watcher, waiter, poller, until-loop, while-loop, sleep, pgrep -f, pkill, ps | grep, grep -q on a log or output file, kill -0, wait, gh run watch, gh run view polling, CI waits, Lean build waits, leanlock waits, Monitor. Covers the self-matching pgrep trap (a watcher whose own command line contains the pattern it waits on never exits), waits on files that are never written, missing timeouts, and cleaning up your own watchers. Use whenever you start a background wait, and when a list of background tasks shows old shells still running.
---

# Background watchers that end

On 2026-11-16 the coordinator found 26 watcher shells still running hours after the agents that started them had
finished. They kept the "background work still running" state alive, matched other agents' process checks, and some
would never have ended on their own. The causes below each happened more than once.

## 1. The self-matching `pgrep -f` trap

```sh
# WRONG: never ends
until ! pgrep -f 'wpt-reftests.py run' >/dev/null; do sleep 10; done
```

`pgrep -f` matches against full command lines. On macOS `pgrep` leaves out itself and its own ancestors, so a single
watcher does end. But a second watcher with the same pattern (another agent, a retry, a later check) has the text
`wpt-reftests.py run` in its command line, so each watcher sees the other as the job it is waiting for, and **both
loop forever, even after the real job has ended**. Tested on this Mac (2026-11-16): two `until ! pgrep -f "x"` loops
started together never end; the same two loops with `[x]` patterns end at once. Six watchers on `wpt-reftests.py run`
and three on `lake build L4Factoidal.JS.FuelMono` were found deadlocked this way. Worse, every other agent's
`pgrep -f wpt` now sees a "running WPT job" that does not exist (this misled the check guarding the 7 GB-cap run of
the JIT proof). On Linux, `pgrep` does not leave out ancestors, so there even one watcher can match its own shell.

The same happens with `ps aux | grep X` (the grep and the watcher both match), `pkill -f X` (it can kill the watcher
or another agent's waiter), and `until ! pgrep -f "lake build L4Factoidal.JS.FuelMono"`.

Do instead, in order of preference:
1. **Wait on the PID you started.** Start the job in the background, keep `$!`, and test that PID:
   ```sh
   job & pid=$!
   while kill -0 "$pid" 2>/dev/null; do sleep 10; done   # or: wait "$pid" in the same shell
   ```
   For a process another tool started, record its PID once (`pgrep -f ... | head -1`, checked by eye) and then wait on
   that PID, never on the pattern again.
2. **Break the pattern so it cannot match any watcher** (tested): `pgrep -f '[w]pt-reftests.py run'`. The regex `[w]pt`
   matches the text `wpt`, but the watcher's own command line contains `[w]pt`, which does not match.
3. **Exclude your own shell** if you must match by name:
   `pgrep -f 'pattern' | grep -vx "$$"` is still fragile (subshells have other PIDs); prefer 1 or 2.
4. On macOS, `kill -0` on another user's process fails with EPERM, which means alive, not gone. Treat only "No such
   process" as gone (the leanlock bug of 2026-11-16).

## 2. Waiting on a file or log line that never comes

```sh
# WRONG: if the job crashes before printing "ended", this never ends
until grep -q "ended" "$out"; do sleep 20; done
```

Thirteen watchers of this shape waited on the output of one build that was stopped before it printed `ended`.

- Wait for the producer's PID to end, then read its output (1 above).
- Match the end states too, success and failure: `grep -qE 'ALL-OK|FAIL|KILLED|error'`.
- Always add a deadline (section 3).

## 3. Every wait has a deadline

```sh
deadline=$(( $(date +%s) + 3*3600 ))
until done_check; do
  [ "$(date +%s)" -ge "$deadline" ] && { echo "TIMEOUT after 3 h"; exit 2; }
  sleep 60
done
```

Pick a deadline from how long the thing takes (a full build.yml run with macOS: hours; Linux jobs: about 50 min; a Lean
group check: under 30 min). Print `TIMEOUT` so the reader knows it was not success.

## 4. CI waits

- Poll one run by ID, not "the newest run": `gh run list ... -L 1` races with other agents' dispatches (two agents
  picked up each other's runs on 2026-11-16). Find your run by its inputs (core_ref in the resolve log) or by the
  time you dispatched it.
- End on `completed` whatever the conclusion, then act on the conclusion:
  ```sh
  until s=$(gh run view "$R" -R danbri/factoidal-builds --json status,conclusion -q '.status+" "+.conclusion') \
        && [ "${s%% *}" = completed ]; do sleep 120; done
  ```
- A run that waits on a job you no longer need (for example the macOS jobs under the Linux merge gate) never reaches
  `completed` quickly: wait on the jobs you need (`--json jobs`) instead, and stop on any `failure` or `cancelled`.
- A rerun or a new dispatch makes an old watcher stale: stop the old one when you start the new one.

## 5. Use the tools' own completion signals when they exist

In Claude Code a command run with `run_in_background` (and a subagent) notifies on exit, so a separate watcher shell
for it is not needed. Don't add an extra "until the output file says X" loop on top. Use one watcher per thing, and
reuse it instead of starting another each time you check.

## 6. Clean up your own watchers

- Before you report and stop, stop every watcher you started that is still running (by its task ID or PID; only
  your own, never another agent's).
- When a coordinator lists background tasks, anything belonging to a finished agent, a merged PR, or a cancelled run is
  stale: check what it waits on, then stop it.
- Never `pkill -f` a pattern to clean up: it can hit other agents' processes. Stop by PID.

## Quick checklist

- [ ] Waiting on a PID (or a `[x]yz` pattern), not a plain `pgrep -f`/`ps | grep` of text that is in my own command.
- [ ] Matches failure as well as success.
- [ ] Has a deadline and prints TIMEOUT.
- [ ] Polls my own run ID, not "the latest".
- [ ] One watcher per thing; stopped when no longer needed.

Related: [`cleanup-and-recovery`](../cleanup-and-recovery/SKILL.md) (disk, stale worktrees), the build lock
`~/working/foafnaut-tools/leanlock.sh`.
