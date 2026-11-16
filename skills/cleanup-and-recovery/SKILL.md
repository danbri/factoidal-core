---
name: cleanup-and-recovery
description: What to do on the shared Mac after an activity closes, an agent crashes or stops, or the machine reboots - first make sure the disk is not filling and no valuable work is lost. Disk floor and where the space goes (worktrees, .lake and .build output, Lean toolchains, ~/.foafnaut/versions, session scratchpads, traces, npm and deno caches) and how to free it safely; finding uncommitted and unpushed work in every worktree and saving it on wip/ branches; what a reboot wipes in /tmp and how to restore the coordination log link, the build lock and the health watch; and the periodic forgotten-branch audit across factoidal-core, factoidal-builds and dickory. Tools: tools/disk-audit.sh and tools/branch-audit.py (both read-only). Use after any session or agent ends, after a crash or reboot, when free disk falls below 6 GiB, and about once a week for branches.
---

# Cleanup and recovery

The order is always: **don't lose work, then free disk, then tidy**. Nothing in this skill discards
uncommitted or unpushed work, and nothing touches another agent's active worktree or process.

Both tools are read-only and print a report:

- `tools/disk-audit.sh [--no-sizes]`: free space against the floor, the big shared consumers, and one row per
  worktree (size, build output, uncommitted files, commits on no remote, processes working in it, hours since
  its index changed, verdict).
- `tools/branch-audit.py [--repo OWNER/NAME[=CLONE]] ... [--json] [--patch-id]`: every branch classified
  (section 4). Tests: `python3 tools/branch-audit-test.py`.

Log every cleanup action in the coordination log (one line: what was removed, how much it freed, why it was
safe), as the agent brief requires for claims and releases.

## 1. Disk

**Floor.** Below 4 GiB free on `/`, stop starting work that writes (builds, WPT runs, clones) and report. The
health watch (`~/working/foafnaut-tools/health-watch.sh`) logs a `health: WARN` line below 6 GiB. Check with
`df -h /` or the first block of `tools/disk-audit.sh`.

**Where the space goes** (measured 2026-11-16 with 5.5 GiB free on a 228 GiB disk):

| Consumer | Size then | Rebuildable? |
|---|---|---|
| Worktrees `~/working/factoidal-*` (25 of them) | 0.02 to 2.3 GiB each, about 14 GiB in all | the checkout yes, uncommitted work no |
| Build output in worktrees: `formal/lean4/.lake`, `labs/demos/foafnaut/.build`, `.wasm-work` | up to 1.7 GiB each | yes, at the cost of a Lean build |
| Lean toolchains `~/.elan/toolchains` | 2.7 to 2.8 GiB each (v4.33.1 in use on main, v4.35.0) | yes (download) |
| Installed Foafnaut builds `~/.foafnaut/versions` | 2.2 GiB (five versions; `current` is a link) | yes (`tools/fetch-builds.sh`) |
| Claude session scratchpads `/private/tmp/claude-*` | 1.9 GiB | no: they belong to their sessions |
| `~/.cache`, `~/.npm`, `~/Library/Caches/deno` | 2.2, 1.0, 0.2 GiB | yes (download) |
| factoidal-builds clones `~/working/factoidal-builds-*` | up to 0.7 GiB each | the clone yes, local changes no |
| Traces `~/Library/Logs/foafnaut` | 13 MiB | evidence: keep while an issue uses them |

**Freeing it safely**, in this order, stopping when there is enough:

1. **Your own build output**, once your branch is pushed: delete `.lake`, `.build`, `.wasm-work` in your own
   worktree. They come back with the next build.
2. **Your own finished worktree**: `git worktree remove <path>` (it refuses a dirty tree; never use `rm -rf`
   on a worktree, and never `--force`). Keep the branch.
3. **A worktree you did not create**, only when every one of these holds, and log the check:
   - `disk-audit.sh` says `clean+pushed+noproc` (no uncommitted files, every commit on a remote, no process
     with its working directory inside);
   - the coordination log has no open CLAIM for it (a CLAIM or START with no RELEASE or DONE after it), and
     its owner released it or is known to be stopped;
   - it has been idle for hours, not minutes (the `IDLEh` column; an agent between two commands has no
     process but is still working).
   An open PR on its branch is no reason to keep the worktree: the branch keeps the work.
4. **Old Foafnaut installs**: keep `current` and the one before it; older directories in
   `~/.foafnaut/versions` can go (check that nothing points at them: `ls -l ~/.foafnaut`).
5. **Toolchains**: a toolchain that no worktree, builds clone or open branch names in its
   `formal/lean4/lean-toolchain` can be removed with `elan toolchain uninstall <name>`. Check all of them
   first; a toolchain upgrade branch may need the newer one.
6. **Caches** (`~/.npm`, deno, `~/.cache`): last, because the next run downloads them again. Never clear a
   cache while a build or test that uses it is running.

Never:

- remove another session's scratchpad, or anything in it;
- kill or signal a process you did not start. When a process must be identified, match it by PID from
  `ps` or `lsof`, never by a path pattern (`pkill -f factoidal` would hit every agent's work);
- delete a branch, local or remote, as a disk measure (branches cost almost nothing; section 4);
- delete a trace or log that an open issue or report cites.

## 2. Work that exists only on this machine

After any session or agent ends, and after a crash or reboot, check every worktree:

```sh
tools/disk-audit.sh --no-sizes     # DIRTY / UNPUSHED rows
git -C <worktree> status --short   # what is uncommitted
git -C <worktree> log --oneline HEAD --not --remotes   # commits on no remote
```

- **Your own work**: commit it and push the `wip/` branch (`git push -u origin HEAD`). A detached HEAD gets a
  branch first: `git switch -c wip/<topic>-rescue`.
- **A stopped agent's work** (its session ended or crashed; nothing in the log says it will resume): the
  coordinator, or the agent that takes the task over, saves it. Log a CLAIM on the worktree, commit the
  changes as they are on a new branch `wip/rescue-<worktree>-<YYYYMMDD>` (message: what was found, uncommitted,
  not tested), push it, and log the branch name. Don't tidy, rebase or test it in the same step.
- **An active agent's work**: leave it. If its disk use is the problem, ask it in the coordination log.
- Never `git stash`, `git checkout -- .`, `git reset --hard` or `git clean` to make a tree look clean: those
  are how work is lost.

## 3. After a reboot

macOS empties `/tmp` (`/private/tmp`) at boot. What that takes with it, and what to do:

| Lost | Restore |
|---|---|
| `/tmp/foafnaut-coordination.log` (a link) | `ln -s /Users/danbri/working/foafnaut/fncg/coordination.log /tmp/foafnaut-coordination.log`; the log itself is under `~/working` and survives |
| Build lock state: `/tmp/foafnaut-lean-build.queue`, `/tmp/foafnaut-lean-build.lock`, `/tmp/foafnaut-timing.lock` | nothing to do: `~/working/foafnaut-tools/leanlock.sh` recreates the queue and clears a lock whose owner is dead. If a lock directory remains with a live owner PID, it is real; wait |
| Claude session scratchpads `/private/tmp/claude-*`, with any worktree inside them | the files are gone; run `git worktree prune --dry-run` in the main checkout to see the dead entries, then `git worktree prune` (it changes only git's records of missing directories) and log it. Their branches remain if they were pushed; section 2 for the rest |
| Files of running tasks in `/tmp/<topic>/` (briefs, run logs, Codex output) | gone; the coordination log and pushed branches are the record |
| The health watch process | `nohup ~/working/foafnaut-tools/health-watch.sh >/dev/null 2>&1 &` (one copy only: check `ps` first) |

Then, for every agent that was running before the reboot (the coordination log's open CLAIMs): check its
worktree with section 2, note in the log that it stopped at the reboot, and leave it to be restarted with a
fresh brief.

## 4. Forgotten branches (about weekly)

```sh
tools/branch-audit.py \
  --repo danbri/factoidal-core=$HOME/working/factoidal-core \
  --repo danbri/factoidal-builds \
  --repo danbri/dickory=$HOME/working/dickory          # add --json for a file, --patch-id for squash checks
```

It reads branches from a local clone (without one, a blob-less mirror in `~/.cache/factoidal-branch-audit/`)
and pull requests with one `gh pr list` per repository, then classifies each branch against the default
branch (read its name; it is `main` in all three today):

| Class | Meaning | Action |
|---|---|---|
| `merged` | head is in the default branch | delete candidate |
| `merged-pr` | a merged PR had exactly this head (squash or rebase merge) | delete candidate |
| `merged-patch` | the branch's whole diff equals one default-branch commit (`--patch-id`) | delete candidate |
| `merged-pr-later` | a PR merged, then the branch got more commits | review: new work or leftovers |
| `open-pr` / `open-pr-stale` | open PR, updated within / not within `--stale-days` (7) | stale: ping in the PR or the log |
| `closed-pr` | PR closed without merging | review |
| `no-pr` | unmerged, no PR | review list |
| `local-unpushed` | local branch has commits its remote branch lacks | push the `wip/` branch, or review |
| `local-only` | local branch with no remote | push it as `wip/`, or review |

Deleting: remote branches only with the owner's agreement, after the list (with each branch's commit id) is
saved in the coordination log or an issue, so any branch can be restored. Local branches that are `merged` or
`merged-pr` may be deleted by the coordinator with `git branch -d` (or `-D` for squash merges, after checking
the class), never one checked out in a worktree.

Report the summary counts per repository and the review and ping lists, not the whole table.
