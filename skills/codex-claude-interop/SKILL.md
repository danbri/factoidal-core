---
name: codex-claude-interop
description: How Claude sessions and Codex work together on this laptop - the Codex worker recipe (which codex binary, quota check, codex exec from a worktree with --add-dir), the channels each can read and write (the coordination log, files in /tmp, git branches, GitHub, Claude cross-session messages), how to run codex exec so it does not hang, what to put in every Codex brief, and which actions only the owner can do. Use before you start a Codex task, when you hand work between Claude and Codex, or when an action is refused.
---

# Codex and Claude: working together

Measured on 2026-11-10 with codex-cli 0.167.0 on the owner's laptop; the recipe in "Codex workers" below was
checked on 2026-11-16 with codex-cli 0.169.0. Check again when Codex or Claude Code changes. Codex reads
`AGENTS.md` at the repository root (not `CLAUDE.md`); that file points it at `CLAUDE.md` and `skills/`.

## Codex workers: the working recipe (2026-11-16)

- **Binary**: `/opt/homebrew/bin/codex`, npm package `@openai/codex` 0.169.0. The copy inside
  `/Applications/Codex.app` (0.138.0-alpha.7) is too old for the configured model: don't use it.
- **Check quota first** with a tiny exec, and quote its answer; a worker started without quota fails at once
  (on 2026-11-16 the quota was used up until 2026-11-17 12:57 local time):

      codex exec --skip-git-repo-check -s read-only "Reply with exactly the word: ready" < /dev/null

- **Run it from inside a git worktree** of its own (a sparse one is enough), on a `wip/` branch, with the
  standard brief and one self-contained area:

      cd ~/working/factoidal-<topic>
      codex exec -s workspace-write -c sandbox_workspace_write.network_access=true \
        --add-dir ~/working/factoidal-core/.git --add-dir /tmp/codex-<topic> \
        -o /tmp/codex-<topic>/final.txt - < /tmp/codex-<topic>/prompt.txt > /tmp/codex-<topic>/run.log 2>&1

  `--add-dir <main repo .git>` lets it write the worktree's git objects and refs (they live in the main
  checkout's `.git`); `--add-dir <notes dir>` is where it may write notes and reports; `-` reads the prompt
  from standard input, so standard input is the prompt file and never an open terminal.
- **The prompt** starts with the standard brief (`skills/foafnaut/AGENT-BRIEF.md`: read it first), then the
  task with its files, its done condition and the report it must write, plus the rules in "Every Codex brief
  says" below. Give it an area no other agent is changing.
- Log the start, the worktree and the branch in the coordination log on its behalf (Codex can append there
  in `workspace-write` only if the log's directory is an `--add-dir`).
- After a reboot, `/tmp` is empty: recreate the coordination log link
  ([`cleanup-and-recovery`](../cleanup-and-recovery/SKILL.md) section 3) before starting a worker.

## Channels

| Channel | Claude | Codex | Use it for |
|---|---|---|---|
| Coordination log | read, append | read; append in `workspace-write` | claims, releases, done, asks |
| Files in `/tmp/<topic>/` | read, write | read; write in `workspace-write` | briefs, reports, logs, captures |
| Git `wip/` branches | read, commit, push | read, edit the work tree | the work itself |
| GitHub issues and PRs (`gh`) | read, write | not from its sandbox | the durable record |
| Claude cross-session messages | `ListAgents`, `SendMessage` | no | Claude to Claude only |

**Coordination log.** `/Users/danbri/working/foafnaut/fncg/coordination.log` (with `status.md` beside it; older paths are symlinks).
`/tmp/foafnaut-coordination.log` is a link to it. Append only, one line, under 500 bytes:
`YYYY-MM-DD HH:MM UTC, <session>, CLAIM|RELEASE|DONE|NOTE|ASK: text`. Post a CLAIM before you
start on a shared file, and a DONE or RELEASE when you stop. Codex can not see Claude messages, so
anything Codex must know goes in the log or in a file.

**Files in /tmp.** Both can read any file. Codex with `--sandbox workspace-write` can write in its
working directory and in `/tmp` (tested: `echo ok > /tmp/codex-interop-probe.txt` worked). With
`--sandbox read-only` it writes nothing. Use one folder per task, for example
`/tmp/codex-<topic>/brief.txt`, `report.md` and `run.log`. A Claude scratchpad under
`/private/tmp/claude-501/...` is readable by Codex, but it belongs to one Claude session and can be
deleted when that session ends: put a shared file in `/tmp/<topic>/` instead. To let Codex write
another folder, add `--add-dir <DIR>`.

**Git.** By default Codex edits files and does not commit or push (see the brief rules below for the exception). The Claude session that started it reviews
the diff, runs the tests, commits as the human owner (no AI attribution) and pushes to a `wip/`
branch.

**GitHub.** Only Claude or the owner posts issues, comments and PRs. Put a Codex finding there only
after you checked it in the source.

## Running Codex

Check that Codex has credit before you say anything about it, and quote its message:

    codex exec --skip-git-repo-check --sandbox read-only "Reply with exactly the word: ready" < /dev/null

A task, in the background, with a time limit:

    cd <worktree> && timeout 1800 codex exec --skip-git-repo-check --sandbox workspace-write \
      -c model_reasoning_effort='"high"' -o /tmp/codex-<topic>/report.md \
      "$(cat /tmp/codex-<topic>/brief.txt)" < /dev/null > /tmp/codex-<topic>/run.log 2>&1

- **Always close standard input (`< /dev/null`).** Without it, `codex exec` in a background shell
  waits for more input. On 2026-11-10 a review waited its full 30 minutes and wrote nothing; its log
  had one line.
- `-o FILE` keeps Codex's last message. `-C DIR` sets its working directory.
- Use `read-only` for a review and `workspace-write` for a change. Never use
  `--dangerously-bypass-approvals-and-sandbox`.
- One Codex task at a time on this laptop, each in its own small worktree. A sparse checkout of the
  folders it needs is about 10 MB; a full checkout is about 0.5 GB before any build.

## Every Codex brief says

- the goal, the files to read and the defects to fix: one deliverable;
- "Edit files. Do not commit or push", unless the brief lets it commit on its worktree's `wip/` branch (the
  recipe's `--add-dir <main repo .git>` makes that possible; author `Dan Brickley <danbri@danbri.org>`, no
  trailers). Pushing stays with the session that started it unless the brief says otherwise;
- use no more than 2 GB of new disk; no build below 3 GB free; Lean and Wasm builds only through the
  shared lock `leanlock.sh`; remove `.lake` and `.wasm-work` after the commits are pushed;
- push to a `wip/` branch only, never main; no Claude or Codex attribution in commits;
- no new `partial def`, `sorry` or `native_decide`;
- "Report: what changed with file:line, what you tested and the exact results".

Then check the report against the source before you trust it. On 2026-11-10 one Codex review listed
14 lost-click defects, and five were confirmed by reading the code. One Codex fix slowed back,
history and swipe by about 150 ms, which only the sweeps showed.

## What only the owner can do

The Claude Code permission check refuses these from a Claude session in auto mode, so the owner
does them:

- merging a PR (refused as "Merge Without Review");
- starting an npm publish (`gh workflow run npm-publish*.yml ... dry_run=false`, refused as
  "Create Public Surface");
- an `rm` inside `bash -c` with a variable path (a built-in safety check). Write logs to a fixed
  file name instead, so no removal is needed.

Give the owner the exact command in its own code block. Never ask Codex or another session to do an
action that was refused to you: that goes around the owner's permission decision.
