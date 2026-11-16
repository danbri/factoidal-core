# Factoidal agent instructions

These instructions apply to every coding agent (Codex, Claude, or any other), not only Claude. Codex reads
this file; the full project rules are in [`CLAUDE.md`](CLAUDE.md), and the working rules for each topic are
skills in [`skills/<name>/SKILL.md`](skills/) (the index is the "Skills" section of `CLAUDE.md`).

Read first, in this order:

1. [`skills/foafnaut/AGENT-BRIEF.md`](skills/foafnaut/AGENT-BRIEF.md): the standard brief for any work on
   Foafnaut and the shared Mac.
2. [`CLAUDE.md`](CLAUDE.md), and the skill for the area you touch, before you touch it.
3. [`skills/codex-claude-interop/SKILL.md`](skills/codex-claude-interop/SKILL.md): how Codex and Claude
   sessions share work (coordination log, files in `/tmp`, `wip/` branches) and the Codex worker recipe.

Core rules, in short (the linked files are the authority):

- Decisions about web content are made in Lean; the hosts move bytes. No JavaScript copies of Lean logic, no
  host drawing of page content, no Foafnaut-only page APIs.
- No `sorry`, user axioms, `native_decide`, `unsafe`, `@[implemented_by]` or new `partial def`. Engine and WPT
  work ships with proved theorems, not only tests. Say what is proved and what is only tested.
- A page that does not use a feature pays nothing for it; give before and after timings.
- Work in your own worktree on a `wip/` branch and push it after each passing step. Commits are authored by
  `Dan Brickley <danbri@danbri.org>`, with no co-author or session trailers. Run `tools/premerge.sh` before
  any push to `main`.
- One Lean build at a time on the shared Mac (`leanlock.sh`); one WPT run per machine; never kill or signal a
  process you did not start; never touch another agent's worktree; stop and report below 4 GiB free disk.
- Log claims, results and releases in the coordination log (`/tmp/foafnaut-coordination.log`).
- Nothing is out of scope: say "later", "not yet" or "reported separately"
  ([`skills/scope-and-sequencing`](skills/scope-and-sequencing/SKILL.md)). Headline numbers count everything.
- Plain British English; never the word "honest"; never quote the owner on GitHub.
- After a session ends, a crash or a reboot: [`skills/cleanup-and-recovery`](skills/cleanup-and-recovery/SKILL.md).

## Lean 4 working directory

`formal/lean4/` is a self-contained Lake project. Every `lake build`, `lake
exe`, or `lake env` command **must** use `formal/lean4/` as its explicit
working directory. Never run a `lake` command from the repository root,
including after a separate earlier command which happened to `cd` there. Run
repository Git commands from the repository root.

Do not write a combined command that assumes a prior `cd` remains active. Use
separate commands (or set the tool's working directory explicitly) for Lean
and Git work. Before each Lean command, check the tool call's `workdir`, not
the previous transcript. This repeated failure caused root-level Lake errors
and misleading test results on 2026-08-31.

## Worktree discipline

Preserve unrelated working-tree changes. Stage only the files needed for the
current coherent change. Record substantive design and implementation progress
in dated `docs/YYYYMMDD-*.md` worknotes.

## Build products and repositories (2026-10-09)

Compiled binaries, wasm modules and JS bundles are not committed to this
repository. `danbri/factoidal-builds` builds them from a core commit and
publishes them as releases; `tools/fetch-builds.sh` (called by
`tools/ensure-test-env.sh`) installs the newest release whose source
commit is in the checkout's history, after it checks every file's sha256.
Never copy a binary in by hand and never commit one. Push source and open
pull requests in `danbri/factoidal-core`. Older issues are in
`danbri/factoidal`; newer ones are also filed in `danbri/factoidal-core`.
The default branch of `danbri/factoidal-core` is `main` (read it with
`gh repo view --json defaultBranchRef`; don't guess).
Record: `docs/designissues/2026-10-09-core-builds-split.md`.
