---
name: github-and-prs
description: Use the GitHub CLI (gh) for the Factoidal repository's PR / issue / branch workflow. Use when the user asks to create / view / merge a PR, list branches, audit stale branches, comment on an issue, or anything involving gh commands. The Factoidal repo's git remote uses a local proxy that confuses gh's repo inference, so all commands need an explicit --repo flag.
---

# GitHub CLI for the Factoidal repo

> **Commit-message attribution:** this repo does NOT list Claude's
> role in commits — no Co-Authored-By, no generated-with, no session
> links. See
> [`skills/github-coauthor-policy/SKILL.md`](../github-coauthor-policy/SKILL.md)
> (iron rule #13). All commit examples elsewhere in this file predate
> that rule; write commit messages without trailers.

The git remote in this project points at a local proxy
(`http://local_proxy@127.0.0.1:.../git/danbri/factoidal`) so that pushes
work in restricted-network environments. As a side effect, `gh` cannot
infer the repo from the remote and fails with:

```
none of the git remotes configured for this repository point to a known GitHub host
```

**Fix: every `gh` command takes `--repo <owner/name>` explicitly.**
This is the single most common failure mode and accounts for ~all
gh-related friction in this project.

**Which repository (since 2026-10-09, the core/builds split):**

| Work | Repository |
|---|---|
| Issues (create, comment, close; every issue URL) | `danbri/factoidal` — issues stay there; do not change issue URLs |
| Pushes, branches and PRs of source (`formal/`, tests, tools, skills, docs sources, npm sources, `bin/<consumer>/`) | `danbri/factoidal-core` |
| Build workflow runs, releases, `legacy-workflows/`, the `toolchain-cache` and `checked-cache` branches | `danbri/factoidal-builds` |

So `--repo danbri/factoidal` in the examples below is correct for issue
commands. For PR, branch and CI-run commands on source, read it as
`--repo danbri/factoidal-core` (the two `gh run` examples as
`--repo danbri/factoidal-builds` when you mean a build). The record is
`docs/designissues/2026-10-09-core-builds-split.md`.

## Auth setup (one-time per sandbox)

If `gh auth status` reports "not logged into any GitHub hosts":

### Device flow (interactive, no token needed)

```bash
curl -sX POST https://github.com/login/device/code \
  -H "Accept: application/json" \
  -d "client_id=178c6fc778ccc68e1d6a&scope=repo+read:org+workflow"
```

Output is JSON with `user_code`, `verification_uri`,
`device_code`. Open `verification_uri` in a browser, enter
`user_code`, authorize. Then poll for the token:

```bash
DEVICE_CODE=...   # from the previous response
curl -sX POST https://github.com/login/oauth/access_token \
  -H "Accept: application/json" \
  -d "client_id=178c6fc778ccc68e1d6a&device_code=$DEVICE_CODE&grant_type=urn:ietf:params:oauth:grant-type:device_code" \
  | python3 -c 'import sys,json; print(json.load(sys.stdin)["access_token"])'
```

Save the token via:

```bash
echo "<token>" | gh auth login --with-token
gh auth status
```

The client_id `178c6fc778ccc68e1d6a` is `gh`'s public client — the
flow is identical to what `gh auth login -w` does internally, just
scriptable.

### Personal access token (faster)

If the user already has a PAT, paste it via:

```bash
echo "$GH_TOKEN" | gh auth login --with-token
```

## Branch + PR conventions

### Branch naming

- `claude/<topic>` for any agent or human work. Topics use kebab-case.
- Examples: `claude/track1-rdfc10-escape-delegate`,
  `claude/build-z3version-flag`, `claude/fstar-only-query-planning-recovery`.
- Avoid project codenames in branch names (per the recovery plan +
  glossary policy). Use the descriptive name for the work.

### PR base

- In `danbri/factoidal` the default base branch was **`claude/main`**,
  not `main`.
- In `danbri/factoidal-core` the base is `main` once the owner renames
  `claude/core-split` to `main`. Until then the base is
  `claude/core-split`. The branch `claude/main` in that repository is
  older and holds merge commits that `danbri/factoidal` does not have;
  the split did not overwrite it (record, section 1).
- Pass `--base` explicitly to gh commands.

### Standard PR creation

```bash
# --base is claude/core-split until the owner renames it to main
gh pr create --repo danbri/factoidal-core \
  --base claude/core-split \
  --head claude/<branch> \
  --title "..." \
  --body "$(cat <<'EOF'
## Summary
- ...

## Test plan
- [ ] ...
EOF
)"
```

### Standard inspection

```bash
gh pr list --repo danbri/factoidal-core --state open
gh pr list --repo danbri/factoidal-core --state merged --limit 50
gh pr view 164 --repo danbri/factoidal-core
gh pr view 164 --repo danbri/factoidal-core --json mergeable,mergeStateStatus
gh pr checks 164 --repo danbri/factoidal-core
```

### Merging

The user merges. **Don't** run `gh pr merge` yourself unless the user
explicitly says so. PRs in this repo are reviewed and merged
manually.

### Before merging a PR that changes shipped code: build its head in CI

A Lean build and the dataflow drift test do not test the package. When a
PR changes Lean source that ships (anything under `formal/lean4/` that the
wasm or the native binaries compile, not only tests and proofs) or anything
under `npm/`, run the factoidal-builds build on the PR's head commit and
merge only when its `web-gates` job passes:

```bash
gh workflow run build.yml --repo danbri/factoidal-builds -f core_ref=<40-hex PR head>
gh run watch <run id> --repo danbri/factoidal-builds --exit-status
```

Take `<40-hex PR head>` from `gh pr view N --json headRefOid` or
`git rev-parse`; never type it. The queue keeps one pending run (see
`skills/subagent-prompting`, "Agents do not dispatch factoidal-builds
runs"), so dispatch one build at a time and check with `gh run list` that
the run you are waiting for was not cancelled. Since factoidal-builds PR 3
(2026-10-24) `web-gates` waits only for the Linux F* job.

`web-gates` runs the npm package suite on the wasm built from that commit.
The local alternative is `bash formal/lean4/Wasm/build-wasm.sh` and then
`cd npm/factoidal && npm test`.

Cost of skipping it, 2026-10-24: PRs 44 to 52 of factoidal-core were merged
after `lake build` and `tests/dataflow/run.sh` only. PR 51 (writers refuse an
invalid language tag) made the RDF 1.2 writer refuse a tag that the RDF 1.1
reader accepts, and `npm/factoidal/test/serialize-turtle.test.js` (issue 870)
failed on main: 614 pass, 1 fail (out of 616). The first CI build of main
after the merges found it, and that build published no web release set, so
no release could be made from main until the fix.

### Force-push policy

Force-push to a PR's head branch is acceptable when:

1. The user has approved it (explicit "Y" or "yes").
2. The branch is the user's own (or a Claude-generated branch).
3. The remote tip has only a CI-shadow auto-commit on top of your
   real work (clobbering the shadow is lossless). (No workflow pushes
   such commits to `danbri/factoidal-core` since 2026-10-09; this case
   applied to `danbri/factoidal`.)

**Never** force-push:

- To `claude/main` or `main`.
- After someone else has commented on the PR (their inline review
  comments will detach from line numbers).

Use `--force-with-lease` first; fall back to `--force` only when a
known-safe CI shadow is the cause of the lease rejection.

## Branch cleanup workflow

The repo accumulates `claude/<topic>` branches faster than they get
deleted. The recipe for safe cleanup:

```bash
# 1. List all merged PRs and their head branches
gh pr list --repo danbri/factoidal-core --state merged --limit 200 \
  --json number,headRefName,title,mergedAt \
  > /tmp/merged-prs.json

# 2. List all remote branches
git ls-remote --heads origin | awk '{print $2}' | sed 's|refs/heads/||' \
  > /tmp/remote-branches.txt

# 3. Cross-reference: branches whose head was merged are safe to delete.
python3 -c '
import json, sys
prs = json.load(open("/tmp/merged-prs.json"))
merged = {p["headRefName"]: p for p in prs}
for line in open("/tmp/remote-branches.txt"):
    b = line.strip()
    if not b.startswith("claude/"): continue
    if b in ("claude/main",): continue
    if b in merged:
        print(f"DELETE {b} (PR #{merged[b]['"'"'number'"'"']} merged {merged[b]['"'"'mergedAt'"'"'][:10]})")
    else:
        print(f"KEEP   {b} (no merged PR; check manually)")
' | sort
```

Surface the DELETE list to the user, get explicit approval, then:

```bash
xargs -n1 git push origin --delete < /tmp/branches-to-delete.txt
```

**Never delete a branch without user approval**, even if it looks
obviously stale. Some branches hold in-progress work that hasn't
been pushed elsewhere.

## CI

Since 2026-10-09 CI is split between two repositories. In
`danbri/factoidal-core` (`.github/workflows/`) the gates need only source
and a toolchain, never a built binary:

| Workflow | Path | Trigger |
|---|---|---|
| `check-extraction` | `.github/workflows/check-extraction.yml` | PR + push |
| `check-fstar-purity` (Omega3) | `.github/workflows/check-fstar-purity.yml` | PR diff |
| `check-derived-files` | `.github/workflows/check-derived-files.yml` | PR |
| `check-ocaml-output-cleanliness` | `.github/workflows/check-ocaml-output-cleanliness.yml` | PR |
| `verify-fstar` | `.github/workflows/verify-fstar.yml` | PR on F\* paths + nightly |
| `verify-lean4` | `.github/workflows/verify-lean4.yml` | push to `main` or `claude/core-split`; PR on `formal/lean4/**` |

In `danbri/factoidal-builds`, `build.yml` builds a core commit, runs the
build gates and publishes the `build-<12 hex>-<set>` releases (four polls
of core a day, or `workflow_dispatch`). The eleven workflows that built,
tested, published or deployed binaries before the split (`w3c-tests`,
`beyond-w3c`, `conformance-rerun`, `dashboard-refresh`, `deploy-pages`,
`fly-deploy`, `npm-publish`, `npm-publish-lean`, `ukparliament-bench`,
`clean-room-build`, `debug-bytecode-build`) are inactive files under
`legacy-workflows/` there; `legacy-workflows/README.md` states what each
port needs.

Before the split the `w3c-tests` workflow auto-pushed a
"ci(linux-x86_64): shadow build artifacts [skip ci]" commit to
`claude/main` whenever the binaries changed, and PRs with stale binaries
conflicted on `bin/ci-linux-x86_64/build-info.json`; the `merge=ours` git
driver was the fix. Neither the commits nor that path exist in
`danbri/factoidal-core`.

```bash
gh run list --repo danbri/factoidal-core --limit 10       # source gates
gh run list --repo danbri/factoidal-builds --limit 10     # builds and releases
gh run view <run-id> --repo danbri/factoidal-core
gh run watch <run-id> --repo danbri/factoidal-core
```

## What this skill does NOT do

- Does not interact with private/forked repos. Scope is
  `danbri/factoidal` (issues), `danbri/factoidal-core` (source) and
  `danbri/factoidal-builds` (builds and releases).
- Does not bypass review — never `gh pr merge` without user OK.
- Does not delete branches without user approval, even when "obviously"
  merged.

## Cross-references

- `fstar-env` skill — toolchain setup if `fstar.exe` is missing.
- `build-and-test` skill — local verification before opening a PR.
- `issue-hygiene` skill — keeping issue checklists/comments in sync as
  the PRs covered by this skill land.
- `docs/claude-rules/anti-patterns.md` — full anti-pattern table.

## Landing while CI keeps moving the branch (2026-07-04 pattern)

CI pushed artifact commits to claude/main every few minutes, so a
plain push from a long-lived local branch usually lost the race (no
workflow pushes artifact commits to `danbri/factoidal-core` since
2026-10-09; the pattern still applies to any concurrent pusher), and
`git rebase` refuses while the tree carries in-flight (gated,
uncommitted) work. The pattern that works:

```bash
git config user.email danbri@danbri.org && git config user.name "Dan Brickley"  # once per clone (iron rule 13: human identity only)
git commit ...                        # commit locally as usual
C=$(git rev-parse HEAD)
git fetch origin claude/main
WT=$(mktemp -d); git worktree add $WT origin/claude/main
git -C $WT cherry-pick $C && git -C $WT push origin HEAD:claude/main
git worktree remove --force $WT; git worktree prune
```

Afterwards, realign with `git reset --hard origin/claude/main` ONLY
when BOTH hold: (1) the local commits verifiably exist upstream
(`git log --format=%s origin/... | grep` — cherry-picked copies have
different hashes, so the stop hook nags about "unverified" local
duplicates until realigned), and (2) `git status` is COMPLETELY clean
AND no subagent is mid-task in this tree. reset --hard discards
other agents' uncommitted in-flight work — it did exactly that on
2026-07-04 (an agent lost its first-pass edits mid-task and had to
recover via reflog). With agents in flight, skip realignment
entirely; the stop-hook nag is cosmetic, lost agent work is not.

If you must realign with agents in flight, the only safe form is
`git reset --mixed origin/claude/main` (moves HEAD AND resets the
index; leaves the working tree alone), optionally followed by a
targeted `git checkout -- <ci-owned-paths>` for CI-managed outputs.
NEVER `reset --soft`: it leaves the index at the old tree, so the
diff between old and new upstream (e.g. a CI dashboard refresh)
sits silently STAGED as a reversion, and your next `git add X &&
git commit` sweeps it in. That exact failure shipped a phantom
dashboard reversion inside an unrelated one-file commit on
2026-07-05 — caught only because the next cherry-pick conflicted on
files a new-file commit had no business touching. After any
worktree cherry-pick, verify with `git show --stat` that the pushed
commit contains exactly the files you meant.

