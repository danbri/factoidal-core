# The core/builds split, as executed (2026-10-09)

Status: EXECUTED. Plan: `docs/designissues/2026-08-27-three-repo-split-plan.md`
(option B). This record states what was done, how it was checked, and what
was decided without an owner ruling (each such decision is labelled
"Claude-inferred default").

Owner instructions:

- 2026-08-27, verbatim: "I have made two new sibling repos under danbri:
  factoidal-core as successor to this one and factoidal-builds for the CI
  that keeps us with fresh binaries. We will need git history only for
  formal/\* file paths. The binaries and their builds will migrate to own
  repo."
- 2026-10-09, verbatim: "We want factoidal to be built in factoidal build
  from fstar and lean4 trees in factoidal-core."

## 1. Result

| Repository | Branch | Content |
|---|---|---|
| `danbri/factoidal-core` | `main` | `formal/` history (2,331 commits) + one snapshot commit with the rest of the source tree + the rewiring commit |
| `danbri/factoidal-builds` | `main` | build workflows and scripts, `latest/<set>.json` pointers |
| `danbri/factoidal-builds` | `toolchain-cache`, `checked-cache` | the F\* toolchain chunks, the Lean wasm work-dir cache, the F\* `.checked` cache (single commits, trees identical to the `danbri/factoidal` branches of the same name at `ec785429ab23` and `5a7d99429b6a`) |
| `danbri/factoidal` | `claude/main` | unchanged: full history, binaries, issues |

The older `claude/main` and `claude/autoexec-scratchpad-assess-37oeok`
branches in `danbri/factoidal-core` were NOT overwritten. `claude/main` there
holds merge commits that `danbri/factoidal` does not have (`f4a81263cde0`),
so a force push would have deleted the only copy. The new history is on
`main`. 🧭 The repository default branch is a GitHub setting; this session
cannot change it. Set it to `main`.

## 2. How the formal/ history was made

The full history of `danbri/factoidal` is about 20 GB on GitHub (all
branches; 1.3 GB of `bin/` at the tip, rewritten in 616 commits). The
session disk had 21 GB free. So:

1. Blob-less bare clone of `claude/main` (commits and trees only: 11 MB,
   6,486 commits).
2. `git log --raw -m --root -- formal/` lists every (blob, path) introduced
   under `formal/`: 47,699 distinct blobs.
3. The path rule `tools/repo-split/core-formal-exclude.py` drops object
   files (`.o .cmx .cmi .cmo`), logs, bytecode and native executables,
   the extraction build state (`ocaml-output/.extract-state/`), the
   `*_DONE` markers and the generated store `formal/lean4/COLL/`. It keeps
   `.fst`, `.fsti`, `.lean`, the extracted `.ml`, scripts and docs.
   Result: 6,255 blobs kept (55 MB), 41,444 dropped. Only the kept blobs
   were fetched (batched `git fetch --stdin`, 13 s).
4. A binary scan of every kept blob (NUL byte, ELF, Mach-O or wasm
   header) found one file: `formal/roaring/paper/roaring.pdf`, 293 KB,
   source material, kept.
5. `tools/repo-split/exact-filter.py` rewrote the history. For each
   original commit it computes the new tree DIRECTLY as the original tree
   filtered by the path rule; a non-merge whose filtered tree equals its
   parent's is pruned; a merge whose mapped parents collapse, or where one
   is an ancestor of another, is reduced. 2,331 commits written, 4,155
   pruned.

### Why not git-filter-repo

`git filter-repo` was tried first (it runs `fast-export --no-data`, so it
works on a blob-less clone). Its tip differed from the expected tip in 3
files (`XPath.Eval.fst`, `XSLT.Transform.fst`,
`cottas_ondisk_z_lazy_open.sh`), each last changed by a 2026-07-19 merge.
Mechanism: `fast-export` emits a merge's file changes relative to the
merge's ORIGINAL first parent. When that parent is pruned (it touched only
dropped paths), the changes are applied to a different base and the
content from the second parent is lost. The direct-tree rewrite in step 5
cannot have this defect: no commit's tree is derived from a diff.

## 3. Verification (split plan section 7)

| Check | Method | Result |
|---|---|---|
| Tip file set and content | `ls-tree -r` of new tip vs original tip filtered by the same rule, blob ids and paths compared | identical, 1,233 files |
| Every commit, not only the tip | 300 rewritten commits sampled at random (seed 1); each tree compared with its original commit's filtered tree | 0 mismatches |
| Snapshot commit | `formal` subtree of the snapshot commit vs its parent | identical (`f183a061`) |
| Authors | `git log --format='%an <%ae>'` | 2,331 Dan Brickley; committer GitHub on 98 PR merges |
| Claude trailers | `Co-Authored-By: Claude`, `Claude-Session:`, "Generated with Claude Code" lines in messages | 0 |

Commit count: the plan expected "near 1,217". That figure did not come from
a stated method. Measured here: 2,554 commits on `claude/main` touch
`formal/`; 223 of them touch only dropped artifacts, which leaves 2,331.

## 4. Decisions without an owner ruling (Claude-inferred defaults)

1. **Author identity.** `Claude <noreply@anthropic.com>` (1,844 original
   commits) and `danbri <danbri@danbri.org>` map to
   `Dan Brickley <danbri@danbri.org>` (`tools/repo-split/mailmap`), and the
   Claude trailer lines are removed from messages. Basis: iron rule 13 and
   the owner's 2026-08-26 instruction "all attributions are to responsible
   human only". `danbri/factoidal` keeps the original records.
2. **What the snapshot commit carries.** Everything source-shaped from
   `danbri/factoidal` at `36f84a0c4969` except the rule in
   `tools/repo-split/core-tip-exclude.py`: `bin/`, `docs/test-results/`
   (generated dashboard), `docs/npm/` and `docs/fstar-extracted/` (Pages
   mirrors of build products), the built engine bundles and wasm under
   `npm/` and `docs/web/hub/assets/l4/`, the deployment files (`Dockerfile`,
   `fly.toml`, `deploy/`, `experiments/`), and stray root logs. 8,222 files
   kept, 992 dropped. The 20 `third_party/testing` submodules keep their
   pinned commits.
3. **Which workflows stay in core.** Only the gates that need source and a
   toolchain, never a built binary: `verify-lean4`, `verify-fstar`,
   `check-extraction`, `check-derived-files`, `check-fstar-purity`,
   `check-ocaml-output-cleanliness`. The other eleven (`w3c-tests`,
   `beyond-w3c`, `conformance-rerun`, `dashboard-refresh`, `deploy-pages`,
   `fly-deploy`, `npm-publish`, `npm-publish-lean`, `ukparliament-bench`,
   `clean-room-build`, `debug-bytecode-build`) build or test binaries, so
   they belong to `danbri/factoidal-builds`. The extraction drift guard
   (`.fst` vs committed `.ml`) stays in one repository, as option B
   requires.
4. **Cache branches** move to `danbri/factoidal-builds`;
   `tools/install-toolchain-cache.sh` reads them from there
   (`FACTOIDAL_CACHE_REMOTE` overrides).

## 5. How a checkout gets binaries now

`tools/fetch-builds.sh` lists the releases of `danbri/factoidal-builds`,
takes the newest release tagged `build-<12-hex core commit>-<set>` whose
commit is HEAD or an ancestor of HEAD, downloads `<set>.tar.gz` and
`build-info.json`, checks the tarball digest, every file's sha256, and that
no file is unlisted or missing, and only then copies the files into the
checkout. Sets: `linux-x86_64` and `darwin-arm64` (native binaries into
`bin/<platform>/`), `web` (wasm and JS bundles into `npm/` and `docs/`).
All installed paths are in `.gitignore`. `tools/ensure-test-env.sh` calls
it and reports the installed tag.

## 6. Reproduce

```
git clone --bare --filter=blob:none --single-branch -b claude/main \
    https://github.com/danbri/factoidal factoidal-blobless.git
# list (blob, path) under formal/, keep by core-formal-exclude.py,
# fetch the kept blobs, then:
python3 tools/repo-split/exact-filter.py factoidal-blobless.git claude/main \
    tools/repo-split/core-formal-exclude.py tools/repo-split/mailmap \
    refs/heads/core-formal
```

The rewrite is deterministic: the same input history gives the same
commit ids.
