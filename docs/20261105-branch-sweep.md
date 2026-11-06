# Branch sweep of danbri/factoidal-core (5 and 6 November 2026)

Owner, 2026-11-05: "sweep, yeah start this overnight." For each unmerged branch: put its work on
`main` if it still applies, or record why it is dead. Before this sweep the repository had 56 branches
other than `main`. Before a branch is deleted, tag `archive/<branch-name>` holds its tip, so no commit is lost.
Restore a branch with `git push origin archive/<name>:refs/heads/<name>`.

Method: `git cherry`, a search of main's log for each commit subject, a count of the added lines that
main holds, then a trial merge. Earlier audit:
https://github.com/danbri/glitchcan-minigam/blob/master/docs/branch-audit-20261104.md

Each batch was verified on a temporary branch `sweep/batch-N` with a `workflow_dispatch` of
"Verify Lean 4 corpus", "npm package suite and dataflow gate" and "Browser host controls". A dispatch on
another ref does not cancel the check on `main`, and no local Lean build of the whole library was needed.
`L4Factoidal/XProc31` is outside those targets, so it was built locally with `lake build l4xproc`.

Status, 2026-11-06, final: of the 56 branches, 26 ALREADY-ON-MAIN, 12 DEAD, 11 LANDED (1 in part), 4 NEEDS-WORK, 3 SKIPPED.
The landing is merge `5605193b5`. The first finished check on main that contains it passed:
https://github.com/danbri/factoidal-core/actions/runs/42229183415 (Verify Lean 4 corpus at `fc1757665`).
Before the landing: https://github.com/danbri/factoidal-core/actions/runs/42214177640 (npm suite and dataflow gate, success),
https://github.com/danbri/factoidal-core/actions/runs/42131194969 (Verify F* Proof Corpus, success, one merge of main earlier).
Not run: the new XMPP login limit and the other new ops in a freshly built wasm (the npm suite uses the last released engine);
the XProc test suite (the `l4xproc` build passes; CI does not build it).

Repairs in the landing: `admitsDest` is noncomputable (proof-only count; the allow list is unchanged);
three parse or type repairs let `l4xproc` build; the login guard was added to the WebSocket path.
Tags `archive/sweep/batch-1` and `archive/sweep/batch-2` keep the temporary branches.

Open PRs after the sweep: 262 and 264 (see their rows; a comment on each states what is needed), 339 (owner decision; it
lowers the partial-def baseline to 162). PR 360 merged in its own session. danbri/glitchcan-minigam has no open PRs.
Out of scope: `wip/rescue*` branches that another session pushed after the reboot, on 2026-11-06.

| Branch | Outcome | Commit on main, or tag | Reason |
| --- | --- | --- | --- |
| `wip/lws-reader-paths-lean` | LANDED | merge on main | PR 338. Container path decisions in Lean, wasm op containerPath. Conflict only in the changelog. |
| `claude/qt4-static-typing-integration` | LANDED | merge on main | PR 281. Optional static typing. Allow-list conflict: both sides kept; the new lines carry reasons. |
| `codex/spatial-filter-planning` | LANDED | merge on main | GeoSPARQL filter planning. StoreDataset conflict: kept the SERVICE join arm of main and the OPTIONAL comment of the branch. |
| `claude/checked-conditional-routing` | LANDED | merge on main | PR 290. Stage.choose, xml-report output. Compositor conflicts: kept 0.29.0 pins of main; added the new Lean targets to the CI build. |
| `claude/compositor-xml-representability` | LANDED, part | merge on main | PR 289. Theorems and record landed. Its expected-defect test and CI step were not landed: checked routing fixed the defect, so that test would fail. |
| `wip/1126-egress` | LANDED | merge on main | PR 300. One egress decision for outbound requests (issue 1126). The earlier CI failure did not repeat on the merge. |
| `claude/webdav-executable-gate` | LANDED | merge on main | PR 265. Read-only WebDAV executable tests and compact Base64 for LWS snapshots. Its executable gate was red at 0.26.0; that is not a CI gate. |
| `claude/xproc31-2` | LANDED | merge on main, then eb7404ae3 repair | PR 340. It never built: three small repairs let l4xproc build locally. Not measured against the XProc test suite. CI does not build XProc31. |
| `claude/qt4-cfg-static-typing` | ALREADY-ON-MAIN | PR 281; tag `archive/claude/qt4-cfg-static-typing` | Superseded by PR 281, now on main. |
| `wip/1125-1128-xmpp-login` | LANDED | merge on main | PR 337. Login limits (issues 1125, 1128). Server.Env gains a guard; the STARTTLS checks moved to the new form; the guard also covers the WebSocket path, which the branch did not have. The npm tests ran against the last released engine, so the new limit has not run in wasm yet. |
| `codex/svg-corpus-overnight` | LANDED | merge on main | PR 310. 21 MB of pinned WPT SVG files with notices. `tests/browser-wpt` on main needed them from a side checkout. |
| `claude/wt-fstar-catchup` | LANDED | merge on main | F* ports of Lean fixes. F* proof corpus and extraction checks pass. `.agent-notes.md` of main kept. |
| `claude/qt4-cfg-xsd10` | NEEDS-WORK | pending | PR 264. 33 conflict blocks, mostly Qt4Run and Core. |
| `claude/qt4-cfg-version-modes` | NEEDS-WORK | pending | PR 262. 18 conflict blocks; its build failed before; it commits .log files (issue 1101). |
| `claude/qt4-cfg-xml-layer` | NEEDS-WORK | pending | 12 conflict blocks; stopped at a usage limit; not measured. |
| `claude/values-seeded-join-wip-20261023` | NEEDS-WORK | 02c328719 took the VALUES leaf | Three theorem drafts that do not build stay here; issue 985 tracks them. Old history, no common ancestor. |
| `claude/wasm-components-clock-findings` | SKIPPED | kept | A subagent reads this branch now (instruction of 5 November). |
| `port/laptop-20260908-owl-dl` | SKIPPED | kept | PR 339. Owner decision: 13,000 lines under _lostandfound. |
| `claude/svg-tiny-pixels` | SKIPPED | kept | PR 360. In active use by session depmap-9b. |
| `claude/hub-sparql-rl` | ALREADY-ON-MAIN | ancestor of main; tag `archive/claude/hub-sparql-rl` | Merged by PR 216. |
| `claude/hub-pods-and-bots-0.21` | ALREADY-ON-MAIN | ancestor of main; tag `archive/claude/hub-pods-and-bots-0.21` | The tip is an ancestor of main. |
| `codex/web-inventory-ci` | ALREADY-ON-MAIN | b0d59a38e, 700457f6a; tag `archive/codex/web-inventory-ci` | All added lines are on main. A later inventory replaced the first commit. |
| `codex/graphics-ci-repairs` | ALREADY-ON-MAIN | be4f66846, 1f5b1d8b4, bf0565d37; tag `archive/codex/graphics-ci-repairs` | Patch-equivalent (git cherry). |
| `codex/svg-standards-overnight` | ALREADY-ON-MAIN | f68992b1c, 69f19579d, c8e2e2eab; tag `archive/codex/svg-standards-overnight` | Patch-equivalent; later SVG work changed the same lines. |
| `codex/native-graphics-source-preparation` | ALREADY-ON-MAIN | 48e3ccfce; tag `archive/codex/native-graphics-source-preparation` | Only comment wording differs from main. |
| `claude/qt4-xquery-2` | ALREADY-ON-MAIN | 51df04684, f1a4138ac; tag `archive/claude/qt4-xquery-2` | The same two commits are on main through PR 210. |
| `claude/rel020-integration` | ALREADY-ON-MAIN | release 0.20.0; tag `archive/claude/rel020-integration` | Released. 97% of added lines are on main; the rest is changelog text. |
| `claude/rel020-release-fixes` | ALREADY-ON-MAIN | release 0.20.0; tag `archive/claude/rel020-release-fixes` | Released. The same three commits as claude/rel020-integration. |
| `batch3/kr12-percache` | ALREADY-ON-MAIN | 0719cb057; tag `archive/batch3/kr12-percache` | Patch-equivalent. |
| `batch3/kr12-rss` | ALREADY-ON-MAIN | 3ca2f4b55, 6f2e4484f; tag `archive/batch3/kr12-rss` | Patch-equivalent. |
| `batch3/kr12-parallel` | ALREADY-ON-MAIN | 3ca2f4b55; tag `archive/batch3/kr12-parallel` | Patch-equivalent. |
| `batch3/kr11-d12` | ALREADY-ON-MAIN | 6121f4982; tag `archive/batch3/kr11-d12` | Patch-equivalent. |
| `batch3/kr11-d14` | ALREADY-ON-MAIN | a407748f0; tag `archive/batch3/kr11-d14` | Patch-equivalent. |
| `batch3/kr11-d14b` | ALREADY-ON-MAIN | d0395d928, 01a8901be, removed by 4ff10b875; tag `archive/batch3/kr11-d14b` | On main, then 4ff10b875 removed the typed FILTER on key bytes on purpose: main compares in the XSD value space (issue 948). |
| `batch3/kr11-d14c` | ALREADY-ON-MAIN | d0395d928, 01a8901be, 30d272061; tag `archive/batch3/kr11-d14c` | As batch3/kr11-d14b, plus 30d272061. |
| `batch3/kr11-d17` | ALREADY-ON-MAIN | ddcd9e546; tag `archive/batch3/kr11-d17` | 99% of added lines are on main. |
| `batch3/kr13-reserve` | ALREADY-ON-MAIN | bda314ac2; tag `archive/batch3/kr13-reserve` | Patch-equivalent. |
| `batch3/kr14-activation-disk` | ALREADY-ON-MAIN | 176e56685; tag `archive/batch3/kr14-activation-disk` | Patch-equivalent. |
| `batch3/kr23-parallel-pack` | ALREADY-ON-MAIN | 3b3370cf5; tag `archive/batch3/kr23-parallel-pack` | 98% of added lines are on main. |
| `batch3/kr24-export-memory` | ALREADY-ON-MAIN | 1ba45311f; tag `archive/batch3/kr24-export-memory` | Patch-equivalent. |
| `batch3/kr31-audit` | ALREADY-ON-MAIN | f12001c5f to 9ad44ac73; tag `archive/batch3/kr31-audit` | Patch-equivalent. |
| `batch3/kr44-webmcp-llm` | ALREADY-ON-MAIN | f6917c3a4; tag `archive/batch3/kr44-webmcp-llm` | Patch-equivalent. |
| `xmpp-serve` | ALREADY-ON-MAIN | 750190752; tag `archive/xmpp-serve` | The same commit is on main; later XMPP work changed its lines. |
| `claude/owl-checked-consistency-review` | ALREADY-ON-MAIN | 65b247150, 87fd052ee, 87af61c9b; tag `archive/claude/owl-checked-consistency-review` | The same three commits are on main. |
| `claude/main` | DEAD | replaced by main; tag `archive/claude/main` | Pre-split history of August (no common ancestor). The Lean tree moved to main; the rest is F* and CI files that main removed or moved. |
| `archive/codex-906527b` | DEAD | replaced by main; tag `archive/archive/codex-906527b` | Old history (no common ancestor). Shardborough work was applied again on main (4bfa8b49, 69e92e14, 19a32098). Only dated JSON benchmark records are not on main. |
| `claude/autoexec-scratchpad-assess-37oeok` | DEAD | replaced by main; tag `archive/claude/autoexec-scratchpad-assess-37oeok` | The same tip as archive/codex-906527b. |
| `claude/standards-reuse-20261022` | DEAD | f1f78d987; tag `archive/claude/standards-reuse-20261022` | Landed as f1f78d987. Record: docs/20261022-standards-reuse-review.md. |
| `claude/hash-grouping-wip-20261022` | DEAD | bbc314325; tag `archive/claude/hash-grouping-wip-20261022` | Superseded: main has its own proved hash grouping. Record: docs/20261022-standards-reuse-review.md. |
| `claude/docs-0.17-0.19` | DEAD | none; tag `archive/claude/docs-0.17-0.19` | README text for releases 0.17 to 0.19. PR 151 was closed. Main describes 0.32.0. |
| `claude/rel022-tailrec-allow` | DEAD | none; tag `archive/claude/rel022-tailrec-allow` | Every allow-list line is on main already. PR 238 was closed. |
| `fix/issue-961-fd` | DEAD | stage 1n record; tag `archive/fix/issue-961-fd` | The measurement showed no gain: a warm run reads about 89 ranges, and one shared descriptor was slower at 4 threads. Record: issue 961, docs/designissues/2026-10-12-parallel-block-scans.md, stage 1n. |
| `batch3/kr11-d19` | DEAD | db0ec5663, 9a77a9c8e; tag `archive/batch3/kr11-d19` | Two AggStream commits were not landed; main took another path (d19 warm 208 ms; issue 862 closed). |
| `batch3/kr11-d19b` | DEAD | db0ec5663, 9a77a9c8e; tag `archive/batch3/kr11-d19b` | As batch3/kr11-d19. |
| `claude/kr1-1025` | DEAD | ea6e6b6e5, PR 83; tag `archive/claude/kr1-1025` | PR 85 was closed as superseded by PR 83. Main has Storage/Medium.lean and openSbm11. |
| `claude/kr1-1025-medium-dataflow-draft` | DEAD | ea6e6b6e5, PR 83; tag `archive/claude/kr1-1025-medium-dataflow-draft` | As claude/kr1-1025, plus an untested draft of a medium dataflow stage. The tag keeps that draft. |
