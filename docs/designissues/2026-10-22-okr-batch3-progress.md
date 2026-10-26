# OKR batch 3: progress and coordination record (2026-10-22)

Batch issue: https://github.com/danbri/factoidal/issues/875 (approved by the
owner on 2026-10-22: "Batch 3 / Work on Batch 3 progress. Issue 880: refusal.").
Index: https://github.com/danbri/factoidal/issues/404.

## Landed on `main` (2026-10-22)

| KR | Commit | Result |
| --- | --- | --- |
| Issue 880 (owner decision: refusal) | a1315ca1, c324cbbe, d89068fe | IBK4 and IBK5 refuse a pack that declares a named graph with no triple, and refuse every update (their query paths do not replay the delta log: https://github.com/danbri/factoidal/issues/935). IBK3 updates still commit and are visible. Issues 880 and 934 closed. |
| 1.1 (d13) | aba9a13a | STRSTARTS window on the scan column: d13 433 ms to 1.95 ms (QLever 1 CPU 26.45 ms). Slower than QLever now 4 of 19: d12 https://github.com/danbri/factoidal/issues/931, d14 https://github.com/danbri/factoidal/issues/930, d17 https://github.com/danbri/factoidal/issues/932, d19 https://github.com/danbri/factoidal/issues/862. Issue 929 closed. |
| 2.1 | 5a40d08e | RDF/XML source read one child of rdf:RDF at a time: pack memory 12.7 to 0.48-0.51 bytes per source byte (bound 0.75). Issue 838 closed; the equality theorem of the children phase is https://github.com/danbri/factoidal/issues/936 (expected failure RX-1). |
| 4.1 | 7e960256 | Plans run against an SBM11 generation through IO (`Plan.execM`, `execM_eq_exec`). The planner accepts 8 of 113 gate queries (no FILTER or GRAPH yet). The run-time driver over IO: https://github.com/danbri/factoidal/issues/933. |
| 4.2 | b65a82ea | Run-time adaptation from measured rows and latency, a cache of call results (`reachable_cache_hit`), row quotas at run time, quotas in admission. |
| 4.3 | 0383de52 | Probes as costed work (`wantProbe_iff_saving`); issue 937 closed. Planner tests 91 pass, 0 fail, 15 expected-fail (out of 106). |

Done by another session in the same window: issue 872 (7bb6b55e, part of KR
3.2) and work on issue 873 (KR 2.5). KR 2.5 is left to that session.

## In flight at 14:10 UTC (pushed to branches, not to `main`)

The owner asked at about 14:10 UTC that this session not touch `main` for 90
minutes, so that another session can land LWS, XMPP and identity work. The three
running agents push to `batch3/<kr>` branches instead:

- `batch3/kr11-d14`: KR 1.1, d14 (https://github.com/danbri/factoidal/issues/930).
- `batch3/kr14-activation-disk`: KR 1.4, activation temporary disk (https://github.com/danbri/factoidal/issues/810).
- `batch3/kr44-webmcp-llm`: KR 4.4, WebMCP and LLM capabilities, plus issues for
  the two probe gaps of KR 4.3.

To land one after the pause: `git fetch origin main batch3/<kr>`, check out the
branch, `git rebase origin/main`, rebuild (`lake build` in `formal/lean4`), run
the gates its commit message names, check
`git merge-base --is-ancestor origin/main HEAD`, push to `main`, delete the
branch.

## Not started

KR 1.2 (parallel scans), 1.3 (Lean kernel against C), 2.2 (JSON-LD streaming
form), 2.3 (Turtle and TriG pack in parallel), 2.4 (export memory and issue
878), 3.1 (502 untriaged audit entries), 3.3 (csimp reach in CI), and the KR 1.1
queries d12, d17, d19.

## Coordination lessons

- Two coordinator sessions pushed to `main` at the same time on 2026-10-22. The
  other session saw store and planner pushes it could not place. Each
  coordinator states in its batch issue which areas it lands, and a pause on
  `main` is kept by pushing finished work to `batch3/<kr>` branches.
- A worktree copy of the build cache is only useful when it was built with the
  current toolchain (Lean v4.33.1 since this week): copy from the newest
  worktree build, not from an older checkout. Three full builds at once on 4
  CPUs took 15 to 20 minutes each.
- Free disk fell to 3.0 GB with three worktrees. Keep at most two worktrees, and
  let the third agent use the main checkout.

## Final state (2026-10-24; written 2026-10-26)

Source: the comments of https://github.com/danbri/factoidal/issues/875 (OKR
batch 3), last one 2026-10-24 13:40 UTC. The sections above are the state at
14:10 UTC on 2026-10-22; every branch named there has landed on `main`.

Batch 3 is finished. Every KR is met except KR 1.2 for query q07.

- O1, SBM11 against QLever. KR 1.1 met: 18 of 19 queries are as fast as
  QLever on 1 CPU or faster (d12 7.55 ms against 10.10 ms; d14 6.03 ms
  against 6.09 ms; d13 and d17 earlier). d19 is 208 ms, 2.0 times QLever,
  within its acceptance target of 300 ms, with the remaining cost named in
  section 11.21 of `2026-10-12-three-engine-benchmark.md` (the KR allows a
  named remaining cost). KR 1.3 met (1.69 times C,
  https://github.com/danbri/factoidal/issues/797). KR 1.4 met (activation
  temporary disk 4.9 to 0.12 times the generation,
  https://github.com/danbri/factoidal/issues/810).
- KR 1.2, 4 threads against 1 thread: closed by the owner on 2026-10-24,
  answer "Close: 3 of 4 met". 4/1 time (target at most 0.4) and peak RSS 4/1
  (target at most 2): d10 0.39 and 1.21, q19 0.38 and 1.80, q21 0.36 and
  1.67 (met); q07 0.50 and 1.22 (time not met). d17 was removed from the KR
  (owner, 2026-10-23, "Remove it": block metadata answers it with no scan).
  Stages 1e to 1p of `2026-10-12-parallel-block-scans.md`. q07 stays open in
  https://github.com/danbri/factoidal/issues/961 (parallel scans, remaining
  costs).
- O2, every syntax in bounded memory: KR 2.1 to 2.5 met
  (https://github.com/danbri/factoidal/issues/873 closed for 2.5).
- O3, stated cost bounds: KR 3.1 to 3.3 met.
- O4, run-time planner: KR 4.1 to 4.4 met.

Follow-ups named at the close, with their state on 2026-10-26:

- https://github.com/danbri/factoidal/issues/949 (long N-Triples and N-Quads
  lines still cost a `List Char`): closed.
- https://github.com/danbri/factoidal/issues/957 (RDFC-1.0 of a dataset with
  an RDF 1.2 triple term: no W3C rule): open, refusal with expected failure.
- https://github.com/danbri/factoidal/issues/958 (OWL 2 Direct Semantics
  checks on a graph with an RDF 1.2 triple term: no mapping rule): open,
  refusal with expected failure.
- https://github.com/danbri/factoidal/issues/960 (OWL public verdicts: model
  certificate, admission, fuel, checked countermodel): closed.
- https://github.com/danbri/factoidal/issues/973 (no theorem that graph
  operations keep a graph a set): closed.
