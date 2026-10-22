# Stable hash grouping — 2026-10-11

The varied corpus exposed a large GROUP BY cost: 5.77 seconds for 300,000
rows in 100 groups, against QLever's 4.41 ms. A separate profile at 100,000
rows found `groupSolutions` in 3,715 of 3,852 sampled worker stacks. These
are prior-stage measurements; the sampled requests are not latency samples.
The owner has asked to continue beyond parity towards SOTA performance.

## Lean implementation and exact refinement

`SPARQL.StableGrouping` accumulates groups in an array with a hash map from
encoded keys to positions. This keeps the first-appearance order of groups.
Rows are prepended during accumulation and reversed once, which retains
input order without repeated append. The generated C consumes the state
and modifies its group array. On a new group, the old array size is read
before push, avoiding an extra live array reference and a copy.

The generic proof does not assume that the original Boolean relation is
an equivalence relation. An exact encoder must identify precisely the class
of each admitted key. A bidirectional invariant certifies every group address
and every map entry. Unsupported keys transfer to a list accumulator whose
reverse-row representation also refines the reference. In particular, a
non-transitive fallback relation can still update several existing groups.
`StableGrouping.fast_eq` proves equality of the complete ordered groups and
their complete ordered rows for every input sequence.

`SPARQL.HashGrouping` instantiates this contract for existing `keysEqual`
and `erEqual`. Admitted keys include unbound values, IRIs, blank nodes,
Booleans and literal datatype/lexical/language fields, including compound
keys. The encoder follows existing SPARQL ordering equality. It does not
use `Term.joinKey`, whose normalization serves a different equality.
Literal direction remains absent because the existing literal ordering does
not compare it; raw language-tag case remains present. Numeric expression
results and triple terms retain the exact fallback. These boundaries
preserve the current evaluator; they are not new standards compliance claims.

`atom_exact`, `key_exact` and `groupSolutionsFast_eq` prove the specialization.
`selectPostFast_eq` proves equality with the entire reference SELECT post
phase for every query, environment, active graph and ordered input. This
includes group aliases, HAVING, post-query VALUES, projection, ORDER BY,
DISTINCT/REDUCED, OFFSET and LIMIT. Only explicit GROUP BY accumulation
changes. The ungrouped and implicit aggregate paths call the reference.

The native backend and two direct disk SELECT paths call this proved wrapper.
The reference evaluator and subquery lowering retain their existing call
sites. There is no compiler replacement of `selectPost` that could make
the fallback recurse into itself. Existing snapshot, metadata and ordered
access refinements must build with the changed backend boundary.

All audited new theorems use only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`). There is no `sorry`, custom axiom or
`native_decide`. F* lineage is `formal/fstar/SPARQL11.Algebra.fst`,
`eval_group_key`, `keys_equal`, `add_to_groups` and `group_by`. The array/hash
algorithm and its refinements are new Lean work, not an inherited F* proof.

## Tests and measurement boundary

Eleven generic guards precede the implementation, followed by seventeen
SPARQL key/group guards and a 60-query modifier matrix plus a fallback guard.
Retained red logs record the missing optimized APIs before implementation.
`tools/blockengine-grouping-test.py` checks fifteen independent complete
answers through both pinned snapshots and fresh native disk queries. It
covers aliases, compound keys, unbound keys, numeric equality fallback,
language-tag ordering, HAVING, VALUES, slicing and ordered GROUP_CONCAT.
These native cases first pass on the archived, unoptimized engine.

The same nine-family relational corpus and exact construction-based answer
oracle remain in use. Local before/after pairs alternate two snapshots;
competitor runs alternate JSONL and HTTP requests. Opening is separate;
RSS after readiness is not peak memory. Builds, correctness checks, profiles
and benchmark windows run separately. Every timed response must match the
complete expected ordered answer, without datatype coercion.

## Host interruption and benchmark correction

The small 5,334-triple pilot passes all nine exact answers, but heavy Chrome
GPU CPU use excludes its timings. The first large pair and QLever run also
pass all complete answers, but the later host power audit shows sleep within
both windows. Their plausible-looking uptime medians do not make those
windows valid. The first Virtuoso run fails with HTTP 500 during sleep/wake.
All these reports remain retained and excluded from performance evidence.

macOS `perf_counter_ns` excludes system sleep. The shared driver now compares
wall-clock and uptime elapsed values over the entire run, including gaps
between requests. More than one second of divergence rejects the measurement;
large wall-clock steps also reject conservatively. Six test-first cases cover
normal time, suspend, forward/backward steps, tolerance and its boundary.
Two complete real-driver runs inject a suspend check failure and verify that
both the local pair and competitor report invalid timing despite exact answers.

Protected reruns use an owned `caffeinate -i` process, which inhibits idle
sleep for that command and changes no global power settings. CPU activity is
still recorded separately. The successful complete Virtuoso retry predates
the clock guard but has a separate power-log audit with no sleep/wake event;
its grouping latency is repeated with the new guard.

## Protected local measurement

The 1,570,231-triple fixture has 300,000 input rows and 100 groups for this
query. Five alternating measured requests follow one warmup for each binary.
The protected pair measures grouping plus two unchanged control workloads:

| Query | Before (ms) | After (ms) |
| --- | ---: | ---: |
| Grouped COUNT as string | 5807.515 | 147.812 |
| Selective chain | 13.423 | 13.212 |
| Numeric top-k | 160.086 | 160.766 |

Grouped COUNT improves **39.3-fold**. Each complete response matches the
independent oracle. The clock difference over the 62-second run is 2.3 ms,
within the one-second rejection bound. Controls remain close to their prior
medians. The earlier 523,477-triple pair also passes all nine full answers;
its raw samples remain in the JSON record, without a cross-size scaling claim.

## Competitor reruns and remaining gaps

At 1,570,231 triples, all nine complete answers match QLever 0.6.0 and
Virtuoso 7.2.17. The protected QLever run uses three measured requests after
one warmup, alternating paired order. Its whole-window clock difference is
3.8 ms. The following medians include full result serialization and transfer:

| Query | Shardborough (ms) | QLever (ms) |
| --- | ---: | ---: |

| chain-two | 882.443 | 1174.030 |
| chain-three | 1168.969 | 1195.887 |
| dimension-join | 830.601 | 1194.173 |
| selective-chain | 14.270 | 21.918 |
| optional-alias | 335.812 | 16.020 |
| union-distinct | 648.489 | 22.176 |
| group-count-string | 153.114 | 4.448 |
| numeric-top | 160.995 | 3.015 |
| values-chain | 588.375 | 9.847 |

The separate protected Virtuoso grouping run measures **148.948 ms versus
8.749 ms**, with every full answer exact and a 0.8 ms whole-window clock
difference. The earlier successful retry checks all nine families, with no
sleep/wake event during its complete interval. Its samples are retained
separately rather than merged with the protected grouping rerun.

QLever uses a 1 GB loader budget, a 1 GB query budget, no result cache,
and one concurrent query; its operator parallelism remains the default.
Virtuoso uses the retained 10,000-buffer configuration, 256 MB query budget
and one query thread. Shardborough is a single immutable full-graph snapshot
using JSONL; the competitors use HTTP. These are scoped local measurements,
not tuned, resource-matched production comparisons. Group counts are strings
specified by STR in the query; there is no datatype coercion or answer exclusion.

Snapshot admission in the protected competitor runs is approximately
9.15 seconds. RSS after readiness is 868 MiB for Shardborough, not peak RSS.
The optimization changes transient grouping, not the persisted layout or
snapshot indexes. The proof does not establish a new peak-memory bound.

**SOTA remains open.** The grouped query is still about 34 times slower
than QLever. VALUES, numeric top-k, OPTIONAL and UNION DISTINCT retain
large gaps. The next physical work is selective access before full row
construction, aggregate pushdown and reduced binding allocation. The new
profile has grouping in 1,428 of 3,714 worker stacks, against 3,715 of 3,852
before; row construction and aggregate evaluation now account for much of
the remaining work. These profiles are diagnostics only.

Standard benchmark suites, production data, larger graphs, tuned competitor
resources, concurrency, updates and recovery remain required. The original
[SP²Bench generator and query suite](https://dbis.informatik.uni-freiburg.de/forschung/projekte/SP2B/)
is one next validation target; this controlled corpus is not that benchmark.

## Revalidation — 2026-10-16

The resumed worktree matches all 36 retained source/log hashes and the recorded
snapshot executable hash. A fresh library, snapshot, triple-query and W3C
runner build passes 720 jobs. All fifteen independent grouping cases pass
through both fresh and snapshot routes; complete JSON smoke checks pass for
IBK3, IBK4 and IBK5. The six clock and five competitor-exclusion guards pass.
These checks validate the pending implementation; they do not refresh the
dated competitor timings or establish parity. Unrelated workspace files are
not part of this change.

## Validation and retained evidence

- Full Lean library plus relevant native targets: **747 successful jobs**.
- W3C SPARQL reference/harness run: **631 pass, zero fail, skip or unsupported**.
  This harness retains its existing comparison tolerances; it is not a native
  server certification. Native exact answers and the wrapper theorem cover
  the changed physical boundary separately.
- Fifteen new grouping answers pass on both the archived and optimized native
  engines, through both fresh CLI and snapshot routes.
- Existing snapshot admission, isolation, delta, error recovery, Unicode/control
  escaping and IBK3/IBK4/IBK5 complete JSON checks pass.
- Six clock guards and both injected-suspend integration checks pass. Existing
  five competitor-answer exclusion guards and Python compilation pass.
- Reference `SPARQL/Query.lean` is byte-identical to the archived baseline.

`docs/20261011-shardborough-hash-grouping.json` records source and binary hashes,
theorem scope, test-first red logs, raw reports, preparation, resource settings,
clock readings, power audit and explicit exclusions. Large interrupted reports
remain marked valid by the old drivers internally; the evidence record overrides
that assessment with `timing_eligible=false`. Their answers remain correctness
evidence. No owned benchmark, server, profiler or sleep assertion remains running.
