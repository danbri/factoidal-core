# Mixed CPU/WebGPU SPARQL queries

2026-11-22. Implementation and assurance record for the ordinary query API
and the registered `gpuSparqlStage` node.

The parser, query planner, RDF matching, query modifiers and result writers
remain in Lean. An eligible join suspends a Lean continuation while the host
executes Lean-generated PVGraph kernels. The host returns numeric buffers;
Lean validates them, reconstructs bindings from its retained RDF values, and
continues the query. This source requires an engine built with the four
`datasetQueryGpu*` entries; it does not imply that an older published binary
contains them.

## Public interface

Both `query(data, sparql, options)` and `dataset.query(sparql, options)` accept:

| Option | Default | Meaning |
| --- | --- | --- |
| `execution` | `"auto"` | Lean estimates eligible joins when a suitable WebGPU adapter is available; other work runs on the CPU. `"cpu"` retains the existing CPU entry. `"gpu"` requires an observed GPU join and rejects device or admission failures. |
| `gpuMinRows` | `1024` in auto, `1` in gpu | Minimum actual row count on **each** side of a candidate join; integer from 0 to 1,000,000. Other eligibility and capacity checks still apply. |
| `gpuMaxPairs` | `1000000` | Maximum numeric candidate pairs for one join; integer from 0 to 2,097,120. Counted before allocating the expanded GPU output. |

```js
const sparql = `SELECT ?s ?value WHERE {
  ?s <urn:relation> ?o .
  ?o <urn:value> ?value
} ORDER BY ?s ?value`;

const automatic = await dataset.query(sparql);
const cpu = await dataset.query(sparql, { execution: "cpu" });
const observed = await dataset.query(sparql, {
  execution: "gpu", gpuMinRows: 1, gpuMaxPairs: 1000000
});
console.log(observed.execution);
```

The mixed-session path attaches non-enumerable `execution` metadata to
SELECT row arrays and CONSTRUCT/DESCRIBE datasets. It records the selected
backend, placement reason, GPU join count, CPU fallback count, per-join input
and candidate counts, and observed dispatch phases/timings. This metadata is
not part of a solution binding. An ordinary CPU entry may have no such
property. ASK remains a boolean, and explicitly formatted results retain
their existing return shape; those values do not carry this property.

Automatic placement excludes adapters identified as software or fallback
adapters. Explicit `execution: "gpu"` can exercise them for validation.
The decision to disable automatic GPU use is cached for that API instance;
later automatic queries take the ordinary CPU entry. Required GPU execution
can still request the device.
WebGPU availability alone is not evidence that a query will run faster.

## Placement and query coverage

[`GpuQuery.worthwhile`](../../formal/lean4/L4Factoidal/SPARQL/GpuQuery.lean)
performs a cheap preflight against the existing backend's cardinality
estimates. It accounts for constant subjects, predicates and objects,
shared variables, disconnected patterns, named graphs, FROM clauses,
VALUES and subqueries. It does not materialise solution rows. When the
estimate offers no useful join, the session retains the previously used CPU
evaluator, including the reference path for entailment and explicit output
formats.

Once evaluation begins, Lean checks actual input cardinalities and missing
keys at each join. These are conservative admission heuristics, not a
calibrated model of launch latency, transfer time or indexed CPU lookup
cost. Estimates can miss an opportunity or admit a join that later takes
the CPU fallback. Neither changes query semantics.

GPU candidates are available for general triple-pattern extensions and
SPARQL inner joins. The continuation composes them through FILTER, UNION,
OPTIONAL, MINUS, fixed and variable GRAPH, BIND and subquery modifiers.
OPTIONAL and MINUS still use their existing Lean join operations; their
children can contain GPU joins. Correlated SERVICE joins, LATERAL and other
unsupported operations retain complete CPU evaluation. Joins without a
usable common key, including relevant unbound-variable cases, also retain
their reference CPU operation.

SELECT, ASK, CONSTRUCT and DESCRIBE use the existing finalisation functions.
Projection, DISTINCT/REDUCED, grouping, aggregates, ORDER BY, OFFSET/LIMIT,
trailing VALUES, template instantiation, blank-node handling and DESCRIBE's
description policy are not reimplemented by the host. The mixed evaluator
preserves the exact reference solution list, including duplicate
occurrences and order. It does not rely on a claim that the shipping CPU
planner's triple-pattern reordering preserves list order.

## Numeric join and RDF reconstruction

[`IndexedJoin`](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/IndexedJoin.lean)
is independent of RDF. It joins UInt64 keys and returns original row-index
pairs, ordered first by the left occurrence and then by the right occurrence.
Its shared PVGraph primitives support lexicographic tuples of up to sixteen
UInt64 columns, represented by low/high UInt32 lanes. The SPARQL adapter uses
one UInt64 hash of a canonical RDF key tuple.

The execution is:

1. Lean retains the original bindings and triples. A shared lazy RDF index
   selects constant-constrained graph candidates in original graph order
   before encoding their keys; a selective predicate does not transfer the
   entire graph for each join.
2. Lean sorts right-side numeric keys, breaking ties by original row index.
   The GPU performs parallel lower/upper-bound searches for the left keys.
3. Lean validates the complete intervals against the prepared sorted index
   and sums their lengths using unbounded `Nat`. Output and allocation
   limits are checked here, before prefix-sum or expansion buffers exist.
4. The GPU scans counts and expands only the admitted matching segments.
   There is no left-by-right Cartesian candidate buffer. Equal-key
   duplicates still produce their full multiplicity, subject to capacity.
5. A streaming Lean decoder checks every returned index, its required order,
   omissions and extra words while translating right-side indices back to
   original positions. It does not allocate a second reference pair buffer
   or repeat the searches or nested reference join.
6. Lean applies the original `tpMatch` or binding compatibility/merge
   operation to the retained payloads. A hash collision can add candidates
   but cannot add a SPARQL solution. Every true RDF match has equal
   canonical keys, so hash filtering cannot remove it.

Preparation sorts `R` right rows in `O(R log R)` on the CPU. Binary searches
have a fixed 32-iteration bound, and segment expansion is output-sensitive.
Interval validation is linear in `L` left rows; readback validation and
reconstruction are `O(L + K)` for `K` candidate pairs. CPU sorting, RDF
encoding, serialization, transfers and exact RDF checks remain part of the
end-to-end cost. GPU dispatch timing alone does not measure that cost.

## Suspension, replay and resources

[`Wasm/Ops/GpuSparql.lean`](../../formal/lean4/Wasm/Ops/GpuSparql.lean)
owns the query session. Its dataset, active graphs, SERVICE snapshots,
extension-function registration snapshot and NOW value are retained across
all suspensions. The host's extension memo and JavaScript function snapshot
are per evaluation. Async extension resolution restarts the same frozen
query session, and reruns the SERVICE failure check. A GPU wait does not
leave one query's extension context installed for another query.

`datasetQueryGpuBegin`, `datasetQueryGpuStep`, `datasetQueryGpuRestart` and
`datasetQueryGpuClose` are the ABI. Replies carry a monotonically advancing
request ID; stale or wrong-phase replies are refused. The first eligible
continuation requests device facts before numeric index preparation or
PVGraph plan encoding. The first job's canonical RDF hash-key arrays already
exist at this point. Lean then decides whether automatic execution should
continue on that adapter. A software-adapter refusal completes the retained
continuation on the CPU, and async replay keeps GPU admission disabled.
The host closes the
session in a `finally` block and releases per-plan GPU buffers. Compiled
pipelines can be reused by the resident transport.

Each input relation is limited to 1,000,000 rows. A session admits at most
256 join requests; at most 32 sessions are live. Automatic execution uses
the CPU when a device, an admission, a readback or an output capacity is
unavailable. Exhausting its join-request budget completes the remaining
continuation on the CPU; exhausting session capacity selects the ordinary
CPU entry. Explicit `"gpu"` execution reports a refusal. No capacity check
returns a truncated solution sequence.

## Shipping registry and proof boundary

The registry entry
[`gpuSparqlStage`](../../formal/lean4/L4Factoidal/Dataflow/GpuSparqlStage.lean)
has a real npm runner in
[`nodes.mjs`](../../npm/factoidal/lib/nodes.mjs). It calls the ordinary query
API with `execution: "gpu"`, so a CPU-only success cannot impersonate this
node's GPU execution:

```js
import { node, run } from "@factoidal/core";

const evaluate = await node("gpuSparqlStage", {
  query: sparql, gpuMinRows: 1, gpuMaxPairs: 1000000
});
const result = await run(evaluate, dataset, { unchecked: true });
console.log(result.evidence.at(-1).artefact.execution);
console.log(result.assumptions, result.proved);
```

The IO registry retains status `assumed` and literally lists
`GpuSparqlDeviceLaw` in `ioAssumptions`; pipeline evidence retains that name.
The pure numeric validation and SPARQL refinement compose as follows:

| Theorem | What it establishes |
| --- | --- |
| `IndexedJoin.accepted_join_eq_reference` | Successful actual `prepare?`, range JSON decoding and pair JSON decoding produce the complete original ordered numeric equijoin. Arbitrary corrupt, omitted, repeated or reordered output is rejected. |
| `GpuQuery.decodePairs_pairs`, `candidateJoin_sound` | Numeric occurrence indices reconstruct the specified payload join; canonical hash equality plus exact RDF checks preserves every result. |
| `GpuQuery.bgpStep_sound`, `innerJoin_sound`, `pattern_sound` | Each eligible join and its surrounding algebra preserve the reference solution sequence under valid numeric replies or CPU refusal. |
| `GpuQuery.begin_sound`, `gpuSparqlPlan_sound` | The complete mixed plan returns the reference answer for every query form under the stated numeric reply law. |
| `checkedGpuSparqlDeviceReply_valid` | The production numeric acceptance functions establish that reply law for arbitrary raw JSON buffers, including missing or corrupt replies. Invalid replies become CPU refusals. |
| `checkedGpuSparqlPlan_sound` | Composing those checked replies with the complete mixed plan returns exactly `referenceAnswer`, with no numeric-device correctness or GPU-fidelity premise. |

The numeric parser theorem is proved in
[`IndexedJoinCorrectness.lean`](../../formal/lean4/L4Factoidal/GpuDomainSpecificLanguage/IndexedJoinCorrectness.lean),
including stable-sort and interval-completeness lemmas.
[`GpuSparqlReadback.lean`](../../formal/lean4/L4Factoidal/Dataflow/GpuSparqlReadback.lean)
composes the actual preparation, capacity checks, range decoder and streaming
pair decoder with the continuation evaluator. Its final theorem quantifies
over arbitrary raw device replies: the numeric law is discharged by the
validators rather than left as a trust premise. The proof uses no hash
injectivity assumption and no CPU replay of a successful SPARQL query.
Theorem axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`.

`checkedGpuSparqlDeviceReply_valid` establishes `GpuSparqlDeviceLaw` for the
pure checked-reply function. A refinement proof connecting the complete
stateful session, ABI and host to that pure composition has not been
supplied. The registry therefore still lists `GpuSparqlDeviceLaw` for the
actual IO execution; it has not replaced it with a separately formalised
session-execution law. That effectful implementation, delivery of retained
request/reply values and resource lifecycle require integration evidence.
Physical WGSL compilation and GPU execution determine whether a dispatch
succeeds and how long it takes; their numerical fidelity is not a premise
of the pure checked-answer theorem. Sorting, interval completeness, numeric
reconstruction and SPARQL semantics are covered by the proof chain above.

## Validation and performance status

[`GpuQueryTests.lean`](../../formal/lean4/L4Factoidal/SPARQL/GpuQueryTests.lean)
compares the actual continuation evaluator with the reference through a
numeric model, all-CPU refusals and mixed refusals. It covers all four query
forms, modifiers, named graphs/FROM, subqueries, unbound values, duplicate
solutions, collisions, UInt64 high lanes, observed placement and selective
right-side transfers.

The device gates are
[`pvgraph-gpu-device-smoke.mjs`](../../tools/pvgraph-gpu-device-smoke.mjs)
for generic PVGraph execution and
[`pvgraph-query-device-smoke.mjs`](../../tools/pvgraph-query-device-smoke.mjs)
for the shipping query session and registry. They require an actual WebGPU
adapter and record its identity, executed phases, timings and source
provenance. A software WebGPU adapter exercises the device API but is not
evidence of hardware acceleration.

This document claims no physical-GPU speedup. A useful crossover must be
measured with the complete optimized native or Wasm pipeline against the
existing indexed CPU evaluator, on the same dataset, query and device,
including preparation, transfer, validation and reconstruction. The default
threshold is a conservative heuristic pending those measurements.
