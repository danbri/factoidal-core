# Streaming JSON escaping — 2026-10-11

Shardborough's native JSON writer now walks each string directly and pushes
ordinary Unicode characters into its output accumulator. It retains the
exact existing escaping output. The previous implementation built character
and escaped-string lists for every value and field name.

## Evidence and Lean refinement

A separate five-second sample of the previous binary's repeated two-pattern
join found result serialization in about 70% of sampled worker stacks.
`JSON.escapeString`, character-list construction and escaped character
strings appeared prominently. This diagnostic run followed all benchmark
timing windows and is not a latency measurement. Its first setup attempt
failed before profiling because of a driver argument error; the successful
retry and failed setup record are retained in the prior stage's evidence.

`JSON/Serialize.lean` keeps the original `escapeString` specification.
`appendEscaped` appends the existing escape string for controls, quotes and
backslashes; it uses `String.push` for an ordinary character. The theorem
`appendEscaped_eq` proves that step equals appending `escapeChar` for every
accumulator and character. `escapeStringFast` folds that step directly over
the string. `escapeStringFast_eq` uses the standard string-fold refinement
and list-fold mapping identity to prove equality for every string.

`escapeString_csimp` installs the proved function equality before the compact
JSON writer is compiled. Generated C confirms that JSON value/field writers
and SPARQL result variable names call `escapeStringFast`. Its loop uses
Lean's UTF-8 character iteration and string push primitives; it does not
construct character lists. There is no new foreign implementation.

The complete output string, and therefore its UTF-8 bytes, is unchanged for
all strings. Mandatory escapes, lowercase hex digits, Unicode scalars and
embedded NULs retain the original behavior. Object field order, RDF terms,
duplicates, bindings and document wrappers keep their previous definitions.
The existing `ResultsJsonFastTheorems` complete-result and byte-equality
refinements still build. Axiom audits list only `propext`, `Classical.choice`
and `Quot.sound`; no new assumptions or admitted proofs are used.

F* lineage remains `formal/fstar/SPARQL.JSON.Escape.fst`'s `json_escape` and
`formal/fstar/SPARQL.Protocol.fst`'s result serialization. This is a new
Lean refinement of the existing Lean character-based escape specification;
it does not borrow a proof of the F* byte-run-splicing implementation.

## Test-first validation

Fourteen guards were added before the implementation; the initial target
failed on the missing API. The passing guards cover all 32 control characters,
explicit mandatory escapes, mixed controls/quotes/backslashes/Unicode,
embedded NUL, scalar boundaries and long plain/escaped strings.

The native Unicode test now has an optional `--escaping-controls` mode. It
adds every control character, quotes and backslashes to its fixture, for 62
rows total. Independent complete answers pass through both the snapshot and
fresh disk CLI, in both sort directions, including full and sliced results.
All 24 route/case answers pass. Existing snapshot admission, corruption,
error recovery, exact counts, delta replay and CURRENT isolation checks pass,
as do complete IBK3/IBK4/IBK5 JSON smokes.

```
cd formal/lean4
lake build L4Factoidal.JSON.EscapeTests L4Factoidal.SPARQL.ResultsJsonFastTheorems
lake build L4Factoidal l4block-snapshot-session l4block-id-v3-query l4block-quad-query l4w3c
```

The full build passes 713 jobs. The W3C reference/evaluator suite remains
631 pass, 0 fail, 0 skip, 0 unsupported. These reference-suite results retain
the existing harness tolerances; they are separate from exact native
answers and universal escaping refinements.

## Measurements

The generated immutable 300,000-triple graph and configurations are unchanged
from the [native string-order stage](20261011-shardborough-native-string-order.md).
The local pair alternates archived/current snapshots with one warmup and
five measured samples. Complete JSONL rendering and transfer are timed;
validation and file writing are outside timing. Both snapshots remain open.
No builds, profiler or other database benchmark overlaps the timing windows.
Ordinary OS activity remains, with CPU observations retained.

Paired medians, milliseconds:

| Query | Archived | Streaming escape |
| --- | ---: | ---: |
| Predicate COUNT | 0.057209 | 0.042708 |
| Object lookup, 10,000 rows | 30.856041 | 14.424083 |
| Two-pattern join, 100,000 rows | 605.381666 | 295.389459 |
| Object-driven join, 10,000 rows | 74.139917 | 43.417375 |
| Three-pattern join, 100,000 rows | 915.302167 | 474.692833 |
| Ordered OFFSET 3 LIMIT 7 | 0.089250 | 0.064542 |

Every measured sample is byte-identical between archived/current binaries,
as well as matching the independent complete-answer oracle. The two-pattern
query is 2.05 times faster. These gains include serialization; they do not
establish faster physical index searches or a different join algorithm.
Tiny count/slice timings do not establish useful new operator speedups.

Opening observations are 2.127 versus 1.904 seconds; RSS after readiness is
192.672 versus 192.328 MiB, not peak RSS. Neither small opening/RSS difference
is claimed as a separate improvement. The graph and ordered arrays are
still built eagerly in memory.

Separate native competitor medians, milliseconds:

| Query | Shardborough / QLever run | QLever | Shardborough / Virtuoso run | Virtuoso |
| --- | ---: | ---: | ---: | ---: |
| limit-zero | 0.045 | 0.576 | 0.042 | 1.545 |
| predicate-count | excluded | excluded | 0.046 | 1.130 |
| ask-present | 0.043 | 0.978 | excluded | excluded |
| ask-absent | 0.031 | 0.443 | excluded | excluded |
| object-index | 14.402 | 19.488 | 14.469 | 117.316 |
| subject-join | 294.166 | 378.124 | 294.135 | 3498.964 |
| object-subject-join | 43.316 | 39.592 | 43.623 | 242.838 |
| subject-triple-join | 471.278 | 574.269 | 472.393 | 5088.266 |
| limit-slice | 0.104 | 3.524 | 0.115 | 133.998 |

The two-/three-pattern and ordered object-lookup queries are faster than
the configured QLever run in these complete-result measurements. The
object-driven join remains slower (43.316 versus 39.592 ms). Exactly compared
SELECT families are faster than the configured Virtuoso run. This is a
scoped fixture result, not industry parity.

QLever COUNT remains excluded for its datatype difference and Virtuoso ASK
for its result shape. Raw differences are retained without coercion. Query
transport differs (JSONL/HTTP), configurations are pinned rather than claimed
optimal, and clients are sequential. These scoped measurements do not
establish industry parity. Larger varied data and queries, resource-normalized
execution, concurrency, persistent execution, updates/recovery and peak
memory remain part of the original objective.

[Evidence JSON](20261011-shardborough-streaming-json-escape.json) contains
commands, full samples/checks, source/binary/log hashes, generated-C evidence
and the diagnostic profile reference. Prior reports retain their own binaries
and measurements.
