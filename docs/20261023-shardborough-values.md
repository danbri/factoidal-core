# VALUES access work — 2026-10-23

The October 11 relational workload exposed a large VALUES-chain gap against
QLever. That dated timing is not a measurement of the current worktree:
shared datatype, expression and grouping semantics have since changed.
The native binaries were absent when this work resumed. The baseline was
rebuilt from the actual core worktree, not an archived or sibling executable.

## Baseline and regression boundary

The library, snapshot session and triple-query targets pass a fresh 745-job
build. Fixture pack/activation targets pass a separate 290-job build.
Thirteen independent complete-answer cases pass through both snapshot and
fresh query routes before the implementation changes. They cover duplicate
VALUES rows, UNDEF, empty tables, tuple bindings, conflicts, repeated pattern
variables, VALUES on either side of a join, ordering/slicing, escaping and ASK.

Nine build-time cases also check three backend configurations. They retain
binding-list order, duplicate variable names and the existing short/extra-cell
behavior of the algebra API. Those malformed AST cases are not a claim that
the SPARQL parser accepts malformed VALUES syntax.

`evalPatternBackend_values_native` and
`evalPatternBackend_values_reference` state complete equality with the existing
`evalValues` operation and lowered reference evaluator for arbitrary
environments, datasets, graph backends and VALUES inputs. They do not require
a well-formed index. They do not assert a runtime cost bound.

```sh
python3 tools/blockengine-values-test.py --output /path/to/new-report.json
```

## Source and proof boundaries

The backend VALUES fallback materializes the dataset and active graph before
calling the graph-independent reference operation. The direct leaf must keep
the same rows, representatives, duplicates and order without those reads.

A separate seeded-join design targets the actual parsed VALUES/BGP join. It
must keep reference planner decisions and reference binding representatives,
use seed constraints only for selective probes, and merge the seed at leaves.
Feeding a VALUES binding directly to the existing replanning evaluator is not
an exact-list refinement: it can change plan and row order. Indexed-search
and seeded-join proofs require an explicit index well-formedness hypothesis;
an arbitrary hand-built index does not satisfy that contract automatically.

The workspace also contains separate standards/reuse changes. This work must
preserve them and must not present a partial performance-only commit as a
compilable snapshot if it depends on those uncommitted interfaces. Old grouping
evidence remains dated; it does not certify the changed identity policy.

Industry parity and SOTA remain unestablished. The controlled relational
fixture does not replace standard benchmark suites, production data,
concurrency, memory, ingestion, updates or recovery measurements.
