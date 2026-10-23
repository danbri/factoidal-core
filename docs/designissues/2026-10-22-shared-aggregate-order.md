# Shared arithmetic in streaming SUM and AVG

Recorded 22 October 2026 during [PR1 reconciliation](../20261022-pr1-main-reconciliation.md).
Main's constant-state grouped aggregate path used scaled arithmetic. PR1 adds
shared typed IEEE arithmetic. Retaining the old accumulator would give the
optimized and reference paths different semantics; buffering every group to
reproduce the old PR1 list traversal would add input-sized memory per group.

The [SPARQL 1.1 Recommendation §18.3](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#defn_ToList)
allows any enumeration of a multiset when converting it to a sequence.
[§18.5.1.3](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#defn_aggSum)
then fixes right-nested numeric addition for that chosen sequence. We choose
the reverse enumeration of the input row list. The implementation is a left
fold with the new value as the left argument and the accumulated value as the
right argument:

```lean
vals.foldl (fun acc v => evalArithmetic .add v acc) (.num 0)
```

`sumNumeric_reverse_enumeration` proves this equals
`vals.reverse.foldr (evalArithmetic .add) (.num 0)`. This is a list identity;
it assumes neither associativity nor commutativity of rounded addition. The
choice is observable for cancellation-sensitive floating values and is pinned
in executable controls. It is not an assertion that reassociation is harmless.

SUM keeps one shared `EvalResult` plus a count. AVG divides that same sum by
the count through the shared arithmetic adapter. COUNT and MIN/MAX keep their
streaming states. Original bound RDF terms reach the numeric decoder, so
source float/double types, NaN, infinity and invalid lexicals are preserved.
Expression errors are filtered as before; a bound nonnumeric operand
poisons SUM/AVG. This error-removal policy for non-COUNT aggregates is retained
compatibility behavior, not established SPARQL 1.1 conformance. The official
[errata-query-6](https://www.w3.org/2013/sparql-errata#errata-query-6)
records ambiguity in aggregate error processing; §18.5.1.1 is not a general
license to drop every aggregate error. The reverse-enumeration argument
concerns the error-free numeric input bag and does not resolve that policy. No list of all values is buffered by the aggregate state.

The streaming theorem proves agreement with this reference producer. The
reverse-enumeration theorem does not prove all W3C arithmetic semantics, full
IEEE input conversion, complete query evaluation or identifier grouping. In
particular, the existing L5k obligation relating grouped identifier rows to
decoded reference groups remains outside this theorem. Tests and generated
native/Wasm checks complement the source proof; successful source elaboration
is not a proof of compiler or serialization correctness.
