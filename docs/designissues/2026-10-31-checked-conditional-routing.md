# Structured conditionals with input-bound evidence

A conditional has two stages with a common output type. Its predicate is an
application choice; the accepted stage takes the original input plus a proof,
and the rejected stage takes the same input plus a refutation. A cached
check result must carry an equation tying it to that input. This prevents a
successful check on one value being used for another value.

`Stage.choose` implements the decision once and invokes the selected stage.
`runRouted` retains the branch tag. Existing sequential `Stage.comp` then
composes contracts with the actual intermediate value. Total Lean functions
provide this pure structured control flow without unbounded recursion.
This does not imply that external IO terminates or succeeds.

The first production use checks serialized SPARQL XML with the actual
XPath/XQuery context loader. It produces a common XML-or-diagnostic report.
The web compositor interprets that report and invokes only the applicable
consumer branch. This host adapter has runtime tests; it is not a proof of
arbitrary JavaScript callbacks or of the entire visual workflow.

The architecture is independent of browser rendering. More predicates and
consumers can use the same Lean primitive. Integrating structured branches
into public graph descriptions remains distinct from the existing flat DAG
runner: an eager select node cannot implement this guarantee by computing
both alternatives first.

Predicate meaning and practical usefulness remain design obligations. A
proof of `P input` does not establish that P is a useful policy. Admission
here names a concrete consumer and exact input; it does not relabel parser
acceptance as complete standards conformance.

[Implementation, tests and release state](../20261031-checked-conditional-routing.md).
