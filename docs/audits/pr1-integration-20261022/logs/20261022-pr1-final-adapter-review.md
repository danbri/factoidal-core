Final PR1 adapter review, 2026-10-22

No additional introduced blocker was found in this bounded source review
after the numeric ORDER BY correction described below. This is a read-only
review of the dirty `integrate-pr1` reconciliation tree, whose Git HEAD is
`87af61c9b7398ed1effa65744cbd3c84afe311be`. It is not a review of a committed
merge or an assertion that the final integration build has passed. The
adjacent JSON manifest records hashes of the inspected source files.

The pass inspected numeric admission, promotion, aggregate order, and
CSVW/RIF unsupported-result propagation. No Lean or native build, runtime
probe, or source edit was performed during this final pass. Earlier
aggregate experiments are linked below with their original results.

- Numeric source types survive the repaired SPARQL routes.
  `SPARQL/Expr.lean:1098` decodes source literals before shared arithmetic;
  `Expr.lean:1138` performs arithmetic over those values. In particular a
  source float is rounded as a float before promotion to double.
  `Expr.lean:1747` accepts the old candidate cast spelling only when its
  parsed value is identical to the shared cast result. RIF's corresponding
  decoder is `RIF/Builtins.lean:181`, with numeric admission at line 247.
  Derived string datatypes normalize to the primitive string value in
  `XSD/Datatypes.lean:1115`; their lack of separate cases in the shared
  primitive cast match is therefore not evidence of a rejected valid cast.
- The intermediate numeric ordering policy tied NaN with every number.
  The owner corrected this during review: `SPARQL/Query.lean:210` now puts
  NaN after other admitted numerics and ties two NaNs. This avoids the
  earlier nontransitive tie relation. `QueryTests.lean:1451` contains
  ordering and MIN/MAX controls. Expression comparisons separately retain
  IEEE unordered behavior in `Fn/Comparison.lean:43`. The preexisting
  fallback for unsupported or invalid pairs remains; this review does not
  establish a total-order theorem for every EvalResult.
- SUM's chosen order is defensible for the SPARQL 1.1 aggregate multiset.
  `Query.lean:1008` uses a flipped left fold, and
  `sumNumeric_reverse_enumeration` at line 1015 equates it to the specified
  right nesting on the reversed enumeration. SPARQL 1.1 section 18.3
  allows any ToList order, while section 18.5.1.3 defines that right
  nesting. No associativity or commutativity of rounded arithmetic is
  assumed. This conclusion concerns error-free aggregate inputs and the
  dated SPARQL 1.1 Recommendation; it does not generalize to every later
  sequence-based draft. The accompanying append-single law in
  `SPARQL/ArithmeticTheorems.lean:11` matches the new fold contract.
  [SPARQL 1.1 Recommendation](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/)
- AVG at `Query.lean:1021` divides the shared SUM result by the length of
  its admitted input list and returns integer zero for an empty list.
  COUNT at line 1058 removes expression errors and uses RDF term identity
  for DISTINCT. The streamed SUM/AVG accumulator follows the same operand
  order and keeps one result plus a count, without buffering the input
  list. Its exact equality with the reference implementation establishes
  that agreement; it does not establish all SPARQL aggregate semantics.
- CSVW preserves unsupported outcomes through the inspected adapters.
  `CSVW/Diagnostics.lean:24` removes the converted value when an unsupported
  issue occurs; `CSVW/Validate.lean:43` and line 636 retain an undecided
  result. `Wasm/Ops/Formats.lean:436`, line 466, and line 478 preserve that
  distinction through dataset construction and JSON serialization.
  Invalid cells and warnings have separate behavior. The new
  `Wasm/FormatsBoundaryTests.lean` checks the public response shape,
  including omission of N-Quads when conversion is unsupported.
- RIF completeness is checked before publishing a saturated graph.
  `RIF/Saturate.lean:57` and line 60 combine blocked, capped, unsupported
  input, and unsupported output flags. `Wasm/Ops/Formats.lean:494` refuses
  unresolved imports and uses the checked graph result. The inspected
  dataset, native harness, and unified embedding callers also consult
  completeness. `RIF/Engine.lean:404` permits a positive witness found
  before a resource boundary but keeps an absent goal undecided when
  search is incomplete. The native harness retains declared-import
  handling, graph-mapping admission, and the newer OWL Direct branch.

One inherited semantic limit remains actionable outside this integration:
`Query.lean:904` removes expression errors before SUM/AVG as well as COUNT.
The dated Recommendation's ListEval retains errors, and COUNT explicitly
removes them. The published erratum identifies ambiguity in aggregate
error treatment; the linked working-group discussion distinguishes the
SUM/AVG error result from the disputed MIN/MAX cases. For example,
`SELECT (SUM(1 / ?x) AS ?s) (AVG(1 / ?x) AS ?a) WHERE { VALUES ?x { 1 0 } }`
is a useful future regression: source tracing indicates the engine drops
the division error and retains the value 1. This query was not executed in
this pass. The behavior predates the reconciliation. The owner has now
qualified the source comment and reconciliation note, so the streaming
proof and compatibility tests no longer purport to establish that policy
as a SPARQL rule.
[SPARQL erratum query-6](https://www.w3.org/2013/sparql-errata#errata-query-6),
[working-group aggregate-error analysis](https://lists.w3.org/Archives/Public/public-sparql-dev/2013OctDec/0004)

Other limits of this review: SPARQL decimal division retains its existing
precision policy; some nonnumeric casts still use legacy adapters; RDF
grouping adequacy and complete source-to-W3C semantic refinement remain
separate obligations. No claim about their resolution follows from shared
numeric code or streamed/reference equality.

Earlier aggregate evidence, preserved without rewriting:

- [Source check and theorem axiom output](pr1-aggstream-source-green.log).
- [Initial targeted build](pr1-aggstream-targeted-build.log) and
  [machine-readable result](pr1-aggstream-targeted-build.json): 27 of 29
  new aggregate guards passed at that point; the two MIN/MAX controls
  exposed the source-float ordering defect subsequently repaired by the
  owner. Existing IdAgg tests passed in that run. This is historical red
  evidence, not the final integration score.
- [Dropped-operand mutation output](pr1-aggstream-drop-operand-mutation.log)
  and [reviewed classification](pr1-aggstream-drop-operand-mutation-reviewed.json):
  the modified accumulator was rejected by the `num_stream` proof through
  an arithmetic proof failure, rather than an import or resource failure.
  The original classifier JSON is retained separately because its narrow
  diagnostic matcher initially missed that proof-failure wording.
- [Earlier CSVW and aggregate review](20261022-pr1-csvw-aggregate-review.md).

Final acceptance still depends on the owner's combined source build and
the parent agent's artifact and corpus replay. This pass adds source
review evidence and records the remaining qualification above.
