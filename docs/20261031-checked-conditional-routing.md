# Checked conditional routing and XML admission

The compositor can reach a valid RDF result whose lexical value contains U+0001.
The old XML serializer emitted that character, and XQuery then refused it.
This change makes that boundary an explicit decision, without changing the RDF
value. Related: [XML representation failure](https://github.com/danbri/factoidal/issues/1215)
and [structured control flow](https://github.com/danbri/factoidal/issues/1132).

## One decision, one selected branch

`Dataflow.Stage.choose` takes a decidable predicate on the input, an accepted
stage receiving a proof of that predicate, and a rejected stage receiving its
refutation. Both stages return the same output type. Its contract is the
selected branch's contract. `runRouted` also retains the admitted/rejected tag.
Branch work must be inside the stage's `run`; constructing an expensive value
before calling `choose` is eager evaluation, outside its guarantee.

This is structured conditional composition. It does not add dynamic skipping
to the existing flat `graph()` DAG, an arbitrary JavaScript predicate evaluator,
a streaming scheduler, unbounded loops, or distributed execution. The pure Lean
operational equations do not establish IO effect traces for arbitrary host code.

## Actual XML producer

`QueryResult.toSrxReport` serializes once, checks that exact text using
`XPath4.Doc.ofString`, caches its outcome with an equation tying it to the text,
and uses `Stage.choose` to return accepted XML or the actual parser diagnostic.
This is the context-document parser used by public `xqueryEval`/`xpath4Eval`.

The producer theorems establish:

- Accepted text is exactly `QueryResult.toSrx` of this query result.
- That text was accepted by `XPath4.Doc.ofString`, with an actual document witness.
- A refusal is the parser's error on that same original serialization.

The current context parser does **not** check namespace well-formedness. Neither
the report nor these theorems claim W3C conformance, SRX schema validity, RDF
round-trip preservation, stylesheet success, HTML existence, or browser safety.
The tests preserve the undeclared `its:dir` acceptance as an explicit limitation.

## Public API

```js
const report = await core.queryRaw(turtle, sparql, {
  dataFormat: 'turtle', output: 'xml-report'
});
switch (report.kind) {
  case 'xml':
    // The exact XML accepted by Lean's context parser.
    console.log(await core.xqueryEval('count(/*)', report.xml));
    break;
  case 'diagnostic':
    console.log(report.code, report.message);
    break;
}
```

`query()` and `Dataset.query()` also accept `output: 'xml-report'`. The host
only decodes the engine's JSON report. Evaluator nodes with an explicit
JSON/report mode advertise a JSON wire; explicit text modes advertise String.
They remain outside the evaluator's proved rendering domain. Without an output
mode, SELECT/ASK/graph forms retain Table/Answer/Dataset wires. The ordinary `output: 'xml'` path uses
the same admission producer and raises an error on refusal; it does not bypass
the check. Invalid query/input syntax and unsupported graph result formats
remain errors, not admission reports. No text is removed or substituted.

## Compositor

The compositor checks the engine's advertised output formats. A rebuilt engine
selects the HTML or diagnostic branch; a diagnostic never invokes the XQuery
projection or XSLT. Both branches produce a final report. Unselected visual
nodes are marked skipped. Diagnostics are inserted with `textContent`, not HTML,
and have no HTML download. A successful empty HTML output remains downloadable.

The published 0.27.0 pin is retained until a rebuilt artifact is tested and
published. That old path is explicitly labelled as lacking checked admission;
it does not invent evidence. The worker also permits an explicitly selected
engine advertising `xml-report`, for local/release testing.

The UI adapters and worker transport are tested, not formally proved. There is
no assertion that the entire manually assembled compositor is a proved graph.

## Validation

- 28 host tests pass against published 0.27.0: existing recipe/failure/evidence
  controls plus three transport-injection routing controls. Injection tests
  establish host branch behavior, **not** Lean admission correctness.
- The actual serializer routing checks pass: 20 guards and three producer
  theorem axiom audits. NodeSettings checks include 13 new transport-wire guards.
- Actual Chrome passes normal recipe rendering and diagnostic presentation
  controls: 12 nodes, visible skipped branch, markup displayed as text, no iframe
  or HTML export on refusal, no page errors. The injected diagnostic tests the
  display boundary, not the engine's refusal producer.
- Lean named targets check conditional contracts and actual serializer routing.
- Native dispatch gate `tests/hub/xml-routing-native.test.mjs` checks both
  output modes and then feeds accepted text into the real XQuery operation.
- `npm/factoidal/test/query-xml-report.test.mjs` requires a rebuilt package and
  covers all three public query surfaces. An old artifact must fail this gate.

Native/public-artifact results must be recorded after they run; source proof
checking alone is not evidence that npm or the live page has changed.
