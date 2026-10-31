# Conditions that prevent compositor HTML output

Scope: the [live compositor](https://danbri.github.io/factoidal/web/hub/data-compositor/)
with its explicitly pinned published core 0.27.0. The fetched live pipeline was
byte-identical to the repository pipeline used for the tests. Core 0.28.0 being
available does not update this demo: its worker explicitly refuses that version.
Tracking: https://github.com/danbri/factoidal/issues/1214.

## What “no HTML” means

Distinguish (1) no successful pipeline result delivered to the UI, (2) a
successful result whose HTML string is empty, and (3) an HTML document containing
zero matching people. The third is not pipeline failure. A visible page is a
further browser/display obligation.

## Formal argument and its boundary

The pinned theorem [Stage.comp_ok](https://github.com/danbri/factoidal-core/blob/a9bd50c3b28b3d42c5071cc8c3e74a5ede8706db/formal/lean4/L4Factoidal/Dataflow/Stage.lean#L165) proves:

    composite success ⇒ there exists an actual successful intermediate run

Consequently a witnessed upstream error rules out downstream success for that
formal composition. The existing comp definition propagates the same error.
Three new kernel-checked corollaries in Dataflow/FailureConditions.lean make the
negative conclusions explicit (all have empty axiom reports):

- Stage.comp_error_left: upstream .error e implies composed .error e.
- Stage.comp_no_success_of_error: upstream error excludes every successful output.
- Stage.comp_no_output_of_incompatible_contracts: if every middle value makes
  the two contracts incompatible for a proposed output, that output cannot be
  returned successfully. This requires a proof of incompatibility, not merely
  the absence of a proof or an unchecked badge.

[parseDocument_error_iff](https://github.com/danbri/factoidal-core/blob/a9bd50c3b28b3d42c5071cc8c3e74a5ede8706db/formal/lean4/L4Factoidal/Dataflow/Reader.lean#L105),
parseDocumentWithPrefixes_error_iff and RdfReader.fails carry a concrete raw
parser error into reader failure. Thus a witnessed Turtle syntax error is a
valid starting point for the formal error-propagation argument.

Pipeline.guarantee_sound and Graph.guarantee_sound establish contracts **given
successful execution and the named assumptions**. They do not assert that an
output exists. Pipeline.run_no_wire_error and Graph.run_stage_error_only exclude
wire/source-reference/port-count failures under their typing and actual-input premises;
stage failures remain possible. nodeChecked_iff describes proof-domain admission,
not whether an unproved component will execute successfully.

Only the compositor's merge is currently expressed as a checked graph. The full
ten-stage JavaScript recipe is not an instance of the Lean composition theorem.
The bridge from these results to the deployed app consists of inspected host
control flow and concrete tests: awaited stage exceptions are rethrown, the
worker sends error rather than complete, and run() clears the previous result.
A complete Lean proof for that host execution is still absent. New union and
normalization source proofs are not retroactive guarantees for 0.27.0.

## Sufficient stops observed on the published engine

These 13 tests assert the specific error and failing stage, and that no final
HTML stage event is emitted. They do not treat arbitrary exceptions as success.

| Input condition | First failing stage | Observation |
|---|---|---|
| Unterminated Turtle string | turtle | Exact syntax error |
| Undecodable CSVW JSON metadata | csvw | metadataJson refusal |
| Query lacks {{MIN_SCORE}} | query | Explicit template guard |
| Invalid SPARQL syntax | query | pipelineCheckNodes parse refusal |
| ASK query in this SELECT-row workflow | query | bindings.map is not a function |
| Blank, -1, 101, NaN or Infinity minimum | filter | Explicit finite 0–100 guard (five tests) |
| Malformed stylesheet XML | xslt | XTSE0165 |
| Valid transform with method=text | xslt | Host requires method=html |
| xsl:message terminate=yes | xslt | XTMM9000 |

ASK is a valid query form, not malformed SPARQL. Its failure exposes a manual
adapter boundary: rowsOf assumes iterable SELECT bindings without a checked
query-form precondition. The preliminary unfiltered query is awaited even
though the later filter executes its own query; that preliminary failure still
prevents HTML. It cannot be disregarded as a display-only diagnostic.

More generally, if any awaited operation rejects, the recipe cannot deliver a
successful result. Additional explicit guards reject an unexpected XQuery
XML-to-JSON envelope or a decoded value that is not an array of string-valued
row objects. These guards were inspected; this audit does not claim a natural
input was found that violates the current engine's fixed XML_ROWS result.
Cleanup in finally and worker message delivery are also required for delivery:
HTML-stage completion alone does not prove the final result was posted.

## Successful runs that do not show people or HTML

Three counterexamples prevent false failure claims:

1. With the default data and minimum 100, there are zero selected rows, but the
   stylesheet emits an HTML document saying “0 artists in this cut.”
2. Removing the RDFS domain/subclass rules empties the roster but still emits
   HTML. RDFS soundness is not a promise that the desired people will be found.
3. An HTML-method stylesheet whose root template is empty returns html="" and
   reaches the final HTML stage successfully. No current output contract asserts
   nonempty HTML, an html root element, useful visible content, or a minimum row
   count. A live browser check shows “Flow complete” and enables Save HTML, but
   the click handler returns immediately for the empty string. This is a UI
   contract gap, not evidence that the XSLT engine failed.

CSVW/XQuery/XSLT run with explicit unchecked permission here. Their tested or
unproved status does not itself stop execution. Missing proof assumptions imply
missing assurance, not necessarily a bad result or failure.

## Host conditions outside these proofs

Failure to fetch/load the engine, a failed WASM integrity check, an unsupported
browser, worker termination or insufficient memory can prevent completion.
The worker also rejects a loaded version other than 0.27.0; the live browser test
confirmed its refusal of 0.28.0. No cited theorem establishes browser scheduling,
wall-clock deadlines, available memory or successful network delivery.

The preview's sandbox and default-src 'none' CSP can block scripts/external
resources needed by a custom stylesheet's output. That can produce a blank or
incomplete display even when the HTML string was generated successfully. This
is distinct from failure to produce the string and has no rendering theorem.

## Reproduction and evidence

The 16 public tests in tests/hub/compositor_failure_test.mjs pass with zero
failures/skips against the installed published 0.27.0 engine. Select that artifact:

    FACTOIDAL_COMPOSITOR_TEST_ENGINE=file:///absolute/path/to/node_modules/@factoidal/core/index.mjs node --test tests/hub/compositor_failure_test.mjs

The default import tests the available @factoidal/core package instead; its
version appears in diagnostic messages. These are finite tests, not a proof
that these are all possible failure conditions.

Three real Chrome checks against the live page passed: invalid minimum clears
the old result and disables saving; an empty HTML result completes with an empty
preview; a worker configured with 0.28.0 reports the explicit version refusal.
The new proof module compiled using the existing Stage definitions and all
three corollaries report no axioms. CI explicitly builds the new module.

Next assurance step: express successful output as a deliberate application
contract (for example, nonempty HTML document versus an intentionally empty
result), make SELECT-row admission explicit, and prove the host recipe refines
the typed composition. Do not turn an unknown into a theorem-backed failure.

Independent proof-scope review passed. The same 16 regressions also pass with
the published 0.28.0 library, separately from the live page's 0.27.0 pin. Stage.lean
is unchanged between the pinned source and the definitions used for the new
lemmas. No browser code or runtime semantics are changed by this audit.
