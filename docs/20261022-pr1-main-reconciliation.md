# PR1 standards reuse reconciled with main

Recorded 22 October 2026. This work ports the delta of PR1
`ed19f0905781008d12275c6fbbff257cb77f044a` onto
`87af61c9b7398ed1effa65744cbd3c84afe311be` (main plus PR2), rather than
replacing files with the old review checkout. Parent integration adds PR3 and
newer main separately. This is a local integration record, not a release or
complete standards-conformance claim.

## Reconciliation decisions

- `Fn.Numeric` owns decimal parsing/rendering, arithmetic and rounding;
  `Fn.Arithmetic` delegates decimal operations to it and retains the shared
  finite IEEE implementation. Main's public numeric names survive as adapters.
  `Fn.Casting` retains temporal lexical APIs and exposes the source-aware
  `Fn.Cast.castFrom` value conversion. Main's date/time, Boolean and list
  function modules remain present.
- Zero yearMonthDuration-to-string conversion retains the source datatype:
  `P0Y` and `P0M` become `P0M`. Generic duration and dayTimeDuration zero
  remain `PT0S`. The target-membership theorem is not a proof of complete
  F&O conversion adequacy; a separate closed theorem pins this zero case.
  Double-to-float narrowing retains F&O 2007 §17.1.3.1's documented truncation
  contract rather than substituting a host IEEE rounding default.
- RIF keeps main's broader function catalogue, iri-string binding,
  OWL-Direct route, import rejection, RDF-only conclusions and fixture
  override reporting. It adds shared datatype decoding, matching and RDF
  mapping. Only declared imports supply facts, using their declared URL as
  base. Missing/malformed imports and incomplete saturation stay separate
  from positive and negative verdicts. The native RIF runner now exits nonzero
  for a decided failure, stale override or empty inventory; its previous zero
  exit on failure cannot be used as a green gate. The old duplicated Boolean `gEqValue`
  is a compatibility view of shared matching; actual matching retains unknown.
- SPARQL retains main's indexed grouping/deduplication and public helper
  APIs. Literal operands retain their original RDF terms until value
  operators decode them. RDF-term grouping/deduplication uses `sameTerm`;
  coarse hash buckets have updated congruence proofs. Derived integer ORDER
  BY remains admitted. Numeric ordering uses the original source-typed shared
  numeric values before literal promotion, including float rounding. ORDER
  BY puts NaN after other admitted numerics and ties only two NaNs; expression
  comparisons retain IEEE unordered semantics. Numeric EBV
  delegates to the shared bounded parser.
  [SUM/AVG choose reverse bag enumeration](designissues/2026-10-22-shared-aggregate-order.md)
  and use a flipped left fold, preserving constant aggregate state. The exact
  equality to reverse-list right nesting needs no floating associativity
  assumption; streamed/reference agreement does not close the existing ID
  grouping adequacy gap. Existing non-COUNT expression-error removal remains
  an explicit compatibility boundary, not a newly proved SPARQL 1.1 rule.
- SHACL retains main's indexed deduplication, with strict `sameTerm` bucket
  checks and a proof that strict identity implies the coarse join key agrees.
  Main's newer unique-list-members, subset and unique-values components also
  use RDF node identity. Their declarative clauses and compiler proofs were
  reconciled with that contract; XMLLiteral distinguishing controls remain.
- Main's XML parser, document/DTD representation and richer version-specific
  normalization are retained. Namespace validation adds NCName component
  checking around main's proved one-pass QName splitter. The namespace view
  feeds vocabulary readers and XPath expanded names, preserving main's
  document-number provenance and fixed prefix presentation order. XPath
  nodes other than elements/attributes have no namespace URI. Raw node forests
  have erased the XML declaration; their namespace checks admit XML 1.1
  undeclarations, while parsed Documents retain their actual version check.
  XSLT checks source/style and external namespaces before execution and keeps
  main's external-document identity. Explicit empty-default fixup survives
  node copying.
- Regex replacement retains ordered span/capture selection and main's
  tail-recursive output loop, with an equivalence theorem. The sentinel
  search implementation does not correctly support all repeated/grouped
  boundary assertions: the explicit profiles refuse repeated unescaped
  start/end anchors and every assertion inside a group. Single `^a$`, escaped
  carets, character classes, and XPath q literals have distinguishing controls.
  RIF matches/replacement use that admission too. This is a documented
  restriction, not a newly complete regex engine. Raw legacy regex and
  SHACL's Boolean pattern API remain outside this new refusal guarantee.
- CSVW conversion and main's newer data validator share format conversion.
  Unsupported ECMA syntax is retained as a finding with no validation verdict,
  and the native validation runner scores it separately, including negative
  cases. `Wasm.Ops.Formats` propagates missing conversion output as an error,
  retaining diagnostics in raw csvwToRdf JSON; dataset-handle creation refuses
  partial conversion. The current npm Dataset API has no warning-delivery
  interface, so success diagnostics are not exposed through that wrapper.
  Its RIF saturation caller likewise refuses incomplete results. `passes` and `cellValueValid` remain Boolean acceptance conveniences;
  callers needing a negative verdict use the Option-valued decision APIs.
- Cleanly applied changes include shared hexadecimal decoding, XSD lexical
  and value identity, CSVW diagnostics, result-XML namespace recognition,
  MathML/Schematron vocabulary projection and RIF saturation flags. Existing
  dated survey/review measurements are preserved as records, not relabelled
  as measurements of current main.

## Explicit corrections to main guards

Main asserted that `xs:date` is inside `xs:dateTime` at midnight and attributed
that to RIF-DTB §3.2. The [2013 Recommendation §2.3](https://www.w3.org/TR/2013/REC-rif-dtb-20130205/#Datatypes)
delegates XML Schema value spaces to XSD, lists date separately, and derives
only dateTimeStamp from dateTime. §4.2 is a membership test; §3.2 is general
built-in semantics. The guard now rejects date-as-dateTime, while the separate
main temporal arithmetic adapter remains implemented. An invalid source
`dateTimeStamp` spelling without timezone yields unknown for both membership
and negative membership, preserving the decoder's assurance boundary; this
is not counted as a semantic pass.

The new XSLT controls inherited old PR1's namespace-declaration presentation
order. Executable probes confirmed that main's fixed namespace-axis order
serializes `xmlns:p` before `xmlns:x`; only these byte expectations changed.
The namespace URIs, element names and provenance expectations remain intact.

## Validation and remaining limits

The focused 99-job reconciliation build passed, followed by all QueryTests
and all 29 shared streaming controls. The latter include cancellation-sensitive
IEEE ordering, source float/double promotion, MIN/MAX rounded source values,
NaN/infinity, error and empty controls. A real mutation that dropped an
aggregate operand was rejected by the universal `num_stream` proof. Full
streaming and public-boundary theorem audits use standard Lean foundations;
no new user axiom or admitted proof is introduced.

At the source commit, the frozen `lake build L4Factoidal l4wasm` run is
**still pending**, after fixing three downstream proof/test compilation
errors exposed by the first complete pass. This is not a full-build pass
claim. The latest run has built the shared Query arithmetic theorem and all
20 public CSVW/RIF producer controls. Final commands, inventories and evidence
hashes will follow in a separate evidence commit. Missing fixtures are not
passes. The W3C main fixture pin and XSD fixture pin will be measured
explicitly rather than borrowing the older checkout's denominators.

Independent reconciliation review found and caught the XPath non-element
namespace fallback, omitted RIF mapping guard and width-recursive namespace
view. A preexisting XSLT limitation remains: copying a prefixed root with
unprefixed descendants under a result default namespace can need additional
default-namespace fixup. That is not established repaired here. Remaining
ORDER BY datatype/fallback choices, the documented IEEE input profile,
full Unicode regex folding and complete F&O/XSD adequacy remain limited.
No F*/OCaml sources, generated binaries or foreign semantic helpers are added.

## RIF baseline comparison (preliminary source replay)

Clean main+PR2+PR3 `eef88c3` was measured independently on the same unmodified
46-case Approved suite: 45 pass, zero fail/undecided/unread, and one documented
local override. The preliminary integrated source replay reports **42 pass,
one fail, three undecided, zero unread**, with all six import-rejection tests
still passing. These are observed score changes, not relabelled successes;
final native replay is recorded with the validation evidence.

| Case | Observed integrated result | Distinguishing fixture text and boundary |
| --- | --- | --- |
| EBusiness_Contract | fail: not entailed | The premise guards `?deliverydate` with `is-literal-dateTime` but binds it to `"2008-07-22Z"^^xs:date`, likewise the schedule date. Main's midnight-subtype accommodation was removed from membership; its separate temporal arithmetic adapter remains. |
| Builtins_PlainLiteral | undecided | `lang-from-PlainLiteral("Hello World!@en"^^rdf:PlainLiteral) = "en"^^xs:lang`; `xs:lang` is not the XSD `xs:language` datatype. No global alias is invented for that IRI. |
| Builtins_Time | undecided | `add-dayTimeDuration-to-dateTime(...) = "2000-11-02T12:27:00"^^xs:dayTime`; the expected symbol-space name is not XSD `xs:dateTime`. The incoming shared decoder does not silently alias it. |
| RDF_Combination_Constant_Equivalence_4 | undecided (main had an override) | Its Turtle import declares `@prefix xs: <www.w3.org/2001/XMLSchema#>`, missing `http://`. With the declared import URL as base this resolves to a different absolute datatype IRI, rather than XSD string. Unsupported value-space identity stays unknown. |

These explanations are checked against the fixture text and the dated
[RIF-DTB datatype list and delegated value mappings](https://www.w3.org/TR/2013/REC-rif-dtb-20130205/#Datatypes),
not inferred solely from this implementation's datatype constructors.
[XSD 2004 §4.2.1](https://www.w3.org/TR/2004/REC-xmlschema-2-20041028/#equal)
explicitly makes primitive value spaces disjoint; §3.2.9 represents date as
a day interval, whereas dateTime represents a point. They
explain the changed decisions without establishing whole-fixture defect
classification or replacing the original suite. The original inputs remain
untouched; no newly unknown case is scored as a pass.
