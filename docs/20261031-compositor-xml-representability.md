# RDF literals need representability admission before XML projection

Tracking: https://github.com/danbri/factoidal/issues/1215 (SPARQL Results XML
representability), under https://github.com/danbri/factoidal/issues/1214
(actual compositor links). Separate follow-up to the
[HTML failure analysis](20261031-compositor-html-failure-analysis.md),
https://github.com/danbri/factoidal-core/pull/287. Its head is unchanged.
No normalization changes are stacked in this branch.

## Concrete counterexample with the default workflow

In DEFAULTS.turtle, replace Mina Chen with the printable Turtle source escape:

```turtle
person:mina foaf:name "Mina\u0001Chen" .
```

Keep DEFAULTS.query (the SELECT with its normal numeric socket),
DEFAULTS.stylesheet, CSV, metadata and minimum unchanged. The source has one
backslash followed by u0001, not a raw control character in the Turtle file.

Measured against both published 0.27.0 and 0.28.0: Turtle, CSVW, merge, closure,
graph partition and the unfiltered default SELECT complete. That SELECT really
returns the lexical value containing U+0001. The filtered SPARQL operation then
returns an XML 1.0 declaration and raw U+0001 inside the literal. The fixed
XQuery projection rejects the context document with FODC0002, invalid character
in text content. The filter stage fails and no HTML stage/result is reached.
The stylesheet has not changed and is not reached.

The regression instruments queryRaw only to retain its unchanged returned
string; all parsing, inference, evaluation, XML serialization and XQuery use
the real engine. The successful default-data control produces HTML using the
same SELECT and stylesheet. This separates representability from malformed
Turtle, an altered query form, or a changed XSLT output method.

## Standards and the required distinction

[RDF 1.1 Concepts section 3.3](https://www.w3.org/TR/rdf11-concepts/#section-Graph-Literal)
defines literal lexical forms as Unicode strings. [Turtle escapes](https://www.w3.org/TR/turtle/#grammar-production-UCHAR)
can represent this code point. XML is a narrower target character space.
[XML 1.0 Char](https://www.w3.org/TR/REC-xml/#NT-Char) excludes U+0001.
A numeric reference does not solve it: [Legal Character](https://www.w3.org/TR/REC-xml/#sec-references)
requires the referenced code point to satisfy the same Char production.
[SPARQL Results XML](https://www.w3.org/TR/sparql11-results-xml/#defn-document)
requires an XML document.

The current SPARQL.ResultsXml.srxEscape escapes markup but passes this code
point through. QueryResult.toSrx returns a String without a representability
refusal. Thus successful RDF parsing, a SELECT result and a String wire do not
supply the XML-document precondition needed by the next component. This is a
specific producer/admission defect, not a failure of the RDF reader or RDFS
soundness. It is not a general claim that all accepted RDF fails XML projection.

## Kernel facts and their scope

SPARQL/ResultsXmlAdmission.lean uses the actual XML character predicate and SRX
producer. It proves U+0001 is excluded by XML 1.0, that any literal occurrence
fails the necessary character-stream admission, and that srxEscape preserves
this occurrence. rdf_term_counterexample supplies a term of the actual RDF.Term
type whose termToXml output fails that admission. The RDF type enforces
its structural literal invariant; this is not a new datatype-value validation
claim. Hence the escaping operation
cannot establish that character guarantee for every admitted RDF term/string.

This is a necessary admission condition, not a complete XML well-formedness,
namespace, schema, serializer round-trip or host-composition theorem. Four
actual parser guards check XML 1.0 raw/reference refusal and XML 1.1
reference acceptance/raw restricted-character refusal. They do not prove
universal parser correctness or universal XML 1.1 interoperability.

## Future repair contract

Before claiming an XML result, the producer must admit values representable in
its declared XML version, preserve their RDF lexical meaning through escaping,
and otherwise return a typed refusal. Admission also has to cover other fields
serialized as XML text or attributes. True character admission alone does not
prove complete XML syntax or result-schema correctness.

An explicit lossless alternate serialization or negotiated XML version is
another possible contract, but all consumers must agree. XML 1.1 needs character
references for restricted controls and still cannot represent every RDF string.
Deleting/replacing U+0001, or writing the literal six characters backslash-u0001
inside XML, changes the lexical value. Such a lossy display policy needs its own
explicit contract and cannot inherit RDF-preservation guarantees.

## Validation and remaining defect

The separate three-test public suite has two ordinary controls and one named
serializer-admission expected failure, on each of published 0.27.0 and 0.28.0.
The expected-failure helper accepts only the observed FODC0002/invalid-character
failure; unrelated exceptions fail, and a producer refusal or consumable XML is
an XPASS requiring the test to be promoted. There are no skips. Together with
PR287's controls, the pinned 0.27 run reports 19 runner passes: 18 controls and
one separate expected defect, not 19 conformance passes.

Named Lean compilation passes (14 jobs), including four parser guards. The
code-point fact has no axioms; the quantified admission fact uses propext;
the SRX/typed-term facts use only propext, Classical.choice and Quot.sound.
There is no new axiom, sorry, native_decide or partial definition.

The existing assurance workflow builds the proof module. The existing npm/dataflow
workflow runs the public suite against its fetched ancestor artifact, reports
the expected-defect bucket separately and fails on missing tests/artifacts,
unknown exceptions or XPASS. Production serializer behavior remains unfixed.
No changes to PR287, its counts or its frozen head are made by this follow-up.
