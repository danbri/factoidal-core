# Web Annotation: documents that break one MUST

Project-local cases for `l4webannotation` (`tests/webannotation/manifest.tsv`). Each is Example 1, 38 or 39 of the Web Annotation Data Model Recommendation (2017-02-23) with one change. The suite has no negative documents; it asks a tester to paste output.

| Document | Base | Rule broken (Data Model section) | Assertion that must fail |
|---|---|---|---|
| `no-context.json` | Example 1 | §3.1 @context MUST be given | `annotations/3.1-annotationContextValidated.json` |
| `wrong-context.json` | Example 1 | §3.1 @context MUST include http://www.w3.org/ns/anno.jsonld | `annotations/3.1-annotationContextValidated.json` |
| `no-id.json` | Example 1 | §3.1 an Annotation MUST have exactly 1 IRI that identifies it | `annotations/3.1-annotationIdValidated.json` |
| `two-ids.json` | Example 1 | §3.1 exactly 1 IRI | `annotations/3.1-annotationIdValidated.json` |
| `no-type.json` | Example 1 | §3.1 an Annotation MUST have 1 or more types, and Annotation MUST be one of them | `annotations/3.1-annotationTypeValidated.json` |
| `wrong-type.json` | Example 1 | §3.1 Annotation MUST be one of the types | `annotations/3.1-annotationTypeValidated.json` |
| `no-target.json` | Example 1 | §3.1 there MUST be 1 or more target relationships | `annotations/3.1-targetKeyFound.json` |
| `body-and-bodyValue.json` | Example 1 | §3.2.5 the bodyValue property MUST NOT be used with body | `annotations/3.2.5-notBodyBodyValue.json` |
| `bodyValue-object.json` | Example 1 | §3.2.5 bodyValue MUST be a single string | `annotations/3.2.5-bodyValueValidated.json` |
| `created-not-datetime.json` | Example 1 | §3.3.1 created MUST be expressed in xsd:dateTime with the UTC timezone | `annotations/3.3.1-annotationCreatedValidated.json` |
| `modified-two-values.json` | Example 1 | §3.3.1 an Annotation SHOULD have at most 1 modified datetime; the value MUST be xsd:dateTime | `annotations/3.3.1-annotationModifiedValidated.json` |
| `generated-date-only.json` | Example 1 | §3.3.1 generated MUST be xsd:dateTime | `annotations/3.3.1-annotationGeneratedValidated.json` |
| `rights-not-iri.json` | Example 1 | §3.3.6 rights MUST be an IRI | `annotations/3.3.6-annotationRightsValidated.json` |
| `canonical-two.json` | Example 1 | §3.3.7 an Annotation MAY have at most 1 canonical IRI | `annotations/3.3.7-annotationCanonicalValidated.json` |
| `via-not-iri.json` | Example 1 | §3.3.7 via MUST be an IRI | `annotations/3.3.7-annotationViaValidated.json` |
| `body-textDirection.json` | Example 1 | §3.2.1 textDirection MUST be one of ltr, rtl, auto | `annotations/bodiesTargets/3.2.1-bodyTextDirectionValidated.json` |
| `collection-wrong-type.json` | Example 38 | §5.1 AnnotationCollection MUST be one of the types | `collections/5.1-collectionTypeValidated.json` |
| `collection-total-negative.json` | Example 38 | §5.1 total MUST be a non-negative integer | `collections/5.1-collectionTotalValidated.json` |
| `page-no-items.json` | Example 39 | §5.2 an AnnotationPage MUST have 1 or more items | `collections/pages/5.2-pageItemsValidated.json` |
