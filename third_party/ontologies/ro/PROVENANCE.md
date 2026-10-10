# OBO Relations Ontology (RO) — provenance

Vendored for `tools/owl-real-bench.py`, which measures OWL 2 RL closure, OWL DL
consistency and OWL DL entailment on real ontologies
(https://github.com/danbri/factoidal/issues/651, plan item 4). Record:
[`docs/designissues/2026-10-10-owl-real-ontologies.md`](../../../docs/designissues/2026-10-10-owl-real-ontologies.md).

Each file is the upstream byte stream, unmodified.

- **Retrieved:** 2026-10-10 (14:28 UTC), with `curl -sSL` through the session HTTPS proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples, Lean `l4factoidal parse` | Statements, F\* `factoidal count` | Triples, rdflib 7.6.0 |
|---|---|---|---:|---:|---:|---:|
| `ro.owl` | http://purl.obolibrary.org/obo/ro.owl (redirects to https://raw.githubusercontent.com/oborel/obo-relations/master/ro.owl) | `9a3190d49564743aa00f0b0f2e2d9c5fc5673ac7bb3c369284bf490294d42f77` | 1,224,640 | 11703 | 11705 | 11705 |

The Lean count is the size of the parsed graph (a set). `factoidal count`
counts statements as read, so a repeated triple counts again.

## OWL 2 species

Verdict of `l4owl-species` on the Lean parser's N-Triples of the file(s), 2026-10-10: **Full**, 523 violations: `untyped-predicate` 296 and `untyped-class` 223 (the document carries SWRL rules, whose `swrl:` vocabulary has no OWL 2 DL typing), `reserved-vocabulary-subject` 4 (declarations of `rdfs:comment`, `rdfs:isDefinedBy`, `rdfs:label`, `rdfs:seeAlso` as `owl:AnnotationProperty`). The verdicts were not compared with a second species checker.

The Lean species checker (`OWL.SyntaxDL.speciesViolations`, run by `l4owl-species`) decides OWL 2 DL against OWL 2 Full. It does not decide the EL, QL or RL profiles, so no profile is recorded here.

## Licence

CC0 1.0 (public domain dedication), stated in the document: `dcterms:license <https://creativecommons.org/publicdomain/zero/1.0/>`.

## Notes

The redirect target is the `master` branch, so the SHA-256 above is the pin. The Lean count is 2 lower than rdflib's because the Lean RDF/XML parser gives an `xml:lang` of one property element to the next sibling element (two literals then collapse into existing ones); see https://github.com/danbri/factoidal/issues/329.
