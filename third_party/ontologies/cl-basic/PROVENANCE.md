# Cell Ontology (CL), basic edition — provenance

Vendored for `tools/owl-real-bench.py`, which measures OWL 2 RL closure, OWL DL
consistency and OWL DL entailment on real ontologies
(https://github.com/danbri/factoidal/issues/651, plan item 4). Record:
[`docs/designissues/2026-10-10-owl-real-ontologies.md`](../../../docs/designissues/2026-10-10-owl-real-ontologies.md).

Each file is the upstream byte stream, unmodified.

- **Retrieved:** 2026-10-10 (14:28 UTC), with `curl -sSL` through the session HTTPS proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples, Lean `l4factoidal parse` | Statements, F\* `factoidal count` | Triples, rdflib 7.6.0 |
|---|---|---|---:|---:|---:|---:|
| `cl-basic.owl` | http://purl.obolibrary.org/obo/cl/cl-basic.owl (redirects to a GitHub release asset of obophenotype/cell-ontology) | `8dffb71f26cdbdb4b44513abb29f53d29284b0820806b3c90906b8d0071efbdb` | 9,557,097 | 78833 | 78835 | 78835 |

The Lean count is the size of the parsed graph (a set). `factoidal count`
counts statements as read, so a repeated triple counts again.

## OWL 2 species

Verdict of `l4owl-species` on the Lean parser's N-Triples of the file(s), 2026-10-10: **Full**, 7 violations, all `reserved-vocabulary-subject` (declarations and annotations of `rdfs:comment`, `rdfs:label`, `rdfs:seeAlso` as `owl:AnnotationProperty`, as written by the OWL API). The verdicts were not compared with a second species checker.

The Lean species checker (`OWL.SyntaxDL.speciesViolations`, run by `l4owl-species`) decides OWL 2 DL against OWL 2 Full. It does not decide the EL, QL or RL profiles, so no profile is recorded here.

## Licence

Creative Commons Attribution 4.0 (CC BY 4.0), stated in the document: `dcterms:license <http://creativecommons.org/licenses/by/4.0/>`.

## Notes

The URL serves the latest release, so the SHA-256 above is the pin. The Lean count is 2 lower than rdflib's for the reason given under RO (https://github.com/danbri/factoidal/issues/329). rdflib also writes 2,724 `xsd:dateTime` literals with `+00:00` where the document has `Z`; that is rdflib's normalisation, not a Lean difference.
