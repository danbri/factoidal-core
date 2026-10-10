# PROV-O: The PROV Ontology (W3C Recommendation 30 April 2013) — provenance

Vendored for `tools/owl-real-bench.py`, which measures OWL 2 RL closure, OWL DL
consistency and OWL DL entailment on real ontologies
(https://github.com/danbri/factoidal/issues/651, plan item 4). Record:
[`docs/designissues/2026-10-10-owl-real-ontologies.md`](../../../docs/designissues/2026-10-10-owl-real-ontologies.md).

Each file is the upstream byte stream, unmodified.

- **Retrieved:** 2026-10-10 (14:28 UTC), with `curl -sSL` through the session HTTPS proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples, Lean `l4factoidal parse` | Statements, F\* `factoidal count` | Triples, rdflib 7.6.0 |
|---|---|---|---:|---:|---:|---:|
| `prov-o.ttl` | https://www.w3.org/ns/prov-o.ttl | `7d203989f67b38bca572253942acc5a1bf24ce3ccfece16f072dcb4be2b79a96` | 68,795 | 1146 | 1146 | 1146 |

The Lean count is the size of the parsed graph (a set). `factoidal count`
counts statements as read, so a repeated triple counts again.

## OWL 2 species

Verdict of `l4owl-species` on the Lean parser's N-Triples of the file(s), 2026-10-10: **Full**, 13 violations: `reserved-vocabulary-subject` 10 (the document types `rdfs:comment`, `rdfs:label`, `rdfs:seeAlso` and other RDFS terms as `owl:AnnotationProperty` and annotates them), `illegal-punning-object-annotation-property` 2, `multiple-root-ontology-headers` 1. The verdicts were not compared with a second species checker.

The Lean species checker (`OWL.SyntaxDL.speciesViolations`, run by `l4owl-species`) decides OWL 2 DL against OWL 2 Full. It does not decide the EL, QL or RL profiles, so no profile is recorded here.

## Licence

W3C Software and Document Notice and License (<https://www.w3.org/copyright/software-license-2023/>); the namespace document of a W3C Recommendation (<https://www.w3.org/TR/prov-o/>).

## Notes

PROV-O is designed as OWL 2 RL (PROV-O §1).
