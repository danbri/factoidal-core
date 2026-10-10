# Basic Formal Ontology 2020 (BFO 2020), core, release 2024-01-29 — provenance

Vendored for `tools/owl-real-bench.py`, which measures OWL 2 RL closure, OWL DL
consistency and OWL DL entailment on real ontologies
(https://github.com/danbri/factoidal/issues/651, plan item 4). Record:
[`docs/designissues/2026-10-10-owl-real-ontologies.md`](../../../docs/designissues/2026-10-10-owl-real-ontologies.md).

Each file is the upstream byte stream, unmodified.

- **Retrieved:** 2026-10-10 (14:28 UTC), with `curl -sSL` through the session HTTPS proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples, Lean `l4factoidal parse` | Statements, F\* `factoidal count` | Triples, rdflib 7.6.0 |
|---|---|---|---:|---:|---:|---:|
| `bfo-core.owl` | http://purl.obolibrary.org/obo/bfo/2020/bfo-core.owl (redirects to https://raw.githubusercontent.com/BFO-ontology/BFO-2020/release-2024-01-29/src/owl/bfo-core.owl) | `af81eb7144c3d3db3a2d2beabff9dd299b14a91dc69cc84e663ca91e0c98039c` | 97,258 | 1015 | 1015 | 1015 |

The Lean count is the size of the parsed graph (a set). `factoidal count`
counts statements as read, so a repeated triple counts again.

## OWL 2 species

Verdict of `l4owl-species` on the Lean parser's N-Triples of the file(s), 2026-10-10: **DL** (0 violations). The verdicts were not compared with a second species checker.

The Lean species checker (`OWL.SyntaxDL.speciesViolations`, run by `l4owl-species`) decides OWL 2 DL against OWL 2 Full. It does not decide the EL, QL or RL profiles, so no profile is recorded here.

## Licence

Creative Commons Attribution 4.0 (CC BY 4.0), stated in the document: `dcterms:license <https://creativecommons.org/licenses/by/4.0/>`.
