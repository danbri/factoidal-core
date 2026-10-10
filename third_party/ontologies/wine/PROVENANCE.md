# W3C OWL Web Ontology Language Guide: the wine and food ontologies — provenance

Vendored for `tools/owl-real-bench.py`, which measures OWL 2 RL closure, OWL DL
consistency and OWL DL entailment on real ontologies
(https://github.com/danbri/factoidal/issues/651, plan item 4). Record:
[`docs/designissues/2026-10-10-owl-real-ontologies.md`](../../../docs/designissues/2026-10-10-owl-real-ontologies.md).

Each file is the upstream byte stream, unmodified.

- **Retrieved:** 2026-10-10 (14:28 UTC), with `curl -sSL` through the session HTTPS proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples, Lean `l4factoidal parse` | Statements, F\* `factoidal count` | Triples, rdflib 7.6.0 |
|---|---|---|---:|---:|---:|---:|
| `wine.rdf` | https://www.w3.org/TR/owl-guide/wine.rdf | `bb1666593f9d7ba2ec9cb06dd4fcc17751ac8d523dc33ce22bcee6beeda778eb` | 78,225 | 1839 | 2012 | 1839 |
| `food.rdf` | https://www.w3.org/TR/owl-guide/food.rdf | `64af31d99ee62f58b7daa18977bbb27973c67a717d5d6317f42400bd53504184` | 45,326 | 870 | 900 | 870 |

The Lean count is the size of the parsed graph (a set). `factoidal count`
counts statements as read, so a repeated triple counts again.

## OWL 2 species

Verdict of `l4owl-species` on the Lean parser's N-Triples of the file(s), 2026-10-10: **DL** for the merge of `wine.rdf` and `food.rdf` (0 violations). `wine.rdf` alone: Full, 1 violation (`unresolved-import` of `food`). The verdicts were not compared with a second species checker.

The Lean species checker (`OWL.SyntaxDL.speciesViolations`, run by `l4owl-species`) decides OWL 2 DL against OWL 2 Full. It does not decide the EL, QL or RL profiles, so no profile is recorded here.

## Licence

W3C Document License (<https://www.w3.org/copyright/document-license-2023/>). The two files are part of the OWL Guide, W3C Recommendation 10 February 2004 (<https://www.w3.org/TR/owl-guide/>). They carry no licence statement of their own; the W3C document licence of the Recommendation applies.

## Notes

`wine.rdf` imports `food` (`owl:imports <http://www.w3.org/TR/2003/PR-owl-guide-20031209/food>`). The benchmark reads the two documents as one RDF merge (RDF 1.1 Semantics §4.1): 2709 triples. `wine.rdf` alone is OWL 2 Full for the species checker only because the import is not resolved (`unresolved-import`).
