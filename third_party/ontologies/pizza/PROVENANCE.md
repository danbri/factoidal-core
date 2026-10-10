# The Pizza ontology (Manchester University / Protégé tutorial), version 2.0 — provenance

Vendored for `tools/owl-real-bench.py`, which measures OWL 2 RL closure, OWL DL
consistency and OWL DL entailment on real ontologies
(https://github.com/danbri/factoidal/issues/651, plan item 4). Record:
[`docs/designissues/2026-10-10-owl-real-ontologies.md`](../../../docs/designissues/2026-10-10-owl-real-ontologies.md).

Each file is the upstream byte stream, unmodified.

- **Retrieved:** 2026-10-10 (14:28 UTC), with `curl -sSL` through the session HTTPS proxy.

| File | Retrieved from | SHA-256 | Bytes | Triples, Lean `l4factoidal parse` | Statements, F\* `factoidal count` | Triples, rdflib 7.6.0 |
|---|---|---|---:|---:|---:|---:|
| `pizza.owl` | https://protege.stanford.edu/ontologies/pizza/pizza.owl | `f1af596252f2e2a9f2df85bc64a9384dcf88a558084c25add5ffedca163ba45a` | 163,301 | 1944 | 1944 | 1944 |

The Lean count is the size of the parsed graph (a set). `factoidal count`
counts statements as read, so a repeated triple counts again.

## OWL 2 species

SPECIES-PLACEHOLDER

The Lean species checker (`OWL.SyntaxDL.speciesViolations`, run by `l4owl-species`) decides OWL 2 DL against OWL 2 Full. It does not decide the EL, QL or RL profiles, so no profile is recorded here.

## Licence

Creative Commons Attribution 3.0 (CC BY 3.0), stated in the document: `<terms:license>Creative Commons Attribution 3.0 (CC BY 3.0)</terms:license>`. Contributors named in the document: Alan Rector, Chris Wroe, Matthew Horridge, Nick Drummond, Robert Stevens.

## Notes

The copy at `https://raw.githubusercontent.com/owlcs/pizza-ontology/master/pizza.owl` (241,414 bytes) carries no licence statement and its repository has no LICENSE file (HTTP 404 on 2026-10-10), so the Protégé copy, which states its licence, is the one vendored.
