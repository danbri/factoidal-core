# OWL reasoning on real ontologies: time and memory (2026-10-10)

Issue: https://github.com/danbri/factoidal/issues/651, plan item 4 of the
2026-10-10 comment: "Measure DL consistency and entailment on a set of real
ontologies; record time and memory; open issues for what does not scale".
Branch `claude/wt-owl-real` of `danbri/factoidal-core`, base commit `eab58d16`.

RESULT-PLACEHOLDER

## 1. What was measured

Ten ontologies that span size and expressivity, each with a licence that
permits redistribution. Six are new under `third_party/ontologies/<name>/`,
each with a `PROVENANCE.md` (URL, retrieval date, SHA-256, licence, triple
counts from three parsers, species). Four were already vendored for the
closure benchmark (`third_party/vocabularies/PROVENANCE.md`,
`third_party/qudt/PROVENANCE.md`). The Gene Ontology is too large to vendor
(118 MB); the harness fetches a dated release at run time with `--optional`
and checks its SHA-256.

| Name | Source | Licence | Source bytes | Expressivity in the file |
|---|---|---|---:|---|
| skos | `third_party/vocabularies/skos.rdf` | W3C | 28,966 | RDFS with a few OWL property axioms |
| foaf | `third_party/vocabularies/foaf.rdf` | CC BY 1.0 | 44,209 | RDFS, inverse-functional properties, disjointness |
| prov-o | `third_party/ontologies/prov-o/prov-o.ttl` | W3C | 68,795 | OWL 2 RL by design |
| bfo | `third_party/ontologies/bfo/bfo-core.owl` | CC BY 4.0 | 97,258 | OWL 2 DL: disjointness, unions, property chains |
| pizza | `third_party/ontologies/pizza/pizza.owl` | CC BY 3.0 | 163,301 | OWL 2 DL: existential and universal restrictions, closure axioms, defined classes |
| wine | `third_party/ontologies/wine/{wine,food}.rdf` | W3C | 123,551 | OWL DL: cardinality, `owl:hasValue`, `owl:oneOf`, individuals |
| ro | `third_party/ontologies/ro/ro.owl` | CC0 1.0 | 1,224,640 | property chains, transitive and functional properties |
| schema.org | `third_party/vocabularies/schemaorg-30.0-current-https.ttl` | CC BY-SA 3.0 | 1,104,341 | RDFS (`schema:domainIncludes`, no OWL axioms) |
| cl-basic | `third_party/ontologies/cl-basic/cl-basic.owl` | CC BY 4.0 | 9,557,097 | OBO style: many existential restrictions, equivalent-class definitions |
| qudt | `third_party/qudt/QUDT-all-in-one-OWL.ttl` | CC BY 4.0 | 6,749,312 | OWL with many individuals (units, quantity kinds) |
| go-basic (optional) | `http://purl.obolibrary.org/obo/go/releases/2026-08-05/go-basic.owl`, SHA-256 `13a907d2a6586d0f7a4ba7cb556b7fe31240039268b85b01857e3f2da53e50d9` | CC BY 4.0 | 118,080,840 | OBO style, no cross-ontology axioms |

For each ontology, `tools/owl-real-bench.py` runs these steps:

| Step | Lean command (`formal/lean4/.lake/build/bin/`) | F\* command (`bin/linux-x86_64/factoidal`) |
|---|---|---|
| parse | `l4factoidal parse FILE --format FMT` (graph size, a set) | `factoidal count FILE` (statements as read; a repeated triple counts again) |
| species | `l4owl-species DOC.nt [IMPORTED.nt ...]` | none |
| closure | `l4factoidal closure MERGED.nt --format nquads --regime owl-rl` | `factoidal entail --data MERGED.nt --regime OWL-RL` |
| consistent | `l4factoidal owl-consistent MERGED.nt --format nquads` | none |
| entails | `l4factoidal owl-entails MERGED.nt CONCL.nt --format nquads` | none |

The F\* command line has no consistency or entailment verb; the F\* engine
decides those only inside `owl_runner` for W3C catalog cases. So the F\*
column covers parse and closure only.

`MERGED.nt` is the RDF merge (RDF 1.1 Semantics §4.1) of the source documents,
written once by the Lean parser (`parse --out nquads`), blank nodes of the
second and later documents prefixed, duplicate lines removed. Both engines
read the same file in the closure step, so the closure rows compare closures
and not the RDF/XML and Turtle parsers.

`l4owl-species` (new, `formal/lean4/Harness/OwlSpeciesFile.lean`) prints the
verdict of `L4Factoidal.OWL.SyntaxDL.speciesViolations`, the function that
`l4owl-probe --species` scores 488 pass, 0 fail, 1 local-override (out of 489)
on the W3C catalogs. It holds no OWL logic. The Lean tree decides OWL 2 DL
against OWL 2 Full; it does not decide the EL, QL or RL profiles.

The entailment checks: for each ontology, up to 20 STATED pairs, a named class
`A` with a stated `A rdfs:subClassOf B` (both IRIs, `B` not `owl:Thing`), and up
to 20 UNRELATED pairs, two named classes with no triple between them in either
direction. Named class: an IRI typed `owl:Class` or `rdfs:Class`. The pairs are
drawn with Python's `random.Random(651)` from the sorted candidates, so a rerun
on the same files checks the same pairs. A stated pair must be entailed (the
conclusion triple is in the premise). An unrelated pair has no expectation:
the verdict is recorded and nothing is scored. `owl-entails` recomputes the
closure of the premise for each check.

Every step runs as

```
/usr/bin/time -v -o T timeout -s KILL CAP prlimit --as=6000000000 -- CMD
```

with `CAP` 600 s for the Lean steps and 300 s for the F\* steps. A step killed
at the cap is TIMEOUT. A step that fails to allocate is OOM. Neither is a
verdict. After a TIMEOUT or OOM among the entailment checks of an ontology,
its remaining checks are NOT_RUN. Each row records wall time, user and system
CPU time, peak resident set size (`ru_maxrss`) and the 1-minute load average
at its start.

MACHINE-PLACEHOLDER

TABLE-PLACEHOLDER
