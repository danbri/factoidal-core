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

Machine: a cloud container, Linux 6.18.44, 4 CPUs (Intel Xeon at 2.10 GHz,
one thread per core), 15.7 GiB of memory, shared with two other agents; the
1-minute load average was 5 to 9 through every run, so wall time is inflated
and the CPU-time column is the better comparison. Binaries: Lean
`l4factoidal` built from `eab58d16` (SHA-256 `40d6dd84…`, copied to a
scratch directory before the run so that no rebuild changes it during the
survey), F\* `factoidal` from release `build-ae3bb5df6f02-linux-x86_64`
(`tools/fetch-builds.sh --set native`, SHA-256 `ff9a633c…`).

## 2. Results

TABLE-PLACEHOLDER

## 3. Entailment checks

ENTAILS-TABLE-PLACEHOLDER

A stated pair is in the premise, so `owl-entails` answers it from the closure
(`via: closure`) without the tableau. Those 20 rows measure the cost of one
closure and check that nothing is lost; they do not test DL reasoning. The
unrelated pairs reach the tableau refuter (`OWL.Refute.negationGoals`, then
`tableauConsistent` on the closure plus the negated conclusion) whenever the
closure does not contain the conclusion.

## 4. The verdicts against HermiT

HERMIT-PLACEHOLDER

## 5. What did not finish, and the issues

Every row below is a step that did not finish under the caps, with its open
issue and its expected-failure row in `tests/stack/owl_real_gate.py`
(`tests/stack/owl_real_gate.sh`).

| What | Measured | Issue | Gate row |
|---|---|---|---|
| Lean `owl-consistent`, Cell Ontology (78,833 triples) | TIMEOUT at 600 s at load 6 to 8; in the gate run at load 3.5 it finished in 598 s with `true`. Prefixes: 5,000 lines 0.69 s CPU, 10,000 5.08 s, 20,000 25.4 s, 40,000 147.5 s. The closure is less than a tenth of it. HermiT: 6.1 s | https://github.com/danbri/factoidal/issues/760 | `cl-basic-consistent` |
| Lean `owl-consistent`, RO (11,703 triples) | TIMEOUT at 600 s. Prefixes: 2,000 lines 1.56 s CPU, 4,000 35.9 s, 8,000 not finished at 200 s. HermiT: 29.8 s | https://github.com/danbri/factoidal/issues/760 (comment) | `cl-basic-consistent` covers the cause |
| Lean `closure --regime owl-rl`, QUDT (130,404 triples) | OOM under `prlimit --as` at 27 s. With the 6 GB resident-set watchdog instead: killed at 6,038 MB after 61 to 78 s. `owl-consistent`, which computes the same closure and does not print it, peaks at 1,346 to 1,362 MB. The output path costs about 10 KB of resident memory per closure triple (QUDT prefixes: 117,250 closure triples in 1,269 MB, 250,490 in 2,470 MB) | https://github.com/danbri/factoidal/issues/758 | `qudt-closure` |
| Lean `owl-consistent` and `owl-entails`, QUDT, under `prlimit --as=6000000000` | OOM at 27 s with 1.25 GB resident. The Lean runtime's mimalloc reserves 1 GiB arenas and two 1 GiB thread stacks; with `MIMALLOC_ARENA_RESERVE=64MiB` the same command finishes under the same cap (41 s, 1,378 MB) | https://github.com/danbri/factoidal/issues/759 | `qudt-consistent` |
| Lean species check (`l4owl-species`), QUDT | finished, but 253 s CPU (323 s wall); prefixes: 32,000 lines 0.91 s, 65,000 lines 31.2 s | https://github.com/danbri/factoidal/issues/766 | `qudt-species` (60 s bound) |
| F\* `entail --regime OWL-RL` on wine and food (2,709 triples), RO, schema.org, the Cell Ontology and QUDT | TIMEOUT at 300 s on all five; Lean on the first four: 5.8 s, 8.0 s, 4.6 s, 26.7 s | https://github.com/danbri/factoidal/issues/765 | `wine-closure-fstar` (skipped when the F\* binary is absent) |
| Lean `owl-entails`, the unrelated pairs of RO and the Cell Ontology | the first unrelated pair of each: TIMEOUT at 600 s; the other 19 of each NOT_RUN. The 20 stated pairs of each: `true`, 8 to 24 s | https://github.com/danbri/factoidal/issues/760 (the same refuter cost) | `cl-basic-consistent` |

QUDT under the resident-set watchdog (`--rss-cap-mb 6000`, no address-space
cap, `--pairs 5`, Lean only; `OUT/results.jsonl` of that run):

| Step | Status | Wall | CPU | Peak resident set |
|---|---|---:|---:|---:|
| parse (Lean) | 130,404 triples | 4.4 s | 1.2 s | 256 MB |
| species | Full, 7,334 violations | 323 s | 253 s | 648 MB |
| closure | RSS_CAP (killed at the 6,000 MB watchdog) | 61 s | — | 6,038 MB sampled |
| consistent | `false` | 72 s | 43 s | 1,346 MB |
| entails, 5 stated pairs | 5 `true` | median 50 s, max 60 s | — | 1,372 MB |
| entails, 5 unrelated pairs | 5 `true` | (included above) | — | (included above) |

`owl-consistent` answers `false`: QUDT 3.4.0 is inconsistent. HermiT 1.3.8 also
reports it inconsistent (`InconsistentOntologyException`), so the verdict agrees
with an independent reasoner. The clash was not located. In an inconsistent
ontology every subclass axiom is entailed, so every entailment check must
answer `true`.

## 6. Other findings

- **The Lean RDF/XML parser gives an `xml:lang` to the next sibling property
  element.** `<ex:p xml:lang="en">x</ex:p><ex:r>y</ex:r>` gives `"y"@en`. RO and
  the Cell Ontology lose 2 triples each against rdflib 7.6.0 (11,703 against
  11,705; 78,833 against 78,835), where a plain literal becomes equal to an
  existing tagged one. The F\* parser has the same defect. Recorded on
  https://github.com/danbri/factoidal/issues/329 (comment of 2026-10-10); gate
  row `ro-parse` (expected failure).
- **`factoidal count` (F\*) counts statements as read**, so a repeated triple
  counts again: wine 2,012 and food 900 against 1,839 and 870 distinct triples.
  The Lean `parse` count is the graph size. `l4factoidal parse --out nquads`
  writes one line per statement read (2,012 lines for wine, 1,839 distinct);
  the harness removes duplicate lines when it writes `merged.nt`.
- **The two OWL RL closures are different sets.** The closure of the empty graph
  is 68 triples in Lean and 319 in F\*; on Pizza Lean adds 10,869 triples and
  F\* 7,774. The difference was not analysed here.
- **Species.** Four of the ten are OWL 2 DL for the Lean checker (SKOS, BFO,
  Pizza, wine with food). FOAF, PROV-O, RO, the Cell Ontology and QUDT are Full.
  The most common reason in the OBO and PROV-O files is
  `reserved-vocabulary-subject`: the files declare `rdfs:label`,
  `rdfs:comment` or `rdfs:seeAlso` as `owl:AnnotationProperty` (the OWL API
  writes these declarations). Whether OWL 2 DL admits those declarations was
  not checked against a second checker. RO carries SWRL rules (`untyped-class`
  223, `untyped-predicate` 296).
- **The resident set of the `closure` verb.** Wine: 421 MB for `closure`
  against 80 MB for `owl-consistent` on the same input; the Cell Ontology:
  1,956 MB. The same output-path cost as https://github.com/danbri/factoidal/issues/758.

## 7. What this method cannot see

- One run per step, at a load average of 5 to 9 on 4 CPUs shared with two
  other agents. Wall times carry that load; CPU times less so. No step was
  repeated, so no row has a spread. Compare rows within this run only
  (`skills/perf-benchmarking`, "Baselines are per-host").
- A stated pair passes from the closure alone. 20 passes of 20 there show that
  the closure keeps the premise and that the command line finishes; they show
  nothing about the tableau.
- An unrelated pair has no expectation in the harness. The HermiT comparison of
  section 4 is the only check of those verdicts, and HermiT decides them from
  its class hierarchy, so a pair that HermiT gets wrong is not seen either.
- The consistency check of a consistent ontology that answers `true` shows that
  the refuter did not close every branch. It does not show that the refuter
  explored them all within its fuel; `unknown` is the budget-out answer, and
  none was returned here.
- The species verdicts come from one checker. They were not compared with a
  second one (for example the OWL API profile checker).
- An address-space cap is not a memory cap for a Lean executable
  (https://github.com/danbri/factoidal/issues/759): the OOM rows under
  `prlimit --as` say that the step did not finish under that cap, not that it
  needs 6 GB. Section 5 gives the resident-set measurements.

## 8. Reproduce

```
tools/fetch-builds.sh --set native                       # F* binary
(cd formal/lean4 && lake build l4factoidal l4owl-species)
python3 tools/owl-real-bench.py --out /tmp/owl-real --cap-s 600 --fstar-cap-s 300
python3 tools/owl-real-bench.py --out /tmp/owl-real-rss --only qudt \
    --rss-cap-mb 6000 --pairs 5 --no-fstar               # section 5
python3 tools/owl-real-hermit.py /tmp/owl-real --hermit-jar HermiT.jar   # section 4
tests/stack/owl_real_gate.sh                             # the gate
```

The table of section 2 is `OUT/table.md`; every number in it is a field of a
row of `OUT/results.jsonl`, and each row carries the exact command it ran
(`cmd`).

