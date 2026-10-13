# OWL reasoning on real ontologies: time and memory (2026-10-10)

Issue: https://github.com/danbri/factoidal/issues/651, plan item 4 of the
2026-10-10 comment: "Measure DL consistency and entailment on a set of real
ontologies; record time and memory; open issues for what does not scale".
Branch `claude/wt-owl-real` of `danbri/factoidal-core`, base commit `eab58d16`.

## 0. Result

Ten real ontologies, 252 to 130,404 triples, were run through the Lean
command line (`l4factoidal`) and, where the F\* command line has the verb,
through F\* (`factoidal`). Caps: 600 s wall clock for Lean steps, 300 s for
F\* steps, `prlimit --as=6000000000` for both.

- 📊 **Lean OWL RL closure:** finished on 9 of 10 (0.06 s to 26.7 s; peak
  resident set 35 MB to 1,956 MB). QUDT did not finish: OOM under the
  address-space cap (https://github.com/danbri/factoidal/issues/759), and more
  than 6 GB resident when the cap is a resident-set watchdog instead
  (https://github.com/danbri/factoidal/issues/758).
- 📊 **Lean DL consistency:** decided on 7 of 10, all `true` (SKOS, FOAF,
  PROV-O, BFO, Pizza, wine with food, schema.org; 0.06 s to 44 s). RO and the
  Cell Ontology: TIMEOUT at 600 s (https://github.com/danbri/factoidal/issues/760;
  HermiT: 29.8 s and 6.1 s). ✅ Repaired 2026-10-12 (section 9): RO 9.9 s and
  the Cell Ontology 13.3 s of CPU time, both `true`. QUDT: OOM under the address-space cap; without it,
  `false` in 72 s with 1.35 GB, and HermiT also finds QUDT 3.4.0 inconsistent.
- 📊 **Lean DL entailment, 354 checks planned:** stated pairs 150 `true`
  (out of 150 run); unrelated pairs 124 decided (4 `true`, 120 `false`); 2
  TIMEOUT (the first unrelated pair of RO and of the Cell Ontology), 1 OOM (the
  first QUDT check), 77 NOT_RUN after those. HermiT agrees with all 284 Lean
  verdicts it could be compared with (section 4); no Lean `true` is a HermiT
  `false`, and no Lean `false` is a HermiT `true`.
- 📊 **F\* OWL RL closure:** finished on 5 of 10 (up to 1,944 triples, up to
  10.3 s); TIMEOUT at 300 s on the other 5, the smallest of them wine and food
  with 2,709 triples (https://github.com/danbri/factoidal/issues/765). The F\*
  command line has no consistency or entailment verb.
- ⚠️ Other defects found: the Lean OWL 2 species check takes 253 s of CPU time
  on QUDT (https://github.com/danbri/factoidal/issues/766); the Lean RDF/XML
  parser holds 40 to 50 bytes of resident memory per document byte (GO basic,
  118 MB: 4.9 GB, F\* 0.83 GB; https://github.com/danbri/factoidal/issues/771);
  the Lean and F\* RDF/XML parsers give an `xml:lang` to the next sibling
  element (https://github.com/danbri/factoidal/issues/329).
- ✅ Every failure above has an open issue and an expected-failure row in
  `tests/stack/owl_real_gate.sh`: 5 pass, 0 fail, 7 expected-fail (out of
  12), exit 0 (11 rows in one run at 16:07 UTC, load average 1.8; the
  `cl-basic-parse-memory` row, added after it, run on its own).
- No Lean library code changed. New: `l4owl-species` (a harness executable),
  `tools/owl-real-bench.py`, `tools/owl-real-hermit.py`, the gate, and six
  vendored ontologies.

## 1. What was measured

Ten ontologies that span size and expressivity, each with a licence that
permits redistribution. Six are new under `third_party/ontologies/<name>/`,
each with a `PROVENANCE.md` (URL, retrieval date, SHA-256, licence, triple
counts from three parsers, species). Four were already vendored for the
closure benchmark (`third_party/vocabularies/PROVENANCE.md`,
`third_party/qudt/PROVENANCE.md`). The Gene Ontology is too large to vendor
(118 MB); the harness fetches a dated release at run time with `--optional`
and checks its SHA-256. The full optional GO row was not run on 2026-10-10;
its parse step was (section 5).

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

The main run was two processes of `tools/owl-real-bench.py` started 10
minutes apart on the same binaries: one for the first eight ontologies, one
for the Cell Ontology and QUDT. Every row of both, the QUDT watchdog run of
section 5 and the HermiT rows of section 4 are in
[`2026-10-10-owl-real-ontologies.results.jsonl`](2026-10-10-owl-real-ontologies.results.jsonl)
(446 lines; field `run` says which; field `cmd` is the command of the row,
with `OUT` for the output directory).

Steps per ontology, from `OUT/table.md` of the run. A cell is: count; wall time (CPU time), peak resident set. "added" is the closure size minus the input size; the first row is the closure of the empty graph (the axiomatic triples each engine adds).

| Ontology | Input triples | Species (Lean) | Parse, Lean | Parse, F* | OWL RL closure, Lean | OWL RL closure, F* | Consistent, Lean |
|---|---:|---|---|---|---|---|---|
| (empty graph) | — | — | — | — | 68 added; 0.05 s (0.03 CPU), 23 MB | 319 added; 0.03 s (0.02 CPU), 15 MB | — |
| skos | 252 | DL (0 violations) | 252; 0.03 s (0.02 CPU), 23 MB | 254; 0.02 s (0.01 CPU), 15 MB | 663 added; 0.06 s (0.05 CPU), 35 MB | 1204 added; 0.13 s (0.12 CPU), 18 MB | true; 0.06 s (0.05 CPU), 24 MB |
| foaf | 631 | FULL (1 violations) | 631; 0.03 s (0.02 CPU), 23 MB | 635; 0.02 s (0.01 CPU), 15 MB | 1241 added; 0.11 s (0.10 CPU), 43 MB | 1796 added; 0.34 s (0.34 CPU), 21 MB | true; 0.14 s (0.12 CPU), 26 MB |
| prov-o | 1146 | FULL (13 violations) | 1146; 0.02 s (0.01 CPU), 23 MB | 1146; 0.03 s (0.02 CPU), 15 MB | 2120 added; 0.28 s (0.26 CPU), 59 MB | 6075 added; 10.35 s (9.40 CPU), 35 MB | true; 1.33 s (0.70 CPU), 28 MB |
| bfo | 1015 | DL (0 violations) | 1015; 0.10 s (0.04 CPU), 25 MB | 1015; 0.13 s (0.04 CPU), 15 MB | 2822 added; 0.52 s (0.30 CPU), 63 MB | 3310 added; 1.05 s (0.71 CPU), 25 MB | true; 2.38 s (1.65 CPU), 33 MB |
| pizza | 1944 | DL (0 violations) | 1944; 0.05 s (0.03 CPU), 27 MB | 1944; 0.05 s (0.04 CPU), 16 MB | 10869 added; 0.98 s (0.90 CPU), 161 MB | 7774 added; 1.99 s (1.89 CPU), 42 MB | true; 0.78 s (0.60 CPU), 43 MB |
| wine | 2709 | DL (0 violations) | 2709; 0.07 s (0.05 CPU), 23 MB | 2912; 0.16 s (0.05 CPU), 15 MB | 26149 added; 5.83 s (5.37 CPU), 421 MB | TIMEOUT at 300 s, memory not recorded | true; 21.92 s (18.01 CPU), 80 MB |
| ro | 11703 | FULL (523 violations) | 11703; 0.38 s (0.35 CPU), 69 MB | 11705; 0.33 s (0.30 CPU), 22 MB | 31033 added; 7.96 s (7.73 CPU), 511 MB | TIMEOUT at 300 s, memory not recorded | TIMEOUT at 600 s, memory not recorded |
| schema.org | 17949 | FULL (10554 violations) | 17949; 0.20 s (0.18 CPU), 30 MB | 17949; 0.35 s (0.33 CPU), 17 MB | 42821 added; 4.60 s (4.46 CPU), 697 MB | TIMEOUT at 300 s, memory not recorded | true; 44.28 s (43.11 CPU), 104 MB |
| cl-basic | 78833 | FULL (7 violations) | 78833; 3.95 s (2.72 CPU), 479 MB | 78835; 3.61 s (2.63 CPU), 73 MB | 84611 added; 26.68 s (19.80 CPU), 1956 MB | TIMEOUT at 300 s, 947 MB sampled | TIMEOUT at 600 s, 446 MB sampled |
| qudt | 130404 | FULL (7334 violations) | 130404; 2.11 s (1.27 CPU), 257 MB | 130404; 3.18 s (2.00 CPU), 28 MB | OOM at 27 s, 1219 MB | TIMEOUT at 300 s, 661 MB sampled | OOM at 34 s, 1219 MB |

## 3. Entailment checks

Pairs per ontology. "not run" counts the checks skipped after a TIMEOUT or OOM of the same ontology. Times are wall time of one `owl-entails` run, closure included.

| Ontology | Named classes | Stated pairs: true / false / unknown / TIMEOUT / OOM / not run (out of N) | Unrelated pairs: true / false / unknown / TIMEOUT / OOM / not run (out of N) | Entailment check time, median and max | Peak RSS, max |
|---|---:|---|---|---|---|
| skos | 4 | 1 / 0 / 0 / 0 / 0 / 0 (out of 1) | 0 / 4 / 0 / 0 / 0 / 0 (out of 4) | 0.06 s, 0.07 s | 24 MB |
| foaf | 15 | 9 / 0 / 0 / 0 / 0 / 0 (out of 9) | 0 / 20 / 0 / 0 / 0 / 0 (out of 20) | 0.14 s, 0.28 s | 26 MB |
| prov-o | 30 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 0 / 20 / 0 / 0 / 0 / 0 (out of 20) | 0.50 s, 1.47 s | 30 MB |
| bfo | 36 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 2 / 18 / 0 / 0 / 0 / 0 (out of 20) | 0.38 s, 3.01 s | 34 MB |
| pizza | 99 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 2 / 18 / 0 / 0 / 0 / 0 (out of 20) | 0.60 s, 1.75 s | 44 MB |
| wine | 137 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 0 / 20 / 0 / 0 / 0 / 0 (out of 20) | 15.88 s, 33.05 s | 83 MB |
| ro | 58 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 0 / 0 / 0 / 1 / 0 / 19 (out of 20) | 10.18 s, 600.01 s | 77 MB |
| schema.org | 1010 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 0 / 20 / 0 / 0 / 0 / 0 (out of 20) | 44.80 s, 51.76 s | 104 MB |
| cl-basic | 3616 | 20 / 0 / 0 / 0 / 0 / 0 (out of 20) | 0 / 0 / 0 / 1 / 0 / 19 (out of 20) | 11.91 s, 600.19 s | 447 MB |
| qudt | 228 | 0 / 0 / 0 / 0 / 1 / 19 (out of 20) | 0 / 0 / 0 / 0 / 0 / 20 (out of 20) | 30.40 s, 30.40 s | 1219 MB |

A stated pair is in the premise, so `owl-entails` answers it from the closure
(`via: closure`) without the tableau. Those 20 rows measure the cost of one
closure and check that nothing is lost; they do not test DL reasoning. The
unrelated pairs reach the tableau refuter (`OWL.Refute.negationGoals`, then
`tableauConsistent` on the closure plus the negated conclusion) whenever the
closure does not contain the conclusion.

## 4. The verdicts against HermiT

`tools/owl-real-hermit.py` ran HermiT 1.3.8 (as shipped in owlready2 0.51,
OpenJDK 21) on the same `merged.nt` of each ontology, without its
`owl:imports` triples: `-k` for consistency, then `-c` for the class hierarchy,
from which it decides each pair.

| Ontology | HermiT consistent | Lean consistent | Pairs | Agree | Lean `true`, HermiT `false` | Lean `false`, HermiT `true` | Lean not decided |
|---|---|---|---:|---:|---:|---:|---:|
| skos | yes | true | 5 | 5 | 0 | 0 | 0 |
| foaf | yes | true | 29 | 29 | 0 | 0 | 0 |
| prov-o | yes | true | 40 | 40 | 0 | 0 | 0 |
| bfo | yes | true | 40 | 40 | 0 | 0 | 0 |
| pizza | yes | true | 40 | 40 | 0 | 0 | 0 |
| wine | yes | true | 40 | 40 | 0 | 0 | 0 |
| ro | yes | TIMEOUT | 40 | 20 | 0 | 0 | 20 |
| schema.org | yes | true | 40 | 40 | 0 | 0 | 0 |
| cl-basic | yes | TIMEOUT | 40 | 20 | 0 | 0 | 20 |
| qudt | **no** | OOM | 40 | 0 | 0 | 0 | 40 |
| qudt, run under the resident-set watchdog, 10 pairs | **no** | false | 10 | 10 | 0 | 0 | 0 |

284 Lean verdicts were compared (274 of the main run, plus the 10 of the
watchdog run); all 284 agree. The 4 unrelated pairs that the Lean engine answers `true` are
subsumptions HermiT also derives: in BFO, site under independent continuant
and relational quality under entity; in Pizza, sundried tomato topping under
food, and `American` under `NonVegetarianPizza`. The last one is not in the
OWL RL closure of Pizza (`closure --regime owl-rl` does not contain the
triple), so the tableau refuter decided it; `NonVegetarianPizza` is defined
with a complement. Gate row `pizza-entails-american` keeps it.

## 5. What did not finish, and the issues

Every row below is a step that did not finish under the caps, with its open
issue and its expected-failure row in `tests/stack/owl_real_gate.py`
(`tests/stack/owl_real_gate.sh`).

| What | Measured | Issue | Gate row |
|---|---|---|---|
| Lean `owl-consistent`, Cell Ontology (78,833 triples). ✅ Repaired 2026-10-12, section 9: 13.3 s CPU | TIMEOUT at 600 s at load 6 to 8; in the gate run at load 3.5 it finished in 598 s with `true`. Prefixes: 5,000 lines 0.69 s CPU, 10,000 5.08 s, 20,000 25.4 s, 40,000 147.5 s. The closure is less than a tenth of it. HermiT: 6.1 s | https://github.com/danbri/factoidal/issues/760 | `cl-basic-consistent` |
| Lean `owl-consistent`, RO (11,703 triples). ✅ Repaired 2026-10-12, section 9: 9.9 s CPU | TIMEOUT at 600 s. Prefixes: 2,000 lines 1.56 s CPU, 4,000 35.9 s, 8,000 not finished at 200 s. HermiT: 29.8 s | https://github.com/danbri/factoidal/issues/760 (comment) | `ro-consistent` (added 2026-10-12) |
| Lean `closure --regime owl-rl`, QUDT (130,404 triples) | OOM under `prlimit --as` at 27 s. With the 6 GB resident-set watchdog instead: killed at 6,038 MB after 61 to 78 s. `owl-consistent`, which computes the same closure and does not print it, peaks at 1,346 to 1,362 MB. The output path costs about 10 KB of resident memory per closure triple (QUDT prefixes: 117,250 closure triples in 1,269 MB, 250,490 in 2,470 MB) | https://github.com/danbri/factoidal/issues/758 | `qudt-closure` |
| Lean `owl-consistent` and `owl-entails`, QUDT, under `prlimit --as=6000000000` | OOM at 27 s with 1.25 GB resident. The Lean runtime's mimalloc reserves 1 GiB arenas and two 1 GiB thread stacks; with `MIMALLOC_ARENA_RESERVE=64MiB` the same command finishes under the same cap (41 s, 1,378 MB) | https://github.com/danbri/factoidal/issues/759 | `qudt-consistent` |
| Lean `parse --format rdfxml`, GO basic 2026-08-05 (118,080,840 bytes; fetched at run time, not vendored) | under `prlimit --as`: `std::bad_alloc` after 0.57 s. With the 6 GB resident-set watchdog: 1,283,913 triples, 52 s (32 s CPU), 4,919 MB peak, 43.7 bytes per document byte; the Cell Ontology: 52.6. F\* `count`: 33.6 s, 831 MB | https://github.com/danbri/factoidal/issues/771 | `cl-basic-parse-memory` (15 bytes per byte) |
| Lean species check (`l4owl-species`), QUDT | finished, but 253 s CPU (323 s wall); prefixes: 32,000 lines 0.91 s, 65,000 lines 31.2 s | https://github.com/danbri/factoidal/issues/766 | `qudt-species` (60 s bound) |
| F\* `entail --regime OWL-RL` on wine and food (2,709 triples), RO, schema.org, the Cell Ontology and QUDT | TIMEOUT at 300 s on all five; Lean on the first four: 5.8 s, 8.0 s, 4.6 s, 26.7 s | https://github.com/danbri/factoidal/issues/765 | `wine-closure-fstar` (skipped when the F\* binary is absent) |
| Lean `owl-entails`, the unrelated pairs of RO and the Cell Ontology. ✅ Repaired 2026-10-12, section 9: all 40 decided, all agree with HermiT | the first unrelated pair of each: TIMEOUT at 600 s; the other 19 of each NOT_RUN. The 20 stated pairs of each: `true`, 8 to 24 s | https://github.com/danbri/factoidal/issues/760 (the same refuter cost) | `cl-basic-consistent` |

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
  Pizza, wine with food). FOAF, PROV-O, RO, schema.org, the Cell Ontology and
  QUDT are Full (schema.org: 10,554 violations, mostly properties used without
  an OWL typing).
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
- Wall time: the first process of the main run timed each step with the
  harness's own clock around the process; the second process and the QUDT
  watchdog run polled every 0.2 s and so round a step up by at most 0.2 s
  (their shortest step took 2.1 s). The harness now takes the wall time from
  `time -v`.
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

## 9. RO and the Cell Ontology: where the time was, and the repair (2026-10-12)

Issue: https://github.com/danbri/factoidal/issues/760; OKR batch 1, key
result 3.3 (https://github.com/danbri/factoidal/issues/768): RO and the Cell
Ontology finish `owl-consistent` in 600 s. Branch `claude/wt-refuter-scaling`
of `danbri/factoidal-core`, base commit `fb263d6f`.

### 9.1 Method

`l4refute-profile FILE.nt [--trace] [--check] [--goal CONCL.nt]` (new,
`formal/lean4/Harness/RefuteProfile.lean`) runs what `owl-consistent` runs:
the OWL 2 RL closure, the graph-level checks, the class-size counting rung,
the TBox read, the initial state, and `OWL.Refute.search`. It calls the
library's phase functions in the order `search` calls them, with the same
threaded budget, and times each one; every timed value is consumed by a
counter before the second clock read (`skills/measuring-inference`, sections
9 and 11), and the parts are printed beside the step total. `--check` runs
`tableauConsistent` on the same closure and fails when the verdicts differ;
`--goal` profiles the refutation `owl-entails` runs (the closure with the
first negation goal of the conclusion appended). It holds no OWL logic. It counts expansion steps (calls of `search`),
saturation passes, union and merge branch points and branches, nodes,
labels and the largest label set, and the calls and time of each rule of a
pass. The refuter has no blocking (a witness-depth cap stands in for it), so
there is no blocking count.

Inputs: the issue's reproduction, `l4factoidal parse … --out nquads | grep . |
sort -u` in the POSIX locale (byte order), then the first N lines. The
prefixes of the issue's table were cut from a file sorted in another order,
so their times are not comparable with these. CPU time is user time of one
run; the load average was 1.5 to 4 on 4 CPUs shared with two other agents.
Callgrind (`valgrind --tool=callgrind`) on the 5,000-line prefix checked the
attribution independently.

### 9.2 What was measured, before the repair (`fb263d6f`)

| Input (first N lines) | Closure triples | TBox axioms | Nodes | Labels (largest set) | Steps | Branch points | RL closure | Counting rung | TBox read + initial state | Search | `owl-consistent` CPU |
|---|---:|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| Cell Ontology 5,000 | 11,187 | 4,572 | 754 | 1,877 (4) | 2 | 0 | 0.28 s | 2.75 s | 0.06 s | 0.014 s | 3.20 s |
| Cell Ontology 10,000 | 26,952 | 13,216 | 1,315 | 3,498 (4) | 2 | 0 | 0.77 s | 19.4 s | 0.19 s | 0.050 s | 19.3 s |
| Cell Ontology 20,000 | 56,839 | 30,061 | 2,535 | 6,994 (4) | 2 | 0 | 1.75 s | 101.9 s | 0.59 s | 0.150 s | 104.3 s |
| RO 2,000 | 5,126 | 580 | 452 | 939 at start | 2 | 0 | 0.09 s | 0.00005 s | 0.02 s | 0.88 s | 1.03 s |
| RO 4,000 | 12,011 | 1,160 | 923 | 342,869 after one pass (374) | 2 | 0 | 0.37 s | 0.00006 s | 0.08 s | 26.8 s | 28.1 s |

Two different causes, one per ontology.

**The Cell Ontology: the class-size counting rung.** The search is two steps
(one pass that changes the state, one that does not) with no branch point,
and it takes 0.15 s at 20,000 lines. 98 % of the time is
`OWL.CountingOracle.classSizeUnsat` (`countingRefutes`), which
`tableauConsistentTraced` runs before the search. The closure has 5
cardinality triples and no datatype property, so it is in the counting
fragment, and `buildLinSystem` builds the class-size linear system:
`finiteClasses` and `lcOneofAll` scan the whole graph once for each IRI of the
graph, and `dedupIris` compares every IRI occurrence with every later one.
That is quadratic in the graph (7.0 and 5.3 times per doubling). Callgrind on
5,000 lines: `classSizeUnsat` 83.8 % of the instructions, `finiteClasses`
67.0 %, `lcOneofAll` 13.5 %. The system it built had no equality row: the
closure declares no functional property and has no `owl:unionOf`. With no
equality row the certificate search has nothing to eliminate and answers
"no certificate", so all of that work could only answer `false`.

**RO: every range axiom on every node.** RO is not in the counting fragment
(it declares two datatype properties), so the rung answers at once. The
search is again two steps with no branch point, but one pass takes 13 s on
4,000 lines. `domainRangeAxioms` reads each `p rdfs:range C` as `⊤ ⊑ ∀p.C`,
and `injectGlobalAxioms` put `∀p.C` on every node. The OWL 2 RL closure of RO
has 8,246 `rdfs:range` and 8,888 `rdfs:domain` triples (the closure carries
each range up the class hierarchy and down the property hierarchy), so the
label count is the node count times the range-axiom count: 342,869 labels on
923 nodes, 374 on the largest node. Per pass: the `∀` rule 7.3 s (675,636
calls, each a successor read that scanned the sub-property and inverse
tables as lists), the datatype range clash 7.9 s (it computed the filler
value space of every property a label mentions, `∀` labels included), the
domain rule 2.2 s (it read the successors of every property with a domain
axiom at every node). On the whole RO graph the TBox has 4,159 axioms
with the antecedent `⊤`, so every one of its 2,728 nodes would carry 4,159
labels from them alone.

### 9.3 The repair

All in the library; no verdict rule changed.

1. **The counting rung answers `false` without building a system that has no
   equality row** (`CountingOracle.noEqualityRows`, `classSizeUnsat`). Every
   equality row comes from a declared `owl:FunctionalProperty` (fibre and
   bijection rows) or an `owl:unionOf` list (disjoint-union rows). Proved:
   `findLinCert_nil` (no equality row, no certificate),
   `buildLinSystem_eqs_nil`, and `classSizeUnsat_eq_ref` (the new verdict
   equals the old one, kept as `classSizeUnsatRef`, on every graph).
2. **Range axioms are applied where there is an edge.** A range axiom
   `⊤ ⊑ ∀p.C` is put on a node only when the node has a possible
   `p`-successor (`TBoxIndex.buildLazy`, `injectLazyRanges`,
   `successorPropsAt`). This is the range half of domain and range
   absorption (D. Tsarkov and I. Horrocks, "Efficient reasoning with range
   and domain constraints", DL 2004; used by FaCT++, Pellet and HermiT); the
   domain half was already there (`applyAxiomsEdges` fires `≥ 1 p ⊑ C` on a
   node's edges). An axiom is applied this way only when its consequent
   cannot matter at a node with no `p`-successor (`lazyRangeAxiom`): `p` is
   not `owl:topObjectProperty`, the datatype rules read the filler as no
   constraint, and `∀p.C` occurs in no other axiom and no initial label, so no
   rule but the `∀` rule reads the label. The label is still added on every
   node with an edge on `p` or a sub-property of it, in either direction, so
   the `∀` rule pushes `C` across every edge as before.
3. **The rules ask only the properties that have successors.**
   `applyAxiomsEdges` reads only the edge properties `successorPropsAt`
   names (the loop skipped every other property at `succ.isEmpty`); the
   datatype range clash asks only properties with an existence obligation
   (`datatypeRangeClash`, proved equal to the old rule:
   `datatypeRangeClash_eq_ref`).
4. **Constant-time role tables, and one TBox index per search.** The
   sub-property, super-property and inverse tables are hash maps
   (`subMap`, `supMap`, `invMap`); each answers as the list lookup it
   replaces, proved (`closureMap_getD`, `inverseMap_getD`,
   `subsOf_initState`, `supsOf_initState`, `inversesOfSt_initState`).
   `onePass` takes the TBox index; `tableauConsistentTraced` builds it once,
   where `onePass` built it on every pass.

Not changed, because the measurement did not point at them: the TBox is
already applied by lazy unfolding (an axiom `A ⊑ C` fires on a node that
carries `A`, `applyAxioms`; it is never a global `¬A ⊔ C`, and the
propositional clash takes it as a clause only for the node it reads); the
refuter has no blocking to tune (a witness-depth cap of 3 stands in for
it); and with no branch point on either ontology, semantic branching and
dependency-directed backjumping have nothing to act on. Told-subsumer
caching would serve classification, which `owl-consistent` does not do.

The certificate path is unchanged: `checkCert` re-derives every forward
consequence itself (`saturate`), so a certificate never relied on a `∀`
label being present on a node with no successor. `#guard`s in
`OWL/RefuteTests.lean` (range on an asserted edge, on an expansion edge, on
an inverse edge, on a sub-property edge, and the domain on a sub-property
edge, each with a twin that has a model) and in `OWL/CountingOracle.lean`
(the short cut on a graph with no equality row, and a graph with two
disjoint unions whose certificate the rung still finds).

### 9.4 After the repair, beside HermiT

| Input | Before: `owl-consistent` CPU | After: CPU (wall), peak RSS | Of which RL closure | Of which search | HermiT 1.3.8, wall |
|---|---:|---:|---:|---:|---:|
| Cell Ontology 5,000 lines | 3.20 s | 0.48 s (0.69 s), 52 MB | 0.23 s | 0.020 s | — |
| Cell Ontology 10,000 lines | 19.3 s | 1.05 s (1.31 s), 86 MB | 0.65 s | 0.059 s | — |
| Cell Ontology 20,000 lines | 104.3 s | 2.74 s (2.89 s), 149 MB | 1.93 s | 0.166 s | — |
| Cell Ontology 40,000 lines | — | 7.48 s (8.42 s), 266 MB | 5.03 s | 0.383 s | — |
| Cell Ontology, whole (78,833 triples) | not finished in 600 s | 13.3 s (14.9 s), 447 MB | 8.9 s | 0.55 s (2 steps) | 6.1 s, 275 MB |
| RO 2,000 lines | 1.03 s | 0.17 s (0.24 s), 31 MB | 0.09 s | 0.018 s | — |
| RO 4,000 lines | 28.1 s | 0.57 s (0.59 s), 42 MB | 0.37 s | 0.067 s | — |
| RO 8,000 lines | not finished in 200 s (issue 760) | 2.33 s (2.54 s), 65 MB | — | — | — |
| RO, whole (11,703 triples) | not finished in 600 s | 9.89 s (10.2 s), 77 MB | 9.1 s | 0.57 s (3 steps) | 29.8 s, 1.6 GB |

Callgrind on the repaired command over the first 20,000 lines of the Cell
Ontology: the OWL 2 RL closure 55.3 % of the instructions
(`stepConclusionsS` 35.1 %, `Index.insertAll` 18.3 %), the refuter 14.1 %
(`collectAxioms` 5.9 %, `initState` 4.2 %, `search` 2.8 %), the class-size
rung below 0.1 %, reading the N-Triples file 26.3 %.

The refuter is no longer the cost on either ontology: on the whole Cell
Ontology the search is 0.55 s of 13.3 s and on RO 0.57 s of 9.9 s. The cost
now is the OWL 2 RL closure, which grows about 2.6 to 3.0 times per doubling
of these prefixes (its output grows about 2.0 times): it re-evaluates every
rule over the whole graph each round (no semi-naive evaluation,
`OWL/RLClosureIndexed.lean` header; https://github.com/danbri/factoidal/issues/756
item 2). On RO the Lean check is three times faster than HermiT and uses a
twentieth of its memory; on the Cell Ontology it is 2.2 times slower, and
the closure is two thirds of it.

The other ontologies of section 2 (`owl-consistent` wall time, before at
load 5 to 9 and after at load 2 to 3): BFO 2.38 s to 0.14 s, PROV-O 1.33 s
to 0.18 s, wine 21.9 s to 13.8 s. On wine the search is now the larger part:
9.1 s of a profile total of 14.2 s, in 19 steps with 8 merge branch points,
where every step re-runs every rule on all 823 nodes (the propositional and
nominal clash checks are 3.9 s of it).

### 9.5 Gates

- `tests/stack/owl_real_gate.py --only cl-basic-consistent,ro-consistent`:
  2 pass, 0 fail, 0 expected-fail (out of 2). `cl-basic-consistent` 15.17 s
  wall, 447 MB, `true`; its expected-failure mark is removed.
  `ro-consistent` (new) 12.61 s wall, 77 MB, `true`. Both rows now have a
  60 s bound. The other rows are unchanged.
- `tests/stack/lean_scaling.py --only owl-consistent-cl` (new row): 1 pass,
  0 fail, 0 expected-fail (out of 1). 1.320 s, 3.180 s and 8.378 s of CPU at
  10,000, 20,000 and 40,000 lines: 2.4 and 2.6 per doubling (bound 3.0),
  6.3 for 4x input (bound 9.0).
- OWL DL catalogs (`tools/lean-scoreboard.sh --only l4owl-probe`, before at
  `fb263d6f` and after, one run each, `MIMALLOC_ARENA_RESERVE=64MiB`):
  all 77 table rows identical (pass, fail, skip/other, total), and every
  runner log identical once the timing fields are removed: every summary
  line, failing id, `PROVED-BY-CERTIFICATE` and `REFUTATION-PROFILE` line.
  The certificate counts did not move: type-inconsistency 50
  certificate-checked, 27 unchecked (out of 77 decided by refutation);
  type-positive-entailment and type-consistency 32 and 23 (out of 55);
  syntax-dl 72 and 41 (out of 113). DL type-inconsistency stays 126 pass,
  1 fail, 1 skip (out of 128). One log line differs: the RDF-Based job (which
  runs no refuter) reported a closure time cap on `WebOnt-miscellaneous-001`
  in the run before and none in the run after; its rows are identical, and
  the cap is the 30 s wall-clock budget of a run that shared the machine
  with the benchmark below.
- HermiT agreement (`tools/owl-real-hermit.py` over a new
  `tools/owl-real-bench.py --no-fstar` run on the repaired binary): 314
  Lean verdicts compared, 314 agree, 0 Lean `true` where HermiT says `false`,
  0 Lean `false` where HermiT says `true`. The 40 new ones are the RO and
  Cell Ontology pairs that were TIMEOUT or NOT_RUN on 2026-10-10. QUDT stays
  undecided under the address-space cap
  (https://github.com/danbri/factoidal/issues/759). Against the run of
  2026-10-10, 322 Lean verdicts are unchanged and 42 changed, each from
  TIMEOUT or NOT_RUN to a verdict. `owl-consistent` of schema.org went from
  44.3 s to 4.0 s wall.
- `tools/lean-tail-recursion-audit.py --gate` (stale IR removed first): pass,
  with three new allow-list lines: the occurrence walk
  `ceSubHashesInto`/`ceListSubHashesInto` (class-expression nesting) and the
  profiler's copy of the search (one frame per expansion step).
- `tools/lean-hygiene-audit.py --build-log`: clean (no `sorry`, axiom,
  `native_decide`, `unsafe` or `implemented_by`; `partial def` 164, the
  baseline). `Wasm/native-smoke.sh`: 350 pass, 0 fail (out of 350). Full
  `lake build`: exit 0.

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

