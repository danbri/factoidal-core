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
  element (https://github.com/danbri/factoidal/issues/329; the Lean parser is
  repaired, 2026-10-14, https://github.com/danbri/factoidal/issues/841).
- ✅ 2026-10-13 (§ 10, OKR batch 1 KR 3.4): the QUDT closure peaks at 1,352 MB
  and writes its lines as it goes (issue 758); the species check of QUDT takes
  2.27 s of CPU time, with indexes proved equal to the readable definition
  (issue 766). A part that stays quadratic in blank-node-to-blank-node
  assertions: https://github.com/danbri/factoidal/issues/812.
- ✅ 2026-10-13 (§ 11, https://github.com/danbri/factoidal/issues/756 item 2):
  the OWL 2 RL closure runs semi-naive rounds, proved to return the same list
  as the naive rounds at every fuel, with the four obligations of issue 756
  proved and fuel adequacy open. CPU time of `closure`: RO 15.9 s to 2.8 s,
  the Cell Ontology 11.7 s to 7.4 s, QUDT 45.8 s and 1,350 MB to 22.6 s and
  659 MB. schema.org `owl-consistent`: 2.8 s of CPU time, HermiT 2.6 s
  (https://github.com/danbri/factoidal/issues/819).
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
| Lean `closure --regime owl-rl`, QUDT (130,404 triples) | OOM under `prlimit --as` at 27 s. With the 6 GB resident-set watchdog instead: killed at 6,038 MB after 61 to 78 s. `owl-consistent`, which computes the same closure and does not print it, peaks at 1,346 to 1,362 MB. The output path costs about 10 KB of resident memory per closure triple (QUDT prefixes: 117,250 closure triples in 1,269 MB, 250,490 in 2,470 MB) | https://github.com/danbri/factoidal/issues/758 | `qudt-closure`. Repaired 2026-10-13 (§ 10.1): 1,352 MB, the row passes under the resident-set watchdog with a 2,000 MB bound; the address-space cap is row `qudt-closure-address-space` (issue 759) |
| Lean `owl-consistent` and `owl-entails`, QUDT, under `prlimit --as=6000000000` | OOM at 27 s with 1.25 GB resident. The Lean runtime's mimalloc reserves 1 GiB arenas and two 1 GiB thread stacks; with `MIMALLOC_ARENA_RESERVE=64MiB` the same command finishes under the same cap (41 s, 1,378 MB) | https://github.com/danbri/factoidal/issues/759 | `qudt-consistent` |
| Lean `parse --format rdfxml`, GO basic 2026-08-05 (118,080,840 bytes; fetched at run time, not vendored) | under `prlimit --as`: `std::bad_alloc` after 0.57 s. With the 6 GB resident-set watchdog: 1,283,913 triples, 52 s (32 s CPU), 4,919 MB peak, 43.7 bytes per document byte; the Cell Ontology: 52.6. F\* `count`: 33.6 s, 831 MB | https://github.com/danbri/factoidal/issues/771 | `cl-basic-parse-memory` (15 bytes per byte) |
| Lean species check (`l4owl-species`), QUDT | finished, but 253 s CPU (323 s wall); prefixes: 32,000 lines 0.91 s, 65,000 lines 31.2 s | https://github.com/danbri/factoidal/issues/766 | `qudt-species` (60 s bound). Repaired 2026-10-13 (§ 10.2): 2.27 s CPU, the row passes |
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
  row `ro-parse` (expected failure). Repaired in the Lean parser on 2026-10-14
  (https://github.com/danbri/factoidal/issues/841, section 3c.7 of
  `2026-09-03-rdf-parsing-strategy.md`): RO reads 11,705 triples and the Cell
  Ontology 78,835, as rdflib does, and `ro-parse` is a pass. The F\* parser
  still has the defect (row `RDFXML-LANG-SCOPE` of `tests/known-defects/run.sh`).
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

- `tests/stack/owl_real_gate.sh` (whole gate, final binary, load average
  4.8): 7 pass, 0 fail, 5 expected-fail (out of 12); 1 skipped
  (`wine-closure-fstar`: no F\* binary in this checkout).
  `cl-basic-consistent` 16.67 s wall, 447 MB, `true`; its expected-failure
  mark is removed. `ro-consistent` (new) 12.65 s wall, 77 MB, `true`. Both
  rows have a 60 s bound. The other rows give what they gave before:
  `ro-parse`, `qudt-species`, `cl-basic-parse-memory`, `qudt-closure` and
  `qudt-consistent` expected failures with their issues; the other four
  pass.
- `tests/stack/lean_scaling.py --only owl-consistent-cl` (new row), final
  binary: 1 pass, 0 fail, 0 expected-fail (out of 1). 1.407 s, 3.169 s and
  7.966 s of CPU at 10,000, 20,000 and 40,000 lines: 2.3 and 2.5 per
  doubling (bound 3.0), 5.7 for 4x input (bound 9.0).
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
  baseline; the `#print axioms` lines of the build, the six new equality
  theorems among them, name only `propext`, `Classical.choice` and
  `Quot.sound`). `Wasm/native-smoke.sh`: 350 pass, 0 fail (out of 350). Full
  `lake build`: exit 0 (1,412 jobs).

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

## 10. OWL RL closure on QUDT and the species check (2026-10-13, OKR batch 1 KR 3.4)

Key result 3.4 of https://github.com/danbri/factoidal/issues/768: "OWL RL
closure on QUDT, and the species check": target "under 2 GB; species check
linear". Issues https://github.com/danbri/factoidal/issues/758 and
https://github.com/danbri/factoidal/issues/766. Branch `claude/wt-qudt-owl`,
base `e3c3aa01`.

Inputs: `qudt.nt` is the Lean parse of `third_party/qudt/QUDT-all-in-one-OWL.ttl`
(`l4factoidal parse --out nquads | grep . | LC_ALL=C sort -u`, 130,404 lines,
18,100,516 bytes; as a set, the same triples as the gate's `merged.nt`), and
its first 16,000, 32,000 and 65,000 lines. The binaries before are copies of
`e3c3aa01`'s. Each closure row ran alone under the resident-set watchdog of
`tools/owl-real-bench.py` (6,000 MB, no address-space cap), at a load average
of 4 to 8 on 4 CPUs shared with two other agents.

### 10.1 Closure: where the memory was

At `e3c3aa01` the QUDT closure already finished: the JSON repairs of
2026-10-12 (`2026-10-10-lean-vs-fstar-performance.md` § 11: `escapeString`
without a character list, the reverse-accumulator JSON parser) removed most
of the 10 KB per closure triple that issue 758 measured at `eab58d16`.

`l4query-phases FILE --closure-op` (new) runs the phases of the `closure`
verb as it was and prints the resident set after each. QUDT, before, MB
(`hwm` is the peak so far):

| Phase | What it holds | Wall, cumulative | RSS after | Peak so far |
|---|---|---:|---:|---:|
| read | the file as a `String` | 0.07 s | 48 | 48 |
| parse | the `Dataset` | 2.3 s | 461 | 651 |
| normalize | `datasetForOps .rdf11` | 3.2 s | 389 | 651 |
| closure | `OWL.RL.closureFix`, 638,420 triples | 48.8 s | 646 | **1,343** |
| ntriples | `Graph.toNTriples`, 72,698,862 bytes | 49.1 s | 661 | 1,343 |
| envelope | `okWith`, the JSON string | 49.6 s | 674 | 1,343 |
| decode | `parseJson` of the envelope, its `nquads` member | 54.0 s | 1,097 | 1,343 |
| output | the member written | 54.1 s | 1,097 | 1,343 |

On the whole file the closure itself sets the peak. On the prefixes the
output path does: the decode (an `Array Char` of 8 bytes per character, and
the `Json` tree) raised the peak from 358 to 443 MB at 32,000 lines and from
492 to 688 MB at 65,000.

**Repair.** `closure` writes one N-Triples line per closure triple
(`Wasm/Cli.lean`, `closureCmd`), from `Ops.closureStreamOf`
(`Wasm/Ops/Reason.lean`): the closure graph of the regime, or the error text.
Before the first line it asks `Graph.firstNTriplesError`, because
`Graph.toNTriples` gives only the first error when a triple does not
serialise. Proved: `Graph.toNTriples_eq_lines` (the document is the first
error, or the lines in order, joined) and `Ops.closureEnvelopeOf_stream` (for
every dataset and every `--regime` value, the old envelope is `errJson` of the
stream's error, or `okWith` of the stream's lines joined, in the member the
command line printed, `nquads` or `ntriples`). Not proved: that the JSON
encoding and decoding of that member gave the string back; the byte
comparison below stands in for it, as in § 9.2 of the performance record.

For `rho-df` and `rdfs-plus` the old envelope also carried a `rounds` member,
counted by running the step function again to the fixpoint; the command line
never printed it and now does not compute it. `closure --regime rdfs-plus` on
schema.org (17,949 triples): 214.7 s of CPU time before, 108.9 s after, the
same output.

`closure --regime owl-rl`, before and after (wall time, CPU time user+system,
peak resident set; output compared with `cmp`):

| Input lines | Closure triples | Output bytes | Before | After | Output |
|---:|---:|---:|---|---|---|
| 16,000 | 117,250 | 14,597,306 | 6.0 s, 5.2 s, 181 MB | 4.9 s, 4.8 s, 153 MB | identical |
| 32,000 | 250,490 | 30,281,632 | 12.9 s, 12.1 s, 457 MB | 10.8 s, 10.6 s, 369 MB | identical |
| 65,000 | 344,044 | 42,006,990 | 22.6 s, 21.4 s, 677 MB | 21.2 s, 20.9 s, 501 MB | identical |
| 130,404 | 638,420 | 72,698,863 | 48.8 s, 45.6 s, 1,352 MB | 43.6 s, 42.7 s, 1,352 MB | identical |

At `eab58d16` (issue 758): 1,269 MB at 16,000 lines, 2,470 MB at 32,000, more
than 6,037 MB on the whole file. After the repair the peak is that of the
closure computation: the output adds nothing measurable. 📊 QUDT: 1,352 MB,
under the 2 GB target. Under `prlimit --as=6000000000` the same command still
stops at about 1.2 GB resident (`INTERNAL PANIC: out of memory`): that is
https://github.com/danbri/factoidal/issues/759, the 1 GiB mimalloc arena
reservations, and the gate keeps it as its own row
(`qudt-closure-address-space`, expected failure).

Byte comparison, binary before against binary after, standard output,
standard error and exit status: the 459 `test:rdfXmlPremiseOntology`
documents of `third_party/testing/owl/all.rdf` under each of the four regimes
(`owl-rl`, `rdfs`, `rho-df`, `rdfs-plus`): 1,836 of 1,836 identical (1,832 exit
0, 4 exit 1 with the same text). The `merged.nt` of the ten ontologies of § 1:
the four regimes for the eight smaller ones, `owl-rl` and `rdfs` for the Cell
Ontology, `owl-rl` for QUDT: 35 of 35 identical. The four QUDT rungs above:
identical. Four `#guard` commands in `Wasm/Cli.lean` compare the stream with the
envelope, after its JSON round trip, for every regime on a graph with
inferences, an escaped literal and an upper-case language tag, check that the
inferred triples are in the text, and check the error path (a triple term,
which the RDF 1.1 round trip refuses).

### 10.2 Species check: where the time was

`l4owl-species --phases DOC.nt` (new) times each part of the readable
definition of `speciesViolations` (the specification's own functions, forced
between two clock reads through an `IO.Ref`), then the whole function, and
checks that the parts, joined in the definition's order, are the list the
whole returned. Before, ms:

| Part | 32,000 lines | 65,000 lines | 130,404 lines |
|---|---:|---:|---:|
| per-triple checks (`tripleViolations`) | 210 | 1,080 | 10,679 |
| simple roles (§ 11.2) | 3 | 11 | 4,061 |
| anonymous individuals (§ 11.2) | 24 | **27,512** | **225,036** |
| all other parts | 123 | 285 | 1,380 |
| sum of the parts | 360 | 28,888 | 241,156 |

**Causes.** (1) The anonymous-individual check counted the named links of
each blank node with a scan of the whole graph (`namedLinks`), and each scan
tested every triple's predicate against the list of declared object
properties: QUDT has 4,860 blank nodes in object property assertions,
130,404 triples and 100 object properties. The jump between 32,000 and 65,000
sorted lines is where the first of those blank nodes appear (1 and 1,308).
(2) The per-triple checks read (subject, predicate) pairs with scans of the
graph (`hasTripleSp`, `countSp`): every literal whose datatype is not built in
costs three scans (QUDT: 1,120 `rdf:HTML` literals), and every `rdf:first` and
`rdf:rest` triple two. (3) The simple-role check scanned the graph seven
times per restriction. (4) `DeclIndex` membership, `dedupStrs` and Table 5
were list scans.

**Repair** (`L4Factoidal/OWL/SyntaxDL.lean`, section "The species check with
indexes"). Three indexes built once per graph: `spIndexOf` (subject key and
predicate to the objects, in graph order), `DeclSets` (the `DeclIndex` lists
as hash sets) and `namedLinkCounts` (each key's named-link count), and
`dedupStrsFast`. Twins of the parts that read them (`table5RedundantI`,
`tripleViolationsI`, `punningViolationsS`, `simpleRoleViolationsI`,
`anonymousIndividualViolationsI`, `graphBodyViolationsI`). Proved, each equal
to its readable definition: `spIndexOf_getD`, `hasTripleSpI_eq`,
`findObjectSpI_eq`, `countSpI_eq`, `hasTypeSpI_eq`, `collectionMembersI_eq`,
`dedupStrsFast_eq`, `namedLinkCounts_getD`, `tripleViolationsI_eq`,
`punningViolationsS_eq`, `simpleRoleViolationsI_eq`,
`anonymousIndividualViolationsI_eq`, `graphBodyViolationsI_eq`,
`speciesViolations_eq_fast`. Five `@[csimp]` theorems make the compiler emit
the twins for `graphBodyViolations`, `speciesViolations`, `speciesIsDl`,
`speciesViolationsFunctional` and `speciesIsDlFunctional`; the readable
definitions and their 101 guards do not change. Thirteen new guards, before
the `csimp` theorems, compare the twin with the definition on a leaf, a tree
without a leaf, a cycle and an undeclared predicate, and check `dedupStrsFast`.

`l4owl-species`, before and after (wall time, CPU time user, peak resident
set; the JSON printed compared with `cmp`):

| Input lines | Violations | Before | After | Output |
|---:|---:|---|---|---|
| 16,000 | 1,337 | 0.57 s, 0.39 s, 100 MB | 0.37 s, 0.24 s, 100 MB | identical |
| 32,000 | 1,838 | 1.10 s, 0.77 s, 192 MB | 0.96 s, 0.51 s, 192 MB | identical |
| 65,000 | 2,527 | 31.2 s CPU (issue 766) | 2.27 s, 1.33 s, 359 MB | identical |
| 130,404 | 7,334 | 253.4 s CPU, 323 s wall (issue 766) | 3.84 s, 2.27 s, 648 MB | parts equal whole |

On the whole file and on 65,000 lines the `--phases` run of the new binary
computed the readable definition part by part (242.6 s and 30.0 s) and the
twin (0.94 s and 0.48 s), and the two lists are equal
(`parts-equal-whole=true`).

Scaling (`tests/stack/lean_scaling.py`, new rows, minimum of 3 runs):
`owl-species`, a generated OWL 2 DL document of 2,000 and 8,000 units (16
triples each: a restriction on a blank node, a union over an RDF list, an
individual with a language-tagged label, a data value and an object property
assertion to a blank node): before, 8,000 units gave no result in 120 s;
after, 0.414 s and 2.279 s, ratio 5.5 for 4 times the input (bound 9).

⚠️ One part stays quadratic: `componentsOf`, which merges the components of
the anonymous individual graph in a list, costs time proportional to the
square of the number of object property assertions between two blank nodes
(8,000 pairs 1.09 s, 16,000 3.58 s, 32,000 14.79 s). QUDT has none.
https://github.com/danbri/factoidal/issues/812; scaling row
`owl-species-bnode-edges`, expected failure (8,000 against 32,000 pairs:
0.882 s and 14.374 s, ratio 16.3).

### 10.3 The same work on other tools

Same machine, same `qudt.nt`, one run each, the Lean rows from § 10.1 and § 10.2.
No tool was vendored: Apache Jena 5.1.0 is the binary distribution from
archive.apache.org (SHA-512 checked against the published one), owlrl 7.1.4
with rdflib 7.6.0 and owlready2 0.51 (HermiT 1.3.8 with the OWL API 3.4) were
installed with `pip install --target` into a scratch directory; OpenJDK
21.0.12. The two Java programs are 40 lines each: `JenaClosure` reads the
N-Triples, builds Jena's inference model and writes every statement of it;
`DlProfile` loads the document with the OWL API and runs `OWL2DLProfile`.

| Tool | Task | Result | Wall | CPU | Peak resident set |
|---|---|---|---:|---:|---:|
| Lean `l4factoidal closure --regime owl-rl` | OWL 2 RL/RDF closure | 638,420 triples | 43.6 s | 42.7 s | 1,352 MB |
| owlrl 7.1.4 (rdflib 7.6.0), `DeductiveClosure(OWLRL_Semantics)` | OWL 2 RL/RDF closure | no result in 600 s | 600 s | — | 544 MB sampled |
| owlrl 7.1.4, first 16,000 lines | OWL 2 RL/RDF closure | 122,973 triples (Lean: 117,250 in 4.9 s) | 59.7 s | 58.8 s | 109 MB |
| Jena 5.1.0 `ReasonerRegistry.getOWLMicroReasoner()`, `java -Xmx5g` | OWL Micro rules, every statement written | no result in 600 s (2,806,127 statements written when stopped) | 600 s | — | 5,560 MB sampled |
| Lean `l4owl-species` | OWL 2 DL against Full (§ 10.2) | Full, 7,334 violations | 3.84 s | 2.27 s | 648 MB |
| OWL API 3.4 (in HermiT.jar 1.3.8), `OWL2DLProfile` | OWL 2 DL profile | not in DL, 32,820 violations; load 5.04 s, check 1.01 s | 6.35 s | 9.42 s | 371 MB |

The closures are not the same set: owlrl gives 122,973 triples on the first
16,000 lines where Lean gives 117,250 (the axiomatic and datatype triples each
adds differ; § 6 notes the same for F\*), and Jena's OWL Micro is a different
rule set. The violation counts are not comparable either: the OWL API counts
one violation per axiom and entity (`IllegalPunning` 15,933,
`DatatypeIRIAlsoUsedAsClassIRI` 14,035, `UseOfUnknownDatatype` 1,118, ...),
the Lean checker one per triple or per component. Both checkers say QUDT
3.4.0 is not OWL 2 DL. The OWL API 3.4 Turtle parser does not read the
original `.ttl` (parse error at line 14,977), so the OWL API rows read
`qudt.nt`.

### 10.4 Gates

Branch `claude/wt-qudt-owl`; load average 4 to 27 (two other agents building).

- 📊 `tests/stack/owl_real_gate.sh`: 7 pass, 0 fail, 5 expected-fail (out of
  12); 1 skipped (the F\* binary is not installed in the worktree). Before:
  5 pass, 0 fail, 7 expected-fail. `qudt-closure` passes (1,352 MB, bound
  2,000 MB, under the resident-set watchdog) and `qudt-species` passes (11.6 s
  at load 27, bound 60 s); both left the expected-failure table. New row
  `qudt-closure-address-space`, expected failure naming issue 759. Every other
  row unchanged.
- 📊 OWL scoreboard (`tools/lean-scoreboard.sh --only l4owl-probe`), compared
  with the coordinator's logs of `main` after the timing lines are removed: 0
  lines missing in each of the 10 logs; species 488 pass, 0 fail, 1
  local-override (out of 489). In the first run the `rdf-based` log had 4
  lines more: `CAP` notes for WebOnt-miscellaneous-001, -002 and -011, whose
  closure ran into the probe's wall-clock cap (`closureIO ... (t1 + capMs)`)
  at load 27. Run again on the binary of the final full build at load 5 to
  10, the `species` and `rdf-based` logs are identical to `main`'s (0 lines
  missing, 0 added).
- 📊 `tests/stack/lean_scaling.sh`: 22 pass, 1 fail, 2 expected-fail (out of
  25). New rows: `owl-species` passes (ratio 5.0 to 7.9 for 4 times the input
  at load 4 to 27), `owl-species-bnode-edges` is an expected failure
  (https://github.com/danbri/factoidal/issues/812). The 1 fail is
  `rdfc-bnode-collide` (issue 751), an expected failure on this branch that
  passed by chance at load 27 (ratio 8.8, bound 9); `main` has its repair and
  the row is an assertion there.
- native-smoke 351 pass, 0 fail (out of 351); cli-smoke 83 pass, 0 fail (out
  of 83); `tools/lean-tail-recursion-audit.py --gate` passes (the collection
  walk of the twins is a loop); `tools/lean-hygiene-audit.py` clean.
- One full `lake build`: 1,621 jobs, exit 0.
- wasm rebuilt (`Wasm/build-wasm.sh`; 11,079,212 bytes full, 5,985,002 core;
  every committed copy agrees); `npm test` in `npm/factoidal`: 413 pass, 0
  fail, 1 skipped (out of 414; the skipped test needs the `esbuild`
  devDependency, which is not installed in the worktree).


## 11. Semi-naive OWL 2 RL closure (2026-10-13, issue 756 item 2)

Issue: https://github.com/danbri/factoidal/issues/756, item 2 (semi-naive OWL
RL), and https://github.com/danbri/factoidal/issues/819 (schema.org
`owl-consistent`). OKR batch 1 (https://github.com/danbri/factoidal/issues/768),
owner's goal of 2026-10-12, verbatim: "/goal OKRs addresses successfully
especially perf and scaling should approach SOTA". Owner, 2026-10-10,
verbatim: "Can we extend this approach to semi-naïve OWL/RDFS evaluation
eventually, but the proof target would change. Instead of proving that both
implementations return identical results after every round, prove that they
compute equivalent saturated closures". Branch `claude/wt-owlrl-seminaive`
of `danbri/factoidal-core`, base `93ad93b9` (`main` `c8836eab` with
`claude/wt-sota-table`).

### 11.1 Result

- ✅ The OWL 2 RL closure runs semi-naive rounds over the index
  (`OWL/RLClosureIndexed.lean` Section 11). Proved: the semi-naive loop
  returns the SAME LIST as the naive loop at every fuel
  (`indexedClosureSN_eq`), so it takes the same rounds, holds the same set
  after each round, and prints the triples in today's order. One `csimp`
  theorem makes every compiled caller of `closure` and `closureFix` (the
  `closure` verb, `owl-consistent`, `owl-entails`, the SPARQL entailment
  regimes, the wasm ops) run it; the OWL probe's own round loop runs it too.
- ✅ The four obligations of issue 756 for this closure
  (`OWL/RLSemiNaiveTheorems.lean`, section 11.4). `#print axioms`:
  `propext`, `Classical.choice`, `Quot.sound` only.
- 🔴 Open, as before this change: fuel adequacy (that `closureFuelBound g`
  rounds and `listFuel` are enough). Expected failure
  `L4Factoidal.OWL.RL.closureFix_saturated` in
  `Harness/ProofObligations.lean`. The semi-naive loop needs no run-time check:
  it takes the naive loop's rounds by proof.

### 11.2 Method

`l4owl-rl-profile FILE.nt [--rows] [--sn]` (new,
`formal/lean4/Harness/OwlRlProfile.lean`) reads one N-Triples file and runs
the closure round by round: the naive indexed rounds (`stepConclusionsS`, then
`Index.insertAll`, as `closureI`), or with `--sn` the semi-naive rounds
(`stepConclusionsSN`). For each round it prints the input size, the delta (the
triples the previous round added), the conclusions emitted before
deduplication, the new triples, and the time of the conclusion list, of the
insertion and (semi-naive) of the delta's index. With `--rows` it also
evaluates each of the 74 rows on its own over every driving triple of the
round and prints, per row and round, the conclusions emitted, how many are not
in the round's input, and the time. Each timed value is consumed by a counter
between the two clock reads (skills/measuring-inference §§ 9 and 11). The row
pass is a separate evaluation; its times add up to about the round time plus
the cost of iterating the input once per row. It holds no OWL logic.

Inputs: the `merged.nt` of each ontology, written by `tools/owl-real-bench.py`
(the Lean parser's N-Triples of the source files, RDF merge). Machine: the
same container as § 1; 4 CPUs shared with two other agents. ⚠️ The load
average was 8 to 50 during these runs (two other agents built wasm modules
with many parallel jobs); every table names the load of its run, wall times
are inflated by it, and the CPU-time columns are the better comparison.

### 11.3 Before: where the naive closure spent its rounds

Naive indexed closure (`closureI`, the closure before this change), one run of
`l4owl-rl-profile` per ontology, load average 15 (QUDT 21). "Emitted" counts
conclusions before deduplication; "New" is what the round added; "ms" is
conclusion list plus insertion, wall clock in the process. The semi-naive
columns are section 11.5; the round structure is the same by proof
(`indexedClosureSN_eq`), and the script checked that input, delta and new
agree in every round.

Cell Ontology:

| Round | Input | Delta | New | Emitted, naive | ms, naive | Emitted, semi-naive | ms, semi-naive |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 78,833 | 78,833 | 34,379 | 221,083 | 1,379 | 221,083 | 1,466 |
| 2 | 113,212 | 34,379 | 21,855 | 736,445 | 2,242 | 515,802 | 2,994 |
| 3 | 135,067 | 21,855 | 23,425 | 1,078,005 | 2,565 | 347,596 | 2,390 |
| 4 | 158,492 | 23,425 | 4,948 | 1,411,247 | 3,792 | 340,347 | 2,057 |
| 5 | 163,440 | 4,948 | 4 | 1,480,747 | 3,561 | 76,611 | 1,324 |
| 6 | 163,444 | 4 | 0 | 1,480,787 | 3,387 | 7,151 | 1,330 |
| all | | | | 6,408,314 | 16,927 | 1,508,590 | 11,561 |

RO:

| Round | Input | Delta | New | Emitted, naive | ms, naive | Emitted, semi-naive | ms, semi-naive |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 11,703 | 11,703 | 9,282 | 37,726 | 502 | 37,726 | 1,184 |
| 2 | 20,985 | 9,282 | 10,124 | 143,347 | 2,664 | 105,726 | 694 |
| 3 | 31,109 | 10,124 | 10,451 | 284,938 | 4,595 | 142,148 | 750 |
| 4 | 41,560 | 10,451 | 1,090 | 414,224 | 4,972 | 130,181 | 1,236 |
| 5 | 42,650 | 1,090 | 86 | 425,924 | 6,976 | 12,807 | 1,267 |
| 6 | 42,736 | 86 | 0 | 426,688 | 4,956 | 1,871 | 1,796 |
| all | | | | 1,732,847 | 24,664 | 430,459 | 6,928 |

Wine and food:

| Round | Input | Delta | New | Emitted, naive | ms, naive | Emitted, semi-naive | ms, semi-naive |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2,709 | 2,709 | 4,215 | 11,762 | 102 | 11,762 | 97 |
| 2 | 6,924 | 4,215 | 6,468 | 67,216 | 510 | 57,211 | 395 |
| 3 | 13,392 | 6,468 | 9,705 | 227,170 | 1,052 | 170,973 | 895 |
| 4 | 23,097 | 9,705 | 4,816 | 516,657 | 1,687 | 324,211 | 1,475 |
| 5 | 27,913 | 4,816 | 935 | 584,438 | 2,687 | 113,230 | 654 |
| 6 | 28,848 | 935 | 10 | 596,150 | 3,134 | 55,408 | 706 |
| 7 | 28,858 | 10 | 0 | 596,623 | 3,099 | 29,769 | 1,043 |
| all | | | | 2,600,016 | 12,272 | 762,564 | 5,266 |

schema.org:

| Round | Input | Delta | New | Emitted, naive | ms, naive | Emitted, semi-naive | ms, semi-naive |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 17,949 | 17,949 | 8,602 | 53,025 | 125 | 53,025 | 146 |
| 2 | 26,551 | 8,602 | 14,635 | 184,628 | 357 | 131,629 | 421 |
| 3 | 41,186 | 14,635 | 17,636 | 332,960 | 727 | 148,766 | 755 |
| 4 | 58,822 | 17,636 | 1,948 | 607,327 | 1,143 | 275,267 | 975 |
| 5 | 60,770 | 1,948 | 0 | 639,942 | 1,079 | 35,833 | 276 |
| all | | | | 1,817,882 | 3,431 | 644,520 | 2,572 |

QUDT:

| Round | Input | Delta | New | Emitted, naive | ms, naive | Emitted, semi-naive | ms, semi-naive |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 130,404 | 130,404 | 236,724 | 605,096 | 3,672 | 605,096 | 3,185 |
| 2 | 367,128 | 236,724 | 173,774 | 4,805,316 | 15,277 | 4,201,235 | 15,413 |
| 3 | 540,902 | 173,774 | 95,799 | 7,310,337 | 24,086 | 2,551,416 | 9,611 |
| 4 | 636,701 | 95,799 | 1,719 | 10,144,628 | 32,585 | 2,885,000 | 10,112 |
| 5 | 638,420 | 1,719 | 0 | 10,168,323 | 28,919 | 116,866 | 2,896 |
| all | | | | 33,033,700 | 104,539 | 10,359,613 | 41,217 |

Per rule family, each row evaluated on its own over every driving triple of
every round (the profile's `--rows` pass; the row times include one pass over
the input per row, so they add up to more than the rounds above):

Cell Ontology, all rounds, each row evaluated on its own (ms):

| Family | Emitted, naive | Emitted and not in the round's input, naive | ms, naive | ms, semi-naive |
|---|---:|---:|---:|---:|
| scm (Table 9) | 1,957,353 | 148,466 | 8,995 | 7,134 |
| eq (Table 4) | 4,327,971 | 222,453 | 7,708 | 1,882 |
| [ext] rows | 48 | 8 | 3,382 | 2,324 |
| prp (Table 5) | 60,813 | 13,514 | 2,351 | 2,047 |
| cls (Table 6) | 0 | 0 | 2,082 | 1,704 |
| cax (Table 7) | 61,973 | 4,769 | 929 | 676 |

Costliest rows, naive: scmSco 2,561 ms (1,794,141 emitted, 130,519 not in the input); eqRepP 2,284 ms (717,369 emitted, 0 not in the input); scmSvf1 1,722 ms (8,641 emitted, 1,683 not in the input); eqRepS 1,543 ms (730,016 emitted, 0 not in the input).
Costliest rows, semi-naive: scmSvf1 2,031 ms (8,641 emitted); scmSvf2 1,320 ms (4,455 emitted); scmEqc2 841 ms (21,652 emitted); scmSco 533 ms (486,763 emitted).

RO, all rounds, each row evaluated on its own (ms):

| Family | Emitted, naive | Emitted and not in the round's input, naive | ms, naive | ms, semi-naive |
|---|---:|---:|---:|---:|
| prp (Table 5) | 37,774 | 2,932 | 18,993 | 3,510 |
| [ext] rows | 32,858 | 3,140 | 3,942 | 2,055 |
| scm (Table 9) | 561,928 | 53,624 | 1,516 | 792 |
| eq (Table 4) | 1,067,481 | 38,381 | 1,400 | 311 |
| cls (Table 6) | 120 | 24 | 1,137 | 767 |
| cax (Table 7) | 18,224 | 1,375 | 121 | 86 |

Costliest rows, naive: prpSpo2 18,629 ms (26,600 emitted, 1,580 not in the input); inverseOfDomRngFlip 2,769 ms (6,487 emitted, 183 not in the input); clsInt1 705 ms (0 emitted, 0 not in the input); chainToTrans 642 ms (0 emitted, 0 not in the input).
Costliest rows, semi-naive: prpSpo2 3,151 ms (5,648 emitted); chainToTrans 1,150 ms (0 emitted); inverseOfDomRngFlip 449 ms (1,676 emitted); clsInt1 295 ms (0 emitted).

Wine and food, all rounds, each row evaluated on its own (ms):

| Family | Emitted, naive | Emitted and not in the round's input, naive | ms, naive | ms, semi-naive |
|---|---:|---:|---:|---:|
| cls (Table 6) | 330,021 | 39,949 | 6,917 | 3,152 |
| [ext] rows | 71,886 | 9,539 | 2,247 | 2,199 |
| scm (Table 9) | 484,137 | 12,053 | 967 | 800 |
| eq (Table 4) | 803,272 | 9,270 | 874 | 141 |
| cax (Table 7) | 793,167 | 4,520 | 524 | 99 |
| prp (Table 5) | 117,351 | 4,336 | 304 | 159 |

Costliest rows, naive: clsInt1 6,290 ms (262,016 emitted, 36,636 not in the input); ifpDiffToDiff 1,216 ms (0 emitted, 0 not in the input); fpDiffToDiff 543 ms (16,211 emitted, 1,888 not in the input); clsInt2 235 ms (3,277 emitted, 192 not in the input).
Costliest rows, semi-naive: clsInt1 2,669 ms (113,933 emitted); ifpDiffToDiff 1,277 ms (0 emitted); fpDiffToDiff 661 ms (16,211 emitted); clsInt2 231 ms (3,277 emitted).

schema.org, all rounds, each row evaluated on its own (ms):

| Family | Emitted, naive | Emitted and not in the round's input, naive | ms, naive | ms, semi-naive |
|---|---:|---:|---:|---:|
| eq (Table 4) | 1,125,036 | 64,820 | 1,364 | 394 |
| prp (Table 5) | 257,856 | 12,344 | 755 | 388 |
| cax (Table 7) | 279,995 | 17,942 | 547 | 148 |
| scm (Table 9) | 134,723 | 14,098 | 542 | 597 |
| [ext] rows | 20,142 | 6,710 | 289 | 427 |
| cls (Table 6) | 0 | 0 | 189 | 560 |

Costliest rows, naive: eqRepP 382 ms (178,811 emitted, 0 not in the input); caxSco 292 ms (174,014 emitted, 15,239 not in the input); eqRepO 245 ms (155,023 emitted, 0 not in the input); eqRepS 240 ms (180,606 emitted, 0 not in the input).
Costliest rows, semi-naive: clsMaxc2 342 ms (0 emitted); scmSco 76 ms (32,134 emitted); eqRepS 74 ms (60,770 emitted); eqRepO 70 ms (51,444 emitted).

What the tables say:

- Most naive work re-derives what the graph holds. Over all rounds the naive
  closure emitted 6.4 million conclusions on the Cell Ontology for 84,611
  added triples, 33.0 million on QUDT for 508,016. In the last two rounds of
  every ontology it emitted as much as in any round and added almost nothing
  (RO rounds 4 to 6: 1.27 million conclusions, 1,176 new triples).
- Two rows cost time without emitting much: prp-spo2 on RO (26,600
  conclusions, 1,580 new, three quarters of the row time) and cls-int1 on
  wine (6.3 s). Both walk every subject of the graph for each
  `owl:propertyChainAxiom` (172 in RO) or `owl:intersectionOf` (80 in wine)
  in every round. A delta term over their premises alone would not remove the
  walk; a test that the delta cannot change the row's output does (section
  11.4).
- eq-rep-s/p/o re-emit every triple once per round through the reflexive
  `owl:sameAs` of its subject, predicate or object (Cell Ontology: 730,016,
  717,369 and 542,006 conclusions, none new).

### 11.4 The semi-naive form and its theorems

A naive round evaluates each of the 74 rows of `conclusionsListS` at each
driving triple `d` of its input `S`. When `S` is the output of the round over
`P` (so `S = P ++ D`, `D` the delta that round appended), a row at `d ∈ P` can
conclude a triple outside `S` only through an instance that reads a triple of
`D`: an instance with every premise in `P` was concluded by the round over `P`,
which put it into `S`. `stepConclusionsSN` evaluates every row at each
`d ∈ D` and, at each `d ∈ P`, the row's DELTA TERM (`RowSpec.delta`):

| Kind | Rows | Delta term at `d ∈ P` |
|---|---|---|
| reads only `d` (`RowSpec.indep`) | 13: eq-ref (3), eq-sym, scm-cls, scm-eqc1, scm-eqp1, scm-op, scm-dp, eq-diff-sym, the XSD axioms, the disjointness complement witness, the min-cardinality witness | nothing |
| one lookup, one graph scan or one membership test (`RowSpec.additive`) | 24: eq-trans, eq-rep-s/p/o, prp-dom, prp-rng, prp-symp, prp-spo1, prp-eqp1/2, prp-inv1/2, cax-sco, cax-eqc1/2, scm-sco, scm-spo, scm-dom1/2, scm-rng1/2, prp-rfl, the datatype range intersection, the inverse domain and range flip | the row over the index of `D` alone |
| collection rows with a test (`prpSpo2Delta`, `clsInt1Delta`) | prp-spo2, cls-int1 | nothing when `D` has no `rdf:first`/`rdf:rest` triple, the collection walk reads the same at the fuel of `P` as at the fuel of `S`, and `D` has no edge on a chain property (prp-spo2) or no typing in a member class (cls-int1); else the row in full |
| the others (`RowSpec.full`) | 35: two or more lookups, collection walks, the six rows whose second premise is a membership test | the row in full, as the naive round |

Each kind carries one obligation, `RowSpec.Ok`: on a graph `P ++ D`, after
removing the triples the row concludes from `P` alone, the full row and the
delta term are the same list. `rowTable_ok` proves it for all 74 rows (the
additive rows by one tactic over the lookups of `P ++ D`; `prpSpo2_ok` and
`clsInt1_ok` with the lemmas that the walk, the chain and the typing test read
the same over `P ++ D` as over `P`).

A fifth kind, `RowSpec.skip` (scm-svf1/2, scm-avf1/2, scm-hv: nothing when the
delta has no triple on the row's fixed predicates), is proved
(`RowSpec.skip_ok`) and NOT used: with it, the Cell Ontology's closure was
slower (section 11.5).

The emitted list keeps the naive round's order (driving triples in graph
order, rows in `conclusionsListS` order) and differs from the naive round's
list only by triples already in `S`; `addAll S` drops exactly those
(`addAll_filter_of_subset`). So one semi-naive round is one naive round as a
list (`addAll_stepConclusionsSN`), given the round invariant `RoundOk` (`S`
starts with `P`, and holds every conclusion of a driving triple of `P` over
`P`), which every naive round establishes for the next (`RoundOk.next`).

At an old driving triple, only rows whose guard is the triple's predicate
can emit (`rowTable_guard`); a hash map from guard predicate to rows
(`dispatchMap`, proved to list exactly those rows: `dispatchMap_getD`,
`oldBlockFast_eq`) replaces 74 guard tests by one lookup.

| Theorem (`OWL/RLClosureIndexed.lean`, `OWL/RLSemiNaiveTheorems.lean`) | Statement |
|---|---|
| `indexedClosureSN_eq` | `indexedClosureSN g fuel = closure g fuel` (lists, every fuel; no hypothesis) |
| `addAll_stepConclusionsSN` | one semi-naive round over `P ++ D` is `step (P ++ D)`, under `RoundOk` |
| `rowTable_ok`, `rowTable_guard`, `oldBlockFast_eq` | the 74 delta terms, the guards, the dispatch |
| 1. `indexedClosureSN_sound` | `t ∈ indexedClosureSN g fuel → Derives g t` (no hypothesis) |
| 2. `stepSNI_saturated`, `stepSNI_closed` | a semi-naive round that adds nothing (empty delta) leaves `S` closed: `step S = S`, every conclusion of every row in `S` |
| 2'. `indexedClosureSN_saturated_or_underfueled` | the result is saturated, or the loop grew the graph by one triple per unit of fuel |
| 3. `indexedClosureSN_complete` | saturated and `ListFuelAdequate` imply `Derives g t → t ∈ indexedClosureSN g fuel` (`complete_of_saturated`: `g ⊆ S`, `S` closed imply `Derives ⊆ S`) |
| 1 + 3. `mem_indexedClosureSN_iff` | `t ∈ C g ↔ Derives g t` under the hypotheses of 3 |
| 4. `mem_indexedClosureSN_iff_closure`, `indexedClosureSN_eq_indexedClosure` | naive and semi-naive have the same members (and the same list) |

Anti-pattern 29 check: no theorem has its conclusion among its hypotheses.
The two hypotheses of 3 (saturation, `ListFuelAdequate`) are those of the
naive loop's T4; they are the open fuel obligation, and
`closure_saturated_or_underfueled` (2') says when saturation holds.

Guards (`OWL/RLTests.lean`): the semi-naive loop equals the scanning loop as a
list on 25 fixtures, three of them built so that the second round needs a
delta term at an OLD driving triple (prp-symp at an old symmetric-property
typing, prp-spo2 at an old chain axiom, cls-int1 at an old intersection).
Teeth: `closureNoOld`, the same loop with no term at old driving triples,
misses the derived triple on each of the three; and a semi-naive round emits
fewer conclusions than the naive round on the second round of a fixture.

### 11.5 After: the semi-naive rounds, and the commands beside HermiT and Jena

The round tables of section 11.3 hold both closures side by side (same runs of
the profile; the semi-naive column is the final binary). Over all rounds the
semi-naive closure emits 0.24 (Cell Ontology), 0.25 (RO), 0.29 (wine), 0.35
(schema.org) and 0.31 (QUDT) of the naive conclusions.

The commands, base binary (`93ad93b9`, naive indexed closure) against the
final binary of this branch, two runs each in alternation, CPU time user
(the smaller of the two runs), peak resident set; output of `closure`
compared with `cmp` and verdict of `owl-consistent` compared, load average
11 to 21:

| Ontology | Closure, base | Closure, semi-naive | Ratio | `owl-consistent`, base | `owl-consistent`, semi-naive | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| SKOS | 0.03 s, 22 MB | 0.01 s, 24 MB | — | 0.03 s, 23 MB | 0.02 s, 24 MB | — |
| FOAF | 0.05 s, 24 MB | 0.05 s, 24 MB | — | 0.09 s, 24 MB | 0.04 s, 24 MB | — |
| PROV-O | 0.11 s, 26 MB | 0.07 s, 26 MB | 1.6 | 0.17 s, 25 MB | 0.06 s, 26 MB | 2.8 |
| BFO | 0.15 s, 26 MB | 0.09 s, 26 MB | 1.7 | 0.19 s, 26 MB | 0.12 s, 26 MB | 1.6 |
| Pizza | 0.40 s, 42 MB | 0.32 s, 33 MB | 1.2 | 0.73 s, 42 MB | 0.64 s, 33 MB | 1.1 |
| Wine and food | 6.58 s, 77 MB | 3.13 s, 55 MB | 2.1 | 17.57 s, 79 MB | 14.79 s, 56 MB | 1.2 |
| RO | 15.89 s, 76 MB | 2.75 s, 77 MB | 5.8 | 16.40 s, 76 MB | 4.07 s, 77 MB | 4.0 |
| schema.org | 2.58 s, 103 MB | 1.64 s, 105 MB | 1.6 | 3.52 s, 103 MB | 2.79 s, 105 MB | 1.3 |
| Cell Ontology | 11.65 s, 446 MB | 7.44 s, 447 MB | 1.6 | 14.67 s, 446 MB | 10.24 s, 447 MB | 1.4 |
| QUDT | 45.78 s, 1,350 MB | 22.55 s, 659 MB | 2.0 | 55.01 s, 1,351 MB | 29.97 s, 659 MB | 1.8 |

Beside the reference engines of the state-of-the-art record
(`2026-10-12-sota-reference.md`, same machine, load 2 to 6; those engines were
not run again here): Jena 6.2.0 OWL Micro, a different rule set, closes RO in
8.6 s wall (16.0 s CPU) and the Cell Ontology in 8.6 s (19.2 s CPU); HermiT
1.3.8 decides the consistency of RO in 14.6 s wall (22.0 s CPU), the Cell
Ontology in 3.4 s (6.0 s CPU), schema.org in 1.4 s (2.6 s CPU) and wine in
2.1 s (3.7 s CPU).

📊 What changed against HermiT: RO, consistency, Lean 4.1 s CPU at load 13
against HermiT 22.0 s CPU; the Cell Ontology, Lean 10.2 s CPU at load 11
against HermiT 6.0 s CPU (1.7 times; 2.4 times before); schema.org, Lean 2.8
s CPU against 2.6 s CPU; wine, Lean 14.8 s CPU against 3.7 s CPU (the
refuter's search is most of it, section 9.4). These Lean numbers are at load
11 to 21, the reference numbers at load 2 to 6: the gap is smaller than the
ratio shows.

Before the five scm rows went back to full evaluation (section 11.4), the
Cell Ontology's semi-naive round 3 took 2.5 s against 0.5 s without the skip
terms (the test reversed the delta's `rdfs:subClassOf` bucket once per old
`owl:someValuesFrom` triple); the measurement made that decision.

Memory: the QUDT closure peaks at 659 MB against 1,382 MB before; wine
at 55 MB against 78 MB. The other ontologies hold their peaks (the index and
the output dominate).

### 11.6 eq-rep: the delta stays small

eq-rep-s/p/o are additive rows: at an old `owl:sameAs` driving triple they
read only the delta's index. Over all rounds each emits about one conclusion
per closure triple (each triple once, through the reflexive `owl:sameAs` of
its subject, predicate or object when that triple first drives the row), where
the naive rows emit one per closure triple per round:

| Ontology | eq-rep-s, naive | eq-rep-s, semi-naive | eq-rep-p, naive | eq-rep-p, semi-naive | eq-rep-o, naive | eq-rep-o, semi-naive | Closure triples |
|---|---:|---:|---:|---:|---:|---:|---:|
| Cell Ontology | 730,016 | 163,444 | 717,369 | 163,444 | 542,006 | 125,840 | 163,444 |
| RO | 176,135 | 42,736 | 174,408 | 42,736 | 148,517 | 36,653 | 42,736 |
| Wine and food | 130,136 | 29,116 | 129,015 | 28,858 | 135,138 | 30,070 | 28,858 |
| schema.org | 180,606 | 60,770 | 178,811 | 60,770 | 155,023 | 51,444 | 60,770 |
| QUDT | not measured | 638,420 | not measured | 638,420 | not measured | 569,421 | 638,420 |

### 11.7 schema.org `owl-consistent` (https://github.com/danbri/factoidal/issues/819)

Re-measured on this base with `l4refute-profile` (the phases of
`owl-consistent`), two runs each, load average 14, wall clock of each phase:

| Phase | Base (naive closure) | This branch |
|---|---:|---:|
| OWL 2 RL closure | 5.62 s, 5.49 s | 3.11 s, 3.05 s |
| TBox read (`collectAxioms`) | 0.93 s, 0.78 s | 0.91 s, 0.88 s |
| initial state | 1.30 s, 1.13 s | 1.23 s, 1.29 s |
| counting rung, immediate clash, TBox index | 0.14 s, 0.11 s | 0.12 s, 0.13 s |
| search | 0.65 s, 0.60 s | 0.59 s, 0.79 s |
| whole command, CPU time | 3.97 s, 3.73 s | 2.91 s, 2.80 s |

The closure holds the time, before and after (about half of the command's wall
time; its 60,770 triples are what the refuter reads). The 43.8 s of the issue
was the range axioms on every node (section 9.3, issue 760): on this base the
command takes 3.5 to 3.8 s of CPU time before this change and 2.8 to 2.9 s
after, against HermiT's 2.6 s CPU (1.4 s wall). The expected-failure row of
`tests/perf/sota_gate.sh` (Lean more than 10 times HermiT) reported UNEXPECTED
PASS on this base and leaves the table.

### 11.8 What is left

- 🔴 Fuel adequacy, for the naive and the semi-naive loop alike (they are
  the same list): `closureFuelBound g` rounds and `listFuel` are not proved
  enough. Expected failure `L4Factoidal.OWL.RL.closureFix_saturated`
  (`Harness/ProofObligations.lean`), https://github.com/danbri/factoidal/issues/756.
- ⚠️ 35 rows are evaluated in full at old driving triples (two or more
  lookups, collection walks, the six rows whose second premise is a
  membership test). Their delta terms would need one proof each, of the kind
  `prpSpo2_ok` has. The measured cost after this change (section 11.5) names
  which of them matter: on the Cell Ontology scm-svf1/2 and the membership
  row scm-eqc2; on wine cls-int1 (its test fails in most rounds, because
  most rounds type an individual in a member class), ifp-diff and fp-diff.
- ⚠️ The delta terms of prp-spo2 and cls-int1 are all-or-nothing per driving
  triple: when the delta holds an edge on a chain property, the chain axiom
  is evaluated in full (every subject of the graph). An instance-level term
  in the naive order needs, for each subject, its first position in the
  graph; the index does not keep positions.
- ⚠️ prp-key is evaluated in full at old driving triples; no delta term over
  list positions was written for it. None of the five ontologies has an
  `owl:hasKey` axiom, and the row costs 6 ms (wine) to 359 ms (Cell
  Ontology) over all semi-naive rounds of the profile.
- ⚠️ The skip terms of scm-svf1/2, scm-avf1/2 and scm-hv (`RowSpec.skip`,
  proved) wait for a store that answers "does the delta hold a triple with
  predicate p" without building the list of those triples; the test that
  builds it cost more than it saved (section 11.5).
- ⚠️ `listFuel s.graph` (the fuel of every collection walk) is
  `List.length` of the graph, and prp-spo2's test and the chain-to-transitive
  row compute it once per chain axiom per round. On RO's late rounds that is
  about 0.5 s per round (172 chain axioms, 42,736 triples), most of what is
  left of those rows (`chainToTrans` 1,150 ms over all rounds, section 11.3).
  A fuel field on `Store`, set once per round, removes it; not done here.
- ⚠️ The order of the output is the naive order by proof. A semi-naive form
  that joins from the delta (the textbook form, n terms for a rule of n
  premises) finds the same set in another order; it would need a sort with
  its own proof, or a measured order. This form keeps the naive order and
  pays for it by visiting every old driving triple once per round (one hash
  lookup each, through `dispatchMap`).

### 11.9 Gates

Final binary of the branch (full `lake build` after the last Lean edit: 1,637
jobs, exit 0). Load average 11 to 50 through the gates (two other agents
built wasm modules); timing gates were read with that in mind.

- 📊 OWL scoreboard (`tools/lean-scoreboard.sh --only
  l4owl-probe,l4rdf-semantics,l4rdfs-semi`), base binaries against the final
  ones: 81 of 81 table rows identical (pass, fail, other and total of each
  row); 11 of 12 logs identical with the timing fields removed, failing ids
  included. The `rdf-based` log differs in 5 lines: the base run printed
  `CAP ... the closure budget ran out` for four units (WebOnt-miscellaneous-001
  and -002, consistency; -011, entailment and consistency) and the final run
  none (`cap_hits` 4 to 0, `rule_triples` 53,515 to 53,555). That budget is a
  wall-clock deadline of 3,000 ms per closure (`--refute-ms 3000`): the naive
  closures of those four units ran past it, the semi-naive ones finish within
  it. Every other line, the verdict lines included, is the same
- 📊 rdf-mt rows: `l4rdf-semantics` 29 pass, 0 fail (out of 29) and
  `l4rdfs-semi` 6 pass, 0 fail (out of 6), before and after, logs identical.
- Byte comparison, base binary against final, standard output, standard
  error and exit status of `l4factoidal closure`: the 459
  `test:rdfXmlPremiseOntology` documents of `third_party/testing/owl/all.rdf`
  under the four regimes (`owl-rl`, `rdfs`, `rho-df`, `rdfs-plus`): 1,836 of
  1,836 identical (1,832 exit 0, 4 exit 1 with the same text). The `merged.nt`
  of the ten ontologies of § 1 under `owl-rl`: 10 of 10 identical, and the
  `owl-consistent` verdicts 10 of 10 identical (section 11.5).
- `tests/stack/owl_real_gate.sh`: before (base binaries, load 24) 9 pass, 0
  fail, 4 expected-fail (out of 13); after (final binary, load 15) 11 pass, 0 fail, 2 expected-fail (out of 13). The rows
  `qudt-closure-address-space` and `qudt-consistent` (issue 759) now pass
  under the address-space cap, because the QUDT closure peaks at 660 MB, and
  leave the expected-failure table. Issue 759 (the Lean runtime reserves
  1 GiB per thread stack and 1 GiB mimalloc arenas) is not repaired, so a
  new expected-failure row keeps a failing test for it:
  `pizza-consistent-address-space-3gb`, the Pizza consistency check (33 MB
  resident) under a 3,000,000,000-byte address-space cap, stops with "failed
  to create thread" (run alone: 0 pass, 0 fail, 1 expected-fail (out of 1)).
  No row is slower: every after time is at
  or below the before time (wall clock, before at load 24, after at load 15: pizza-consistent 2.37 s to 0.99 s, pizza-entails-american 2.68 s to 1.30 s, wine-consistent 51.01 s to 28.76 s, ro-closure 40.93 s to 7.16 s, cl-basic-closure 38.92 s to 20.20 s, cl-basic-consistent 46.79 s to 24.15 s, ro-consistent 57.67 s to 14.48 s, qudt-species 14.8 s to 9.3 s, qudt-closure 161.85 s and 1,350 MB to 64.09 s and 660 MB; the loads differ, so the CPU times of section 11.5 are the comparison).
- `tests/stack/lean_scaling.sh`: final binary, 3 runs per point, load 12: 23 pass, 2 fail, 3 expected-fail (out of 28). The two failures are the first doubling of `owl-consistent-cl` (0.99 s to 3.16 s, 3.2; bound 3.0) and of `owlrl-closure-cl` (0.81 s to 2.45 s, 3.0). Both rows again with 5 runs per point, load 13: pass (`owl-consistent-cl` 0.85 s, 2.29 s, 5.59 s CPU, 2.7 and 2.4 per doubling; the base binary in the same run 1.45 s, 3.77 s, 8.87 s, 2.6 and 2.4). An earlier run of the whole gate on this branch (load 35, before the five scm rows went back to full evaluation) gave 25 pass, 0 fail, 3 expected-fail (out of 28). New row `owlrl-closure-cl` (the OWL
  2 RL closure of the first 10,000, 20,000 and 40,000 lines of the sorted
  Cell Ontology; closures of 26,953, 56,840 and 105,771 triples, 2.1 and 1.9
  times per doubling): 0.69 s, 1.73 s and 4.25 s CPU (2.5 and 2.5 per doubling; 5 runs per point, load 13); the base binary in the same run gave 1.11 s, 2.67 s and 7.64 s (2.4 and 2.9). ⚠️ The bound is the series bound of
  `owl-consistent-cl` (3.0 per doubling); the closure is not linear in these
  prefixes, partly because the output is not (section 11.8).
- `tests/perf/sota_gate.sh`: the two workloads that call the closure (`--workloads owl-rl-closure,owl-dl-consistent`), final binary, load 4 to 10: 17 pass, 0 fail (out of 17). CPU time against the recorded median: RO closure 2.79 s (recorded 11.02 s), Cell Ontology closure 7.17 s (13.17 s), wine closure 2.71 s (4.68 s), schema.org consistency 2.50 s (43.13 s), QUDT consistency 31.81 s and 659 MB (54.7 s and 1,351 MB). The other workloads (parsing, SPARQL, RDFC-1.0) do not call the changed code and were not run
- HermiT agreement (`tools/owl-real-hermit.py` over a `tools/owl-real-bench.py
  --no-fstar` run on the final binary): 10 of 10 consistency verdicts agree (QUDT inconsistent for both, the other nine consistent); 354 of 354 entailment pairs agree; 0 disagreements. ⚠️ The first run gave "HermiT not decided" on every pair and exit 0: the JAR path was wrong and Java could not load HermiT. The script now exits 2 when the JAR is not a file or Java cannot start HermiT
- `Wasm/native-smoke.sh` 353 pass, 0 fail, 2 xfail (out of 355);
  `Wasm/cli-smoke.sh` 83 pass, 0 fail, 0 xfail (out of 83).
- `tools/lean-tail-recursion-audit.py --gate` (stale IR removed first): GATE
  PASS. `tools/lean-hygiene-audit.py --build-log`: clean (sorry, user axiom,
  `native_decide`, `unsafe`, `implemented_by` 0; `partial def` 163, the
  baseline). `Harness.ProofObligations`: 0 pass, 0 fail, 2 expected-fail (out
  of 2), the new row `L4Factoidal.OWL.RL.closureFix_saturated`.
- wasm rebuilt (`Wasm/build-wasm.sh`), `npm test` in `npm/factoidal`: 413 pass, 0 fail, 1 skipped (out of 414). The four wasm copies agree (digest `eafe1a4f`); the wasm is not committed, and the `version.json` files and `l4factoidal.js` stay as on `main`

### 11.10 Reproduce

```
(cd formal/lean4 && lake build l4owl-rl-profile l4factoidal)
python3 tools/owl-real-bench.py --out /tmp/owl-real --no-fstar     # writes OUT/<name>/merged.nt
formal/lean4/.lake/build/bin/l4owl-rl-profile /tmp/owl-real/ro/merged.nt            # naive rounds
formal/lean4/.lake/build/bin/l4owl-rl-profile /tmp/owl-real/ro/merged.nt --sn       # semi-naive rounds
formal/lean4/.lake/build/bin/l4owl-rl-profile /tmp/owl-real/ro/merged.nt --sn --rows
tests/stack/lean_scaling.sh --only owlrl-closure-cl
```
