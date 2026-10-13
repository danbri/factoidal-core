# The Lean engine against state-of-the-art engines: parse, SPARQL, RDFC-1.0, OWL

Date: 2026-10-13 (the record name keeps the date of the owner's goal,
2026-10-12). Status: record (measurement). Key result 2.7 of
https://github.com/danbri/factoidal/issues/768 (OKRs batch 1). Issue:
https://github.com/danbri/factoidal/issues/811. Branch `claude/wt-sota-table`
of `danbri/factoidal-core`, base commit `e3c3aa01`.

Owner, 2026-10-12, verbatim: "/goal OKRs addresses successfully especially perf
and scaling should approach SOTA".

This record answers one question for each performance and scaling row of the
Lean engine: on the same machine and the same input file, how many times the
time and the peak memory of a state-of-the-art engine does the Lean engine
take? It changes no engine code. Script: `tools/sota-bench.py`. Gate:
`tests/perf/sota_gate.sh`. All rows: `2026-10-12-sota-reference.results.jsonl`
beside this file.

## 1. Result

Ratio = Lean / the fastest reference engine on the same file, at the largest
size (time: median wall time; memory: median peak resident set). Above 1, Lean
is slower or larger. Section 4 has every size; section 6 lists the rows over 10.

| Row | Lean | Fastest reference | Time ratio | Memory ratio | Issue |
|---|---|---|---:|---:|---|
| Parse N-Triples, 400,000 triples, to N-Quads | `parse --out nquads`: 2.97 s, 1,186 MB | Serd 0.53 s, 2 MB | 5.6 | 625 | https://github.com/danbri/factoidal/issues/813 |
| the same, Lean streaming reader | `parse --lenient --out nquads`: 2.69 s, 24 MB | Serd | 5.1 | 12.5 (4.2 MB above process start) | — |
| Parse Turtle, gene.ttl, 346,100 triples | 1.95 s, 243 MB | Serd 0.58 s, 2 MB | 3.3 | 128 | https://github.com/danbri/factoidal/issues/813 |
| the same, Lean streaming reader | 1.84 s, 24 MB | Serd | 3.2 | 12.5 (4.3 MB above start) | — |
| Parse RDF/XML, 100,000 triples | 5.33 s, 671 MB | Oxigraph 0.36 s, 23 MB | 15.0 | 29.4 | https://github.com/danbri/factoidal/issues/814, https://github.com/danbri/factoidal/issues/771 |
| Parse RDF/XML, the Cell Ontology (9.6 MB) | 2.46 s, 479 MB | Oxigraph 0.26 s, 23 MB | 9.5 | 21.1 | as above |
| Count statements, N-Triples 400,000 (no output) | 5.13 s, 1,186 MB; streaming 2.30 s, 24 MB | Jena `riot --count` 2.85 s, 267 MB | 1.8; streaming 0.81 | 4.4; streaming 0.09 | https://github.com/danbri/factoidal/issues/813 |
| Count, npm package (wasm), gene.ttl 346,100 triples | 11.51 s, 4,045 MB (wasm from before the issue 744 repair) | Jena 2.29 s, 296 MB | 5.0 | 13.6 | https://github.com/danbri/factoidal/issues/744 |
| SPARQL in memory, gene.ttl 346,100 triples, four queries (bound subject, COUNT, join, OPTIONAL+FILTER) | 3.97 to 4.77 s, 193 to 195 MB | Oxigraph 1.17 to 1.30 s, 141 MB | 3.4 to 4.1 | 1.4 | — |
| RDFC-1.0, 100,000 quads, IRIs only | 2.24 s, 306 MB | Oxigraph 1.51 s, 189 MB | 1.5 | 1.6 | — |
| RDFC-1.0, 20,000 persons (one blank node each) | 1.64 s, 127 MB | Oxigraph 0.80 s, 128 MB | 2.0 | 0.99 | — |
| RDFC-1.0, 8,000 blank node pairs (two collision groups) | 10.23 s, 33 MB (`e3c3aa01`, before the repair) | Oxigraph 0.20 s, 48 MB | 50.3 | 0.67 | https://github.com/danbri/factoidal/issues/751 |
| OWL RL closure, nine real ontologies (SKOS to the Cell Ontology) | 0.07 to 13.4 s, 25 to 446 MB | Jena OWL Micro 1.7 to 19.9 s, 147 to 1,658 MB (a different rule set; more than one thread) | 0.04 to 1.6 (CPU: 0.02 to 0.69) | 0.06 to 0.72 | — |
| OWL 2 DL consistency, SKOS, FOAF, PROV-O, BFO, Pizza | 0.07 to 1.39 s, 24 to 43 MB | HermiT 1.0 to 1.6 s, 75 to 82 MB | 0.07 to 1.1 | 0.3 to 0.5 | — |
| OWL 2 DL consistency, wine and food | 18.8 s, 80 MB | HermiT 2.1 s, 110 MB | 8.8 | 0.73 | — |
| OWL 2 DL consistency, schema.org | 43.8 s, 104 MB | HermiT 1.4 s, 134 MB | 31.2 | 0.78 | https://github.com/danbri/factoidal/issues/819 |
| OWL 2 DL consistency, QUDT (both: inconsistent) | 55.8 s, 1,351 MB | HermiT 6.5 s, 470 MB | 8.6 | 2.9 | — |
| OWL 2 DL consistency, RO | TIMEOUT at 600 s (`e3c3aa01`; the repair, not in this binary, is reported at 9.9 s) | HermiT 14.6 s, 1,609 MB | over 41 | — | https://github.com/danbri/factoidal/issues/760 |
| OWL 2 DL consistency, the Cell Ontology | TIMEOUT at 600 s (`e3c3aa01`; reported 13.3 s with the repair) | HermiT 3.4 s, 284 MB | over 178 | — | https://github.com/danbri/factoidal/issues/760 |

- 📊 Parsing: the Lean streaming reader takes 2.7 to 5.1 times the time of
  Serd and Oxigraph at the largest sizes, with constant memory (24 MB, of which 19.5 MB is the Lean process
  start). The default strict `parse` keeps the whole dataset in memory, 33 to
  35 bytes per input byte (https://github.com/danbri/factoidal/issues/813).
  RDF/XML is 13 to 15 times Oxigraph's time
  (https://github.com/danbri/factoidal/issues/814).
- 📊 SPARQL over a file in memory: 3.0 to 4.3 times Oxigraph's time at every
  size, 1.2 to 1.4 times its memory; faster than Jena `arq` at every size (Jena
  includes 1.2 s of JVM start).
- 📊 RDFC-1.0: 1.3 to 2.0 times Oxigraph where blank nodes have distinct
  first-degree hashes. The pairs shape is 9 to 50 times on `e3c3aa01`; the repair of
  https://github.com/danbri/factoidal/issues/751 (merging on 2026-10-13) takes
  the shared-hash shape to 2.8 times Oxigraph. rdf-canonize, the JavaScript
  reference implementation, is slower than Lean on every shape except pairs
  and is superlinear on IRIs only (25,000 quads 10.8 s of CPU time, 100,000
  quads 305 s: one run each in the trial run of 2026-10-13 00:58 UTC at load
  4; the results file has the 25,000 case only).
- 📊 OWL RL closure: Lean takes less wall time than Jena's OWL Micro rule
  reasoner on seven of nine ontologies and 1.3 and 1.6 times its wall time on
  RO and the Cell Ontology, where Jena uses 1.4 times Lean's CPU time on more
  than one thread. Lean uses less memory on all nine. The rule sets differ
  (section 2).
- 📊 OWL 2 DL consistency: Lean is faster than HermiT on SKOS, FOAF, PROV-O
  and Pizza and 1.1 times its time on BFO; 8.6 to 8.8 times on wine and QUDT;
  31 times on
  schema.org (https://github.com/danbri/factoidal/issues/819).
  RO and the Cell Ontology: TIMEOUT at 600 s on `e3c3aa01` against HermiT's
  14.6 s and 3.4 s (https://github.com/danbri/factoidal/issues/760).
- ⚠️ Lean rows: `l4factoidal` from `e3c3aa01`. The repairs of key results
  3.3 (OWL DL refuter), 2.4 (RDFC-1.0 shared hashes) and 3.4 (QUDT closure)
  were merging into `main` during the run and are not in these rows; the
  coordinator reported RO 9.9 s, the Cell Ontology 13.3 s, 64,000 colliding
  blank nodes 2.66 s and the QUDT closure at 1,352 MB peak with them. Run
  `tests/perf/sota_gate.sh` on the new binary: a repaired row over 10 shows
  as UNEXPECTED PASS and its row and issue are then updated.
- ⚠️ Load average: 1.9 to 5.9 for every Lean, Oxigraph, Serd, Jena and HermiT
  row (the SPARQL, RDFC and OWL RL rows first measured at load 6 to 30 were
  measured again; the results file keeps both, and the report takes the later
  one). The npm and rdf-canonize RDFC rows were measured at load 10 to 26 and
  not repeated; they are informative.
- Persisted store (SBM11 against QLever and Virtuoso): not measured again;
  section 5 cites the records.


## 2. Engines

| Engine | Version | How it runs here | Source, digest |
|---|---|---|---|
| Lean (`lean`) | `l4factoidal` built from `e3c3aa01` (Lean `v4.33.1`), copied once to a scratch directory before the run | the command line, one process per run | SHA-256 `98d5bc128281718eb82f325a359a0b02b6068d4b8bcef96e3c5c22ba9dd0f1d8` |
| Lean, streaming reader (`lean-stream`) | the same binary | `parse --lenient`: the reader that takes a file in 64 KiB chunks and writes each statement as it is read; on valid input it keeps every statement (N-Triples and Turtle only) | as above |
| Lean in wasm (`npm`) | `@factoidal/core` from `npm/factoidal`, wasm from release `build-3bf333414efd-web` of `danbri/factoidal-builds` (core commit `3bf33341`, an ancestor of `e3c3aa01`; before the issue 744 repair of `a7bdc189`) | Node 22.22.0, `tools/sota_bench_npm.mjs`: `parse()` then the dataset size, or `canonicalize()` | `tools/fetch-builds.sh --set web` (checks every file against the release's `build-info.json`); `l4factoidal.wasm` SHA-256 in the JSON meta line |
| Oxigraph (`oxigraph`) | pyoxigraph 0.5.11 (the Rust Oxigraph library) | Python 3.13, `tools/sota_bench_oxigraph.py`: `parse` + `serialize` to N-Quads; an in-memory `Store`, `load`, `query`, TSV results; `Dataset.canonicalize(RDFC_1_0)` | `pip install pyoxigraph==0.5.11` into a venv under `/tmp/sota-dl` |
| Serd (`serd`) | `serdi` 0.32.2 | `serdi -i FORMAT -o nquads FILE`; no RDF/XML reader | Ubuntu 24.04 packages `serdi_0.32.2-1_amd64.deb` (SHA-256 `a76f7fee…d460`) and `libserd-0-0_0.32.2-1_amd64.deb` (`5ede35e6…f57a`), unpacked with `dpkg -x`, not installed |
| Apache Jena (`jena`) | 6.2.0, OpenJDK 21.0.12 | `riot --output=nquads`, `riot --count`, `arq --data FILE --query Q --results=TSV`; `JVM_ARGS=-Xmx4g` | `https://dlcdn.apache.org/jena/binaries/apache-jena-6.2.0.tar.gz`, SHA-256 `14c12ef4aa2f0078a473be4b10b015e0e0b85e767d6867e8581679de8fec3f6e` (the SHA-512 equals Apache's published `.sha512`) |
| Jena OWL Micro (`jena-owl-micro`) | Jena 6.2.0 `OWLMicroFBRuleReasoner` | `arq --desc=ASSEMBLER --query 'SELECT ?s ?p ?o WHERE { ?s ?p ?o }' --results=TSV` over an `ja:InfModel` | as above |
| HermiT (`hermit`) | 1.3.8, as shipped in owlready2 0.51 | `java -Xmx4g -cp HermiT.jar org.semanticweb.HermiT.cli.CommandLine --ignoreUnsupportedDatatypes -k FILE` (as `tools/owl-real-hermit.py`) | `pip install --target … owlready2==0.51`; `HermiT.jar` SHA-256 `97e53f519720a0a2e328556e03b806aa239347c85e57637a935e6433ed2ad3a8` |
| rdf-canonize (`rdf-canonize`) | 5.0.0 (Digital Bazaar, JavaScript) | Node 22.22.0, `tools/sota_bench_rdfcanonize.mjs`, `canonize(dataset, {algorithm: 'RDFC-1.0'})`, default `maxWorkFactor` | `npm install rdf-canonize@5.0.0` under `/tmp/sota-dl` |

`tools/sota-bench.py --install` fetches every reference engine into one
directory (default `/tmp/sota-dl`) and checks the digests above. Nothing is
vendored into the repository.

What is a state-of-the-art engine for each row: for parsing, Serd (C) and
Oxigraph's parsers (Rust); for in-memory SPARQL, Oxigraph; for RDFC-1.0,
Oxigraph (rdf-canonize is the reference implementation of the specification
editors, measured for information); for OWL 2 DL consistency, HermiT. For OWL
RL closure the reference here is Jena's OWL Micro rule reasoner, which is
neither OWL 2 RL nor the speed state of the art (RDFox and VLog are; neither is
installed here). Its closure has a different rule set, so the closure sizes are
not compared and the ratio says only that the Lean closure and a widely used
rule engine take similar or different time on the same file.

## 3. Machine and method

**Machine.** Firecracker VM, Linux 6.18.44, Intel Xeon @ 2.80 GHz, 4 vCPU,
16,479,424 kB of memory, no swap. Shared with two other agents (OWL refuter
scaling, QUDT closure memory) and the coordinator's gates; every row carries the
1-minute load average before each of its runs.

**One number.** Each engine runs on the same file as
`/usr/bin/time -v -o T timeout -s KILL 600 COMMAND`, three times. The table gives
the median wall time of the runs (the harness clock around the process), the
spread (maximum minus minimum, over the median), the median CPU time (user plus
system, from `time -v`) and the median peak resident set (`Maximum resident set
size`). A run killed at 600 s is TIMEOUT: a status, not a time; the case is not
run again. A case whose first run takes more than 150 s runs once. When the
spread is over 30 % and the median over 0.2 s, the case runs two more times and
the median is over all five runs. Before each case the harness waits up to 30 s
for the load average to fall under 5.0. Every time includes process start
(row `start`: Lean 0.05 s, Oxigraph's Python 0.02 s, Serd 0.006 s, Jena's JVM
1.2 s, Node with the wasm module 0.4 s, HermiT's JVM 0.1 s).

**The answer of each engine.** The harness reads the whole standard output and
computes one answer per run: the number of N-Quads statements written (parse),
the number reported (count), the number of TSV solution lines or the COUNT
value (SPARQL), the SHA-256 of the canonical N-Quads lines (RDFC-1.0), the
number of closure triples (OWL RL), the verdict (OWL DL). Empty lines are not
counted (the Lean command line ends its output with one). An answer that
differs from the other engines of the same case is marked in the table. A time
is a result only where the answers agree.

**Ratio.** Lean time over reference time, and Lean peak resident set over
reference peak resident set, at the same size. The summary table compares each
Lean variant with the fastest reference engine of the case.

**Inputs.** Generated with the generators of `tools/bench_lean_vs_fstar.py`
(written to `/tmp/sota-dl/fixtures`, not committed) or real files:

- N-Triples: `<ex:s{i}> <ex:p> <ex:o{i}>` (full IRIs); mixed terms (IRIs, plain,
  language-tagged and typed literals, blank nodes).
- Turtle: slices of `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`
  (17,363,312 bytes, SHA-256 `dd0cc622cf9664df43692a04df3524c24217e76f15f63ae17040bc0bd3ba6cd6`;
  a slice of k paragraphs takes every (N/k)-th statement block, so it has the
  composition of the whole file); generated Turtle with predicate lists, object
  lists, typed literals and blank node property lists.
- RDF/XML: one `rdf:Description` per triple; the Cell Ontology
  (`third_party/ontologies/cl-basic/cl-basic.owl`, 9,557,097 bytes).
- SPARQL: the gene.ttl slices and four queries: the statements of one subject
  (the subject of the first statement block, present in every slice), COUNT(*)
  over all statements, a join on `?s` of `wdt:P688` and `wdt:P1057`, and
  `wdt:P1057` with OPTIONAL `wdt:P688` and `FILTER(isIRI(?o1))`. Each engine
  loads the file and runs the query in one process.
- RDFC-1.0: IRIs only (no blank nodes); one blank node per person with shared
  literal values; k pairs `_:a{i} ex:p _:b{i}` (two collision groups of k blank
  nodes, the shape of https://github.com/danbri/factoidal/issues/751).
- OWL: the ontologies of `tools/owl-real-bench.py`. The input of both engines
  is the RDF merge of the source documents written as N-Triples by the Lean
  parser, without the `owl:imports` triples (HermiT would fetch the imports).

## 4. Every size: Lean against the fastest reference engine

Ratio = Lean / reference (time: median wall time; CPU: median user plus system time; memory: median peak resident set). Above 1, Lean is slower or larger. The fastest reference is the one with the least median wall time.

RSS above start: each engine's peak resident set minus the peak resident set of its own process start (row `start`); a reference that holds less than 1 MB above its start counts as 1 MB.

| Workload | Size | Reference (fastest) | Reference time, RSS | Lean variant | Lean time, RSS | Time ratio | CPU ratio | RSS ratio | RSS above start, ratio |
|---|---:|---|---|---|---|---:|---:|---:|---:|
| parse-nt | 100000 | serd | 0.140 s, 2 MB | lean | 0.905 s ±122%, 306 MB | 6.5 | 9.4 | 160.9 | 286.3 |
| parse-nt | 100000 | serd | 0.140 s, 2 MB | lean-stream | 0.670 s ±5%, 24 MB | 4.8 | 6.9 | 12.5 | 4.2 |
| parse-nt | 200000 | serd | 0.206 s, 2 MB | lean | 2.233 s ±79%, 599 MB | 10.8 | 15.5 | 315.4 | 579.8 |
| parse-nt | 200000 | serd | 0.206 s, 2 MB | lean-stream | 1.402 s ±10%, 24 MB | 6.8 | 9.5 | 12.4 | 4.1 |
| parse-nt | 400000 | serd | 0.530 s, 2 MB | lean | 2.973 s ±164%, 1186 MB | 5.6 | 7.8 | 624.5 | 1167.0 |
| parse-nt | 400000 | serd | 0.530 s, 2 MB | lean-stream | 2.686 s ±17%, 24 MB | 5.1 | 6.8 | 12.5 | 4.2 |
| parse-nt-mixed | 100000 | serd | 0.143 s, 2 MB | lean | 0.940 s ±133%, 306 MB | 6.5 | 8.8 | 160.8 | 286.1 |
| parse-nt-mixed | 100000 | serd | 0.143 s, 2 MB | lean-stream | 0.690 s ±13%, 24 MB | 4.8 | 6.6 | 12.5 | 4.3 |
| parse-nt-mixed | 200000 | serd | 0.288 s, 2 MB | lean | 2.940 s ±99%, 595 MB | 10.2 | 13.5 | 312.9 | 575.1 |
| parse-nt-mixed | 200000 | serd | 0.288 s, 2 MB | lean-stream | 1.587 s ±18%, 24 MB | 5.5 | 7.0 | 12.4 | 4.1 |
| parse-nt-mixed | 400000 | serd | 0.588 s, 2 MB | lean | 3.518 s ±139%, 1177 MB | 6.0 | 7.3 | 619.5 | 1157.6 |
| parse-nt-mixed | 400000 | serd | 0.588 s, 2 MB | lean-stream | 2.959 s ±6%, 24 MB | 5.0 | 6.2 | 12.5 | 4.2 |
| parse-ttl-gene | 20000 | serd | 0.154 s, 2 MB | lean | 0.539 s ±40%, 71 MB | 3.5 | 4.8 | 35.6 | 51.7 |
| parse-ttl-gene | 20000 | serd | 0.154 s, 2 MB | lean-stream | 0.466 s ±12%, 24 MB | 3.0 | 4.1 | 11.9 | 4.3 |
| parse-ttl-gene | 40000 | serd | 0.316 s, 2 MB | lean | 1.220 s ±52%, 122 MB | 3.9 | 5.2 | 61.0 | 102.4 |
| parse-ttl-gene | 40000 | serd | 0.316 s, 2 MB | lean-stream | 0.882 s ±8%, 24 MB | 2.8 | 3.7 | 11.8 | 4.2 |
| parse-ttl-gene | 80000 | serd | 0.583 s, 2 MB | lean | 1.951 s ±50%, 243 MB | 3.3 | 4.3 | 128.1 | 223.8 |
| parse-ttl-gene | 80000 | serd | 0.583 s, 2 MB | lean-stream | 1.845 s ±1%, 24 MB | 3.2 | 4.2 | 12.5 | 4.3 |
| parse-ttl-rich | 100000 | serd | 0.122 s, 2 MB | lean | 0.735 s ±28%, 74 MB | 6.0 | 8.6 | 33.6 | 54.5 |
| parse-ttl-rich | 100000 | serd | 0.122 s, 2 MB | lean-stream | 0.613 s ±19%, 24 MB | 5.0 | 7.1 | 10.8 | 4.3 |
| parse-ttl-rich | 200000 | serd | 0.268 s, 2 MB | lean | 1.209 s ±26%, 122 MB | 4.5 | 6.7 | 58.3 | 102.9 |
| parse-ttl-rich | 200000 | serd | 0.268 s, 2 MB | lean-stream | 1.241 s ±10%, 24 MB | 4.6 | 7.2 | 11.3 | 4.3 |
| parse-ttl-rich | 400000 | serd | 0.573 s, 2 MB | lean | 3.011 s ±17%, 227 MB | 5.3 | 6.6 | 103.1 | 207.3 |
| parse-ttl-rich | 400000 | serd | 0.573 s, 2 MB | lean-stream | 2.405 s ±6%, 24 MB | 4.2 | 5.0 | 10.8 | 4.3 |
| parse-rdfxml | 25000 | oxigraph | 0.115 s, 23 MB | lean | 1.472 s ±37%, 151 MB | 12.8 | 18.0 | 6.7 | 131.7 |
| parse-rdfxml | 50000 | oxigraph | 0.191 s, 23 MB | lean | 2.695 s ±32%, 281 MB | 14.1 | 16.3 | 12.3 | 261.7 |
| parse-rdfxml | 100000 | oxigraph | 0.356 s, 23 MB | lean | 5.331 s ±30%, 671 MB | 15.0 | 16.5 | 29.4 | 651.6 |
| parse-rdfxml-real | 1 | oxigraph | 0.258 s, 23 MB | lean | 2.464 s ±97%, 479 MB | 9.5 | 11.9 | 21.1 | 459.6 |
| count-nt | 100000 | jena | 1.776 s, 156 MB | lean | 0.893 s ±147%, 306 MB | 0.50 | 0.32 | 2.0 | 4.4 |
| count-nt | 100000 | jena | 1.776 s, 156 MB | lean-stream | 0.503 s ±6%, 24 MB | 0.28 | 0.18 | 0.15 | 0.07 |
| count-nt | 100000 | jena | 1.776 s, 156 MB | npm | 6.085 s ±22%, 889 MB | 3.4 | 2.3 | 5.7 | 11.9 |
| count-nt | 200000 | jena | 2.532 s, 178 MB | lean | 2.357 s ±103%, 599 MB | 0.93 | 0.76 | 3.4 | 6.7 |
| count-nt | 200000 | jena | 2.532 s, 178 MB | lean-stream | 1.118 s ±8%, 24 MB | 0.44 | 0.36 | 0.13 | 0.05 |
| count-nt | 200000 | jena | 2.532 s, 178 MB | npm | 10.048 s ±21%, 1660 MB | 4.0 | 3.4 | 9.3 | 17.9 |
| count-nt | 400000 | jena | 2.847 s, 267 MB | lean | 5.128 s ±55%, 1186 MB | 1.8 | 1.5 | 4.4 | 6.7 |
| count-nt | 400000 | jena | 2.847 s, 267 MB | lean-stream | 2.296 s ±7%, 24 MB | 0.81 | 0.65 | 0.09 | 0.02 |
| count-nt | 400000 | jena | 2.847 s, 267 MB | npm | 21.971 s ±5%, 3140 MB | 7.7 | 6.4 | 11.8 | 17.2 |
| count-ttl-gene | 20000 | jena | 2.748 s, 201 MB | lean | 0.660 s ±52%, 57 MB | 0.24 | 0.17 | 0.29 | 0.35 |
| count-ttl-gene | 20000 | jena | 2.748 s, 201 MB | lean-stream | 0.411 s ±9%, 24 MB | 0.15 | 0.11 | 0.12 | 0.04 |
| count-ttl-gene | 20000 | jena | 2.748 s, 201 MB | npm | 3.676 s ±5%, 1095 MB | 1.3 | 1.0 | 5.5 | 8.9 |
| count-ttl-gene | 40000 | jena | 2.873 s, 285 MB | lean | 1.338 s ±26%, 93 MB | 0.47 | 0.33 | 0.33 | 0.38 |
| count-ttl-gene | 40000 | jena | 2.873 s, 285 MB | lean-stream | 0.809 s ±15%, 24 MB | 0.28 | 0.19 | 0.08 | 0.02 |
| count-ttl-gene | 40000 | jena | 2.873 s, 285 MB | npm | 6.546 s ±4%, 2122 MB | 2.3 | 1.7 | 7.4 | 10.3 |
| count-ttl-gene | 80000 | jena | 2.290 s, 296 MB | lean | 2.927 s ±28%, 163 MB | 1.3 | 0.54 | 0.55 | 0.70 |
| count-ttl-gene | 80000 | jena | 2.290 s, 296 MB | lean-stream | 1.539 s ±3%, 24 MB | 0.67 | 0.27 | 0.08 | 0.02 |
| count-ttl-gene | 80000 | jena | 2.290 s, 296 MB | npm | 11.514 s ±5%, 4045 MB | 5.0 | 2.4 | 13.6 | 19.2 |
| sparql-bound-subject | 20000 | oxigraph | 0.279 s, 56 MB | lean | 1.212 s ±6%, 65 MB | 4.3 | 4.5 | 1.2 | 1.4 |
| sparql-bound-subject | 40000 | oxigraph | 0.535 s, 84 MB | lean | 2.025 s ±11%, 112 MB | 3.8 | 3.7 | 1.3 | 1.5 |
| sparql-bound-subject | 80000 | oxigraph | 1.296 s, 141 MB | lean | 4.356 s ±25%, 193 MB | 3.4 | 3.8 | 1.4 | 1.5 |
| sparql-count | 20000 | oxigraph | 0.312 s, 56 MB | lean | 0.939 s ±10%, 65 MB | 3.0 | 3.0 | 1.2 | 1.4 |
| sparql-count | 40000 | oxigraph | 0.664 s, 84 MB | lean | 1.992 s ±12%, 112 MB | 3.0 | 3.1 | 1.3 | 1.5 |
| sparql-count | 80000 | oxigraph | 1.228 s, 141 MB | lean | 4.529 s ±9%, 193 MB | 3.7 | 3.7 | 1.4 | 1.5 |
| sparql-join | 20000 | oxigraph | 0.320 s, 56 MB | lean | 0.984 s ±4%, 67 MB | 3.1 | 3.2 | 1.2 | 1.4 |
| sparql-join | 40000 | oxigraph | 0.566 s, 84 MB | lean | 2.211 s ±8%, 111 MB | 3.9 | 3.9 | 1.3 | 1.5 |
| sparql-join | 80000 | oxigraph | 1.175 s, 141 MB | lean | 3.972 s ±18%, 195 MB | 3.4 | 3.4 | 1.4 | 1.5 |
| sparql-optional-filter | 20000 | oxigraph | 0.313 s, 56 MB | lean | 1.074 s ±20%, 67 MB | 3.4 | 3.2 | 1.2 | 1.4 |
| sparql-optional-filter | 40000 | oxigraph | 0.598 s, 84 MB | lean | 2.255 s ±10%, 114 MB | 3.8 | 3.5 | 1.4 | 1.5 |
| sparql-optional-filter | 80000 | oxigraph | 1.171 s, 141 MB | lean | 4.769 s ±13%, 195 MB | 4.1 | 4.1 | 1.4 | 1.5 |
| rdfc-iri | 25000 | oxigraph | 0.448 s, 63 MB | lean | 0.583 s ±59%, 90 MB | 1.3 | 1.6 | 1.4 | 1.8 |
| rdfc-iri | 25000 | oxigraph | 0.448 s, 63 MB | npm | 3.467 s ±55%, 264 MB | 7.7 | 5.8 | 4.2 | 3.5 |
| rdfc-iri | 50000 | oxigraph | 0.778 s, 105 MB | lean | 1.081 s ±67%, 162 MB | 1.4 | 1.6 | 1.5 | 1.7 |
| rdfc-iri | 50000 | oxigraph | 0.778 s, 105 MB | npm | 4.196 s ±25%, 494 MB | 5.4 | 5.3 | 4.7 | 4.5 |
| rdfc-iri | 100000 | oxigraph | 1.512 s, 189 MB | lean | 2.240 s ±28%, 306 MB | 1.5 | 1.5 | 1.6 | 1.7 |
| rdfc-iri | 100000 | oxigraph | 1.512 s, 189 MB | npm | 6.824 s ±19%, 873 MB | 4.5 | 4.0 | 4.6 | 4.5 |
| rdfc-person | 5000 | oxigraph | 0.178 s, 49 MB | lean | 0.334 s ±12%, 47 MB | 1.9 | 2.1 | 0.96 | 1.1 |
| rdfc-person | 5000 | oxigraph | 0.178 s, 49 MB | npm | 1.669 s ±21%, 166 MB | 9.4 | 9.4 | 3.4 | 1.7 |
| rdfc-person | 10000 | oxigraph | 0.382 s, 75 MB | lean | 0.721 s ±8%, 72 MB | 1.9 | 1.9 | 0.96 | 1.0 |
| rdfc-person | 10000 | oxigraph | 0.382 s, 75 MB | npm | 2.602 s ±5%, 237 MB | 6.8 | 6.7 | 3.2 | 2.2 |
| rdfc-person | 20000 | oxigraph | 0.804 s, 128 MB | lean | 1.639 s ±29%, 127 MB | 2.0 | 2.1 | 0.99 | 1.0 |
| rdfc-person | 20000 | oxigraph | 0.804 s, 128 MB | npm | 4.753 s ±10%, 410 MB | 5.9 | 5.0 | 3.2 | 2.7 |
| rdfc-pairs | 2000 | oxigraph | 0.065 s, 29 MB | lean | 0.606 s ±24%, 24 MB | 9.3 | 11.2 | 0.85 | 0.85 |
| rdfc-pairs | 2000 | oxigraph | 0.065 s, 29 MB | npm | 1.610 s ±24%, 131 MB | 24.8 | 27.8 | 4.6 | 1.6 |
| rdfc-pairs | 4000 | oxigraph | 0.100 s, 35 MB | lean | 2.075 s ±7%, 27 MB | 20.8 | 25.5 | 0.77 | 0.62 |
| rdfc-pairs | 4000 | oxigraph | 0.100 s, 35 MB | npm | 4.058 s ±8%, 136 MB | 40.6 | 41.2 | 3.8 | 1.1 |
| rdfc-pairs | 8000 | oxigraph | 0.203 s, 48 MB | lean | 10.229 s ±6%, 33 MB | 50.3 | 55.4 | 0.67 | 0.51 |
| rdfc-pairs | 8000 | oxigraph | 0.203 s, 48 MB | npm | exit1 (10.353 s), 149 MB | > 51 (exit1) | — | — | — |
| owl-rl-closure | skos | jena-owl-micro | 1.668 s, 148 MB | lean | 0.071 s ±41%, 25 MB | 0.04 | 0.02 | 0.17 | 0.09 |
| owl-rl-closure | foaf | jena-owl-micro | 1.877 s, 161 MB | lean | 0.102 s ±18%, 27 MB | 0.05 | 0.02 | 0.17 | 0.10 |
| owl-rl-closure | prov-o | jena-owl-micro | 1.828 s, 147 MB | lean | 0.195 s ±8%, 30 MB | 0.11 | 0.04 | 0.20 | 0.18 |
| owl-rl-closure | bfo | jena-owl-micro | 2.019 s, 158 MB | lean | 0.140 s ±16%, 29 MB | 0.07 | 0.03 | 0.18 | 0.14 |
| owl-rl-closure | pizza | jena-owl-micro | 2.296 s, 238 MB | lean | 0.410 s ±10%, 47 MB | 0.18 | 0.08 | 0.20 | 0.19 |
| owl-rl-closure | wine | jena-owl-micro | 7.405 s, 548 MB | lean | 4.765 s ±11%, 89 MB | 0.64 | 0.39 | 0.16 | 0.15 |
| owl-rl-closure | schema.org | jena-owl-micro | 19.868 s, 1658 MB | lean | 2.840 s ±18%, 108 MB | 0.14 | 0.11 | 0.06 | 0.06 |
| owl-rl-closure | ro | jena-owl-micro | 8.584 s, 849 MB | lean | 11.259 s ±10%, 77 MB | 1.3 | 0.69 | 0.09 | 0.08 |
| owl-rl-closure | cl-basic | jena-owl-micro | 8.632 s, 619 MB | lean | 13.443 s ±6%, 446 MB | 1.6 | 0.69 | 0.72 | 0.81 |
| owl-dl-consistent | skos | hermit | 0.991 s, 77 MB | lean | 0.068 s ±17%, 24 MB | 0.07 | 0.06 | 0.31 | 0.12 |
| owl-dl-consistent | foaf | hermit | 1.065 s, 75 MB | lean | 0.143 s ±36%, 26 MB | 0.13 | 0.12 | 0.34 | 0.19 |
| owl-dl-consistent | prov-o | hermit | 1.591 s, 82 MB | lean | 0.592 s ±16%, 30 MB | 0.37 | 0.36 | 0.36 | 0.27 |
| owl-dl-consistent | bfo | hermit | 1.289 s, 79 MB | lean | 1.394 s ±15%, 33 MB | 1.1 | 1.2 | 0.42 | 0.39 |
| owl-dl-consistent | pizza | hermit | 1.371 s, 82 MB | lean | 0.775 s ±6%, 43 MB | 0.57 | 0.54 | 0.53 | 0.62 |
| owl-dl-consistent | wine | hermit | 2.135 s, 110 MB | lean | 18.778 s ±6%, 80 MB | 8.8 | 4.9 | 0.73 | 0.91 |
| owl-dl-consistent | schema.org | hermit | 1.402 s, 134 MB | lean | 43.751 s ±1%, 104 MB | 31.2 | 16.8 | 0.78 | 0.94 |
| owl-dl-consistent | qudt | hermit | 6.480 s, 470 MB | lean | 55.830 s ±9%, 1351 MB | 8.6 | 4.8 | 2.9 | 3.1 |
| owl-dl-consistent | ro | hermit | 14.628 s, 1609 MB | lean | TIMEOUT (600.013 s), 2 MB | > 41 (TIMEOUT) | — | — | — |
| owl-dl-consistent | cl-basic | hermit | 3.360 s, 284 MB | lean | TIMEOUT (600.005 s), 2 MB | > 179 (TIMEOUT) | — | — | — |


## 5. Rows measured in other records (not measured again here)

| Row | Lean | State of the art | Ratio | Record |
|---|---|---|---|---|
| Persisted store, DBpedia 2016-10 slice (23,269,560 triples): load | SBM11 pack 1,334 s | Virtuoso 7.2 bulk load 203 s; QLever index 56.5 s (2,069 MB) | 6.6 (Virtuoso), 23.6 (QLever) | [`2026-10-12-three-engine-benchmark.md`](2026-10-12-three-engine-benchmark.md) section 1, https://github.com/danbri/factoidal/issues/798 |
| Persisted store, DBpedia slice: size on disk | SBM11 567.7 MB | Virtuoso 1,746.9 MB; QLever 872.5 MB | 0.33 (Virtuoso), 0.65 (QLever) | as above |
| Persisted store, DBpedia slice: warm joins d05 to d09 | SBM11 | Virtuoso 3.6 to 26 times faster on joins; QLever 6.4 to 13 times faster | 3.6 to 26 | as above; https://github.com/danbri/factoidal/issues/799, https://github.com/danbri/factoidal/issues/801 |
| Persisted store, DBpedia slice: scans and aggregates over large ranges, lookups | SBM11 | Virtuoso | SBM11 5.9 to 14 times faster (d10, d13, d16, d17) | as above |
| Persisted store, DBpedia slice: OPTIONAL (d11) | SBM11 reference fallback 48.7 s, 849 MB | Virtuoso 19 ms | about 2,560 | as above; https://github.com/danbri/factoidal/issues/775 |
| QLever's own index read from Lean (`l4qlvr`), four-pattern join q07, warm | 75 ms (23 ms with libzstd) | QLever 19 ms of computation | 3.9 (1.2) | [`2026-10-11-qlvr-performance.md`](2026-10-11-qlvr-performance.md), https://github.com/danbri/factoidal/issues/778 |
| The q07 kernel, Lean against C | Lean | the same algorithm in C | 9 to 16 on `ByteArray`, 2.5 to 2.9 on word arrays | as above; https://github.com/danbri/factoidal/issues/797 |
| RDFC-1.0, k blank nodes that share one first-degree hash, 64,000 | 2.66 s, 222 MB (after the repair of https://github.com/danbri/factoidal/issues/751, branch `claude/wt-rdfc-collide`, not yet on `main`) | Oxigraph 0.96 s, 167 MB; rdf-canonize 37.80 s | 2.8 (Oxigraph); 0.07 (rdf-canonize) | [`2026-10-10-npm-lean-only.md`](2026-10-10-npm-lean-only.md) section 10 on that branch, https://github.com/danbri/factoidal/issues/751 |

The persisted-store rows belong to the SBM11 work (https://github.com/danbri/factoidal/issues/798, https://github.com/danbri/factoidal/issues/799, https://github.com/danbri/factoidal/issues/801, https://github.com/danbri/factoidal/issues/775); this record does not measure them again.

## 6. Rows over 10, and their issues

A row is over 10 when the Lean time is more than 10 times the time of the
fastest reference engine of the case, or when the Lean peak resident set is
more than 10 times the reference's and also more than 10 times its memory above
process start (a reference under 1 MB above its start counts as 1 MB; this
keeps the 19.5 MB of the Lean process start against Serd's 1.8 MB from listing
the streaming reader).

| Rows | Cause, as far as measured | Issue | Gate |
|---|---|---|---|
| `parse-nt`, `parse-nt-mixed` (all sizes; time 10.2 and 10.8 at 200,000), `parse-ttl-gene`, `parse-ttl-rich` (memory) | the strict `parse` keeps the whole dataset in memory, 33 to 35 bytes per input byte; the streaming reader of the same binary holds 24 MB | https://github.com/danbri/factoidal/issues/813 (new) | expected failure `parse-nt` 400,000, `parse-ttl-gene` 80,000 |
| `parse-rdfxml` (all sizes), `parse-rdfxml-real` (memory) | not located; 48 to 49 bytes per input byte (the memory is https://github.com/danbri/factoidal/issues/771) | https://github.com/danbri/factoidal/issues/814 (new) | expected failure `parse-rdfxml` 100,000 |
| `count-nt` 400,000 and `count-ttl-gene` 80,000, npm (memory) | wasm of release `build-3bf333414efd-web`, before the repair `a7bdc189` | https://github.com/danbri/factoidal/issues/744 (comment with these rows) | — (the gate runs native Lean only) |
| `rdfc-pairs` 4,000 and 8,000 (Lean), 2,000 to 8,000 (npm; 8,000 stops with "Maximum call stack size exceeded") | Hash N-Degree Quads over a collision group, repaired on branch `claude/wt-rdfc-collide` | https://github.com/danbri/factoidal/issues/751 (comment with these rows) | expected failure `rdfc-pairs` 8,000 |
| `owl-dl-consistent` schema.org | not located; HermiT decides the file in 1.4 s | https://github.com/danbri/factoidal/issues/819 (new) | expected failure `owl-dl-consistent` schema.org |
| `owl-dl-consistent` RO and the Cell Ontology: TIMEOUT at 600 s | the tableau refuter's growth; repaired on the branch of key result 3.3, merging into `main` | https://github.com/danbri/factoidal/issues/760 (comment with these rows) | — (a TIMEOUT row is not re-run by the gate; `tests/stack/owl_real_gate.sh` holds the expected failure) |

The list the report prints (`tools/sota-bench.py --report`), every Lean variant:

- parse-nt 100000, lean against serd: time ratio 6.5, RSS ratio 160.9
- parse-nt 200000, lean against serd: time ratio 10.8, RSS ratio 315.4
- parse-nt 400000, lean against serd: time ratio 5.6, RSS ratio 624.5
- parse-nt-mixed 100000, lean against serd: time ratio 6.5, RSS ratio 160.8
- parse-nt-mixed 200000, lean against serd: time ratio 10.2, RSS ratio 312.9
- parse-nt-mixed 400000, lean against serd: time ratio 6.0, RSS ratio 619.5
- parse-ttl-gene 20000, lean against serd: time ratio 3.5, RSS ratio 35.6
- parse-ttl-gene 40000, lean against serd: time ratio 3.9, RSS ratio 61.0
- parse-ttl-gene 80000, lean against serd: time ratio 3.3, RSS ratio 128.1
- parse-ttl-rich 100000, lean against serd: time ratio 6.0, RSS ratio 33.6
- parse-ttl-rich 200000, lean against serd: time ratio 4.5, RSS ratio 58.3
- parse-ttl-rich 400000, lean against serd: time ratio 5.3, RSS ratio 103.1
- parse-rdfxml 25000, lean against oxigraph: time ratio 12.8, RSS ratio 6.7
- parse-rdfxml 50000, lean against oxigraph: time ratio 14.1, RSS ratio 12.3
- parse-rdfxml 100000, lean against oxigraph: time ratio 15.0, RSS ratio 29.4
- parse-rdfxml-real 1, lean against oxigraph: time ratio 9.5, RSS ratio 21.1
- count-nt 400000, npm against jena: time ratio 7.7, RSS ratio 11.8
- count-ttl-gene 80000, npm against jena: time ratio 5.0, RSS ratio 13.6
- rdfc-pairs 2000, npm against oxigraph: time ratio 24.8, RSS ratio 4.6
- rdfc-pairs 4000, lean against oxigraph: time ratio 20.8, RSS ratio 0.8
- rdfc-pairs 4000, npm against oxigraph: time ratio 40.6, RSS ratio 3.8
- rdfc-pairs 8000, lean against oxigraph: time ratio 50.3, RSS ratio 0.7
- rdfc-pairs 8000, npm against oxigraph: time ratio not finished, RSS ratio —
- owl-dl-consistent schema.org, lean against hermit: time ratio 31.2, RSS ratio 0.8
- owl-dl-consistent ro, lean against hermit: time ratio not finished, RSS ratio —
- owl-dl-consistent cl-basic, lean against hermit: time ratio not finished, RSS ratio —



## 7. What this method cannot see

- A row measures a command line, including process start, reading the file and
  writing the answer. Oxigraph runs inside Python, Jena and HermiT inside a
  JVM; for small inputs the start of the process is most of the time (row
  `start`).
- Jena uses more than one thread (JIT compiler, garbage collector), so its CPU
  time is above its wall time. Lean, Serd and Oxigraph's parsers use one.
- The load average was 4 to 5 on 4 CPUs for the parse and count rows and 6 to
  30 for the SPARQL, RDFC and OWL rows (other agents built the wasm module and
  ran their gates). Wall times carry that load; the CPU column carries less of
  it. The Lean default `parse` of N-Triples was bimodal at load 4 (100,000
  triples: 0.67 to 1.78 s over five runs); the median of five is in the table.
  Small rows (under 0.3 s) at load 10 have spreads near 100 %.
- Peak resident set of a streaming parser (Serd: 2 MB) is the floor of the
  method. A ratio against it compares an engine that keeps the dataset in
  memory with one that keeps nothing; the `lean-stream` rows are the like for
  like comparison.
- The SPARQL rows load a file and run one query; they do not measure a warm
  store, concurrent queries, property paths, aggregates other than COUNT,
  updates or the persisted store.
- One input shape per row. The RDFC rows do not include the shape where every
  blank node has the same first-degree hash; that row is in
  `2026-10-10-npm-lean-only.md` section 10 (issue 751).
- The OWL RL rows compare different rule sets (section 2). The OWL RL closure
  of QUDT was not run on `e3c3aa01`: it needs more than 6 GB there
  (https://github.com/danbri/factoidal/issues/758; the repair of key result
  3.4 reports 1,352 MB). The workload includes QUDT for the next binary.
- A TIMEOUT row has no memory figure: `time -v` then reports the `timeout`
  process (1.8 MB), not the killed step.
- Every Lean row is the `l4factoidal` of `e3c3aa01` (SHA-256 prefix
  `98d5bc128281718e`, field `lean_sha256` of the later rows). The repairs of
  key results 3.3, 2.4 and 3.4, which the coordinator was merging into `main`
  during the run, are not in it.
- The OWL DL rows decide consistency only (`owl:Thing` satisfiable); no
  classification, no entailment checks.

## 8. Reproduce

```
cd formal/lean4 && lake build l4factoidal          # the Lean binary
tools/fetch-builds.sh --set web                     # the wasm for the npm rows
python3 tools/sota-bench.py --install               # reference engines into /tmp/sota-dl
python3 tools/sota-bench.py --out /tmp/sota.jsonl   # every row, about 90 minutes
python3 tools/sota-bench.py --report /tmp/sota.jsonl
tests/perf/sota_gate.sh                             # the Lean rows against this record
rm -rf /tmp/sota-dl                                 # the downloads
```

## Appendix: every measurement

| Workload | Size | Engine | Wall, median (spread) | CPU, median | Peak RSS, median | Answer | Load (1 min) |
|---|---:|---|---:|---:|---:|---|---|
| start | 0 | lean | 0.047 s ±12% | 0.03 s | 20 MB | — | 4.11 to 4.11 |
| start | 0 | oxigraph | 0.025 s ±3% | 0.01 s | 23 MB | — | 4.11 to 4.11 |
| start | 0 | serd | 0.005 s ±20% | 0.00 s | 2 MB | — | 4.11 to 4.11 |
| start | 0 | jena | 1.193 s ±6% | 1.69 s | 92 MB | — | 4.11 to 4.11 |
| start | 0 | npm | 0.409 s ±6% | 0.50 s | 122 MB | — | 4.02 to 4.11 |
| start | 0 | hermit | 0.107 s ±8% | 0.11 s | 43 MB | — | 4.02 to 4.02 |
| parse-nt | 100000 | lean | 0.905 s ±122% | 0.85 s | 306 MB | 100000 | 3.94 to 4.02 |
| parse-nt | 100000 | lean-stream | 0.670 s ±5% | 0.62 s | 24 MB | 100000 | 3.94 to 3.94 |
| parse-nt | 100000 | oxigraph | 0.173 s ±3% | 0.13 s | 23 MB | 100000 | 3.87 to 3.94 |
| parse-nt | 100000 | serd | 0.140 s ±30% | 0.09 s | 2 MB | 100000 | 3.87 to 3.87 |
| parse-nt | 100000 | jena | 2.756 s ±43% | 3.18 s | 160 MB | 100000 | 3.87 to 4.12 |
| parse-nt | 200000 | lean | 2.233 s ±79% | 2.01 s | 599 MB | 200000 | 4.1 to 4.11 |
| parse-nt | 200000 | lean-stream | 1.402 s ±10% | 1.24 s | 24 MB | 200000 | 4.09 to 4.09 |
| parse-nt | 200000 | oxigraph | 0.339 s ±6% | 0.25 s | 23 MB | 200000 | 4.09 to 4.09 |
| parse-nt | 200000 | serd | 0.206 s ±17% | 0.13 s | 2 MB | 200000 | 4.09 to 4.09 |
| parse-nt | 200000 | jena | 3.464 s ±12% | 3.39 s | 176 MB | 200000 | 4.09 to 4.39 |
| parse-nt | 400000 | lean | 2.973 s ±164% | 2.80 s | 1186 MB | 400000 | 4.44 to 4.67 |
| parse-nt | 400000 | lean-stream | 2.686 s ±17% | 2.43 s | 24 MB | 400000 | 4.67 to 4.77 |
| parse-nt | 400000 | oxigraph | 0.586 s ±31% | 0.45 s | 23 MB | 400000 | 4.71 to 4.89 |
| parse-nt | 400000 | serd | 0.530 s ±25% | 0.36 s | 2 MB | 400000 | 4.89 to 4.89 |
| parse-nt | 400000 | jena | 2.937 s ±9% | 3.92 s | 225 MB | 400000 | 4.74 to 4.89 |
| parse-nt-mixed | 100000 | lean | 0.940 s ±133% | 0.88 s | 306 MB | 100000 | 4.47 to 4.6 |
| parse-nt-mixed | 100000 | lean-stream | 0.690 s ±13% | 0.66 s | 24 MB | 100000 | 4.47 to 4.47 |
| parse-nt-mixed | 100000 | oxigraph | 0.217 s ±14% | 0.18 s | 23 MB | 100000 | 4.47 to 4.47 |
| parse-nt-mixed | 100000 | serd | 0.143 s ±22% | 0.10 s | 2 MB | 100000 | 4.43 to 4.47 |
| parse-nt-mixed | 100000 | jena | 2.339 s ±11% | 3.92 s | 155 MB | 100000 | 4.43 to 4.48 |
| parse-nt-mixed | 200000 | lean | 2.940 s ±99% | 2.83 s | 595 MB | 200000 | 4.25 to 4.48 |
| parse-nt-mixed | 200000 | lean-stream | 1.587 s ±18% | 1.47 s | 24 MB | 200000 | 3.98 to 4.15 |
| parse-nt-mixed | 200000 | oxigraph | 0.413 s ±7% | 0.33 s | 23 MB | 200000 | 3.98 to 3.98 |
| parse-nt-mixed | 200000 | serd | 0.288 s ±50% | 0.21 s | 2 MB | 200000 | 3.98 to 4.22 |
| parse-nt-mixed | 200000 | jena | 2.818 s ±14% | 4.17 s | 174 MB | 200000 | 4.22 to 4.44 |
| parse-nt-mixed | 400000 | lean | 3.518 s ±139% | 3.29 s | 1177 MB | 400000 | 4.02 to 4.44 |
| parse-nt-mixed | 400000 | lean-stream | 2.959 s ±6% | 2.81 s | 24 MB | 400000 | 3.94 to 4.02 |
| parse-nt-mixed | 400000 | oxigraph | 0.683 s ±12% | 0.53 s | 23 MB | 400000 | 4.02 to 4.18 |
| parse-nt-mixed | 400000 | serd | 0.588 s ±28% | 0.45 s | 2 MB | 400000 | 4.18 to 4.18 |
| parse-nt-mixed | 400000 | jena | 2.995 s ±26% | 4.55 s | 268 MB | 400000 | 4.08 to 4.16 |
| parse-ttl-gene | 20000 | lean | 0.539 s ±40% | 0.48 s | 71 MB | 87468 | 3.99 to 4.16 |
| parse-ttl-gene | 20000 | lean-stream | 0.466 s ±12% | 0.41 s | 24 MB | 87468 | 3.99 to 3.99 |
| parse-ttl-gene | 20000 | oxigraph | 0.195 s ±45% | 0.14 s | 23 MB | 87468 | 3.91 to 3.99 |
| parse-ttl-gene | 20000 | serd | 0.154 s ±24% | 0.10 s | 2 MB | 87468 | 3.91 to 3.91 |
| parse-ttl-gene | 20000 | jena | 2.178 s ±11% | 3.61 s | 203 MB | 87468 | 3.91 to 3.99 |
| parse-ttl-gene | 40000 | lean | 1.220 s ±52% | 1.09 s | 122 MB | 174225 | 3.91 to 3.99 |
| parse-ttl-gene | 40000 | lean-stream | 0.882 s ±8% | 0.78 s | 24 MB | 174225 | 3.91 to 4.08 |
| parse-ttl-gene | 40000 | oxigraph | 0.362 s ±7% | 0.27 s | 23 MB | 174225 | 4.08 to 4.08 |
| parse-ttl-gene | 40000 | serd | 0.316 s ±13% | 0.21 s | 2 MB | 174225 | 4.07 to 4.08 |
| parse-ttl-gene | 40000 | jena | 2.067 s ±17% | 4.60 s | 256 MB | 174225 | 4.07 to 4.15 |
| parse-ttl-gene | 80000 | lean | 1.951 s ±50% | 1.71 s | 243 MB | 346100 | 3.82 to 4.15 |
| parse-ttl-gene | 80000 | lean-stream | 1.845 s ±1% | 1.69 s | 24 MB | 346100 | 3.67 to 3.82 |
| parse-ttl-gene | 80000 | oxigraph | 0.686 s ±11% | 0.52 s | 23 MB | 346100 | 3.54 to 3.54 |
| parse-ttl-gene | 80000 | serd | 0.583 s ±25% | 0.40 s | 2 MB | 346100 | 3.54 to 3.57 |
| parse-ttl-gene | 80000 | jena | 4.134 s ±12% | 6.09 s | 294 MB | 346100 | 3.57 to 3.72 |
| parse-ttl-rich | 100000 | lean | 0.735 s ±28% | 0.69 s | 74 MB | 114280 | 3.9 to 3.9 |
| parse-ttl-rich | 100000 | lean-stream | 0.613 s ±19% | 0.57 s | 24 MB | 114280 | 3.9 to 3.9 |
| parse-ttl-rich | 100000 | oxigraph | 0.236 s ±14% | 0.20 s | 23 MB | 114280 | 3.9 to 3.91 |
| parse-ttl-rich | 100000 | serd | 0.122 s ±6% | 0.08 s | 2 MB | 114280 | 3.91 to 3.91 |
| parse-ttl-rich | 100000 | jena | 2.325 s ±4% | 3.68 s | 179 MB | 114280 | 3.91 to 4.16 |
| parse-ttl-rich | 200000 | lean | 1.209 s ±26% | 1.07 s | 122 MB | 228568 | 3.99 to 4.16 |
| parse-ttl-rich | 200000 | lean-stream | 1.241 s ±10% | 1.15 s | 24 MB | 228568 | 3.99 to 3.99 |
| parse-ttl-rich | 200000 | oxigraph | 0.437 s ±5% | 0.34 s | 23 MB | 228568 | 3.83 to 3.83 |
| parse-ttl-rich | 200000 | serd | 0.268 s ±50% | 0.16 s | 2 MB | 228568 | 3.83 to 3.83 |
| parse-ttl-rich | 200000 | jena | 3.217 s ±48% | 4.49 s | 201 MB | 228568 | 4.32 to 4.59 |
| parse-ttl-rich | 400000 | lean | 3.011 s ±17% | 2.82 s | 227 MB | 457136 | 4.94 to 4.94 |
| parse-ttl-rich | 400000 | lean-stream | 2.405 s ±6% | 2.17 s | 24 MB | 457136 | 4.79 to 4.89 |
| parse-ttl-rich | 400000 | oxigraph | 0.833 s ±13% | 0.68 s | 23 MB | 457136 | 4.81 to 4.89 |
| parse-ttl-rich | 400000 | serd | 0.573 s ±11% | 0.43 s | 2 MB | 457136 | 4.81 to 4.81 |
| parse-ttl-rich | 400000 | jena | 3.929 s ±8% | 6.14 s | 276 MB | 457136 | 4.81 to 4.92 |
| parse-rdfxml | 25000 | lean | 1.472 s ±37% | 1.44 s | 151 MB | 25000 | 4.7 to 4.85 |
| parse-rdfxml | 25000 | oxigraph | 0.115 s ±5% | 0.08 s | 23 MB | 25000 | 4.56 to 4.56 |
| parse-rdfxml | 25000 | jena | 2.090 s ±10% | 3.06 s | 130 MB | 25000 | 4.56 to 4.92 |
| parse-rdfxml | 50000 | lean | 2.695 s ±32% | 2.61 s | 281 MB | 50000 | 4.92 to 5.25 |
| parse-rdfxml | 50000 | oxigraph | 0.191 s ±14% | 0.16 s | 23 MB | 50000 | 4.98 to 4.98 |
| parse-rdfxml | 50000 | jena | 2.676 s ±4% | 4.10 s | 177 MB | 50000 | 4.98 to 5.14 |
| parse-rdfxml | 100000 | lean | 5.331 s ±30% | 5.12 s | 671 MB | 100000 | 5.36 to 5.79 |
| parse-rdfxml | 100000 | oxigraph | 0.356 s ±9% | 0.31 s | 23 MB | 100000 | 4.83 to 4.83 |
| parse-rdfxml | 100000 | jena | 2.951 s ±7% | 4.79 s | 267 MB | 100000 | 4.83 to 4.92 |
| parse-rdfxml-real | 1 | lean | 2.464 s ±97% | 2.38 s | 479 MB | 78835 | 4.57 to 4.93 |
| parse-rdfxml-real | 1 | oxigraph | 0.258 s ±11% | 0.20 s | 23 MB | 78835 | 4.57 to 4.57 |
| parse-rdfxml-real | 1 | jena | 2.507 s ±51% | 3.88 s | 139 MB | 78835 | 4.57 to 4.96 |
| count-nt | 100000 | lean | 0.893 s ±147% | 0.84 s | 306 MB | 100000 | 4.8 to 4.96 |
| count-nt | 100000 | lean-stream | 0.503 s ±6% | 0.49 s | 24 MB | 100000 | 4.66 to 4.66 |
| count-nt | 100000 | npm | 6.085 s ±22% | 6.18 s | 889 MB | 100000 | 4.52 to 4.88 |
| count-nt | 100000 | jena | 1.776 s ±12% | 2.66 s | 156 MB | 100000 | 4.73 to 4.75 |
| count-nt | 200000 | lean | 2.357 s ±103% | 2.31 s | 599 MB | 200000 | 4.56 to 4.68 |
| count-nt | 200000 | lean-stream | 1.118 s ±8% | 1.10 s | 24 MB | 200000 | 4.46 to 4.68 |
| count-nt | 200000 | npm | 10.048 s ±21% | 10.26 s | 1660 MB | 200000 | 4.26 to 4.46 |
| count-nt | 200000 | jena | 2.532 s ±8% | 3.02 s | 178 MB | 200000 | 4.47 to 4.59 |
| count-nt | 400000 | lean | 5.128 s ±55% | 5.07 s | 1186 MB | 400000 | 4.36 to 4.59 |
| count-nt | 400000 | lean-stream | 2.296 s ±7% | 2.25 s | 24 MB | 400000 | 4.38 to 4.41 |
| count-nt | 400000 | npm | 21.971 s ±5% | 22.15 s | 3140 MB | 400000 | 4.35 to 4.55 |
| count-nt | 400000 | jena | 2.847 s ±14% | 3.45 s | 267 MB | 400000 | 4.6 to 4.71 |
| count-ttl-gene | 20000 | lean | 0.660 s ±52% | 0.63 s | 57 MB | 87468 | 4.58 to 4.58 |
| count-ttl-gene | 20000 | lean-stream | 0.411 s ±9% | 0.39 s | 24 MB | 87468 | 4.53 to 4.53 |
| count-ttl-gene | 20000 | npm | 3.676 s ±5% | 3.79 s | 1095 MB | 87468 | 4.53 to 4.65 |
| count-ttl-gene | 20000 | jena | 2.748 s ±18% | 3.61 s | 201 MB | 87468 | 4.6 to 4.79 |
| count-ttl-gene | 40000 | lean | 1.338 s ±26% | 1.27 s | 93 MB | 174225 | 4.93 to 4.93 |
| count-ttl-gene | 40000 | lean-stream | 0.809 s ±15% | 0.75 s | 24 MB | 174225 | 4.93 to 5.02 |
| count-ttl-gene | 40000 | npm | 6.546 s ±4% | 6.70 s | 2122 MB | 174225 | 4.84 to 5.08 |
| count-ttl-gene | 40000 | jena | 2.873 s ±18% | 3.90 s | 285 MB | 174225 | 5.07 to 5.23 |
| count-ttl-gene | 80000 | lean | 2.927 s ±28% | 2.82 s | 163 MB | 346100 | 5.47 to 5.76 |
| count-ttl-gene | 80000 | lean-stream | 1.539 s ±3% | 1.43 s | 24 MB | 346100 | 5.94 to 6.03 |
| count-ttl-gene | 80000 | npm | 11.514 s ±5% | 12.74 s | 4045 MB | 346100 | 4.82 to 5.79 |
| count-ttl-gene | 80000 | jena | 2.290 s ±9% | 5.23 s | 296 MB | 346100 | 4.27 to 4.38 |
| sparql-bound-subject | 20000 | lean | 1.212 s ±6% | 1.16 s | 65 MB | 1 | 4.84 to 4.84 |
| sparql-bound-subject | 20000 | oxigraph | 0.279 s ±27% | 0.26 s | 56 MB | 1 | 3.92 to 4.09 |
| sparql-bound-subject | 20000 | jena | 2.370 s ±15% | 5.00 s | 353 MB | 1 | 3.92 to 3.93 |
| sparql-bound-subject | 40000 | lean | 2.025 s ±11% | 1.91 s | 112 MB | 1 | 4.7 to 4.84 |
| sparql-bound-subject | 40000 | oxigraph | 0.535 s ±18% | 0.52 s | 84 MB | 1 | 3.63 to 3.77 |
| sparql-bound-subject | 40000 | jena | 3.006 s ±11% | 6.48 s | 516 MB | 1 | 3.63 to 3.9 |
| sparql-bound-subject | 80000 | lean | 4.356 s ±25% | 4.27 s | 193 MB | 1 | 4.44 to 4.48 |
| sparql-bound-subject | 80000 | oxigraph | 1.296 s ±19% | 1.12 s | 141 MB | 1 | 3.48 to 3.68 |
| sparql-bound-subject | 80000 | jena | 6.784 s ±3% | 8.22 s | 771 MB | 1 | 3.68 to 5.2 |
| sparql-count | 20000 | lean | 0.939 s ±10% | 0.90 s | 65 MB | 87468 | 4.22 to 4.33 |
| sparql-count | 20000 | oxigraph | 0.312 s ±10% | 0.30 s | 56 MB | 87468 | 4.58 to 4.58 |
| sparql-count | 20000 | jena | 3.596 s ±14% | 5.97 s | 360 MB | 87468 | 4.45 to 4.49 |
| sparql-count | 40000 | lean | 1.992 s ±12% | 1.95 s | 112 MB | 174225 | 4.12 to 4.22 |
| sparql-count | 40000 | oxigraph | 0.664 s ±3% | 0.62 s | 84 MB | 174225 | 4.53 to 4.53 |
| sparql-count | 40000 | jena | 4.985 s ±5% | 8.02 s | 619 MB | 174225 | 4.53 to 4.61 |
| sparql-count | 80000 | lean | 4.529 s ±9% | 4.42 s | 193 MB | 346100 | 4.02 to 4.12 |
| sparql-count | 80000 | oxigraph | 1.228 s ±18% | 1.20 s | 141 MB | 346100 | 4.51 to 4.64 |
| sparql-count | 80000 | jena | 7.401 s ±10% | 11.38 s | 916 MB | 346100 | 4.51 to 4.55 |
| sparql-join | 20000 | lean | 0.984 s ±4% | 0.95 s | 67 MB | 101 | 4.1 to 4.1 |
| sparql-join | 20000 | oxigraph | 0.320 s ±22% | 0.30 s | 56 MB | 101 | 4.57 to 4.57 |
| sparql-join | 20000 | jena | 3.212 s ±10% | 5.59 s | 384 MB | 101 | 4.57 to 4.79 |
| sparql-join | 40000 | lean | 2.211 s ±8% | 2.10 s | 111 MB | 365 | 4.01 to 4.1 |
| sparql-join | 40000 | oxigraph | 0.566 s ±13% | 0.54 s | 84 MB | 365 | 4.72 to 4.79 |
| sparql-join | 40000 | jena | 4.055 s ±12% | 6.45 s | 517 MB | 365 | 4.72 to 4.75 |
| sparql-join | 80000 | lean | 3.972 s ±18% | 3.91 s | 195 MB | 1392 | 3.86 to 3.93 |
| sparql-join | 80000 | oxigraph | 1.175 s ±3% | 1.16 s | 141 MB | 1392 | 4.48 to 4.61 |
| sparql-join | 80000 | jena | 5.845 s ±4% | 8.81 s | 743 MB | 1392 | 4.48 to 4.56 |
| sparql-optional-filter | 20000 | lean | 1.074 s ±20% | 0.97 s | 67 MB | 2428 | 3.95 to 3.95 |
| sparql-optional-filter | 20000 | oxigraph | 0.313 s ±20% | 0.30 s | 56 MB | 2428 | 4.51 to 4.55 |
| sparql-optional-filter | 20000 | jena | 3.826 s ±10% | 6.18 s | 405 MB | 2428 | 4.55 to 4.67 |
| sparql-optional-filter | 40000 | lean | 2.255 s ±10% | 2.00 s | 114 MB | 4870 | 3.95 to 4.2 |
| sparql-optional-filter | 40000 | oxigraph | 0.598 s ±8% | 0.57 s | 84 MB | 4870 | 4.69 to 4.69 |
| sparql-optional-filter | 40000 | jena | 4.384 s ±6% | 7.34 s | 542 MB | 4870 | 4.56 to 4.69 |
| sparql-optional-filter | 80000 | lean | 4.769 s ±13% | 4.68 s | 195 MB | 9768 | 4.01 to 4.2 |
| sparql-optional-filter | 80000 | oxigraph | 1.171 s ±12% | 1.14 s | 141 MB | 9768 | 4.63 to 4.63 |
| sparql-optional-filter | 80000 | jena | 9.753 s ±48% | 9.91 s | 772 MB | 9768 | 4.38 to 7.8 |
| rdfc-iri | 25000 | lean | 0.583 s ±59% | 0.53 s | 90 MB | 9140d087a6bd9ea6 | 3.72 to 3.78 |
| rdfc-iri | 25000 | oxigraph | 0.448 s ±68% | 0.33 s | 63 MB | 9140d087a6bd9ea6 | 9.17 to 9.17 |
| rdfc-iri | 25000 | rdf-canonize | 21.561 s ±9% | 11.31 s | 89 MB | 9140d087a6bd9ea6 | 21.63 to 24.13 |
| rdfc-iri | 25000 | npm | 3.467 s ±55% | 1.93 s | 264 MB | 9140d087a6bd9ea6 | 25.2 to 26.14 |
| rdfc-iri | 50000 | lean | 1.081 s ±67% | 1.03 s | 162 MB | 67a533c65f2caa2c | 3.66 to 3.72 |
| rdfc-iri | 50000 | oxigraph | 0.778 s ±23% | 0.64 s | 105 MB | 67a533c65f2caa2c | 8.66 to 8.69 |
| rdfc-iri | 50000 | npm | 4.196 s ±25% | 3.41 s | 494 MB | 67a533c65f2caa2c | 16.6 to 16.88 |
| rdfc-iri | 100000 | lean | 2.240 s ±28% | 2.16 s | 306 MB | fd78a6ba0579f813 | 3.61 to 3.66 |
| rdfc-iri | 100000 | oxigraph | 1.512 s ±32% | 1.42 s | 189 MB | fd78a6ba0579f813 | 6.99 to 6.99 |
| rdfc-iri | 100000 | npm | 6.824 s ±19% | 5.66 s | 873 MB | fd78a6ba0579f813 | 14.82 to 15.95 |
| rdfc-person | 5000 | lean | 0.334 s ±12% | 0.32 s | 47 MB | 07d1a396c611f0f1 | 3.56 to 3.56 |
| rdfc-person | 5000 | oxigraph | 0.178 s ±63% | 0.15 s | 49 MB | 07d1a396c611f0f1 | 5.39 to 5.39 |
| rdfc-person | 5000 | rdf-canonize | 2.231 s ±5% | 1.96 s | 90 MB | 07d1a396c611f0f1 | 13.7 to 13.73 |
| rdfc-person | 5000 | npm | 1.669 s ±21% | 1.41 s | 166 MB | 07d1a396c611f0f1 | 12.4 to 12.4 |
| rdfc-person | 10000 | lean | 0.721 s ±8% | 0.70 s | 72 MB | 4c0220890254a1d0 | 3.56 to 3.56 |
| rdfc-person | 10000 | oxigraph | 0.382 s ±3% | 0.36 s | 75 MB | 4c0220890254a1d0 | 4.87 to 4.87 |
| rdfc-person | 10000 | rdf-canonize | 9.732 s ±14% | 9.03 s | 108 MB | 4c0220890254a1d0 | 13.04 to 13.27 |
| rdfc-person | 10000 | npm | 2.602 s ±5% | 2.40 s | 237 MB | 4c0220890254a1d0 | 12.7 to 12.77 |
| rdfc-person | 20000 | lean | 1.639 s ±29% | 1.60 s | 127 MB | 75628897e2a94f4a | 3.51 to 3.56 |
| rdfc-person | 20000 | oxigraph | 0.804 s ±25% | 0.77 s | 128 MB | 75628897e2a94f4a | 4.87 to 4.87 |
| rdfc-person | 20000 | npm | 4.753 s ±10% | 3.86 s | 410 MB | 75628897e2a94f4a | 10.49 to 10.71 |
| rdfc-pairs | 2000 | lean | 0.606 s ±24% | 0.56 s | 24 MB | aed2277484f581a3 | 3.51 to 3.51 |
| rdfc-pairs | 2000 | oxigraph | 0.065 s ±10% | 0.05 s | 29 MB | aed2277484f581a3 | 4.87 to 4.87 |
| rdfc-pairs | 2000 | rdf-canonize | 0.378 s ±41% | 0.29 s | 69 MB | aed2277484f581a3 | 12.9 to 12.9 |
| rdfc-pairs | 2000 | npm | 1.610 s ±24% | 1.39 s | 131 MB | aed2277484f581a3 | 11.84 to 12.0 |
| rdfc-pairs | 4000 | lean | 2.075 s ±7% | 2.04 s | 27 MB | 3fe79d4bce6afb88 | 3.47 to 3.47 |
| rdfc-pairs | 4000 | oxigraph | 0.100 s ±9% | 0.08 s | 35 MB | 3fe79d4bce6afb88 | 4.72 to 4.72 |
| rdfc-pairs | 4000 | rdf-canonize | 0.468 s ±24% | 0.40 s | 82 MB | 3fe79d4bce6afb88 | 12.35 to 12.38 |
| rdfc-pairs | 4000 | npm | 4.058 s ±8% | 3.30 s | 136 MB | 3fe79d4bce6afb88 | 12.71 to 13.61 |
| rdfc-pairs | 8000 | lean | 10.229 s ±6% | 9.97 s | 33 MB | 84015726b01cb1d9 | 3.43 to 3.61 |
| rdfc-pairs | 8000 | oxigraph | 0.203 s ±23% | 0.18 s | 48 MB | 84015726b01cb1d9 | 4.72 to 4.72 |
| rdfc-pairs | 8000 | rdf-canonize | 0.927 s ±10% | 0.89 s | 104 MB | 84015726b01cb1d9 | 10.18 to 10.18 |
| rdfc-pairs | 8000 | npm | exit1 (10.353 s) | — | 149 MB | — | 13.32 to 13.32 |
| owl-rl-closure | skos | lean | 0.071 s ±41% | 0.06 s | 25 MB | 915 | 1.86 to 1.86 |
| owl-rl-closure | skos | jena-owl-micro | 1.668 s ±9% | 3.34 s | 148 MB | 1023 | 1.86 to 2.12 |
| owl-rl-closure | foaf | lean | 0.102 s ±18% | 0.08 s | 27 MB | 1872 | 2.12 to 2.12 |
| owl-rl-closure | foaf | jena-owl-micro | 1.877 s ±7% | 3.48 s | 161 MB | 1909 | 2.11 to 2.12 |
| owl-rl-closure | prov-o | lean | 0.195 s ±8% | 0.17 s | 30 MB | 3266 | 2.11 to 2.11 |
| owl-rl-closure | prov-o | jena-owl-micro | 1.828 s ±6% | 3.88 s | 147 MB | 3240 | 2.11 to 2.34 |
| owl-rl-closure | bfo | lean | 0.140 s ±16% | 0.13 s | 29 MB | 3837 | 2.34 to 2.34 |
| owl-rl-closure | bfo | jena-owl-micro | 2.019 s ±17% | 4.07 s | 158 MB | 3675 | 2.31 to 2.34 |
| owl-rl-closure | pizza | lean | 0.410 s ±10% | 0.39 s | 47 MB | 12813 | 2.53 to 2.53 |
| owl-rl-closure | pizza | jena-owl-micro | 2.296 s ±7% | 5.15 s | 238 MB | 10804 | 2.53 to 2.64 |
| owl-rl-closure | wine | lean | 4.765 s ±11% | 4.68 s | 89 MB | 28855 | 2.59 to 2.64 |
| owl-rl-closure | wine | jena-owl-micro | 7.405 s ±254% | 12.00 s | 548 MB | 26650 | 2.58 to 4.3 |
| owl-rl-closure | schema.org | lean | 2.840 s ±18% | 2.70 s | 108 MB | 60770 | 4.73 to 4.75 |
| owl-rl-closure | schema.org | jena-owl-micro | 19.868 s ±4% | 25.36 s | 1658 MB | 43793 | 4.77 to 4.83 |
| owl-rl-closure | ro | lean | 11.259 s ±10% | 11.02 s | 77 MB | 42736 | 4.6 to 4.71 |
| owl-rl-closure | ro | jena-owl-micro | 8.584 s ±28% | 15.96 s | 849 MB | 36703 | 4.76 to 5.1 |
| owl-rl-closure | cl-basic | lean | 13.443 s ±6% | 13.17 s | 446 MB | 163444 | 4.54 to 4.95 |
| owl-rl-closure | cl-basic | jena-owl-micro | 8.632 s ±3% | 19.21 s | 619 MB | 149426 | 3.67 to 4.03 |
| owl-dl-consistent | skos | lean | 0.068 s ±17% | 0.05 s | 24 MB | true | 3.37 to 3.37 |
| owl-dl-consistent | skos | hermit | 0.991 s ±19% | 0.88 s | 77 MB | true | 11.4 to 11.4 |
| owl-dl-consistent | foaf | lean | 0.143 s ±36% | 0.13 s | 26 MB | true | 3.37 to 3.37 |
| owl-dl-consistent | foaf | hermit | 1.065 s ±12% | 1.06 s | 75 MB | true | 10.66 to 10.8 |
| owl-dl-consistent | prov-o | lean | 0.592 s ±16% | 0.56 s | 30 MB | true | 3.37 to 3.37 |
| owl-dl-consistent | prov-o | hermit | 1.591 s ±38% | 1.56 s | 82 MB | true | 10.04 to 10.11 |
| owl-dl-consistent | bfo | lean | 1.394 s ±15% | 1.38 s | 33 MB | true | 3.34 to 3.37 |
| owl-dl-consistent | bfo | hermit | 1.289 s ±1% | 1.16 s | 79 MB | true | 8.49 to 8.62 |
| owl-dl-consistent | pizza | lean | 0.775 s ±6% | 0.73 s | 43 MB | true | 3.31 to 3.34 |
| owl-dl-consistent | pizza | hermit | 1.371 s ±27% | 1.36 s | 82 MB | true | 7.58 to 8.01 |
| owl-dl-consistent | wine | lean | 18.778 s ±6% | 18.45 s | 80 MB | true | 3.31 to 3.59 |
| owl-dl-consistent | wine | hermit | 2.135 s ±11% | 3.74 s | 110 MB | true | 5.82 to 5.9 |
| owl-dl-consistent | schema.org | lean | 43.751 s ±1% | 43.13 s | 104 MB | true | 3.86 to 4.14 |
| owl-dl-consistent | schema.org | hermit | 1.402 s ±14% | 2.57 s | 134 MB | true | 4.66 to 4.8 |
| owl-dl-consistent | qudt | lean | 55.830 s ±9% | 54.70 s | 1351 MB | false | 3.91 to 4.84 |
| owl-dl-consistent | qudt | hermit | 6.480 s ±67% | 11.50 s | 470 MB | false | 4.35 to 4.72 |
| owl-dl-consistent | ro | lean | TIMEOUT (600.013 s) | — | 2 MB | — | 5.35 to 5.35 |
| owl-dl-consistent | ro | hermit | 14.628 s ±7% | 22.04 s | 1609 MB | true | 4.71 to 5.27 |
| owl-dl-consistent | cl-basic | lean | TIMEOUT (600.005 s) | — | 2 MB | — | 5.91 to 5.91 |
| owl-dl-consistent | cl-basic | hermit | 3.360 s ±5% | 6.02 s | 284 MB | true | 4.8 to 4.9 |
