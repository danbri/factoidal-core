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

<!-- RESULT -->

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

<!-- TABLES -->

## 7. What this method cannot see

- A row measures a command line, including process start, reading the file and
  writing the answer. Oxigraph runs inside Python, Jena and HermiT inside a
  JVM; for small inputs the start of the process is most of the time (row
  `start`).
- Jena uses more than one thread (JIT compiler, garbage collector), so its CPU
  time is above its wall time. Lean, Serd and Oxigraph's parsers use one.
- The load average was about 4 on 4 CPUs through the run (two other agents).
  Wall times carry that load. The Lean default `parse` of N-Triples was
  bimodal under it (100,000 triples: 0.67 to 1.78 s over five runs); the
  median of five is in the table.
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
- The OWL RL rows compare different rule sets (section 2).
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
