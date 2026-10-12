# Lean against F*: performance survey of 2026-10-10

Date: 2026-10-10. Branch: `claude/wt-perf-survey`, base commit `267457c4`.
Owner goal, 2026-10-09, verbatim: "complete performant suite all in lean4".

This record answers three questions. Where is the Lean engine slow, against the
F* engine and against its own input size? What did the worst rows cost and what
repaired them? Which ranked rows are still open, with their numbers?

## 1. Result

The survey has 48 rows: parse, parse and serialise, SPARQL query, RDFS and OWL RL
closure on synthetic shapes and on real vocabularies, RDFC-1.0, SHACL and
JSON-LD. 45 were measured before and after the repairs; 3 (DISTINCT,
COUNT(DISTINCT), ORDER BY) were added late and are measured after only.

**Before the repairs**, 34 of the 45 rows were ranked, and Lean reached the
120 s cap on the RDFS closure of schema.org and of QUDT while F* did not. The
worst ratios, Lean time over F* time: TriG parse 124 (40,000 triples), RDFC-1.0
105 to 222, RDFS closure 34 to 178, Turtle output 67, GROUP BY 49 to 57.

**Nine commits repair them**, one cause each. Output is unchanged in every case;
section 4 gives the proof or the byte comparison for each.

| # | Commit | Change | Measured effect (Lean, before to after) |
|---|---|---|---|
| 1 | `e73aafec` | RDFS closure: indexed rounds, proved equal | chain 160: 358.6 s to 1.21 s (F*: 0.66 s); dense 2,000: 131.7 s to 0.85 s |
| 2 | `7f0cc8ec` | TriG parser: linear time | 40,000 triples: 108 s to 0.30 s (F*: 0.87 s) |
| 3 | `f5b38771` | Turtle pretty-printer: merge sort for the prefix table, proved equal | 10,000 paragraphs: 71.5 s to 3.0 s |
| 4 | `4fa638ec` | RDFC-1.0: merge sort in five places, proved equal | 4,000 IRIs, no blank nodes: 25.5 s to 0.35 s |
| 5 | `a59dbd5b` | SPARQL GROUP BY: hash-indexed grouping | GROUP BY ?s, 5,000 paragraphs: over 120 s to 1.45 s (F*: 9.6 s) |
| 6 | `db7a3c96` | Process start: test fixtures out of the executables | `version`: 43.1 ms to 7.4 ms of CPU time |
| 7 | `e4f15713` | OWL RL closure: the command line runs the indexed loop | chain 80: 8.58 s to 0.22 s (F*: 1.24 s); schema.org: over 120 s to 6.4 s |
| 8 | `4d8cafbd` | `parse`: count without the N-Quads and JSON round trip | gene 80,000 paragraphs: 17.1 s to 1.3 s; 3,659 MB to 256 MB |
| 9 | `acb8e060` | RDFC-1.0: string comparison through Lean's native order, proved equal | 2,000 IRIs: 1.07 to 0.47 billion instructions |

**After the repairs**, of the 44 rows with a ratio, Lean is at or below the F*
time on 22, between 1.0 and 2.0 times on 14, and above 2.0 times on 8. The 8:
query-q1 to q6 (2.8 to 4.6 times), shacl-person (3.7), ser-ttl-gene (3.6).
Two more rows, measured late, are open: COUNT(DISTINCT) (28.7 times at 5,000
paragraphs, quadratic) and ORDER BY (4.2 times). Section 5 lists all 15 ranked
rows with their numbers, causes and the repair each needs.

**Proof status.** Proved equal to the superseded code as lists: RDFS closure,
Turtle prefix sort, RDFC sorts, RDFC string order, TriG dataset accumulator,
GROUP BY bucket soundness, OWL RL (existing theorem, now used). Not proved, with
guards and byte comparisons in their place: the TriG reader's fuel and position
change, the GROUP BY array-and-index fold, the command line `parse` count.

**Gates after the last commit**, all equal to the values before the first:
SPARQL 1.1 650 pass, 0 fail (out of 650); RDF 1.1 1041 pass (out of 1041); RDF
1.2 1358 pass (out of 1358); RDFC-1.0 86 pass (out of 86), `l4rdfc-probe` 63 of
63, 1 of 1, 21 of 21, 1 of 1; OWL probe RL 1233 pass, 222 fail, 2 skip (out of
1457); SHACL core 1.0 98, SPARQL 1.0 22, core 1.2 138, SPARQL 1.2 25 pass (out
of the same), equal to the baseline binary; JSON-LD API 791 pass, 0 fail, 2
local-override (out of 793); RDF semantics 29 pass (out of 29); `Wasm/native-smoke.sh`
143 pass, 0 fail (out of 143); full `lake build` exits 0 (1290 jobs); the scaling
gate 12 pass, 0 fail (out of 12). The Lean hygiene audit reports 0 sorry, 0
axiom, 0 native_decide, 0 unsafe, 0 implemented_by and 166 partial def; the
baseline file `tools/lean-partial-def-baseline.txt` says 171, a gap that comes
from the base commit and not from this branch, so the file is unchanged here.

## 2. Method, and what it cannot see

**Machine.** 4 CPUs, 15 GB, Linux 6.18, shared with up to two other agents. The
load average was 2 to 15 during the baseline survey, 5 to 11 during the survey
after the repairs, and 34 to 45 during one GROUP BY run. Every number in the
tables has its load average beside it. Use the ratio between the two engines; absolute
times vary with load.

**Programs.**

* Lean before: `l4factoidal`, `l4shacl` and `l4jsonld-api` built with
  `lake build` from the base commit, copied once and used through
  `BENCH_LEAN_BIN_DIR` (a `lake build` during a survey replaces the binaries).
* Lean after: the same three programs built from the last commit of this branch.
* F*: `bin/linux-x86_64/factoidal`, built by `bash ./build-ocaml.sh compile`
  from the committed `.ml`. Nothing in `formal/fstar` changed.

**What one number is.** The wall time from process start to process exit, the
minimum of 3 runs. A case whose first run took more than 15 s was run once. A
run that took more than 120 s was killed and is shown as ">120 (cap)". CPU time
and peak resident set size of the fastest run are in the JSON lines. The time
includes reading the file and starting the process (F*: 6 ms; Lean before the
start-up repair: 43 ms; Lean after: 7 ms).

**Growth per doubling.** Lean wall time at 2n divided by Lean wall time at n,
for the last doubling whose smaller case took at least 0.05 s. 2.0 is linear.
An n log n cost gives 2.1 to 2.3 at these sizes. 4.0 is quadratic.

**Ranked.** A row is ranked when, at its largest size where both engines
finished, Lean takes more than 2.0 times the F* time, or when its growth per
doubling is more than 2.5 and the larger case took at least 0.2 s. Where Lean
reached the cap and F* did not, the ratio is a lower bound. Since section 10
(https://github.com/danbri/factoidal/issues/729) a row is also ranked when, at
that size, the Lean peak resident set is more than 3 times the F* one
(`--report` prints both peaks and their ratio). The first three rounds ranked
by time only, so a query that held 9 times the F* memory did not rank.

**Inputs.** The generators are in `tools/bench_lean_vs_fstar.py`; the files are
written to `/tmp/factoidal-bench-lean-vs-fstar` and not committed.

* Real data: slices of `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`
  (888,949 triples; a "paragraph" is one statement block of the file, about 4.4
  triples), and the vocabularies in `third_party/vocabularies` (SKOS, FOAF,
  Dublin Core Terms, schema.org with 21,721 lines, QUDT).
* Generated: N-Triples and N-Quads (IRIs; and a mix of IRIs, plain, language
  tagged and typed literals and blank nodes), Turtle (prefixed names; and a rich
  form with predicate lists, object lists and nested blank nodes), TriG (50
  triples per graph), RDF/XML (one `rdf:Description` per triple), RDFC-1.0
  inputs of four shapes, SHACL (4 property shapes over n `ex:Person` nodes) and
  five closure shapes (`tools/bench_closure.py`: chain, tree, diamond, wideflat,
  dense).
* The UK Parliament corpus (331 MB of TriG) and its endpoint are not in the
  checkout; only the 24 `.rq` files are. The SPARQL rows use `gene.ttl` and the
  six queries of `tools/bench_competitive_queries.py`, plus GROUP BY ?s,
  DISTINCT, COUNT(DISTINCT) and ORDER BY rows added here.

**Commands compared.** Lean `parse` prints the quad count; F* `count`. Lean
`query FILE --query-string Q`; F* `query --data FILE -e Q`. Lean `parse --out
nquads|turtle`; F* `dump-nq`, `dump-turtle`. Lean `canonicalize`; F*
`canonicalize`. Lean `closure --regime rdfs|owl-rl`; F* `entail`. Lean `l4shacl
--conforms-only` on a one-entry manifest (its time includes reading the
manifest); F* `shacl`. JSON-LD: the Lean `l4jsonld-api --scale` builds the
document in process, the F* `jsonld` reads it from a file.

What the method cannot see (anti-pattern 28):

1. A row measures a command line. The Lean command line wraps every operation in
   the JSON envelope of the wasm ABI (sections 3.1 and 4.8). A ratio on such a row compares
   two programs, which include the plumbing around the parser or the evaluator.
   Section 6.1 is the case where this nearly produced a wrong ranking.
2. A row has one input shape. A quadratic cost in another shape stays hidden.
   The RDFS closure of a chain, a diamond and a dense schema grew by 4.5 to 27.6
   per doubling; a wide flat schema grew by only 3.2.
3. Callgrind counts instructions. It does not see page faults, cache misses or
   allocation volume. Resident set size, read from `wait4`, found the memory use
   of section 6.1 and the profile did not.
4. The SPARQL rows are 6 queries and 4 further shapes (GROUP BY ?s, DISTINCT,
   COUNT(DISTINCT), ORDER BY). Property
   paths, EXISTS, MINUS, sub-selects, SERVICE, UPDATE, JSON-LD framing and
   compaction, and ShEx are not measured here.
5. Four-point ladders (the closure shapes) give a growth figure with large
   noise; the last doubling is the most informative and the least stable.
6. Two measurements of one case at different loads differ by up to 25 percent
   (one binary measured twice at the same size gave 5.0 and 6.3 s of CPU time).
   Only ratios above about 1.3 are results.

## 3. The survey

Columns: `n` is the size of the case compared. `Lean s before` and `F* s` come
from the baseline survey; `Lean s after`, the second `F* s` and `Lean/F* after`
come from the survey with the binaries of the last commit. `growth` is the Lean
growth per doubling. `load` is the larger load average of the two cases.
"not run" means an earlier size reached the cap.

| row | n | Lean s before | F* s | Lean/F* before | growth before | load | Lean s after | F* s | Lean/F* after | growth after | load |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| parse-nt | 160000 triples | 6.519 | 1.853 | 3.5 | 3.3 | 11 | 2.147 | 2.294 | 0.9 | 2.0 | 10 |
| parse-nt-mixed | 80000 triples | 3.369 | 0.976 | 3.5 | 3.5 | 10 | 0.997 | 1.152 | 0.9 | 2.4 | 10 |
| parse-nq | 80000 triples | 3.936 | 1.356 | 2.9 | 2.6 | 9 | 2.011 | 1.450 | 1.4 | 2.6 | 10 |
| parse-ttl | 80000 triples | 1.487 | 0.952 | 1.6 | 1.9 | 8 | 0.566 | 1.132 | 0.5 | 2.1 | 10 |
| parse-ttl-rich | 80000 triples | 2.547 | 0.588 | 4.3 | 3.1 | 8 | 0.321 | 0.574 | 0.6 | 1.9 | 11 |
| parse-ttl-gene | 80000 paragraphs | 17.1 | 2.983 | 5.7 | 3.4 | 9 | 1.296 | 2.975 | 0.4 | 2.1 | 10 |
| parse-trig | 40000 triples | 108 | 0.870 | 124.2 | 3.9 | 8 | 0.301 | 0.953 | 0.3 | 2.0 | 8 |
| parse-rdfxml | 40000 triples | 3.674 | 1.742 | 2.1 | 1.6 | 14 | 2.015 | 1.504 | 1.3 | 1.8 | 8 |
| ser-nq-nt | 80000 triples | 2.400 | 1.989 | 1.2 | 1.3 | 15 | 1.750 | 1.858 | 0.9 | 2.0 | 7 |
| ser-nq-ttl-gene | 40000 paragraphs | 8.868 | 7.176 | 1.2 | 3.1 | 15 | 6.911 | 9.061 | 0.8 | 3.0 | 8 |
| ser-ttl-gene | 10000 paragraphs | 71.5 | 1.063 | 67.2 | 4.0 | 15 | 3.045 | 0.858 | 3.6 | 2.7 | 8 |
| query-q1 | 80000 paragraphs | 9.198 | 2.745 | 3.4 | 2.1 | 13 | 11.8 | 2.992 | 4.0 | 2.1 | 6 |
| query-q2 | 80000 paragraphs | 9.680 | 2.704 | 3.6 | 2.5 | 11 | 15.7 | 3.434 | 4.6 | 2.0 | 6 |
| query-q3 | 80000 paragraphs | 8.757 | 3.154 | 2.8 | 2.2 | 11 | 11.1 | 3.700 | 3.0 | 2.4 | 5 |
| query-q4 | 80000 paragraphs | 11.1 | 3.751 | 2.9 | 2.6 | 13 | 15.1 | 4.423 | 3.4 | 2.5 | 4 |
| query-q5 | 20000 paragraphs | 45.0 | 0.790 | 57.0 | 5.3 | 11 | 2.583 | 0.916 | 2.8 | 3.3 | 4 |
| query-q6 | 80000 paragraphs | 11.1 | 4.353 | 2.6 | 2.5 | 4 | 14.3 | 5.077 | 2.8 | 2.2 | 6 |
| rdfc-iri | 4000 n | 25.5 | 0.114 | 222.5 | 5.3 | 2 | 0.168 | 0.123 | 1.4 | 2.4 | 4 |
| rdfc-uniq | 1000 n | 7.099 | 0.068 | 104.8 | 4.1 | 3 | 0.129 | 0.071 | 1.8 | 2.4 | 4 |
| rdfc-person | 1000 n | 11.9 | 0.112 | 106.7 | 4.5 | 4 | 0.163 | 0.154 | 1.1 | 2.5 | 4 |
| rdfc-chain | 200 n | 1.963 | 0.943 | 2.1 | 4.2 | 4 | 1.738 | 0.995 | 1.7 | 4.9 | 4 |
| shacl-person | 4000 n | 23.6 | 5.812 | 4.1 | 6.6 | 4 | 23.3 | 6.232 | 3.7 | 6.4 | 6 |
| jsonld-torf-hub | 2000 n | 0.090 | 0.148 | 0.6 | 1.6 | 4 | 0.084 | 0.166 | 0.5 | - | 4 |
| jsonld-torf-fanout | 2000 n | 0.049 | 0.058 | 0.8 | - | 4 | 0.033 | 0.058 | 0.6 | - | 4 |
| jsonld-torf-bnode | 2000 n | 0.066 | 0.082 | 0.8 | - | 4 | 0.070 | 0.094 | 0.8 | - | 4 |
| jsonld-torf-graphs | 2000 n | 0.056 | 0.079 | 0.7 | - | 4 | 0.055 | 0.095 | 0.6 | - | 4 |
| jsonld-torf-wide | 2000 n | 0.028 | 0.125 | 0.2 | - | 4 | 0.028 | 0.144 | 0.2 | - | 4 |
| rdfs-chain | 80 n | 11.2 | 0.115 | 97.6 | 15.2 | 4 | 0.199 | 0.126 | 1.6 | 2.9 | 5 |
| rdfs-tree | 512 n | 7.469 | 0.168 | 44.6 | 4.5 | 3 | 0.210 | 0.159 | 1.3 | 1.8 | 5 |
| rdfs-diamond | 128 n | 54.9 | 0.308 | 178.1 | 27.6 | 3 | 0.410 | 0.402 | 1.0 | 6.0 | 5 |
| rdfs-wideflat | 2000 n | 7.727 | 0.230 | 33.6 | 3.2 | 3 | 0.229 | 0.228 | 1.0 | 2.1 | 5 |
| rdfs-dense | 1000 n | 26.0 | 0.364 | 71.5 | 4.7 | 4 | 0.327 | 0.452 | 0.7 | 1.7 | 4 |
| owlrl-chain | 80 n | 8.577 | 1.236 | 6.9 | 17.8 | 4 | 0.148 | 1.287 | 0.1 | - | 4 |
| owlrl-wideflat | 1000 n | 2.826 | 0.568 | 5.0 | 3.7 | 4 | 0.117 | 0.575 | 0.2 | 1.9 | 4 |
| owlrl-dense | 500 n | 5.541 | 8.486 | 0.7 | 4.0 | 4 | 0.167 | 8.248 | 0.0 | 2.1 | 4 |
| rdfs-vocab-skos | file | 0.137 | 0.019 | 7.3 | - | 5 | 0.039 | 0.028 | 1.4 | - | 3 |
| owlrl-vocab-skos | file | 0.276 | 0.154 | 1.8 | - | 5 | 0.056 | 0.143 | 0.4 | - | 3 |
| rdfs-vocab-foaf | file | 0.274 | 0.034 | 8.0 | - | 5 | 0.058 | 0.042 | 1.4 | - | 3 |
| owlrl-vocab-foaf | file | 0.926 | 0.250 | 3.7 | - | 5 | 0.096 | 0.261 | 0.4 | - | 3 |
| rdfs-vocab-dcterms | file | 0.353 | 0.057 | 6.1 | - | 5 | 0.067 | 0.065 | 1.0 | - | 3 |
| owlrl-vocab-dcterms | file | 0.767 | 0.361 | 2.1 | - | 5 | 0.114 | 0.359 | 0.3 | - | 3 |
| rdfs-vocab-schemaorg | file | >120 (cap) | 1.879 | - | - | 5 | 2.097 | 1.718 | 1.2 | - | 3 |
| owlrl-vocab-schemaorg | - | - | - | - | - | - | - | - | - | - | - |
| query-groupby-subject | 2500 paragraphs | 61.2 | 1.247 | 49.1 | 4.4 | 6 | 0.393 | 1.430 | 0.3 | 3.0 | 7 |
| rdfs-vocab-qudt | file | >120 (cap) | 95.9 | - | - | 41 | 53.6 | 101 | 0.5 | - | 12 |
| owlrl-vocab-schemaorg | file | >120 (cap) | >120 (cap) | - | - | 4 | 5.602 | >120 (cap) | <0.05 | - | 3 |
| owlrl-vocab-qudt | file | not run | not run | - | - | - | 79.7 | see note | - | - | 12 |
| query-distinct | 10000 paragraphs | not run | not run | - | - | - | 2.466 | 16.6 | 0.15 | 3.1 | 3 |
| query-count-distinct | 5000 paragraphs | not run | not run | - | - | - | 21.0 | 0.731 | 28.7 | 3.9 | 2 |
| query-orderby | 10000 paragraphs | not run | not run | - | - | - | 2.250 | 0.538 | 4.2 | 2.4 | 6 |

### 3.1 Where the dominant cost was

Callgrind (`valgrind --tool=callgrind`, inclusive instruction counts; `perf` is
not installed) on the smallest input of a ranked row, Lean binary before the
repair unless the row says "after". The percentages are shares of the
instructions of the whole command.

| Rows | Command and input profiled | Dominant cost (share of all instructions) | Binary |
|---|---|---|---|
| rdfs-* | `closure --regime rdfs`, dense schema, n=125 | `RDFS.addAll` to `Graph.add` to `Graph.mem` to `Triple.eqb`: 82 % (`Triple.eqb` 62 %); `stepConclusions` 7 % | before |
| owlrl-* | `closure --regime owl-rl`, chain, n=40 | `memB` list scan (`List.any`, `Triple` equality 64 %): 83 %, reached from `OWL.RL.addAll` and `addOne` (77 %); `stepConclusions` 15 % | before |
| parse-trig | `parse --format trig`, 2,500 triples | `readGraphBody` and `readTriGStatement`: 77 to 78 % | before |
| ser-ttl-gene | `parse --out turtle`, 1,250 paragraphs | `sortStrs` and `insertStr` (insertion sort of the prefix table): 55.7 %; `turtleOfGraphAuto` 67.7 % | before |
| rdfc-* | `canonicalize`, no blank nodes, n=500 | `insertSortedBy` to `strLe`: 91 %; `lean_string_data` 51 % | before |
| rdfc-* | `canonicalize`, no blank nodes, n=2,000 | `strLe` 56.5 % (`lean_string_data` 39 %; the comparator of `dedupQQuads` 28 %) | after 4.4 |
| rdfc-* | the same | `parseNQuadsFast` 56.6 % (the command line parses N-Quads text twice); JSON decode of the result 18 %; `Canonical.canonicalize` itself 3.7 % | after 4.9 |
| query-q5, groupby | `query` GROUP BY ?p, gene, 2,500 paragraphs | `groupWhere` to `addToGroups`: 57 %; `keysEqual` 36 % | before |
| parse-* | `parse`, N-Triples, 20,000 triples | `Ops.parseToDatasetJson` 62 %, of which the parser `parseNTriples` is 39 %; JSON encode 22 %; JSON decode in `parseEnvelope` 27 % | before |
| parse-ttl-* | `parse --format turtle`, gene, 5,000 paragraphs | `parseTurtle` 92.6 %: `readTurtleIri` 65 %, `mkIri` and `isIri` 36 %; `lean_string_data` 27 % | after 4.8 |
| parse-rdfxml | `parse --format rdfxml`, 5,000 triples | `RdfXml.nodeElement` 71.9 %: `XML.splitQName` 53 % (called by `findNsAttr` and `resolveAttributeName`, which convert a string to a list and back); `lean_string_data` 28.7 % | after 4.8 |
| query-q1 to q6 | `query` COUNT(*), gene, 5,000 paragraphs | `Ops.queryDataset` 80 %: `parseNQuadsFast` 74.7 % (the command line parses the N-Quads text it wrote from the Turtle parse; `readIriRef` 47 %, `isIri` 22 %); the Turtle parse 17.8 %; `Index.ofGraph` 4.3 % | after |
| ser-ttl-gene | `parse --out turtle`, gene, 2,500 paragraphs | `serializeTurtle` 61 %: `turtleOfGraphAuto` 33 % (`candidateNamespaces` and `nsSplit` 22 %), `parseNQuadsFast` 26 %; JSON decode 19 %; `parseToDatasetJson` 19 % | after 4.3 |
| shacl-person | `l4shacl`, 500 persons | `SHACL.objectsOf` (a `List.filter` of the whole data graph): 74.6 %, called from `evalPathFuel` 44.9 % and `isShaclInstance` 32.2 % for each focus node | unchanged |

### 3.2 Per-size ladders of the repaired rows

**rdfs-chain** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 10 | 0.097 | 0.010 | 0.005 | 0.008 | 4 | 5 |
| 20 | 0.133 | 0.025 | 0.010 | 0.015 | 4 | 5 |
| 40 | 0.740 | 0.069 | 0.031 | 0.036 | 4 | 5 |
| 80 | 11.2 | 0.199 | 0.115 | 0.126 | 4 | 5 |

**rdfs-diamond** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 0.073 | 0.017 | 0.011 | 0.009 | 3 | 5 |
| 32 | 0.152 | 0.028 | 0.017 | 0.014 | 3 | 5 |
| 64 | 1.987 | 0.069 | 0.062 | 0.062 | 3 | 5 |
| 128 | 54.9 | 0.410 | 0.308 | 0.402 | 3 | 5 |

**rdfs-tree** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 64 | 0.139 | 0.028 | 0.015 | 0.018 | 4 | 5 |
| 128 | 0.344 | 0.045 | 0.028 | 0.031 | 4 | 5 |
| 256 | 1.647 | 0.117 | 0.067 | 0.065 | 4 | 5 |
| 512 | 7.469 | 0.210 | 0.168 | 0.159 | 3 | 5 |

**rdfs-wideflat** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 250 | 0.230 | 0.031 | 0.028 | 0.030 | 2 | 5 |
| 500 | 0.710 | 0.058 | 0.053 | 0.064 | 3 | 5 |
| 1000 | 2.393 | 0.110 | 0.107 | 0.116 | 3 | 5 |
| 2000 | 7.727 | 0.229 | 0.230 | 0.228 | 3 | 5 |

**rdfs-dense** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 125 | 0.511 | 0.053 | 0.045 | 0.043 | 3 | 5 |
| 250 | 1.533 | 0.107 | 0.079 | 0.084 | 3 | 5 |
| 500 | 5.588 | 0.191 | 0.154 | 0.183 | 3 | 5 |
| 1000 | 26.0 | 0.327 | 0.364 | 0.452 | 4 | 4 |

**parse-trig** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 10000 | 6.299 | 0.071 | 0.143 | 0.131 | 8 | 8 |
| 20000 | 27.7 | 0.152 | 0.315 | 0.331 | 8 | 8 |
| 40000 | 108.1 | 0.301 | 0.870 | 0.953 | 8 | 8 |
| 80000 | >120 (cap) | 0.589 | 3.090 | 2.783 | 11 | 8 |

**ser-ttl-gene** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 5000 | 18.1 | 1.669 | 0.440 | 0.429 | 14 | 8 |
| 10000 | 71.5 | 3.045 | 1.063 | 0.858 | 15 | 8 |
| 20000 | >120 (cap) | 6.420 | exit ? | exit ? | 15 | 7 |
| 40000 | not run | 17.6 | exit ? | exit ? | 13 | 6 |

**rdfc-iri** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 500 | 0.482 | 0.025 | 0.019 | 0.021 | 2 | 4 |
| 1000 | 2.218 | 0.048 | 0.033 | 0.033 | 2 | 4 |
| 2000 | 4.782 | 0.070 | 0.064 | 0.066 | 2 | 4 |
| 4000 | 25.5 | 0.168 | 0.114 | 0.123 | 2 | 4 |

**rdfc-uniq** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 125 | 0.129 | 0.026 | 0.008 | 0.014 | 2 | 4 |
| 250 | 0.362 | 0.025 | 0.017 | 0.022 | 2 | 4 |
| 500 | 1.712 | 0.055 | 0.039 | 0.039 | 3 | 4 |
| 1000 | 7.099 | 0.129 | 0.068 | 0.071 | 3 | 4 |

**rdfc-person** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 125 | 0.182 | 0.021 | 0.000 | 0.017 | 3 | 4 |
| 250 | 0.586 | 0.039 | 0.012 | 0.027 | 3 | 4 |
| 500 | 2.647 | 0.065 | 0.048 | 0.047 | 4 | 4 |
| 1000 | 11.9 | 0.163 | 0.112 | 0.154 | 4 | 4 |

**query-q5** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 5000 | 2.566 | 0.548 | 0.209 | 0.237 | 11 | 4 |
| 10000 | 8.517 | 1.339 | 0.371 | 0.444 | 11 | 4 |
| 20000 | 45.0 | 2.583 | 0.790 | 0.916 | 11 | 4 |
| 40000 | >120 (cap) | 5.317 | 1.739 | 1.999 | 11 | 4 |
| 80000 | not run | 17.5 | 3.471 | 4.017 | 6 | 5 |

**query-groupby-subject** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 1250 | 13.9 | 0.197 | 0.286 | 0.292 | 6 | 7 |
| 2500 | 61.2 | 0.393 | 1.247 | 1.430 | 6 | 7 |
| 5000 | >120 (cap) | 1.454 | 9.588 | 6.491 | 22 | 7 |
| 10000 | not run | 2.423 | 41.2 | 29.4 | 23 | 8 |
| 20000 | not run | 7.289 | >120 (cap) | >120 (cap) | 22 | 6 |

**owlrl-chain** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 10 | 0.069 | 0.013 | 0.020 | 0.027 | 4 | 4 |
| 20 | 0.065 | 0.018 | 0.038 | 0.052 | 4 | 4 |
| 40 | 0.482 | 0.037 | 0.189 | 0.190 | 4 | 4 |
| 80 | 8.577 | 0.148 | 1.236 | 1.287 | 4 | 4 |

**owlrl-wideflat** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 125 | 0.118 | 0.027 | 0.065 | 0.060 | 4 | 4 |
| 250 | 0.250 | 0.033 | 0.112 | 0.104 | 4 | 4 |
| 500 | 0.770 | 0.062 | 0.238 | 0.225 | 4 | 4 |
| 1000 | 2.826 | 0.117 | 0.568 | 0.575 | 4 | 4 |

**owlrl-dense** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 62 | 0.198 | 0.026 | 0.581 | 0.536 | 4 | 4 |
| 125 | 0.456 | 0.064 | 1.216 | 1.272 | 4 | 4 |
| 250 | 1.393 | 0.080 | 2.998 | 3.191 | 4 | 4 |
| 500 | 5.541 | 0.167 | 8.486 | 8.248 | 4 | 4 |

**parse-ttl-gene** (seconds, wall)

| n | Lean before | Lean after | F* (before run) | F* (after run) | load before | load after |
|---:|---:|---:|---:|---:|---:|---:|
| 5000 | 0.578 | 0.083 | 0.198 | 0.181 | 8 | 11 |
| 10000 | 1.228 | 0.207 | 0.376 | 0.366 | 8 | 11 |
| 20000 | 2.727 | 0.352 | 0.752 | 0.780 | 9 | 11 |
| 40000 | 4.973 | 0.623 | 1.481 | 1.418 | 9 | 10 |
| 80000 | 17.1 | 1.296 | 2.983 | 2.975 | 9 | 10 |


## 4. The repairs

One commit each. Every one keeps the output of the command unchanged. Where a
proof was cheap the commit has it; where it was not, the commit says "not
proved" and names the byte comparison and the guards that stand in for it.

### 4.1 RDFS closure: indexed rounds (`e73aafec`)

* **Rows.** rdfs-chain, -tree, -diamond, -wideflat, -dense, rdfs-vocab-*.
* **Cause.** `RDFS.step` read each premise by scanning the graph
  (`triplesWithPredicate`, `objectsOf`) and added each conclusion with
  `Graph.add`, which scans again. One round cost O(n^2) and the loop runs one
  round per derivation depth. Callgrind, dense 125: `Graph.add` to `Graph.mem`
  to `Triple.eqb` is 82 percent.
* **Change.** `StepIndex` (hash buckets by predicate, and by subject and
  predicate, in graph order), the `Ix` twin of each of the six row functions,
  `stepFast`, `closureFast`, and the same for the full RDFS loop. Duplicate
  removal uses `FastGraph` (new module `RDF/FastGraph.lean`, moved from
  `Syntax/NQuadsFast.lean`): buckets keyed on subject, predicate and
  `Term.joinKey`, with `Triple.eqb` deciding membership inside a bucket.
  `@[csimp]` makes every later caller of `closure` and `fullClosureLoop` use
  the fast function.
* **Proved.** Each fast function returns the same LIST as the scanning one
  (`rdfs7ForIx_eq` to `rdfs5ForIx_eq`, `stepConclusionsIx_eq`, `stepFast_eq`,
  `closureFast_eq`, `fullStepFast_eq`, `fullClosureLoopFast_eq`), from the
  invariant `FastGraph.Inv`. The definitions of `closure` and `fullClosureLoop`,
  and every theorem about them, are unchanged.
* **Evidence.** Output byte-identical for chain 40 and 80, diamond 64, dense
  500, wideflat 1000, tree 512 in the rdfs, rho-df and rdfs-plus regimes (18
  comparisons, 0 differ). Chain 160: 358.6 s before, 1.21 s after (F*: 0.66 s).
  Scaling rows: rdfs-closure-wideflat, -dense, -tree.

### 4.2 TriG parser: linear time (`7f0cc8ec`)

* **Rows.** parse-trig.
* **Cause.** `readGraphBody` and `parseTriGStatements` computed `List.length`
  of the whole remaining input at every statement (the fuel and the no-progress
  guard), appended `acc ++ ts` per statement, and added each triple to the
  dataset with `addQuad` (a `Graph.add` scan). Callgrind, 2,500 triples:
  `readGraphBody` and `readTriGStatement` are 77 percent.
* **Change.** The reader follows `Syntax.Turtle.parseStatements`: fuel is the
  input length plus 2 and declines once per statement; the no-progress guard
  compares positions; the triples of a block collect newest first and are
  reversed once; the dataset is built with the `FastDataset` accumulator of
  `Syntax/NQuadsFast.lean`. The old reader is kept as `parseTriGSpec`.
* **Proved.** `addTriplesToFast_toDataset`: a statement's triples denote the same
  dataset under the indexed accumulator as under `addQuad`. **Not proved:** the
  fuel and position change. Stand-ins: 7 `#guard` lines comparing `parseTriG`
  with `parseTriGSpec` on 20 documents in both RDF modes, including the error
  message and offset; sabotage check (dropping the final reverse fails the
  build); 420 of 420 W3C `.trig` files byte-identical in standard output,
  standard error and exit status.
* **Evidence.** 40,000 triples: 108 s before, 0.30 s after (F*: 0.87 s).
  Scaling rows: trig-parse, trig-big-graph.

### 4.3 Turtle pretty-printer: merge sort for the prefix table (`f5b38771`)

* **Rows.** ser-ttl-gene.
* **Cause.** `turtleOfGraphAuto` sorts one namespace string per IRI occurrence
  (about three per triple) with a list insertion sort. Callgrind, 1,250
  paragraphs: `sortStrs` and `insertStr` are 55.7 percent and the share grows
  with n.
* **Change.** `sortStrs := List.mergeSort`. The insertion sort stays as
  `sortStrsSpec`.
* **Proved.** `sortStrs_eq`: both return a sorted permutation of the input and
  `<=` on `String` is antisymmetric, so the lists are equal.
* **Evidence.** Byte-identical on 9 of 9 files (gene slices of 2,500 and 5,000
  paragraphs, SKOS, FOAF, Dublin Core Terms, two ontologies, two generated
  files). 10,000 paragraphs: 71.5 s before, 3.0 s after. Scaling row:
  turtle-serialize.

### 4.4 RDFC-1.0: merge sort for the five sorts that grow with the dataset (`4fa638ec`)

* **Rows.** rdfc-iri, -uniq, -person.
* **Cause.** `canonicalize` sorted with `sortBy`, a stable insertion sort, in
  five places. Callgrind, 500 IRIs: `insertSortedBy` and `strLe` are 91 percent.
* **Change.** `sortByFast := List.mergeSort` in `sortStrings`, `dedupQQuads`,
  `groupByHfdq`, `processCollisionMembers` and the issued-identifier list.
  `sortBy` stays as the specification.
* **Proved.** `sortBy_eq_mergeSort` for every transitive, total `le`, ties
  included: both are the unique permutation sorted under `List.zipIdxLE`, the
  comparator that breaks ties by input position.
* **Evidence.** 13 of 13 generated files byte-identical. No blank nodes, 4,000
  quads: 25.5 s before, 0.35 s after. Scaling rows: rdfc-iri, rdfc-person.

### 4.5 SPARQL GROUP BY: hash-indexed grouping (`a59dbd5b`)

* **Rows.** query-q5, query-groupby-subject.
* **Cause.** `addToGroups` compared each row's key with every group and appended
  the row with `++ [mu]`. Callgrind, q5 on 2,500 paragraphs: `groupWhere` is 57
  percent, `keysEqual` 36.
* **Change.** `groupSolutionsFast`: an array of groups in creation order with
  their rows newest first (reversed once), and a hash index from a key bucket to
  the groups of that bucket. `erBucket` is constant on order-equal values
  (integer, decimal and double share one bucket).
* **Proved.** `literalOrder_eq_zero`, `erEqual_erBucket`,
  `keysEqual_keyBucket`: the bucket never hides a match. **Not proved:** that
  the array-and-index fold returns the list `addToGroups` returns. Stand-ins:
  15 `#guard` lines on 26 key shapes in 1, 2, 3 and 7 cycles, with group sizes
  and row order; 6 of 6 queries byte-identical; SPARQL 1.1 aggregates 47 of 47
  and grouping 6 of 6; sabotage check (every row a new group fails the build).
* **Evidence.** GROUP BY ?s, 5,000 paragraphs: over 120 s before, 1.45 s after
  (F*: 9.6 s). Scaling rows: group-by-few, group-by-many.
* **Not changed.** `COUNT(DISTINCT ...)` uses `dedupEr`, a list scan (section 5).

### 4.6 Process start: five modules' test fixtures (`db7a3c96`)

* **Rows.** Every small row.
* **Cause.** Lean evaluates a top-level constant when the module is initialised.
  Five modules held 70,000-byte literals, SHA-256 hashes and encoded blocks as
  `private def`s next to their `#guard`s. Callgrind on `l4factoidal version`:
  304,962,107 instructions, of which 5 hashes of a 70 KB literal are 209
  million.
* **Change.** The checks moved, unchanged, into `TermWireV2Tests`,
  `IndexedBlockWireV5Tests`, `PagedTermDictionaryV2Tests`, `BlockV5PlanTests`
  and `InflateTests`. The umbrella imports them (so `lake build` runs every
  `#guard`); no executable does.
* **Evidence.** 25,590,678 instructions after. CPU time, minimum of 15 runs, load
  35: 43.1 ms before, 7.4 ms after (F*: 5.7 ms). About 25 million instructions
  of start-up cost remain in `GeoBBoxIndexWire`, `TermLocalIndexWire` and
  `SubjectRowIndexWireV2`. The wasm module runs the same initialisation when it
  is instantiated. Scaling row: startup (at most 20 ms).

### 4.7 OWL RL closure: the command line runs the indexed loop (`e4f15713`)

* **Rows.** owlrl-chain, -wideflat, -dense, owlrl-vocab-*.
* **Cause.** `closure --regime owl-rl`, `owl-consistent`, `owl-entails` and the
  SPARQL entailment-regime dispatch called `OWL.RL.closure` and `closureFix`, the
  scanning loop. `RLClosureIndexed.lean` has had the indexed loop, with
  `indexedClosure_eq` (same list at every fuel), since August; only the probe
  harness called it. Callgrind, chain 40: `List.any` in `memB` is 83 percent,
  reached from `addAll` and `addOne`.
* **Change.** Two `csimp` theorems: `closure = indexedClosure` and
  `closureFix = closureFixIndexed`. `RegimeDispatch` imports
  `RLClosureIndexed` so that its call is replaced.
* **Proved.** `indexedClosure_eq` (existing). The two `csimp` theorems follow
  from it.
* **Evidence.** 15 of 15 `closure --regime owl-rl` outputs, 7 of 7
  `owl-consistent` and 2 of 2 `owl-entails` outputs identical. Chain 80: 8.58 s
  before, 0.22 s after (F*: 1.24 s). schema.org: over 120 s before, 6.4 s after
  (F*: over 120 s). The existing differential guards would compare the indexed
  loop with itself after the `csimp`; they now compare with `closureScan`
  (section 6.2). Scaling row: owlrl-closure-chain.

### 4.8 Command line `parse`: the count without the N-Quads and JSON round trip (`4d8cafbd`)

* **Rows.** parse-nt, -nt-mixed, -nq, -ttl, -ttl-rich, -ttl-gene, -trig, -rdfxml.
* **Cause.** Section 6.1. `parse` without `--out` asked `Ops.parseToDatasetJson`,
  which writes the dataset as canonical N-Quads inside a JSON string, and then
  parsed that JSON to read one number: 49 percent of the instructions on 20,000
  N-Triples (JSON encode 22, JSON decode 27) and 3,659 MB of resident memory on
  80,000 paragraphs of `gene.ttl`.
* **Change.** `parseCountOutput` calls `Ops.parseTextToDataset` and prints
  `datasetQuadCount`, and the parser's error text. `--out nquads` and
  `--out turtle` are unchanged.
* **Proved.** Nothing; the function is IO plumbing. 14 `#guard` lines compare it
  with the count read back from the envelope on N-Triples, Turtle, TriG,
  N-Quads, empty input, malformed input and an unknown format, and check the
  values.
* **Evidence.** 4,138 of 4,138 comparisons of standard output, standard error
  and exit status, baseline against new: every `.ttl`, `.nt`, `.nq`, `.trig` and
  `.rdf` file under `third_party/testing/w3c/rdf/rdf11` and `rdf12` (2,666 exit
  0, 1,460 exit non-zero with the same text), with and without `--out nquads`,
  seven generated files and five usage cases. Peak resident set size, 80,000
  paragraphs: 3,659 MB before, 256 MB after (F*: 76 MB).

### 4.9 RDFC-1.0: string comparison through Lean's native order (`acb8e060`)

* **Rows.** rdfc-iri, -uniq, -person.
* **Cause.** After 4.4, `strLe` built two character lists per comparison:
  56.5 percent of the instructions on 2,000 IRIs, `lean_string_data` 39 percent.
* **Change.** `strLeFast a b := !decide (b < a)`, registered with `@[csimp]`
  right after `strLe`.
* **Proved.** `charsLe_eq_not_lt` for all lists, by induction with
  `List.cons_lt_cons_iff`; `strLe_eq_not_lt`.
* **Evidence.** 1,066,857,749 instructions before, 465,133,591 after. 12 of 12
  outputs byte-identical to the baseline binary. 9 new guards, one of which
  compares the native order with `charsLe` on all pairs of 18 strings.

## 5. Rows that remain ranked

Later rounds: COUNT(DISTINCT) and shacl-person were repaired in section 8;
query-q1 to q6, ORDER BY and ser-ttl-gene in section 9 (9.3 has the numbers
after); the peak memory of query-q1 and q2 in section 10. The table below is
the state after the first round.

Ranked by the rule in section 2, after all repairs, from the survey with the
binaries of the last commit. The coordinator opens one issue per row; the links
are missing because this branch has no issue numbers yet. Each open row also
needs a test that fails today and is marked as an expected failure naming its
issue (CLAUDE.md, "A stated shortfall"); the coordinator adds both when the
issue exists. A row marked
"F* same" has the same growth in the F* engine, so the algorithm that the
specification names causes the cost.

| row | n | Lean s | F* s | Lean/F* | Lean growth | F* growth | load |
|---|---|---:|---:|---:|---:|---:|---:|
| query-q2 | 80000 paragraphs | 15.7 | 3.434 | 4.6 | 2.0 | 1.4 | 6 |
| query-q1 | 80000 paragraphs | 11.8 | 2.992 | 4.0 | 2.1 | 1.7 | 6 |
| shacl-person | 4000 n | 23.3 | 6.232 | 3.7 | 6.4 | 4.1 | 6 |
| ser-ttl-gene | 10000 paragraphs | 3.045 | 0.858 | 3.6 | 2.7 | 2.0 | 8 |
| query-q4 | 80000 paragraphs | 15.1 | 4.423 | 3.4 | 2.5 | 2.0 | 4 |
| query-q3 | 80000 paragraphs | 11.1 | 3.700 | 3.0 | 2.4 | 2.1 | 5 |
| query-q5 | 20000 paragraphs | 2.583 | 0.916 | 2.8 | 3.3 | 2.0 | 4 |
| query-q6 | 80000 paragraphs | 14.3 | 5.077 | 2.8 | 2.2 | 2.3 | 6 |
| rdfc-chain | 200 n | 1.738 | 0.995 | 1.7 | 4.9 | 5.1 | 4 |
| parse-nq | 80000 triples | 2.011 | 1.450 | 1.4 | 2.6 | 1.7 | 10 |
| rdfs-diamond | 128 n | 0.410 | 0.402 | 1.0 | 6.0 | 6.4 | 5 |
| ser-nq-ttl-gene | 40000 paragraphs | 6.911 | 9.061 | 0.8 | 3.0 | 2.3 | 8 |
| query-groupby-subject | 2500 paragraphs | 0.393 | 1.430 | 0.3 | 3.0 | 4.5 | 7 |

Two rows measured late, with Lean and F* in the same run (final binary; load 2
to 6; no baseline run, because the code path is unchanged by the repairs):

| row | n paragraphs | Lean s | F* s | Lean/F* | Lean growth |
|---|---:|---:|---:|---:|---:|
| query-count-distinct | 1,250 | 1.320 | 0.080 | 16.5 | |
| query-count-distinct | 2,500 | 5.384 | 0.243 | 22.2 | 4.1 |
| query-count-distinct | 5,000 | 21.0 | 0.731 | 28.7 | 3.9 |
| query-count-distinct | 10,000 | >60 (cap) | 2.594 | >23 | |
| query-orderby | 1,250 | 0.199 | 0.059 | 3.4 | |
| query-orderby | 2,500 | 0.543 | 0.135 | 4.0 | 2.7 |
| query-orderby | 5,000 | 1.293 | 0.290 | 4.5 | 2.4 |
| query-orderby | 10,000 | 2.250 | 0.538 | 4.2 | 1.7 |
| query-distinct | 10,000 | 2.466 | 16.608 | 0.15 | 3.1 |

The ranked rows by measured cost, largest first:

1. **query-count-distinct.** Quadratic in the number of distinct values (growth
   4.0 per doubling), 28.7 times the F* time at 5,000 paragraphs. Cause, not yet
   profiled: aggregates with DISTINCT deduplicate with `dedupEr`, a list scan
   (named in the message of `a59dbd5b`). Repair: the bucket of `erBucket` that
   `groupSolutionsFast` uses; the soundness lemmas `erEqual_erBucket` and
   `keysEqual_keyBucket` exist.
2. **shacl-person.** 3.7 times the F* time (23.3 s against 6.2 s, 4,000
   persons), growth 6.4 per doubling; F* grows 4.1, so both are quadratic.
   `SHACL.objectsOf` is a `List.filter` of the whole data graph, called for each
   focus node from `evalPathFuel` (44.9 %) and `isShaclInstance` (32.2 %).
   Repair: a subject-predicate index built once per validation, carried in
   `ValidationEnv` or in place of `data : Graph`; list-equality proof as in
   `RDFS/Closure.lean`.
3. **query-q1 to q6, ORDER BY, GROUP BY ?p (query-q5).** 2.8 to 4.6 times the F*
   time with growth 2.0 to 2.5 (q5: 3.3, F* 2.0), and 1,691 MB of resident
   memory at 80,000 paragraphs against 27 MB. 80 % of the instructions of a
   COUNT query are `Ops.queryDataset`, of which `parseNQuadsFast` is 74.7 %: the
   command line writes the Turtle parse as N-Quads text and parses the text
   again. Repair: give `Ops.queryParsedDatasetWith` the parsed `Dataset`. This
   needs `parseNQuadsFast (Dataset.toCanonicalNQuads ds) = ds` (literal canonical
   forms and blank-node labels are the doubts); without it the row order of a
   query without ORDER BY can change. The same round trip is in `canonicalize`,
   `update` and `closure`. ORDER BY was not profiled.
4. **ser-ttl-gene.** 3.6 times the F* time at 10,000 paragraphs, growth 2.7.
   `turtleOfGraphAuto` is 33 % (`candidateNamespaces`, `nsSplit` 22 %); the rest
   is the same command line round trip. F* fails on this row from 20,000
   paragraphs (stack overflow in `count_runs`), Lean does not (7.3 s at 20,000,
   19.4 s at 40,000).
5. **Rows ranked by growth only.** At or below 1.7 times the F* time:
   rdfc-chain (growth 4.9, F* 5.1: N-degree hashing of indistinguishable blank
   nodes, fixed by the specification), rdfs-diamond (6.0, F* 6.4: the closure is
   quadratic in output), query-groupby-subject (3.0, F* 4.5), parse-nq (2.6, F*
   1.7; N-Quads reader `readIriRef`/`isIri`), ser-nq-ttl-gene (3.0, F* 2.3).
6. **parse-rdfxml.** 1.3 times the F* time (2.0 s against 1.5 s, 40,000
   triples). `XML.splitQName` is 53 % of the instructions: it converts a string
   to a list and back for every attribute lookup (`findNsAttr`,
   `resolveAttributeName`).
7. **Start-up.** About 25 million instructions remain in `GeoBBoxIndexWire`,
   `TermLocalIndexWire` and `SubjectRowIndexWireV2` (7.4 ms of CPU time; F* 5.7).

The SPARQL rows cover 6 queries and 4 further shapes on `gene.ttl`. The UK
Parliament queries, property paths, EXISTS, MINUS, sub-selects, UPDATE, JSON-LD
framing and ShEx have no row. A later agent should add them before assuming the
evaluator has no further quadratic cost: COUNT(DISTINCT) was found only because
one more shape was tried.

## 6. Corrections and traps

### 6.1 The parse rows measured the command line

The first survey ranked `parse-ttl-gene` at 5.7 times the F* time with 3,659 MB
of resident memory at 80,000 paragraphs (a 6.8 MB file), and `parse-nt` at 3.5
times. The plan was to profile the Turtle parser. Callgrind on the N-Triples
file showed the parser (`parseNTriples`) at 39 percent of the instructions; the
other 61 percent was `Ops.parseToDatasetJson` writing the dataset as N-Quads in
a JSON string, and the command line parsing that JSON to print one number. With
the round trip removed, the same parsers take 0.3 to 0.9 times the F* time and
256 MB. The rule that follows, in `skills/perf-benchmarking/SKILL.md`: profile
the phases of a ranked row before attributing its ratio to a component.

### 6.2 A `csimp` makes a differential guard compare a function with itself

After `closure = indexedClosure` is registered with `@[csimp]`, the guards in
`OWL/RLTests.lean` of the form `indexedClosure g n == closure g n` run the
indexed code on both sides. The repair restates the scanning loop as
`closureScan` in the test module, proves `closureScan_eq`, and compares with it.
Any later `csimp` needs the same step. (`skills/lean4-performance/SKILL.md`.)

### 6.3 Mistakes in commit messages

Commits are pushed and cannot be amended here. The messages are wrong in these
places:

* `7f0cc8ec` says "24 #guard comparisons" for the TriG reader. The count is 7
  `#guard` lines over 20 documents in two RDF modes (40 comparisons). The
  message of `f5b38771` corrects it.
* `a59dbd5b` says "14 new #guard lines" for GROUP BY. The count is 15.
* `acb8e060` says "17 strings" in the string-order guard. The count is 18.

### 6.4 Method mistakes that cost a re-run

* A `git mv` of the harness while a background loop still called the old file
  name made four groups of rows exit with status 2 and measure nothing.
* A `lake build` in the middle of the baseline survey would have replaced the
  measured binaries. The survey uses frozen copies.
* The GROUP BY "after" rows ran at load 34 to 45 and the "before" rows at load
  6. Their wall times are not comparable; CPU time and the ratio to F*, which ran
  in the same minutes, are.
* The F* engine fails on `dump-turtle` for 20,000 paragraphs of `gene.ttl` and
  above: `Fatal error: exception Stack overflow` in
  `RDF_Turtle_Serialize.count_runs` (non-tail recursion, 8,192 KB stack). The
  survey records the exit status 2. Nothing in `formal/fstar` was changed.

## 8. Second round: issues 722, 723 and 724 (branch `claude/wt-perf-2`)

The three ranked rows of section 5 with the largest cost, one issue each. For
each, an expected-failure row was added to `tests/stack/lean_scaling.py` first
(new `XFAIL` table: a listed row counts as expected-fail while it fails and as
a failure when it passes), then the code was profiled, then repaired, then the
row was made an assertion. Binaries before: built from `c8dbe2ab`; F*:
`tools/fetch-builds.sh --set native` (`build-e7519f87314f`).

### 8.1 Aggregates with DISTINCT (https://github.com/danbri/factoidal/issues/722)

* **Cause.** `COUNT`, `SUM`, `AVG`, `MIN`, `MAX` and `GROUP_CONCAT` with
  DISTINCT removed duplicates with `dedupErAcc` (each value against every kept
  value); `COUNT(DISTINCT *)` used `distinctSolutions` (each row against every
  later row). The DISTINCT modifier already used the proved
  `distinctSolutionsFast`; REDUCED keeps every row. Callgrind, 625 paragraphs:
  `COUNT(DISTINCT ?s)` 3.70 billion instructions, `dedupErAcc` 89.1 percent
  (`strCompare` 87.9 percent inside it); `COUNT(DISTINCT *)` 1.60 billion,
  `distinctSolutions` 74.8 percent.
* **Change.** `dedupErFast` (hash buckets on `erBucket`, `csimp`);
  `COUNT(DISTINCT *)` calls `distinctSolutionsFast`.
* **Proved.** `dedupErFastGo_eq`, `dedupEr_eq_dedupErFast`,
  `evalAggregate_countDistinctStar`.
* **Evidence.** 20 of 20 query outputs identical; SPARQL 1.1 650 of 650 and 1.2
  271 of 271, logs identical.

| paragraphs | Lean before s | Lean after s | F* s | Lean/F* after | peak RSS after (Lean / F*) |
|---:|---:|---:|---:|---:|---:|
| 1,250 | 1.469 | 0.101 | 0.083 | 1.2 | 42 MB / 17 MB |
| 2,500 | 6.409 | 0.244 | 0.241 | 1.0 | 69 MB / 20 MB |
| 5,000 | 22.46 | 0.554 | 0.700 | 0.79 | 126 MB / 26 MB |
| 10,000 | >60 (cap) | 1.048 | 2.597 | 0.40 | 227 MB / 35 MB |
| 20,000 | not run | 2.668 | 10.09 | 0.26 | 439 MB / 57 MB |

Load 6 to 12. The memory column is issue 724 (8.3), not the aggregate.

### 8.2 SHACL validation (https://github.com/danbri/factoidal/issues/723)

* **Cause.** `objectsOf` filters the whole data graph; validation called it per
  focus node and property shape (`valueNodes`), and `isShaclInstance` called it
  per `sh:class` value node and per class-target subject, with `superClasses`
  reading `g.length` and filtering per step. Callgrind, 500 persons: 2.10
  billion instructions, the filter 74.6 percent. With the index alone, at 2,000
  persons: `distinctSubjects` 61.8 percent and `dedupTerms` 17.9 percent of
  3.37 billion (list scan plus `acc ++ [x]`).
* **Change.** `SHACL/DataIndex.lean`: (subject, predicate) to objects in graph
  order, and the graph length, built once by `ValidationConfig.envFor` and
  carried in `ValidationEnv.dataIx`; indexed twins of the path evaluation, the
  SHACL-instance test and the `sh:class` check. `distinctSubjects` and
  `dedupTerms` get hash forms registered with `csimp`.
* **Proved.** Every twin returns the same list under a coherent index
  (`evalPathFuelIx_eq` over the four mutual functions, `isShaclInstanceIx_eq`,
  `simpleValueCheckIx_eq`, ...), `DataIndex.ofGraph_coherent`, and the two
  `csimp` equalities. `conformance_iff` and three theorems that use it now take
  `env.dataIx.Coherent g`; `envFor_dataIx_coherent` discharges it, so
  `validate_conforms_iff` is unchanged.
* **Evidence.** SHACL Core 1.0, SHACL-SPARQL 1.0, 1.2 core, 1.2 sparql, node
  expressions and rules: runner logs byte-identical to the binary before.

| persons | Lean before s | Lean after s | F* s | Lean/F* after |
|---:|---:|---:|---:|---:|
| 500 | 0.263 | 0.029 | 0.169 | 0.17 |
| 1,000 | 1.149 | 0.051 | 0.540 | 0.09 |
| 2,000 | 4.123 | 0.111 | 1.879 | 0.06 |
| 4,000 | 27.81 | 0.242 | 7.498 | 0.03 |

Peak RSS at 4,000: 27 MB before and after (F*: 38 MB). Load 4 to 6.

### 8.3 The command line's N-Quads round trip (https://github.com/danbri/factoidal/issues/724): open

* **Measured.** Row `query-vs-parse` (new row kind: a verb against `parse` of
  the same file, at most 2.0 times the CPU time and the peak memory). 5,000
  paragraphs: `query` COUNT(*) 0.463 s and 125 MB, `parse` 0.081 s and 34 MB
  (5.7 and 3.7 times). It is an expected failure naming the issue.
* **Why not repaired here.** `Dataset.toCanonicalNQuads` followed by
  `parseNQuadsFast` is not the identity on a parsed dataset: the canonical form
  writes language tags in lower case, and the N-Quads reader keeps each quad of
  a graph once, while the Turtle reader keeps a repeated triple (a `#guard` in
  `SHACL/ShaclTests.lean` shows a Turtle graph with a repeated triple). Giving
  the parsed dataset to the query directly can therefore change answers
  (`COUNT(*)` over a file with a repeated triple; the case of a language tag in
  a result). Measured on a three-line Turtle file with one triple written
  twice and a tag `@EN`: `parse` prints 3, `parse --out nquads` prints the
  repeated line twice with `@en`, and `query` `COUNT(*)` prints 2. The two
  verbs disagree today; an RDF graph is a set, so 2 is the count RDF 1.1
  Concepts gives. The repair needs a function on `Dataset` proved equal to the round
  trip (lower-case language tags, one quad per graph, graphs of one name
  merged), or a decision that the round trip's normalisation is not wanted.
  Neither was done in the time. Repaired in section 9.2.

### 8.4 Gates after the last commit of this round

Each equal to the run with the binaries before 8.1, and each runner log
byte-identical: SPARQL 1.1 manifest-all 650 pass, 0 fail (out of 650);
SPARQL 1.2 271 pass, 0 fail (out of 271); SHACL Core 1.0 98, SHACL-SPARQL 1.0
22, SHACL 1.2 core 138, SHACL 1.2 sparql 25 pass, 0 fail (out of the same);
SHACL 1.2 node expressions 140 pass, 0 fail, 2 unsupported (out of 142);
SHACL 1.2 rules 88 pass (out of 88); RDF 1.1 1041 pass (out of 1041); RDF 1.2
1358 pass (out of 1358); RDFC-1.0 86 pass (out of 86); RDF semantics 29 pass
(out of 29); `l4rdfc-probe` 63 of 63, 1 of 1, 21 of 21, 1 of 1.
`Wasm/cli-smoke.sh` 53 pass, 0 fail (out of 53); `Wasm/native-smoke.sh` 282
pass, 0 fail (out of 282; not run before 8.1). Full `lake build` exits 0 (1314
jobs). `tests/stack/lean_scaling.sh`: 15 pass, 0 fail, 1 expected-fail (out of
16), the expected failure being `query-vs-parse` (issue 724). Lean hygiene
audit: 0 sorry, 0 axiom, 0 native_decide, 0 unsafe, 0 implemented_by, 166
partial def (unchanged).

### 8.5 ORDER BY: profiled, recorded

Callgrind, `ORDER BY ?s ?p LIMIT 20`, 1,250 paragraphs, binary after 8.2: 1.72
billion instructions. `sortSolutionsFast` (Lean's merge sort, already n log n)
57.8 percent, of which `sparqlOrder` 54.5 and `strCompare` 53.6 percent
(`lean_string_data` 36.2, `utf8_decode` 23.6: `strCompare` converts both
strings to character lists); the N-Quads round trip of 8.3 28.9 percent. The
repair is a `csimp` from `strCompare` to Lean's native string order, proved as
`charsLe_eq_not_lt` was for RDFC-1.0 (section 4.9); it rebuilds every SPARQL
module and was not done in the time. It would also speed up `COUNT(DISTINCT)`,
whose remaining cost after 8.1 is the same comparison. Repaired in section 9.1.

## 9. Third round: string order and the command line's round trip (branch `claude/wt-perf-3`)

Two repairs, in this order: SPARQL string comparison (section 8.5) and the
N-Quads round trip of the command line
(https://github.com/danbri/factoidal/issues/724, section 8.3). Binaries
before: built from `0c834393` and copied once. F*: `tools/fetch-builds.sh
--set native` (`build-19c2f705e3e8`). Callgrind counts are from 1,250
paragraphs of `gene.ttl`.

### 9.1 SPARQL string order

* **Cause.** `strCompare` built two character lists per comparison (section
  8.5: 53.6 percent of an ORDER BY).
* **Change.** `strCompareFast a b := if a < b then -1 else if a = b then 0
  else 1` (`String.decidableLT` and `String.decEq`, native code), registered
  with `@[csimp]` directly after `strCompare` in `SPARQL/Expr.lean`, so every
  ordering compiled after it uses it: ORDER BY (`sparqlOrder`), the GROUP BY
  and DISTINCT-aggregate keys (`erEqual`, `keysEqual`), MIN and MAX, and `<`
  on IRIs and literals (`valueCompare`).
* **Proved.** `listCharCompare_eq_lt` (induction with
  `List.cons_lt_cons_iff`), `strCompare_eq_fast`,
  `strCompare_eq_strCompareFast`. The definition of `strCompare` and every
  theorem about it are unchanged.
* **Evidence.** Output identical: ORDER BY on 1,250 paragraphs, the 151
  command-line comparisons of 9.2, and the SPARQL runner logs of 9.4. Guards: the native
  order against `listCharCompare` on all pairs of 18 strings (the list form is
  not rewritten, so the guard compares two programs), and 8 `sparqlOrder` /
  `erEqual` cases.

| query (1,250 paragraphs) | before | after 9.1 | after 9.1 and 9.2 |
|---|---:|---:|---:|
| `ORDER BY ?s ?p LIMIT 20` | 1,716,385,516 | 800,708,680 | 366,846,454 |
| `COUNT(DISTINCT ?s)` | 778,899,813 | 721,044,169 | 286,573,651 |
| `GROUP BY ?p` (q5) | 805,789,131 | 725,867,375 | 291,628,516 |
| `MIN(?o) MAX(?o) ... GROUP BY ?p` | 962,084,714 | 733,651,811 | 299,423,335 |

Instructions executed (callgrind). After 9.1 the sort comparator of ORDER BY
fell from 984 to 68 million instructions. Other character-list comparisons on
the query path: after 9.1, evaluation is 2.7 to 4.2 percent of the
instructions of COUNT(DISTINCT), GROUP BY and MIN/MAX, and no comparison that
builds a list is above 1 percent; the rest was the round trip of 9.2. Nothing
else needed a repair.

### 9.2 The command line's round trip (issue 724)

* **Decision** (coordinator, on the issue, from the specification): RDF 1.1
  Concepts §3, "An RDF graph is a set of RDF triples", and §3.3, "Lexical
  representations of language tags MAY be converted to lower case." The round
  trip's normalisation stays; it becomes a function on `Dataset`.
* **Change.** `RDF/DatasetNormalize.lean`: `normalizeDataset` lower-cases
  every language tag (inside triple terms too) and adds the quads, in the
  order of the canonical document, to the accumulator `parseNQuadsFast` uses
  (`addQuadFast`: one copy per graph by `Triple.eqb`, graphs of one name
  merged). `Wasm/Ops/FromDataset.lean`: `withOpsDataset`. The ops gain `*Of`
  forms over a parsed dataset (`queryDatasetOf`, `updateDatasetOf`,
  `canonicalizeOf`, `owlClosureOf`, `rhoDfClosureOf`, `rdfsPlusClosureOf`,
  `owlIsConsistentOf`, `owlEntailsOf`, `serializeTurtleTextOf`); the text ops
  call the same `*Parsed` bodies, unchanged. `Wasm/Cli.lean`: `query`,
  `update`, `canonicalize`, `closure`, `owl-consistent` and `owl-entails` call
  the `*Of` forms; `parse` prints the size of `normalizeDataset`; `parse
  --out nquads|turtle` print the op's text without the JSON envelope.
* **Proved.**
  `parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode = .ok (normalizeDataset ds)`
  for both modes, for every `ds` with `roundTripSafe mode ds`
  (`parseNQuadsFast_toCanonicalNQuads`). The hypothesis is a decidable check
  of the terms: IRIs print-safe (`iriPrintSafe`; `RDF.isIri` admits a space,
  IRIREF does not), blank-node labels in BLANK_NODE_LABEL, language tags (lower
  case) in LANGTAG with subtags of 1 to 8 characters, no lexical-form
  character that the canonical form writes as a `\u` escape (the proof reads
  back the seven ECHAR escapes; a dataset with such a character takes the
  text path), and in RDF 1.1 mode no triple term and no base direction. It mentions neither the parser nor the serialiser (anti-pattern
  29: the conclusion is not among the premises). `datasetForOps` returns
  `normalizeDataset ds` when the check passes and the text round trip
  otherwise; `datasetForOps_eq` proves it equal to the text round trip for
  EVERY dataset. From it: `queryDatasetOf_eq`, `updateDatasetOf_eq`,
  `canonicalizeOf_eq`, `owlClosureOf_eq`, `rhoDfClosureOf_eq`,
  `rdfsPlusClosureOf_eq`, `owlIsConsistentOf_eq`, `owlEntailsOf_eq` and
  `serializeTurtleTextOf_eq`: each op on the parsed dataset answers the
  envelope the text op answers on its canonical N-Quads, byte for byte. So the
  answers of the command line, and the row order of a query without ORDER BY,
  are unchanged. **Not proved:** that encoding a string into the JSON envelope
  and decoding it gives the string back (`parse --out` and the error text);
  the byte comparison below stands in for it.
* **What changed on purpose.** `parse` counts the set: on issue 724's
  three-line file (one triple written twice, a tag `@EN`) `parse` and `query`
  `COUNT(*)` both print 2 (before: 3 and 2). `parse --out nquads` still prints
  the parser's list, repeated line included.
* **Cost of the check.** The first `roundTripSafe` read each IRI through
  `String.toList`: 36.2 percent of the instructions of `query` `COUNT(*)`, as
  much as the Turtle parse (37.3). `iriPrintSafeFast` (`String.all`, proved
  equal by `String.all_bool_eq`, `csimp`) took it to 21.3 percent.
* **Evidence.**
  * Callgrind, `query` `COUNT(*)`: 705,734,080 instructions before,
    271,560,893 after (`parseNQuadsFast` was 70 percent before; after, the
    Turtle parse is 46 percent and the check 21). `parse --out turtle`:
    2,023,194,174 before, 887,506,064 after. `canonicalize` of the same
    file: 1,321,391,256 before, 868,571,357 after.
  * Byte comparison, standard output, standard error and exit status, binary
    before against binary after: every `.ttl`, `.nt`, `.nq`, `.trig` and `.rdf`
    file under `third_party/testing/w3c/rdf/rdf11` and `rdf12` (2,087 files):
    `query` (all quads, no ORDER BY) 2,087 of 2,087 identical, `canonicalize`
    2,087 of 2,087 identical, `parse --out nquads`, `--out turtle` and `--out bogus` 2,090 of 2,090 identical each (the 2,087 files, two `gene.ttl` slices and the three-line file). `parse`: 2,081 identical, 6 differ,
    each by the number of repeated triples in the file (five EARL reports and
    `turtle12-eval-annotation-07.ttl`, which states `:s :p :o` twice).
    On 1,250 and 5,000 paragraphs of `gene.ttl`: the six survey queries, DISTINCT,
    COUNT(DISTINCT ?s) and COUNT(DISTINCT *), two ORDER BY forms, GROUP BY ?s,
    MIN and MAX, `SELECT *` with and without LIMIT and OFFSET, a join without
    ORDER BY, FILTER EXISTS, FILTER NOT EXISTS, MINUS, OPTIONAL with FILTER, a
    sub-SELECT, CONSTRUCT, DESCRIBE, ASK, GRAPH and a string FILTER, each with
    and without `--table`; two updates; `canonicalize`; the four closure
    regimes; five closure shapes with `owl-consistent`; generated RDFC-1.0
    inputs; the vocabularies: 151 of 151 identical. `owl-entails` on nine
    premise and conclusion pairs: 9 of 9 identical.
  * Guards (`RDF/DatasetNormalizeTests.lean`): the check accepts repeated
    triples, upper-case tags, escapes, blank nodes, named graphs of one name
    and nested triple terms with a base direction, and refuses an IRI with a
    space, a label ending on `.`, U+0001 in a lexical form, the tag `en--x`,
    and RDF 1.2 terms in 1.1 mode; on all of them `datasetForOps` equals the
    text round trip; `normalizeDataset` of the three-line file has 2 quads
    and the tag `en`. `Wasm/Cli.lean`: `parse` prints 2 and `query`
    `COUNT(*)` answers 2 on that file.
  * `tests/stack/lean_scaling.sh`, row `query-vs-parse` (5,000 paragraphs):
    5.7 times the CPU time and 3.7 times the peak memory of `parse` before,
    1.1 to 1.6 (two runs, load 2 and 4) and 1.0 after; the row is now an
    assertion.

### 9.3 Survey rows, before and after

`tools/bench_lean_vs_fstar.py --rows query-q1,...,query-q6,query-orderby,query-count-distinct,ser-ttl-gene --runs 3 --cap 120 --single-over 15`,
once with the binary before (`BENCH_LEAN_BIN_DIR` holding copies built from
`0c834393`) and once with the binary after; the F* binary measured in both
runs. Wall time in seconds, the minimum of up to three runs; peak resident set
size in MB of that run (`wait4`). `F* s` and `F* MB` are from the run with the
binary after; `Lean/F* before` divides by the F* time of the run before. Load
average 3 to 10. "rc2": F* exits with status 2 (stack overflow in
`count_runs`, section 6.4).

| row | n | Lean s before | Lean MB before | Lean s after | Lean MB after | F* s | F* MB | Lean/F* before | Lean/F* after | load |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| query-q1 | 5000 | 0.562 | 126 | 0.140 | 35 | 0.191 | 16 | 2.6 | 0.7 | 4 |
| query-q1 | 10000 | 1.216 | 228 | 0.341 | 51 | 0.376 | 16 | 2.7 | 0.9 | 4 |
| query-q1 | 20000 | 2.151 | 439 | 0.758 | 81 | 0.753 | 18 | 2.5 | 1.0 | 4 |
| query-q1 | 40000 | 4.911 | 857 | 1.650 | 141 | 1.486 | 22 | 2.7 | 1.1 | 4 |
| query-q1 | 80000 | 16.2 | 1694 | 3.568 | 259 | 2.952 | 28 | 5.1 | 1.2 | 4 |
| query-q2 | 5000 | 0.461 | 127 | 0.147 | 35 | 0.197 | 16 | 2.2 | 0.7 | 4 |
| query-q2 | 10000 | 0.935 | 228 | 0.402 | 51 | 0.387 | 16 | 2.5 | 1.0 | 4 |
| query-q2 | 20000 | 2.201 | 439 | 0.771 | 81 | 0.751 | 18 | 2.7 | 1.0 | 4 |
| query-q2 | 40000 | 4.598 | 857 | 1.779 | 141 | 1.442 | 22 | 3.0 | 1.2 | 4 |
| query-q2 | 80000 | 15.4 | 1694 | 3.832 | 259 | 3.010 | 28 | 4.7 | 1.3 | 3 |
| query-q3 | 5000 | 0.465 | 127 | 0.152 | 35 | 0.214 | 23 | 2.0 | 0.7 | 3 |
| query-q3 | 10000 | 1.033 | 228 | 0.286 | 51 | 0.429 | 31 | 2.0 | 0.7 | 3 |
| query-q3 | 20000 | 2.062 | 439 | 0.792 | 81 | 0.844 | 51 | 2.4 | 0.9 | 3 |
| query-q3 | 40000 | 4.496 | 857 | 1.604 | 141 | 1.741 | 89 | 2.2 | 0.9 | 3 |
| query-q3 | 80000 | 15.2 | 1694 | 3.982 | 259 | 3.872 | 167 | 4.3 | 1.0 | 4 |
| query-q4 | 5000 | 0.480 | 127 | 0.221 | 35 | 0.225 | 30 | 2.0 | 1.0 | 5 |
| query-q4 | 10000 | 1.047 | 228 | 0.303 | 51 | 0.533 | 40 | 2.2 | 0.6 | 6 |
| query-q4 | 20000 | 2.053 | 439 | 0.854 | 81 | 1.026 | 72 | 2.1 | 0.8 | 6 |
| query-q4 | 40000 | 4.974 | 857 | 1.694 | 141 | 2.060 | 124 | 2.4 | 0.8 | 6 |
| query-q4 | 80000 | 11.6 | 1694 | 3.886 | 259 | 4.449 | 233 | 2.1 | 0.9 | 6 |
| query-q5 | 5000 | 0.754 | 127 | 0.221 | 39 | 0.205 | 26 | 2.4 | 1.1 | 7 |
| query-q5 | 10000 | 1.336 | 228 | 0.362 | 54 | 0.443 | 34 | 2.8 | 0.8 | 7 |
| query-q5 | 20000 | 2.556 | 439 | 0.992 | 89 | 1.129 | 56 | 2.7 | 0.9 | 7 |
| query-q5 | 40000 | 8.194 | 857 | 2.205 | 154 | 2.151 | 96 | 3.8 | 1.0 | 7 |
| query-q5 | 80000 | 19.0 | 1694 | 6.118 | 281 | 4.437 | 174 | 4.4 | 1.4 | 8 |
| query-q6 | 5000 | 0.577 | 126 | 0.201 | 35 | 0.255 | 30 | 2.1 | 0.8 | 10 |
| query-q6 | 10000 | 1.545 | 228 | 0.530 | 51 | 0.530 | 40 | 2.9 | 1.0 | 10 |
| query-q6 | 20000 | 2.823 | 439 | 0.791 | 81 | 1.066 | 72 | 2.4 | 0.7 | 10 |
| query-q6 | 40000 | 6.779 | 857 | 1.941 | 141 | 2.173 | 124 | 2.6 | 0.9 | 9 |
| query-q6 | 80000 | 16.6 | 1694 | 5.109 | 259 | 4.866 | 233 | 3.6 | 1.1 | 8 |
| query-orderby | 1250 | 0.226 | 43 | 0.050 | 26 | 0.078 | 21 | 4.2 | 0.6 | 6 |
| query-orderby | 2500 | 0.537 | 69 | 0.107 | 30 | 0.147 | 21 | 4.2 | 0.7 | 6 |
| query-orderby | 5000 | 0.976 | 127 | 0.220 | 41 | 0.353 | 26 | 3.3 | 0.6 | 6 |
| query-orderby | 10000 | 2.086 | 228 | 0.548 | 56 | 0.638 | 44 | 3.5 | 0.9 | 6 |
| query-orderby | 20000 | 4.332 | 439 | 1.302 | 90 | 1.287 | 68 | 3.6 | 1.0 | 6 |
| query-count-distinct | 1250 | 0.108 | 43 | 0.045 | 25 | 0.092 | 21 | 1.2 | 0.5 | 5 |
| query-count-distinct | 2500 | 0.242 | 69 | 0.083 | 31 | 0.245 | 21 | 0.9 | 0.3 | 5 |
| query-count-distinct | 5000 | 0.558 | 127 | 0.178 | 39 | 0.733 | 26 | 0.8 | 0.2 | 5 |
| query-count-distinct | 10000 | 1.052 | 228 | 0.433 | 55 | 2.650 | 35 | 0.4 | 0.2 | 5 |
| query-count-distinct | 20000 | 2.865 | 439 | 0.990 | 89 | 9.355 | 57 | 0.3 | 0.1 | 5 |
| ser-ttl-gene | 5000 | 1.312 | 276 | 0.441 | 40 | 0.449 | 34 | 2.9 | 1.0 | 5 |
| ser-ttl-gene | 10000 | 3.718 | 532 | 0.971 | 59 | 0.903 | 51 | 4.1 | 1.1 | 5 |
| ser-ttl-gene | 20000 | 7.049 | 1101 | 1.898 | 99 | rc2 | - | - | - | 5 |
| ser-ttl-gene | 40000 | 18.9 | 2139 | 4.191 | 175 | rc2 | - | - | - | 5 |

At the largest sizes, Lean time over F* time before and after: q1 5.1 to 1.2,
q2 4.7 to 1.3, q3 4.3 to 1.0, q4 2.1 to 0.9, q5 4.4 to 1.4, q6 3.6 to 1.1 (80,000
paragraphs), ORDER BY 3.6 to 1.0 (20,000), COUNT(DISTINCT) 0.3 to 0.1 (20,000),
ser-ttl-gene 4.1 to 1.1 (10,000; F* fails above). Peak memory of a query at
80,000 paragraphs: 1,694 MB before, 259 to 281 MB after. By time ratio none of
the nine rows is ranked by the rule of section 2 any more (largest 1.4). By
growth per doubling, from 40,000 to 80,000 paragraphs and by CPU time (the
wall times of q5 and q6 were measured at load 8): q1 2.2, q2 2.2, q3 2.5, q4
2.3, q5 2.2, q6 2.6 (F* 2.2). q6 (OPTIONAL with FILTER) is above 2.5 and so
stays ranked by growth only, at 1.1 times the F* time; it was 2.4 before,
when the round trip hid it. Not profiled in this round.

Not repaired, and recorded here: memory. At 80,000 paragraphs a Lean query
takes 259 MB against 28 MB for F* on q1 and q2 (233 MB for both engines on q4
and q6, whose answers are large). The Lean dataset is a list of `Triple`
values built by the Turtle reader, plus the index of `indexedDatasetBackend`;
the parse alone (`parse`, 5,000 paragraphs) takes 35 MB, the same as the
query. The ranking rule of section 2 does not cover memory.

### 9.4 Gates after the last commit of this round

Each equal to the run with the binaries before 9.1, and each runner log
byte-identical: SPARQL 1.1 manifest-all 650 pass, 0 fail (out of 650); SPARQL
1.2 271 pass, 0 fail (out of 271); RDF 1.1 1041 pass, 0 fail (out of 1041); RDF
1.2 1358 pass, 0 fail (out of 1358); RDFC-1.0 86 pass, 0 fail (out of 86);
SHACL Core 1.0 98, SHACL-SPARQL 1.0 22, SHACL 1.2 core 138, SHACL 1.2 sparql
25 pass, 0 fail (out of the same); SHACL 1.2 rules 88 pass (out of 88); SHACL
1.2 node expressions 140 pass, 0 fail, 2 unsupported (out of 142).
`Wasm/cli-smoke.sh` 53 pass, 0 fail (out of 53) before, 54 pass, 0 fail (out
of 54) after (one new case: `parse` and `query` `COUNT(*)` print 2 on issue
724's file); `Wasm/native-smoke.sh` 297 pass, 0 fail (out of 297) before and
after. `tests/stack/lean_scaling.sh` 16 pass, 0 fail, 0 expected-fail (out of
16); `query-vs-parse` is an assertion. Full `lake build` exits 0 (1323 jobs).
Lean hygiene audit: 0 sorry, 0 axiom, 0 native_decide, 0 unsafe, 0
implemented_by, 166 partial def (unchanged).

## 10. Fourth round: peak memory of a query (https://github.com/danbri/factoidal/issues/729, branch `claude/wt-perf-mem`)

Section 9.3 left one cost open: at 80,000 paragraphs of `gene.ttl` a Lean
`query` peaked at 259 MB of resident memory and the F* engine at 28 MB. The
ranking rule of section 2 ranked time only, so the row did not rank. This
round measured where the memory is held, repaired the largest holder, and
added the memory rule (section 2) and two gate rows.

Binaries: before, built from `f7aa1a33` and copied once
(`l4factoidal` and the phase harness below); after, built from the last
commit of the branch and copied once. F*: `bin/linux-x86_64/factoidal` of the
core checkout. Load average 2 to 16 during the measurements; peak resident
memory does not depend on load, time does.

### 10.1 Method, and what it cannot see

* **Peak resident set**, `/usr/bin/time -v` ("Maximum resident set size"),
  one run per case, over the ladder 10,000, 20,000, 40,000, 80,000 and
  160,000 paragraphs (847,023 to 13,509,433 bytes; 160,000 is about 16
  times 10,000, so the slope is not fitted over a 4x span only, the error of
  `2026-09-05-shard-pack-profile-and-memory.md` section 3).
* **Phases.** `l4query-phases FILE --stop-after PHASE` (new,
  `formal/lean4/Harness/QueryPhases.lean`) runs the functions of `queryCmd`
  in its order: `read` (`IO.FS.readFile`), `parse`
  (`Ops.parseTextToDataset`), `normalize` (`datasetForOps`, which is
  `normalizeDataset` on these files), `index` (`indexedDatasetBackend`),
  `eval` (`queryParsedDatasetWith`), `output`. It prints `VmRSS` and `VmHWM`
  after each phase. The peak of a process that stops after a phase is the
  most that this phase and the ones before it held at one time. A diagnostic
  phase `chars` computes only `text.toList.length`.
* **Bytes per input byte** is the slope (peak at 160,000 minus peak at 10,000)
  divided by (bytes at 160,000 minus bytes at 10,000). The start-up memory of
  the process (about 12 MB for Lean, 14 MB for F*) cancels.

What it cannot see:

1. The allocator keeps and reuses freed memory. A phase that frees memory and
   a later phase that allocates the same amount do not add; the increments
   below are increments of the PEAK, not sizes of data structures.
2. Lean exposes no allocation counter, and `valgrind --tool=massif` sees the
   allocator's segments, not the objects. No heap profile was taken.
3. One query shape (COUNT) and one file. A query that returns many rows (q4,
   q6 of section 9.3) holds its answer as well.

### 10.2 Where the memory was

Peak resident set (KB) of `l4query-phases` stopping after each phase, query
`SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }`:

| paragraphs | bytes | read | parse | normalize | index | eval |
|---:|---:|---:|---:|---:|---:|---:|
| 10,000 | 847,023 | 14,324 | 42,972 | 42,928 | 42,812 | 43,012 |
| 20,000 | 1,706,149 | 16,260 | 73,908 | 73,708 | 73,712 | 73,752 |
| 40,000 | 3,399,450 | 18,204 | 135,352 | 135,080 | 135,328 | 135,272 |
| 80,000 | 6,761,194 | 24,064 | 256,140 | 256,216 | 256,064 | 256,280 |
| 160,000 | 13,509,433 | 38,944 | 499,892 | 499,872 | 500,096 | 500,032 |

Bytes of peak per input byte: read 2.0, parse 37.0, and no later phase adds
anything. At 80,000 paragraphs, `--stop-after chars` (the `String.toList` of
the file and nothing else) peaks at 255,908 KB, the same as the whole query.

**Cause.** `Syntax.parseTurtle` begins with `let cs := text.toList`. A cons
cell is 24 bytes and one allocation per character; with the allocator's
overhead the list costs 35 bytes of peak resident memory per input byte, the
whole of the peak. The parser frees the list as it reads it, so the dataset,
the normalised dataset and the index are built inside memory the list
released, and none of them raised the peak. The other causes the issue named
were checked: the input is held as `String` and as `List Char` at once (yes,
this); terms are full `String`s per occurrence (yes, but they did not set the
peak); a list of quads beside an indexed form (`normalizeDataset` builds
`quadList`, but it did not set the peak; see 10.5); the solution sequence of
COUNT is a full list (yes: the reference evaluator without the index also
peaks at 190 MB at 80,000 paragraphs after the repair; it did not set the peak
before it).

### 10.3 Repair: Turtle read without the whole-document character list

* **Change.** `Syntax/TurtleChunkFold.lean`: `parseTurtleText text base mode`.
  It reads the characters of the `String` in place (`String.foldl`), gives
  them one at a time to the statement scanner (`TurtleStatementScan`,
  `TurtleChunkFoldState.feedChar`), and reads each completed candidate with
  the reference grammar's `readStatement`, carrying `TurtleState` across
  candidates, as the shard packer has done since 2026-09-05. Only the current
  candidate is a character list. The generated blank-node prefix is computed
  from the whole text without a list (`freshBnodePrefixText`). A document
  that contains `<<` is read by `parseTurtle` (the scanner reads `<` as an
  IRIREF up to the first `>`, so inside an RDF 1.2 triple term its lexical
  mode can differ from the grammar's). When the walk fails, the document is
  read again by `parseTurtle`. `Ops.parseTextToDataset` (the input of every
  RDF verb of the command line, and of the wasm `parse`, `datasetOpen` and
  `queryDataset` family) reads Turtle with it.
* **Proved.** `freshBnodePrefixText_eq` (the prefix is
  `freshBnodePrefix`'s); `parseTurtleText_error` (every error
  `parseTurtleText` reports is the one `parseTurtle` reports, message and
  offset); `parseTurtleText_eq_of_walk` (where the walk gives `parseTurtle`'s
  answer, so does `parseTurtleText`). **Not proved:** that the walk gives
  `parseTurtle`'s graph whenever it succeeds: the chunk-boundary half of
  `2026-09-03-rdf-parsing-strategy.md` section 2.3, open since September.
  Stand-ins:
  * `#guard`s in `Syntax/TurtleChunkFoldTests.lean`: the walk ALONE equals
    `parseTurtle` on 23 accepted documents in both RDF modes, and on one more
    with a base IRI (comments, the no-dot directives, long strings holding dots and
    quotes, decimals, a dot after an integer, blank-node property lists,
    collections, a document label next to the generated prefix, empty and
    comment-only documents, relative IRIs under a changing base, prefixed
    names with dots); `parseTurtleText` equals `parseTurtle`, error included,
    on those and on 7 refused documents; the walk refuses two documents
    `parseTurtle` accepts (a `PREFIX` split over two lines, a subject `base:s`
    whose statement goes on to the next line) and `parseTurtleText` falls back
    and agrees; `hasDoubleLt` on four strings; the RDF 1.2 triple-term
    document goes to `parseTurtle`. Sabotage check: dropping the final
    reverse of the walk fails three guards.
  * The walk alone against `parseTurtle`, `l4query-phases --walk-check LIST`:
    every `.ttl` and `.nt` file of the W3C RDF 1.1 and 1.2 suites (1,130
    files), in both RDF modes, with and without a base IRI: `parseTurtle`
    accepts 3,104 cases, and the walk gives the same graph on 3,104, refuses
    0 and differs on 0; `parseTurtle` refuses 752; 664 cases contain `<<` and
    are not walked. The nine `gene.ttl` slices of 625 to 160,000 paragraphs:
    36 of 36 the same.
  * Byte comparison of standard output, standard error and exit status,
    binary before against the binary of the last commit (which also has the
    change of 10.5a): `parse`, `parse --out nquads` and `query 'SELECT *
    WHERE { ?s ?p ?o }'`, formats `turtle` and `ttl12`, with and without
    `--base`, on the 1,130 `.ttl` and `.nt` files of the W3C RDF 1.1 and 1.2
    suites and on 10,000 paragraphs of `gene.ttl`: 13,572 identical, 0
    differ, 0 timed out (out of 13,572). 166 of the W3C files contain `<<`
    and take the `parseTurtle` path. On 20,000, 40,000, 80,000 and 160,000
    paragraphs, q1, q2, `GROUP BY ?p`, `SELECT DISTINCT ?o WHERE { ?s a ?o }`,
    `parse` and `parse --out nquads`: 24 identical, 0 differ (out of 24). An
    earlier run with the binary of 10.3 alone gave 13,560 of 13,560 on the W3C
    files.
* **Found on the way.** `TurtleChunkFoldTests.lean`,
  `TurtleStatementScanTests.lean` and `Utf8StreamTests.lean` were imported by
  no module, so `lake build` never built them and their guards never ran
  (anti-pattern 28: section 2.2 of the parsing record cites "1,115 chunkings,
  0 disagreements" from the first of them). The umbrella now imports all
  three; they pass.

### 10.4 After

Peak resident set (MB), `l4factoidal query`, q1 = COUNT(*), q2 = COUNT of
`wdt:P684`, and `parse`:

| paragraphs | q1 before | q1 after | q2 after | parse before | parse after | F* q1 | Lean/F* q1 before | after |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 10,000 | 49.0 | 43.5 | 42.7 | 49.0 | 39.1 | 16.0 | 3.1 | 2.7 |
| 20,000 | 81.0 | 65.1 | 69.1 | 80.8 | 56.9 | 17.9 | 4.5 | 3.6 |
| 40,000 | 140.2 | 111.0 | 114.7 | 140.8 | 92.8 | 21.2 | 6.6 | 5.2 |
| 80,000 | 257.7 | 192.7 | 200.8 | 259.0 | 163.0 | 28.0 | 9.2 | 6.9 |
| 160,000 | 495.7 | 357.0 | 375.0 | 497.3 | 305.1 | 41.0 | 12.1 | 8.7 |

Bytes of peak per input byte: q1 37.0 before, 26.0 after; q2 27.5 after;
`parse` 37.1 before, 22.0 after; F* 2.1.

Phases after (KB, as in 10.2):

| paragraphs | read | parse | normalize | index | eval |
|---:|---:|---:|---:|---:|---:|
| 10,000 | 14,320 | 24,672 | 30,464 | 36,700 | 36,888 |
| 20,000 | 16,332 | 36,604 | 48,904 | 59,288 | 59,464 |
| 40,000 | 17,912 | 59,384 | 85,828 | 103,336 | 103,576 |
| 80,000 | 24,600 | 106,288 | 157,560 | 188,180 | 188,016 |
| 160,000 | 38,704 | 200,580 | 302,872 | 355,772 | 356,404 |

Bytes of peak per input byte, after: read 2.0, parse 14.2, normalize 22.0,
index 25.8, eval 25.8. Each later phase now raises the peak.

Time, CPU seconds (user plus system), minimum of 3 runs, the three programs
interleaved, load 2.4 to 7.3:

| case | Lean before | Lean after | F* | Lean/F* before | after |
|---|---:|---:|---:|---:|---:|
| q1, 80,000 | 4.36 | 4.76 | 3.04 | 1.4 | 1.6 |
| q2, 80,000 | 4.81 | 4.52 | 3.21 | 1.5 | 1.4 |
| `parse`, 80,000 | 2.09 | 2.43 | - | - | - |
| q1, 160,000 | 8.38 | 8.65 | 6.22 | 1.3 | 1.4 |
| q2, 160,000 | 9.73 | 8.95 | 6.18 | 1.6 | 1.4 |
| `parse`, 160,000 | 5.64 | 6.24 | - | - | - |

The walk costs `parse` 11 to 16 percent more CPU time than `parseTurtle`
(per character it advances the scanner's state and keeps the current
candidate as a reversed list, then turns each candidate into a `String` and
back into a list); a query differs by less than the noise of these runs (plus
or minus 10 percent). The F* q1 time at 160,000 is from three separate runs
(6.22 to 7.76 s): in the interleaved run one F* run ended early and its time
is not used. No row's time ratio is above 2.0.

### 10.5 What holds the memory now, and what was tried

Issue 729 stays open: Lean is 6.9 times the F* peak at 80,000 paragraphs and
8.7 times at 160,000, above the rule of section 2. In the order of the phase
table:

1. **The parsed graph**, 12 bytes per input byte above the text (about 240
   bytes per triple at 80,000 paragraphs: a list cell, a `Triple`, a `Term`
   per position and a `String` per IRI occurrence; the parser makes a new
   `String` for each prefixed name it expands, so `wdt:P684` is stored once
   per statement that writes it: 514,957 IRI tokens with 77,505 distinct
   values at 80,000 paragraphs). Tried: `internGraph` after the parse (a
   table from a string to the first equal string, carried with its
   invariant; `internGraph g = g` proved), applied in `parseTextToDataset`.
   Peak 188 to 179 MB at 80,000 paragraphs and 0.36 s more CPU time (4.43 to
   4.79 s), so it was not landed: the duplicates are allocated by the parse
   before the pass frees them. The repair to try is the same table inside
   the walk's statement step, so that a duplicate is freed as soon as it is
   read; the equality then needs a simulation lemma for the chunk fold
   (`consumeText`, `consumeCandidates`, `feedChar`) over two step functions.
2. **`normalizeDataset`**, 8 more: the `FastGraph` that removes repeated
   triples holds a key tuple, a hash-map node and two list cells per triple
   while the parsed graph is still live. Tried: `normalizeDatasetFast` (no
   `quadList`; a triple whose object has no language tag kept as the same
   value; `@[csimp]`, proved). Peak unchanged at 80,000 paragraphs (157 MB
   and 188 MB), so it was not landed. The step that would help is to remove
   repeated triples while parsing, so that the parsed graph is not live
   beside a second structure.
3. **The index** (`OWL.RL.Index.ofGraph`, built for every query): an array, a
   hash set and five hash maps of lists. COUNT(*) reads none of the maps
   (`igSearch` with no bound position returns `all`), q2 reads `byP` only.
   Repair: build each access path when a query first needs it; the SPARQL
   refinement proofs are stated over `igSearch`, which would need the same
   statement over the lazy form.
4. **The solution sequence.** `evalSelect` builds every solution before the
   aggregate counts them; the reference evaluator without the index peaks at
   190 MB at 80,000 paragraphs (`--no-index`).

### 10.5a Found while comparing: `SELECT *` is quadratic in the command line

The byte comparison of 10.3 ran `SELECT * WHERE { ?s ?p ?o }` on `gene.ttl`
slices, and a run on 20,000 paragraphs took over 100 s. Measured with the
binary of 10.3: 1,250, 2,500 and 5,000 paragraphs took 0.42, 1.84 and 9.79 s
of CPU time (growth 4.4 and 5.3 per doubling) and 63, 104 and 216 MB (F* at
5,000: 1.43 s, 26 MB). Callgrind, 1,250 paragraphs: 4.47 billion
instructions, of which `QueryResult.toSrj` 61 percent, all in `rowsJoined`
(`rowJson r ++ "," ++ rowsJoined rest` copies the text of all later rows once
per row; `memcpy` 54 percent).

* **Repaired:** an accumulator form that appends each row at the end of a
  string it owns, proved equal and registered with `@[csimp]`
  (`SPARQL/ResultsJson.lean`). This branch wrote `rowsJoinedAcc` /
  `rowsJoined_eq_rowsJoinedFast`; npm stage 5 (issue 713) repaired the same
  function independently as `rowsJoinedTR` / `rowsJoined_eq_rowsJoinedTR`
  for a stack overflow, and the merge (2026-10-10) kept that one only, since
  two `csimp` theorems for one constant cannot both stand. So `toSrj` and every theorem about it are
  unchanged and the output is the same string. Callgrind, 1,250 paragraphs:
  2.11 billion instructions after; `toSrj` 0.44 billion (2.75 before),
  `memcpy` 0.11 billion (2.39 before). The wasm `queryDataset` envelope is
  built by the same function.
* **Open:** the command line then parses the envelope as JSON
  (`parseEnvelope`, 36 percent after) and pretty-prints it (26 percent).
  `JSON.parseItems` and `parseMembers` append each item with `acc ++ [v]`,
  inside a `mutual` block, where a `csimp` does not reach (the trap recorded
  in `skills/danbri-function-precrime-checkers`), and `JSON.Chars` holds the
  whole envelope as an `Array Char`. Measured in one run, load 7: before
  0.44, 2.04 and 11.56 s and 64, 107 and 210 MB; after 0.47, 1.54 and 7.88 s
  and 65, 105 and 215 MB; F* 0.34, 0.86 and 1.61 s and 16, 19 and 25 MB
  (1,250, 2,500 and 5,000 paragraphs). The row `select-star` of
  `tests/stack/lean_scaling.py` (1,250 to 5,000 paragraphs, time at most 9
  times) is an expected failure naming issue 729. The repair is the one
  section 4.8 made for `parse`: print the result without the JSON envelope
  round trip.

### 10.6 The memory rule and the gate rows

* Section 2 now ranks a row when its Lean peak resident set at the largest
  size where both engines finished is more than 3 times the F* one.
  `tools/bench_lean_vs_fstar.py --report` prints both peaks and the ratio.
  By this rule, query-q1 and q2 rank (9.2 before, 6.9 after, at 80,000
  paragraphs); q3 to q6, for which the F* engine also holds 167 to 233 MB,
  were 1.1 to 1.6 in section 9.3 and do not.
* `tests/stack/lean_scaling.py` row `query-memory`: the bytes of peak per
  input byte of `query` COUNT(*), 10,000 to 40,000 paragraphs, at most 32.
  The whole-document `List Char` costs 35 on its own (10.2), so any path that
  builds it again fails the row. 37.8 before (expected failure naming issue
  729), 27.1 and 27.3 after (assertion).
* Row `query-memory-fstar`: the same slope, at most 6.0, which is 3 times the
  F* engine's 2.1. It is an expected failure naming issue 729 (27.2 after):
  the open part of the issue as a test that fails today.
* Row `select-star` (10.5a): expected failure naming issue 729.

### 10.7 Gates after the last commit of this round

The SPARQL, RDF and RDFC-1.0 counts are equal to those of section 9.4:
SPARQL 1.1 manifest-all 650 pass, 0 fail (out of 650); SPARQL 1.2 271 pass, 0
fail (out of 271); RDF 1.1 1041 pass, 0 fail (out of 1041); RDF 1.2 1358 pass,
0 fail (out of 1358); RDFC-1.0 86 pass, 0 fail (out of 86) (`l4w3c --quiet`
on each manifest). `Wasm/native-smoke.sh` 303 pass, 0 fail (out of 303);
`Wasm/cli-smoke.sh` 54 pass, 0 fail (out of 54).
`tests/stack/lean_scaling.sh` 17 pass, 0 fail, 2 expected-fail (out of 19),
the expected failures being `query-memory-fstar` and `select-star` (issue
729). `tests/stack/lenient_scaling.sh` 16 pass, 0 fail (out of 16). Full `lake
build` exits 0 (1360 jobs). The gates were run twice, after 10.3 and after
10.5a, with the same counts. Hygiene: the diff adds no `sorry`, `axiom`,
`native_decide`, `unsafe`, `implemented_by` or `partial def`.

### 10.8 Text for the issue

For a comment on https://github.com/danbri/factoidal/issues/729, which stays
open:

> **Partly repaired** (`claude/wt-perf-mem`, design record section 10).
> Phase measurement (`l4query-phases --stop-after PHASE`, 10,000 to 160,000
> paragraphs of `gene.ttl`): the whole peak was `parseTurtle`'s
> `text.toList`, 35 bytes of resident memory per input byte; nothing after it
> raised the peak. `Ops.parseTextToDataset` now reads Turtle with
> `parseTurtleText` (the statement scanner over the `String`, falling back to
> `parseTurtle` on `<<` and on every refusal). Not proved equal; the walk
> alone agrees with `parseTurtle` on 3,104 of 3,104 accepted W3C cases and the
> command line's output is byte-identical on 13,572 of 13,572.
> Peak, `query` COUNT(*), 80,000 paragraphs: 257.7 MB before, 192.7 MB
> after; F* 28.0 MB (6.9 times). Bytes of peak per input byte: 37.0 before,
> 26.0 after, F* 2.1. Time within 10 percent; `parse` 11 to 16 percent slower.
> Still open: the parsed graph (12 bytes per input byte, one `String` per IRI
> occurrence), `normalizeDataset`'s duplicate-removal table while the parsed
> graph is live (8), the index built for every query (4), the solution
> sequence of COUNT. Gate rows: `query-memory` (at most 32 bytes per input
> byte, passes) and `query-memory-fstar` (at most 6, expected failure naming
> this issue).
> Also found: `SELECT *` through the command line is quadratic (5,000
> paragraphs: 9.8 s and 216 MB; F* 1.4 s and 26 MB). `rowsJoined` copied the
> document once per row; repaired (an accumulator form, proved, `csimp`; in the tree as `rowsJoinedTR`). Still
> open: the command line parses the JSON envelope (`JSON.parseItems` appends
> with `acc ++ [v]` in a mutual block) and pretty-prints it. Row
> `select-star`: expected failure naming this issue.

## 11. Fifth round: `SELECT *` time and the wasm `parse()` memory (https://github.com/danbri/factoidal/issues/768 KR 2.3, branch `claude/wt-query-mem`)

Key result 2.3 of OKR batch 1: "query time and memory linear". Three rows: the
`select-star` row of `tests/stack/lean_scaling.py` (an expected failure naming
https://github.com/danbri/factoidal/issues/729 since section 10.5a), the
command line's peak memory (https://github.com/danbri/factoidal/issues/729),
and the wasm module's linear memory after `parse()` of 48,000 triples
(https://github.com/danbri/factoidal/issues/744, `MEMORY_XFAIL` of
`tests/perf/npm_speed_gate.mjs`). Base: core `a3ee3e2a`. The binaries before
are copies of that commit's `l4factoidal` and `l4query-phases`; the wasm
before is the module the coordinator built from the same commit
(sha256 `b8895465...`).

### 11.1 Method, and what it cannot see

* **Phases of `l4factoidal query`.** `l4query-phases` (section 10.1) has five
  more phases after `index`: `solutions` (the solution sequence alone, by the
  evaluator the op calls), `eval` (the op's envelope string:
  `queryParsedDatasetWith`, which computes the solutions again, then
  `QueryResult.toSrj`), `decode` (the JSON parse of the envelope that
  `Cli.parseEnvelope` makes), `render` (the text `Cli.printQueryResult`
  prints: `srj.toStringPretty`) and `output` (that text written). Each
  report line has `ms=`, the wall time since the start of the process; a phase
  is the difference of two lines of one process. `solutions` is measured in
  the process that stops after it. `tools/query_phase_ladder.py` runs the
  ladder and prints the tables below; peak resident memory is
  `/usr/bin/time`'s maximum resident set of the process that stops after the
  phase.
* **Phases of the wasm `parse()`.** `tests/perf/l4_parse_memory_ladder.mjs`
  runs each (size, phase) in its own Node child and prints `HEAPU8.byteLength`
  after the phase's dispatch calls: `load` (the engine and a one-triple
  parse), `open` (`datasetOpen`: the Turtle reader with the prefix table, the
  blank-node scope and the index, no N-Quads text), `parse1` and `parse6`
  (`parseToDatasetJson` once and six times: the op `parse()` calls, and the
  number of calls the speed gate makes), `nquads1` (`serializeNQuads` of the
  same data as N-Quads: no Turtle reader). The input is the bench's: K
  people, 3K triples. `l4query-phases FILE --parse-op` runs the same op's
  phases natively (`read`, `parse`, `scope`, `nquads`, `envelope`, `output`).

What it cannot see:

1. Wall times were measured at load averages of 4 to 41 (two other agents
   built Lean and wasm on the same 4 CPUs). A phase below about 50 ms is
   noise; the growth figures are for the phases above that.
2. Wasm linear memory grows in steps that Emscripten chooses and never
   shrinks, so a figure is an upper bound of the high-water mark, with a
   resolution of several MB.
3. One query shape for time (`SELECT *` over `gene.ttl`) and one data shape
   for the wasm memory (the bench's people).

### 11.2 `select-star` before, by phase

`SELECT * WHERE { ?s ?p ?o }` over 1,250 to 10,000 paragraphs of `gene.ttl`,
binary before. Wall time of each phase in ms (one run; load 4 to 6 for the
first three sizes, 20 to 38 for the last):

| paragraphs | bytes | parse | normalize | index | solutions | eval | decode | render | whole, CPU s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,250 | 96,581 | 20 | 6 | 5 | 7 | 52 | 199 | 54 | 0.32 |
| 2,500 | 205,706 | 97 | 18 | 13 | 6 | 106 | 1,141 | 124 | 1.42 |
| 5,000 | 430,251 | 187 | 48 | 31 | 29 | 251 | 8,873 | 279 | 8.57 |
| 10,000 | 847,023 | 195 | 72 | 62 | 130 | 411 | 72,197 | 980 | 51.32 |

Growth per doubling: `decode` 5.7, 7.8 and 8.1; `eval` 2.0, 2.4 and 1.6;
`render` 2.3, 2.2 and 3.5 (the last at load 38); `parse` 4.8, 1.9 and 1.0
(below 0.2 s). `read` and `output` are below 3 ms. The `solutions` column is
from a separate run of the binary before (load 17 to 24).

Peak resident set (MB) of a process that stops after the phase:

| paragraphs | parse | normalize | index | solutions | eval | decode | render | output |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,250 | 13.6 | 13.5 | 15.4 | 15.6 | 17.7 | 49.0 | 55.8 | 55.9 |
| 2,500 | 13.6 | 15.7 | 17.7 | 20.0 | 26.1 | 96.3 | 95.8 | 96.1 |
| 5,000 | 17.5 | 19.8 | 23.5 | 29.8 | 37.9 | 204.0 | 205.8 | 206.0 |
| 10,000 | 23.8 | 29.9 | 35.9 | 46.1 | 47.4 | 367.9 | 367.8 | 368.1 |

**Cause.** The faster-than-linear phase is `decode`, the JSON parse of the
envelope (0.98 MB at 1,250 paragraphs, 9.3 MB at 10,000). `JSON.parseItems`
appends each item to the end of the list read so far, `acc ++ [v]`, and the
`bindings` array has one item per solution (4,651 to 43,251 here), so it
copies n²/2 list cells; `parseMembers` does the same per object member. The
same phase raises the peak by 31 to 320 MB, about 34 bytes per envelope
character: `parseJsonText` turns the envelope into a `List Char` before it
builds the `Array Char` it indexes (section 10.2 measured 35 bytes per
character for such a list). Section 10.5a named the parse; this table
confirms it is the whole growth: every other phase grows by at most 2.7 per
doubling where it is above 50 ms.

### 11.3 `query` COUNT(*) peak memory before, by phase (issue 729)

`SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }`, binary before, peak resident set
(MB) of a process that stops after the phase:

| paragraphs | bytes | read | parse | normalize | index | eval | output |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10,000 | 847,023 | 13.3 | 23.7 | 29.8 | 35.8 | 36.1 | 36.0 |
| 20,000 | 1,706,149 | 15.7 | 35.9 | 47.5 | 57.5 | 57.9 | 57.9 |
| 40,000 | 3,399,450 | 17.6 | 57.8 | 83.8 | 101.8 | 101.9 | 101.8 |
| 80,000 | 6,761,194 | 23.5 | 103.2 | 153.5 | 183.2 | 184.1 | 183.6 |
| 160,000 | 13,509,433 | 37.7 | 195.8 | 295.6 | 347.7 | 348.0 | 348.1 |

Bytes of peak per input byte, 10,000 to 160,000 paragraphs: read 2.0, parse
14.2, normalize 22.0, index 25.8, eval 25.8, output 25.8. These are the
figures of section 10.4: the holders are the parsed graph,
`normalizeDataset`'s duplicate-removal table and the index (section 10.5). The
JSON parse is not on this path's peak (a COUNT envelope is 177 bytes).

### 11.4 wasm `parse()` linear memory before, by phase (issue 744)

`node tests/perf/l4_parse_memory_ladder.mjs`, wasm before, linear memory in
MB at the end of the phase (load 20 to 21):

| people | triples | Turtle bytes | load | open | parse1 | parse6 | nquads1 |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2,000 | 6,000 | 99,814 | 44.1 | 52.9 | 88.1 | 88.1 | 88.1 |
| 4,000 | 12,000 | 201,814 | 44.1 | 52.9 | 132.1 | 132.1 | 132.1 |
| 8,000 | 24,000 | 405,814 | 44.1 | 52.9 | 220.9 | 220.9 | 270.9 |
| 16,000 | 48,000 | 825,814 | 44.1 | 88.1 | 640.7 | 1,226.5 | 666.1 |

The 640.7 and 1,226.5 MB of issue 744 are reproduced. **Cause.** `open`, which
reads the Turtle and indexes the dataset, ends at 88.1 MB; `parse1`, which
also writes the dataset as canonical N-Quads and puts that text into the JSON
envelope, ends at 640.7; `nquads1`, which has no Turtle reader at all, ends at
666.1. So the holder is the N-Quads text's way into the envelope: the
envelope's `Json.string` member is written by `escapeString`, which is
`(s.toList.map escapeChar).foldl (· ++ ·) ""`. For the 3.3 MB of canonical
N-Quads of 48,000 triples it builds a `List Char` (on wasm32 a list cell and a
heap-allocated boxed `Char` per character, `Wasm/build-wasm.sh` step 1b), then
a list of one-character `String`s, then joins them. The Turtle reader
(`parseTurtleWithPrefixes`, which still builds the whole-document character
list that `parseTurtleText` avoids, section 10.3) and the JSON parse of the
call's arguments (the text travels as a JSON array, `engine.call`) are each
below the 35 MB step from 52.9 to 88.1 MB.

### 11.5 Repair 1: the JSON parser with reverse accumulators (`select-star`)

* **Change.** `JSON/Parser.lean`: the five functions of the parser's `mutual`
  block (`parseValue`, `parseObject`, `parseMembers`, `parseArray`,
  `parseItems`) have twins with an `R` suffix that are the same grammar,
  except that `parseMembersR` and `parseItemsR` put each element at the front
  of a reversed accumulator and reverse it once, at the closing bracket.
  `parseJsonTextCharsR` calls them. `charsOfString` reads the characters of a
  `String` in place (`String.foldl`) into the `Array Char` the parser indexes,
  without the whole-document `List Char`; `parseJsonTextFast` uses it.
* **Proved.** `parseR_eq`: at every fuel, on every input, each twin answers
  what its specification answers, the accumulators differing by one
  `reverse` (induction on the fuel, all five at once). `charsOfString_eq`:
  `charsOfString s = s.toList.toArray`. Two `@[csimp]` theorems,
  `parseJsonTextChars_eq_R` and `parseJsonText_eq_fast`, make the compiler
  emit the fast forms for every call of `parseJsonTextChars` and
  `parseJsonText`, so `parseJson` and `parseJson?` run them (the emitted C of
  `parseJson` calls `parseJsonTextFast`, which calls `charsOfString` and
  `parseJsonTextCharsR`). A `csimp` cannot replace a call between two members
  of one `mutual` block (`skills/danbri-function-precrime-checkers`), so the
  whole block has a twin and the replacement is made at the first function
  outside it. Every theorem about the parser is stated about the
  specification and is unchanged.
* **Guards** (`JSON/Tests.lean`): element order of arrays, objects with a
  repeated key, nested arrays and objects, 3,000 items in order; the message
  and position of five rejections (a trailing comma in an array and in an
  object, a missing comma in both, trailing content); `charsOfString` on
  multi-byte characters and on the empty string.
* **Output.** Equal by the theorems above. Measured as well: `l4factoidal
  query`, binary before against binary after, standard output, standard
  error and exit status (section 11.8).

`SELECT *` after, wall time of each phase in ms (one run, load 15 to 21):

| paragraphs | bytes | parse | normalize | index | solutions | eval | decode | render | whole, CPU s |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1,250 | 96,581 | 35 | 19 | 16 | 2 | 28 | 60 | 27 | 0.11 |
| 2,500 | 205,706 | 126 | 39 | 23 | 8 | 61 | 156 | 75 | 0.37 |
| 5,000 | 430,251 | 161 | 34 | 42 | 41 | 159 | 567 | 214 | 1.10 |
| 10,000 | 847,023 | 200 | 102 | 91 | 86 | 224 | 878 | 312 | 1.55 |
| 20,000 | 1,706,149 | 422 | 277 | 279 | 210 | 632 | 1,256 | 544 | 2.72 |

`decode`: 72.2 s before, 0.88 s after at 10,000 paragraphs; growth per
doubling 2.6, 3.6, 1.5 and 1.4 (5.7, 7.8 and 8.1 before). The whole command at
5,000 paragraphs: 8.57 s of CPU time before, 1.10 s after (F*: 1.43 s,
section 10.5a). Peak resident set after the `output` phase: 26.3, 50.2, 90.0,
160.0 and 311.7 MB (55.9, 96.1, 206.0 and 368.1 MB before at the first four
sizes); `decode` still adds 10 to 12 bytes of peak per envelope character at 2,500
paragraphs and above (the `Array Char`, 8 bytes per character, and the `Json`
tree; about 34 before), and `render` holds
the pretty-printed text beside the tree.

The gate row `select-star` (`tests/stack/lean_scaling.sh --only select-star`,
minimum of 3 runs, load 15): 0.236 s at 1,250 paragraphs, 0.614 s at 5,000,
ratio 2.6 for 4 times the input (bound 9). It reported "UNEXPECTED PASS", and
the row is now an assertion (removed from `XFAIL`). Before: 0.32 s and 6.24 s,
ratio 19.7.

## 7. How to repeat

```
cd formal/lean4 && lake build                 # Lean binaries
cd formal/fstar && bash ./build-ocaml.sh compile   # F* binary
python3 tools/bench_lean_vs_fstar.py --list
BENCH_LEAN_BIN_DIR=/path/to/copy python3 tools/bench_lean_vs_fstar.py \
    --rows parse-nt,rdfc-iri --runs 3 --cap 120 --out /tmp/x.jsonl
python3 tools/bench_lean_vs_fstar.py --report /tmp/x.jsonl
tests/stack/lean_scaling.sh                   # the regression gate
valgrind --tool=callgrind --callgrind-out-file=/tmp/cg.out \
    formal/lean4/.lake/build/bin/l4factoidal parse FILE --format turtle
callgrind_annotate --inclusive=yes /tmp/cg.out | head -40
# peak memory by phase (section 10)
/usr/bin/time -v formal/lean4/.lake/build/bin/l4query-phases FILE --stop-after parse
formal/lean4/.lake/build/bin/l4query-phases --walk-check LIST   # walk against parseTurtle
```

`tests/stack/lean_scaling.sh` asserts time(4x) <= 9.0 x max(time(x), 50 ms) for
RDFS closure (wide, dense, tree), TriG (many graphs, one graph), the Turtle
pretty-printer, RDFC-1.0 (no blank nodes, one blank node per person), GROUP BY
(6 groups, one group per subject), and that `l4factoidal version` takes at most
20 ms of CPU time. The OWL RL chain row uses the bound 20.0 because the closure
of n axioms has n(n-1)/2 triples. The baseline binaries fail every one of these
rows; the final binary passes them all.
