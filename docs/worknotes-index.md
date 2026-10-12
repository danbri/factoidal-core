# Worknote index

One row per dated note under `docs/`. The commit is the one that added the
file (`git log --diff-filter=A`). The status column records what the
2026-09-02 review found: which notes the
[Shardborough storage specification](shardborough-storage-spec.md) has
absorbed, which pairs cover one topic, and which notes are current inputs to
work. A new note gets a row here in the same commit.

Status values: **current** (an input to open work), **absorbed** (its
content is in the specification section named), **record** (a landed
worknote, kept as the record of a decision or a measurement),
**historical** (pre-dates the Lean tree or the Shardborough family),
**moved** (its subject left this repository).

| Date | Note | Commit | Status |
| --- | --- | --- | --- |
| 2026-04-20 | [SPARQL demo review](20260420-sparqldemo-review.md) | 7d5c00ed9 | historical |
| 2026-04-21 | [Large Turtle stack overflow fix sketch](2026-04-21-large-turtle-stack-overflow-fix-sketch.md) | c29698f98 | historical |
| 2026-08 | [Factoidal verified RDF block engine](2026-08-blockengine.md) | 27f9308f4 | current: design, part 1 |
| 2026-08 | [Block engine, part 2](2026-08-blockengine_part2.md) | 27f9308f4 | current: design, part 2 |
| 2026-08 | [Block engine, part 3: symbolic plans, dataflow, portable execution](2026-08-blockengine_part3.md) | 27f9308f4 | current: design, part 3 |
| 2026-08-29 | [Block engine repository baseline](20260829-blockengine-baseline.md) | 27f9308f4 | current |
| 2026-08-29 | [Block engine MVP: executable in-memory scan](20260829-blockengine-mvp.md) | 27f9308f4 | record |
| 2026-08-30 | [Block engine corpus ladder](20260830-blockengine-corpora.md) | b49bd0bf5 | absorbed: superseded by the 2026-09-01 catalogue |
| 2026-08-30 | [Host adapter audit](20260830-blockengine-host-audit.md) | 83a7d153d | record |
| 2026-08-30 | [PostgreSQL opaque-byte vertical](20260830-blockengine-postgres-smoke.md) | 265f8bdb9 | record |
| 2026-08-30 | [Symbolic-plan input](20260830-blockengine-symbolic-plans.md) | 27f9308f4 | record |
| 2026-08-30 | [Persisted file to SPARQL](20260830-blockfile-e2e.md) | b9c46f066 | record |
| 2026-08-30 | [BLK0 byte boundary](20260830-blockwirev0.md) | 27f9308f4 | absorbed: spec section 6 |
| 2026-08-30 | [Hub demos and the block-engine boundary](20260830-hub-blockengine.md) | c601be059 | record |
| 2026-08-30 | [Hub SPARQL result components](20260830-hub-sparql-result-components.md) | 1640032d5 | record |
| 2026-08-30 | [IBK2 ingest scale gate](20260830-ibk2-ingest-scale.md) | 487e857de | record |
| 2026-08-30 | [Indexed-block differential gate](20260830-indexedblock-differential.md) | 39e3ce548 | record |
| 2026-08-30 | [Dictionary-backed indexed block](20260830-indexedblock.md) | 802ff6f85 | record |
| 2026-08-30 | [Direct ID-block bytes (IBK1)](20260830-indexedblockwirev1.md) | 07f200d79 | absorbed: spec section 6 |
| 2026-08-30 | [Query observability](20260830-query-observability.md) | d3033fd14 | current |
| 2026-08-30 | [Segmented IBK design decision](20260830-segmented-ibk-design.md) | a9c560dc5 | record |
| 2026-08-30 | [Web corpus working sets and derived RDF blocks](20260830-web-corpus-working-sets.md) | 4f2031862 | current |
| 2026-08-31 | [Concurrent-agent handoff protocol](20260831-agent-coordination.md) | c02e7e20b | record: same topic as epoch-safe compaction |
| 2026-08-31 | [Delta-log proof port](20260831-deltalog-proof-port.md) | 9ab3a3e40 | record |
| 2026-08-31 | [Direct streaming Turtle to IBK3 publication](20260831-direct-turtle-to-ibk3.md) | bf0904765 | record |
| 2026-08-31 | [Durable SPARQL Update slice](20260831-durable-sparql-update-slice.md) | 4613e922a | record |
| 2026-08-31 | [Epoch-safe Shardborough compaction](20260831-epoch-safe-compaction.md) | c02e7e20b | record: same topic as the handoff protocol |
| 2026-08-31 | [Foafmixer loopback MIX pilot](20260831-foafmixer-pilot.md) | 5bcd015c1 | moved: foafmixer-mix repository |
| 2026-08-31 | [Gene shard scale baseline](20260831-gene-shard-scale-baseline.md) | 1d1eb77c7 | record |
| 2026-08-31 | [IBK2 native byte slicing](20260831-ibk2-bytearray-slicing.md) | d6028eb6a | absorbed: spec section 6 |
| 2026-08-31 | [IBK2 gene.ttl ingest gate](20260831-ibk2-gene-ingest-gate.md) | ee6457157 | record |
| 2026-08-31 | [IBK3 decode hot path](20260831-ibk3-decode-hot-path.md) | a4787d633 | current: spec section 11 links it |
| 2026-08-31 | [IBK3 Merkle-verified paged scan](20260831-ibk3-merkle-paged-scan.md) | 884794bb9 | record |
| 2026-08-31 | [IBK2 to IBK3 migration publisher](20260831-ibk3-migration-publisher.md) | 725cafa03 | absorbed: spec section 6 |
| 2026-08-31 | [IBK3: predicate-local rows with a pageable dictionary](20260831-ibk3-paged-dictionary-layout.md) | b85e156ea | absorbed: spec section 6 |
| 2026-08-31 | [Parsed SPARQL over direct IBK3 storage](20260831-ibk3-parsed-sparql.md) | d0de192f2 | record |
| 2026-08-31 | [IBK3 parsed-query host packaging boundary](20260831-ibk3-query-host-packaging.md) | 58e03b392 | record |
| 2026-08-31 | [Immutable generation activation](20260831-immutable-generation-activation.md) | bd4ae512f | record |
| 2026-08-31 | [Lean 4 full-corpus gate](20260831-lean-ci-gate.md) | 009f2ab53 | record |
| 2026-08-31 | [Lean Lake working-directory invariant](20260831-lean-lake-workdir-invariant.md) | 4f069d346 | record: rule now in CLAUDE.md |
| 2026-08-31 | [Native verified-range slicing](20260831-native-range-slicing.md) | 88ab42197 | absorbed: spec section 6 |
| 2026-08-31 | [Packed IBK2 selective reader](20260831-packed-ibk2-selective-reader.md) | cf1d6c5f6 | absorbed: spec section 6 |
| 2026-08-31 | [Pageable term dictionary prototype (PTD1)](20260831-paged-term-dictionary.md) | 7e62bf8a4 | absorbed: spec section 6 |
| 2026-08-31 | [Podman machine audit](20260831-podman-machine-audit.md) | 4058d19d6 | moved: foafmixer-mix repository |
| 2026-08-31 | [Repository review](20260831-repo-review.md) | d3033fd14 | current: review |
| 2026-08-31 | [SRI2: paged Subject Row Index](20260831-sri2-paged-subject-index.md) | ddb403c10 | absorbed: spec section 6 |
| 2026-08-31 | [TLI1: Term-to-Local-ID Index](20260831-tli1-term-local-index.md) | 4030f837f | absorbed: spec section 6 |
| 2026-08-31 | [Agent collaboration: local MIX pilot](20260831-xmpp-mix-pilot.md) | c02e7e20b | moved: foafmixer-mix repository |
| 2026-09-01 | [Block engine Tuesday OKRs](20260901-blockengine-tuesday-okrs.md) | 9b6f60d9f | current |
| 2026-09-01 | [Shardborough corpus ladder: catalogue and rules](20260901-corpus-ladder-catalogue.md) | 3091fb475 | current |
| 2026-09-01 | [Deterministic heterogeneous Shardborough fixture](20260901-heterogeneous-fixture.md) | 6866c9ea3 | current |
| 2026-09-01 | [IBK3 worker and browser SPARQL milestone](20260901-ibk3-wasm-worker-demo.md) | 144bff3d8 | current |
| 2026-09-01 | [Persisted-path W3C executability census](20260901-persisted-executability-census.md) | 6ed315b52 | current |
| 2026-09-01 | [Persisted SPARQL language-tag index safety](20260901-persisted-sparql-language-index-safety.md) | 5028e0545 | record: five topics in one file |
| 2026-09-02 | [Fresh-eyes repository review](20260902-fresh-eyes-review.md) | d3033fd14 | current: review; section 7 is the open hygiene list |
| 2026-09-02 | [Persisted query ladder](20260902-persisted-query-ladder.md) | 3b3a14bb6 | current: measurement record for the 2026-09-02 owner goal; milestone table and rung 2.5 |
| 2026-09-02 | [Quad-aware block layout](designissues/2026-09-02-quad-aware-block-layout.md) | 4c037dd68 | current: proposal for spec gate 4; owner decisions pending |
| 2026-09-03 | [RDF parsing strategy: layers, entry points, proofs, costs](designissues/2026-09-03-rdf-parsing-strategy.md) | 4c037dd68 | current: the record of how Turtle and the other syntaxes are parsed |
| 2026-08-23 | [Specification coverage ledger](designissues/2026-08-23-spec-coverage-ledger.md) | 71db0d505 | record: structure current, scores are 2026-08-22 |
| 2026-09-03 | [A browser reads a Shardborough generation: the three WASM store operations](designissues/2026-09-03-wasm-shardborough-store-ops.md) | b68bec8e5 | current: the record of the WASM store ABI, its blob transport and its caps |
| 2026-09-03 | [Internal test inventory and the internal-tests.sh runner](20260903-internal-test-inventory.md) | 5b3036bc5 | current: the one-runner catalogue for non-W3C project-internal suites |
| 2026-09-05 | [Wire version 10: the format that scales past the source](designissues/2026-09-05-wire-version-10-scale.md) | 11373102a | current: the ceilings, term codec v2, PTD2, IBK5, SBM10 zone maps and blob table, LGI2, publication every batch; tracking https://github.com/danbri/factoidal/issues/658 |
| 2026-09-05 | [The packer publishes every batch](designissues/2026-09-05-pack-publication-every-batch.md) | 43351dbfd | current: the publication policy of wire version 10, what it proves, the memory ladder and gate 2 |
| 2026-10-10 | [JSON-LD node map scaling](designissues/2026-10-10-jsonld-node-map-scaling.md) | 21206659 | record |
| 2026-10-10 | [Unicode case mapping in the Lean tree](designissues/2026-10-10-unicode-case-mapping.md) | 9b77e9f3 | current: the record of `UCASE`/`LCASE`/`fn:upper-case`, the regex flag `i`, the Final_Sigma rule, the generated Unicode 15.1.0 tables, the ASCII-by-specification call sites and the literal search index fold; tracking https://github.com/danbri/factoidal/issues/706 |
| 2026-10-10 | [npm @factoidal/core: the Lean 4 engine only](designissues/2026-10-10-npm-lean-only.md) | (this commit) | current: the state, the answer to "100% Lean?" and the plan; issue https://github.com/danbri/factoidal/issues/713 |
| 2026-10-10 | [F* W3C runner and engine against w3c/rdf-tests ec2ba15](designissues/2026-10-10-fstar-w3c-ec2ba15.md) | 435b939e0 | record: manifest shapes, the 73 failures classified, post-query VALUES, local overrides, exit status of the test step |
| 2026-10-10 | [LGI3 and LGI4: new wire names for the literal gram index](designissues/2026-10-10-literal-index-lgi3.md) | 5d977aa6 | current: why the index fold change renamed LGI1 and LGI2, the two-name and kept-wire-version decisions, how each reader refuses a retired name, the two gates that could pass without testing the index, and the tests; tracking https://github.com/danbri/factoidal/issues/706 |
| 2026-10-10 | [Lean and F\* SPARQL 1.1 differential (`l4diff`): triage](designissues/2026-10-10-lean-vs-fstar-differential.md) | (this commit) | record: the 18 disagreements and 6 F\* command-line errors, each with the W3C expected answer and the specification section; the Lean LIBRARY follows the specification in all 24, the Lean command line did not in 6 (corrected the same day, issues https://github.com/danbri/factoidal/issues/741 and https://github.com/danbri/factoidal/issues/742, both fixed); five F\* causes; tracking https://github.com/danbri/factoidal/issues/718 |
| 2026-10-10 | [F\* solver artifacts as input to the Lean port, and the state of the migration](designissues/2026-10-10-fstar-smt-artifacts-and-lean-migration.md) | (this commit) | record: an outside proposal to port F\* proofs through Z3 unsat cores, checked against the tree (the two model-theory targets are ported; Lean proves truth preservation for every OWL 2 RL row where F\* proves four); one `--query_stats` measurement; the migration state with the port-gap and W3C numbers |
| 2026-10-10 | [F\* theorem classification](theorem-registry.md#f-theorem-classification-issue-757) | (this commit) | current: the inventory of the 1787 top-level F\* lemmas, the relevance rule (1383 relevant), the classes R/S/F/A/U, the checker, and the first tranche (17 R, 71 F); tracking https://github.com/danbri/factoidal/issues/757 |
| 2026-10-10 | [`factoidal serve`: a SPARQL 1.1 endpoint over a Shardborough collection](designissues/2026-10-10-store-serve.md) | (this commit) | current: where each HTTP and SPARQL decision is, the served view, how an update becomes one delta-log batch, the write scope per layout, the gates; tracking https://github.com/danbri/factoidal/issues/669, gap https://github.com/danbri/factoidal/issues/770 |
| 2026-10-11 | [The QLever index format, read for Factoidal/qlvr](designissues/2026-10-11-qlever-index-format.md) | (this commit) | current: every file of a QLever index (commit ceace86) with its byte layout, source lines, instance hexdumps; the stage 3 Lean reader plan; skill `qlvr`; tracking https://github.com/danbri/factoidal/issues/778 |
| 2026-10-11 | [Factoidal/qlvr performance: the Lean implementation against the design](designissues/2026-10-11-qlvr-performance.md) | (this commit) | current: warm against process times, phase shares, the Lean zstd decoder against libzstd (1,860 frames), the q07 kernel in Lean and in C, the remainder against QLever with source lines, the speed work and its effect; skill `qlvr`; tracking https://github.com/danbri/factoidal/issues/778 |
| 2026-10-11 | [Shardborough and QLever on the same data, and a layout with global term ids](designissues/2026-10-11-shardborough-vs-qlever.md) | (this commit) | current: IBK3 and IBK5 disk query paths on the olympics instance against `l4qlvr` and QLever (21 oracle queries, sizes, phase profiles), the structural causes with source lines on both sides, two defects found (IBK5 term parser fuel, `xsd:int` numeric FILTER), the proposed SBM11 layout and its migration stages; scripts `tools/shardborough-cmp/`; tracking https://github.com/danbri/factoidal/issues/775 and https://github.com/danbri/factoidal/issues/776 |
| 2026-10-12 | [SBM11 stage 2: 64-bit term ids and the global dictionary (GDV1, GDX1)](designissues/2026-10-12-sbm11-stage2.md) | (this commit) | current: term id layout (tags, inline canonical integers and booleans, graph ids), key classes, GDV1/GDX1 bytes, round-trip theorems, the byte-array page decoder proved equal to the list decoder, `l4sbm11-dict-pack` phases 1 and 2 with 4 workers, measurements against the stage 2 targets; tracking https://github.com/danbri/factoidal/issues/788 |
| 2026-10-12 | [SBM11 stage 3: sorted quad permutations (PRB1, PRM1), the SBM11 manifest, packer phase 3](designissues/2026-10-12-sbm11-stage3.md) | (this commit) | current: PRB1 column frames (constant, raw, delta; zstd reserved), PRM1 block metadata, `manifest.sbm11`, round-trip and first/last-row theorems, `l4sbm11-pack` phases 1 to 3 and `l4sbm11` (scan, count, dump, verify, activate), measurements against the stage 3 targets; tracking https://github.com/danbri/factoidal/issues/789 |
| 2026-10-12 | [SBM11 stage 4: SPARQL on term ids over an SBM11 generation](designissues/2026-10-12-sbm11-stage4.md) | (this commit) | current: `l4sbm11 query` and `serve`, the id fragment and plan rules, FILTER on ids and its semantics (theorem and sample tests against the reference evaluator), the reference fallback under the `quadEntriesForQuery` guard and its gate queries, oracle 21 pass, W3C census on SBM11, measurements against the stage 4 targets; tracking https://github.com/danbri/factoidal/issues/790 |
