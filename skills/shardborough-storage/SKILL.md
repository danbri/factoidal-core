---
name: shardborough-storage
description: Operate and extend the Lean 4 persisted RDF store (Shardborough) — pack RDF from any of six syntaxes, from a Dataset in memory or from an HDT file into IBK3, IBK4, IBK5 and SBM11 generations, activate through CURRENT, query the activated collection, apply SPARQL Update through the delta log, compact, and read the format registry, the corpus ladder, the executability census and the round-trip theorem status. Use for any l4block-* CLI question or on-disk Lean storage work; not for the F* COTTAS store (see disk-storage-format).
---

# Shardborough storage: the Lean persisted path

Shardborough is the Lean 4 tree's on-disk RDF store family: predicate-local
`IBK3` blocks with an embedded `PTD1` paged dictionary, `SRI2`/`OLI2`
postings sidecars, a `TLI1` term index, an `SBM6` manifest with Merkle chunk
commitments, a `DLOG` durable delta log, and a `CURRENT` pointer that
activates one immutable generation. The normative description is
[`docs/shardborough-storage-spec.md`](../../docs/shardborough-storage-spec.md);
this skill is the operating manual. Every command below was run on
2026-09-02 against `examples/wikidata/subsets/lifesci-kgx/data/sequence_variant.ttl`
(6,455 triples) and the outputs quoted are from that run.

All binaries live in `formal/lean4/.lake/build/bin/` after
`cd formal/lean4 && lake build` (run Lake only from `formal/lean4/`). Below,
`$B` is that directory.

## The lifecycle in five commands

```bash
# 1. Pack: Turtle -> one immutable generation directory
$B/l4block-shard-pack INPUT.ttl COLLECTION/gen-1 ibk3
# prints: format=predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0 triples=6455 blocks=5
#         manifest=manifest.sbm2 wire-version=6 chunk-bytes=65536

# 2. Activate: verify every artifact and cross-artifact relation, then
#    atomically write COLLECTION/CURRENT = "gen-1"
$B/l4block-shard-activate COLLECTION gen-1
# prints: verified-logical-bytes=393735 pointer=CURRENT

# 3. Query the ACTIVATED COLLECTION ROOT (not the generation directory)
$B/l4block-id-v3-query COLLECTION --query 'SELECT (COUNT(*) AS ?n) WHERE { ?v <http://www.wikidata.org/prop/direct/P1057> ?c }'
# prints the SSE plan, then: rows=1 preview=[[("n", ... "1357" ...)]]

# 4. Update: append a durable delta batch (routed through CURRENT);
#    the query path replays committed batches, so it is visible at once
$B/l4block-delta-log COLLECTION --update 'INSERT DATA { <http://example.org/a> <http://example.org/b> <http://example.org/c> }'
# prints: committed path=.../gen-1/deltas.dlog seq=1 epoch=1 ops=1 sync=file
$B/l4block-delta-log COLLECTION/gen-1 --inspect
# prints: committed-batches=1 committed-ops=1 clean-tail=true

# 5. Compact: fold the delta history into a fresh generation, then activate it
$B/l4block-shard-compact COLLECTION/gen-1 COLLECTION/gen-2
# prints: base-triples=6455 delta-batches=1 compacted-triples=6456 epoch=1
$B/l4block-shard-activate COLLECTION gen-2
```

Rules the commands enforce:

- **A failed pack or activation never becomes current.** `CURRENT` is
  replaced only after full verification; readers keep the previous
  generation until then.
- **Query the collection root.** `l4block-id-v3-query` on a generation
  directory is refused with "SBM5 and later require an activated collection
  root (CURRENT)". The older `l4block-shard-query` and
  `l4block-shard-merkle-query` read pre-SBM5 layouts (`manifest.sbm0`) and
  reject current generations; they are kept for the superseded formats.
- **`NOW()` in the `l4block-*` query tools.** Each query tool reads the system
  clock once per query execution (`Wasm/Ops/Clock.lean` `emptyEnvNow`), so
  every `NOW()` of that query is one `xsd:dateTime` (SPARQL 1.1 §17.4.5.1,
  https://github.com/danbri/factoidal/issues/748). Until 2026-10-10 they built
  `emptyEnv`, and W3C `functions/now01.rq` answered `false`. A tool that
  evaluates a user query must build its environment with `emptyEnvNow`, not
  `emptyEnv`; `tools/blockengine-ibk4-quad-smoke.sh` checks one tool.
- **An empty input packs and activates an empty generation.** Seen
  2026-09-02: a broken TriG-to-Turtle conversion produced a 0-byte file,
  `l4block-shard-pack` reported `triples=0 blocks=0` and
  `l4block-shard-activate` made it current with `verified-logical-bytes=0`.
  Read the `triples=` count in the pack output before activating; an empty
  RDF dataset is valid, so the tools do not refuse it.
- **TriG input.** The `ibk3` packer reads Turtle only. Pack a TriG file with
  `ibk4` or `ibk5`, or with `l4sbm11-pack` (section "The source layer"). Before
  2026-09-03 the way to pack a TriG file whose only block was an unlabelled
  `{ … }` was to drop that line and the closing `}` and pack the result as
  Turtle; that is no longer needed.
- **Updates route through CURRENT.** `l4block-delta-log COLLECTION --update`
  appends to the active generation's `deltas.dlog`; passing the generation
  directory does the same. Replay is exactly the valid suffix after the
  compacted epoch, so a crash between compaction and activation cannot
  apply a batch twice (spec section 2.3).

## What a generation directory contains

```
manifest.sbm2            SBM manifest (wire version 6 = SBM6 content)
manifest.tsv             human-readable artifact table
predicate-N.ibk3         one predicate's rows + embedded PTD1 dictionary
predicate-N.ibk3.merkle  32-byte leaf hashes per 65,536-byte chunk
predicate-N.ibk3.sri2    subject -> row offsets (SRI2 postings codec)
predicate-N.ibk3.oli2    object  -> row offsets (same codec, object role)
predicate-N.ibk3.tli1    canonical term bytes -> local ID
predicate-N.ibk4         a quad generation's block (wire version 7, 8 or 9)
predicate-N.ibk4.lgi3    literal 3-gram index, LGI3 (SBM8, SBM9)
predicate-N.ibk4.gbi1    geometry bounding-box index (SBM9)
predicate-N.ibk5         a wire-version-10 block: IBK4 layout over a PTD2
                         dictionary of version-2 terms
predicate-N.ibk5.lgi4    literal 3-gram index plus the opaque-literal list, LGI4
predicate-N.ibk5.gbi1    geometry bounding-box index, unchanged from SBM9
blob-<sha256 hex>.lit    one out-of-line literal's UTF-8 lexical form; the
                         digest in the name is the artifact's own SHA-256, so
                         a version-2 tag-4 term names its own file (SBM10)
*.merkle                 one per sidecar and per blob
deltas.dlog              appears after the first --update
compacted.epoch          CEP1 marker, written by compaction
compacted.source.sha256  identity of the source generation compaction read
```

Format registry with status and executable definitions: spec section 6.

Retired names. A retired name is never written and never read; a reader that
meets one refuses it and says why.

| Retired | Replaced by | Date | Reason |
| --- | --- | --- | --- |
| `LGI1` (magic and version byte 1; sidecar `.lgi1`; layout labels `quad-ibk4-ptd1-lgi1-merkle-v0` and `quad-ibk4-ptd1-lgi1-gbi1-merkle-v0`) | `LGI3` (magic `LGI3`, version byte 3; `.lgi3`; labels with `lgi3`) | 2026-10-10 | the gram fold changed from ASCII-only `String.toLower` to Unicode `Text.CaseMap.searchFold` ([issue 706](https://github.com/danbri/factoidal/issues/706)); the bytes of a non-ASCII literal differ |
| `LGI2` (magic and version byte 2; `.lgi2`; label `quad-ibk5-ptd2-lgi2-gbi1-merkle-v0`) | `LGI4` (magic `LGI4`, version byte 4; `.lgi4`; label with `lgi4`) | 2026-10-10 | same |

The byte layouts did not change: LGI3 is the LGI1 layout and LGI4 is the LGI2
layout. The manifest wire versions 8, 9 and 10 keep their numbers; their layout
labels changed. Record: [`docs/designissues/2026-10-10-literal-index-lgi3.md`](../../docs/designissues/2026-10-10-literal-index-lgi3.md).

A generation packed before 2026-10-10 is repacked, not migrated. The tools say
so:

```
l4block-shard-activate failure: manifest layout 'quad-ibk4-ptd1-lgi1-gbi1-merkle-v0' names a literal index that was folded with the ASCII-only fold. That index does not hold all the rows that the Unicode LCASE keeps. Re-pack the generation with the current packer. The packer writes LGI3 or LGI4.
```

Round-trip theorem status per codec: spec section 10.1 (term codec, PTD1 and
IBK3 proved 2026-09-02 with `encode? = some bytes` as the only hypothesis;
SRI2/OLI2 and TLI1 in progress the same day; SBM6 and Merkle range admission
open).

`IBK4`, the quad-aware block (a graph column in every row, a header graph-set
summary, the same PTD1 dictionary), is defined in spec section 6.1.1 and
proved in `Storage/IndexedBlockWireV4Theorems.lean` (2026-09-03). `SBM7` is
its manifest (spec section 6.3.1). `l4block-shard-pack ... ibk4` writes a
quad generation, `l4block-shard-activate` admits one, and
`l4block-quad-query` runs SPARQL over it; the graph-aware index sidecars are
not written yet.

## Other CLIs, by purpose

| Purpose | Command |
| --- | --- |
| Query a Turtle file directly (no persistence; reference path) | `l4block-corpus PATH.ttl --query SELECT...` |
| Predicate histogram of a file | `l4block-corpus PATH.ttl [PREDICATE-IRI]` |
| Verified range read of one block | `l4block-shard-merkle-pread SHARD-DIR PREDICATE-IRI [OFFSET LENGTH]` |
| Verified range read of a synthetic chunked file (test data for the readers of `PosixRangeIO`; the shard packer writes no artifact above about 64 chunks) | `l4merkle-range-read make DIR CHUNKS [TAIL]`; `l4merkle-range-read read DIR [--reader leaves\|tree\|cached] [--offset O] [--length L] [--check]` |
| Bounded Merkle scan or row range | `l4block-id-v3-merkle-scan SHARD-DIR PREDICATE-IRI LIMIT` / `--range START COUNT` |
| Convert an IBK2 block to IBK3 | `l4block-id-v3-convert INPUT.ibk2 OUTPUT-DIR PREDICATE-IRI` |
| Session of many SELECTs over one shard | `l4block-shard-merkle-session SHARD-DIR < queries.rq` |
| Pack a quad generation (IBK4, wire version 9) | `l4block-shard-pack INPUT OUTPUT-DIR ibk4 [--batch-bytes N]` (the syntax comes from the extension: `.nt`, `.nq`, `.ttl`, `.trig`, `.rdf`, `.jsonld`; any other extension is read as Turtle) |
| Pack a quad generation (IBK5, wire version 10) | `l4block-shard-pack INPUT OUTPUT-DIR ibk5 [--batch-bytes N]` — same syntaxes, read as RDF 1.2 |
| SBM11 packer phases 1 and 2: the global dictionary `dict.gdv1` + `dict.gdx1` (stage 2, no query path yet) | `l4sbm11-dict-pack SOURCE OUTDIR [--format F] [--base IRI] [--run-terms N] [--workers K]` (SOURCE in any of the six syntaxes, read through the source layer as `l4sbm11-pack` reads it); check every key and every source term: `--check SOURCE OUTDIR [--exact]`; string-to-id by `pread`: `--lookup-bench OUTDIR [N] [ABSENT]` |
| SBM11 packer phases 1 to 3: dictionary, PSO/POS/SPO/OSP blocks, manifest (stage 3) | `l4sbm11-pack SOURCE OUTDIR [--format F] [--base IRI] [--workers K] [--run-terms N] [--block-rows B] [--sort-rows M]` (SOURCE in any of the six syntaxes; section "The source layer"); `--phase2-only` stops after the term-run merge and keeps `dict.gdv1`, `dict.gdx1` and the remap files (`run-W-J.tmp.remap`), to time phase 2 and compare its output byte for byte (`tests/sbm11/phase2_scaling.sh`, https://github.com/danbri/factoidal/issues/804) |
| SBM11 query (stage 4) | `l4sbm11 query GEN ('SPARQL' \| --file Q.rq) [--base IRI] [--explain] [--repeat N] [--reference-render] [--reference] [--verify merkle\|none] [--threads N] [--sip auto\|always\|off]`; `l4sbm11 serve GEN [--verify merkle\|none]` (default `none` on a generation `CURRENT` names, else `merkle`); decoder checks `l4sbm11 prm-check GEN` (PRM1 decoders, and the issue 805 range search against decoding the whole file on 385 keys per PRM1 file, over bytes, `pread` and Merkle chunks), `l4sbm11 frame-check GEN`; environment: `SBM11_PAGES` (dictionary page cache, default 2,048 pages), `SBM11_TASK_PAGES` (a scan task's own page cache, default 1,024), `SBM11_MIN_RANGE_ROWS` (fewest estimated rows per block range, default 8,192; 0 divides every scan, for tests) |
| SBM11 reader | `l4sbm11 stats GEN`; `scan GEN PERM [KEY...] [--limit N] [--ids]` (KEY an IRI `<...>` or an id); `count GEN PERM [KEY...]`; `dump GEN [PERM]`; `dump-ids GEN PERM`; `graphs GEN` (the named graphs of the base, empty ones included: the GNL1 list, or the graph names of the quads when the generation has no list); `export GEN --format F [--out FILE] [--graph default\|all\|IRI] [--prefix LABEL=IRI]...` (the dataset in any of the six syntaxes; section "The source layer", subsection "Export"); `canon SOURCE [--format F] [--base IRI]`; `verify GEN`; `activate ROOT NAME`; `reseal GEN` (test support) |
| Convert a dataset between syntaxes with the Lean serialisers (test data, comparisons) | `l4source-convert SOURCE OUT [--from F] [--to G] [--base IRI]` |
| Query an activated quad generation | `l4block-quad-query COLLECTION-ROOT [--json] [--base IRI] --query SELECT...` |
| Superseded formats (BLK0, IBK1, IBK2) | `l4block-pack`, `l4block-id-pack`, `l4block-id-v2-pack` and their `*-file-query` / `*-diff` partners |

`l4block-shard-merkle-query SHARD-DIR --explain|--explain-json|--explain-analyze` prints the physical plan and, with `-analyze`, the executed
read trace; it targets the Merkle session layout, not an SBM6 collection.

## IBK4 generations (quad-aware, landed 2026-09-03)

`l4block-shard-pack INPUT OUTPUT ibk4` writes a quad generation, with a graph
column in every row and a graph-set summary in the block header and in the
SBM7 manifest entry. The input syntax comes from the file extension
(`RdfFormat.formatOfPath`): `.nt`, `.nq`/`.nquads`, `.ttl`/`.turtle`, `.trig`,
`.rdf`/`.xml`/`.owl`, `.jsonld`/`.json-ld`. Any other extension is read as
Turtle, with every triple in the default graph.

**The block set.** Quads are bucketed by the PAIR (predicate, graph), and a
bucket is cut into blocks by two size targets only: 16,384 rows and 2,097,152
bytes of estimated wire size. So every block holds one predicate in ONE
graph, its manifest `graphSet` has exactly one member, and a
`GRAPH <iri> { ?s <p> ?o }` reads exactly the blocks of that pair.

Until 2026-09-05 the bucket key was the predicate alone and a third rule cut
a run at every GRAPH CHANGE. That rule had no lower bound on block size, so
an N-Quads source whose graphs interleave line by line produced one block per
graph run: 11,636 blocks against 483 for the same 50,386 statements, a
generation of 304,820 KiB against 20,792 KiB, and a query of 23.76 s against
0.50 s. The (predicate, graph) key removes it; interleaving never closes a
run
(`docs/designissues/2026-09-05-wire-version-10-scale.md` section 5 and its
subsection "The repair, measured 2026-09-05").

**Block order.** Blocks are published in the FIRST-OCCURRENCE ORDER OF THE
KEY. The whole-source route (`quadArtifacts`, now reached only with
`L4_PACK_BUFFERED=1`) sees that order in the graph-major `quadsOfDataset`
flattening; the streamed route (all of TriG, N-Quads, Turtle, N-Triples since
2026-10-14, https://github.com/danbri/factoidal/issues/769) publishes a run
when a size target closes it and, at a flush, in the same first-occurrence key
order of the SOURCE. They agree byte for byte when each named graph is one
contiguous block, the default graph comes first, and the source has fewer than
1,048,576 quads (`maxCarriedRows`); otherwise block order or the block set
differs (https://github.com/danbri/factoidal/issues/836). Test knobs of
`l4block-shard-pack`: `L4_PACK_BUFFERED=1` (whole-source route),
`L4_PACK_CHUNK_BYTES=N` (read N bytes at a time). Checks:
`tests/trig-pack/compare_w3c.sh`, `tests/trig-pack/order_xfail.sh`, scaling row
`pack-trig-memory`. The SBM11 packer `l4sbm11-pack` and its
phases 1 and 2 alone, `l4sbm11-dict-pack`, read all six syntaxes
(section "The source layer").

```bash
l4block-shard-pack tests/local/data/quad_sample.trig /tmp/store/gen-1 ibk4
# format=quad-ibk4-ptd1-merkle-v0 syntax=trig quads=6 blocks=2 graphs=3
# manifest=manifest.sbm2 wire-version=7 blank-node-scope=<source SHA-256 hex>
l4block-shard-activate /tmp/store gen-1
l4block-quad-query /tmp/store --query 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }'
```

Wire version 10 is the same three steps with the tag `ibk5`. It stores what
version 9 refuses — an RDF 1.2 triple term, a directional literal, and a
literal above 65,536 bytes, which goes into its own `blob-<hex>.lit` artifact
— and its manifest carries a subject and an object zone map per entry, so a
bound-subject query opens fewer blocks. `l4block-quad-query` reports that as
`zone-excluded=N` and reads a version-10 generation's queries as SPARQL 1.2.

```bash
l4block-shard-pack tests/local/data/rdf12_sample.trig /tmp/store10/gen-1 ibk5
# format=quad-ibk5-ptd2-lgi4-gbi1-merkle-v0 syntax=trig quads=5 blocks=5
# graphs=2 manifest=manifest.sbm2 wire-version=10
l4block-shard-activate /tmp/store10 gen-1
l4block-quad-query /tmp/store10 --query \
  'SELECT ?d WHERE { ?s <http://example.org/label> ?o BIND(LANGDIR(?o) AS ?d) }'
```

Both tags are kept: version 9 is the differential oracle for version 10
(`docs/designissues/2026-09-05-wire-version-10-scale.md` gate 4).

Memory. The N-Quads, Turtle and N-Triples routes stream the source in
65,536-byte chunks (`PackStream.quadIngestFeed`), and since 2026-09-05 they
also PUBLISH during the ingest pass, so peak memory is bounded by the
operator's `--batch-bytes` (default 268,435,456 source bytes) rather than by
the source
(`docs/designissues/2026-09-05-pack-publication-every-batch.md`). TriG joined
them on 2026-10-14 (https://github.com/danbri/factoidal/issues/769), and RDF/XML
on 2026-10-22 (one child of `rdf:RDF` at a time,
https://github.com/danbri/factoidal/issues/838), and JSON-LD on 2026-10-22 (one top-level
node object at a time, when `Prepass` finds the document in streaming form,
https://github.com/danbri/factoidal/issues/839). Measured on skosdex N-Quads
prefixes, 2026-09-05: peak footprint 222,955,392 bytes for 52,428,626 of
source, 328,272,128 for 104,857,577, 331,581,824 for 209,715,187 and
472,746,624 for 1,543,478,120 — a 2.12x rise over a 29.4x source, against
15.25x before. The residue that still grows is the manifest, one entry per
block, written at the end. Byte identity of the streamed PARSE against the
buffered one is PROVED for N-Quads (`NQuadsFold.streamConsume11_eq_batch`)
and only MEASURED for Turtle — the Turtle accumulator half is proved
(`Syntax.parseTurtle_eq_fold`), the chunk-boundary half is not. What
publication every batch preserves is proved per (predicate, graph) key in
`PackStreamTheorems` (`pubRun_published_eq_fed`, `streamed_eq_buffered`), and
`PredicateQuadBlocksTheorems.bucket_one_graph` is what keeps a block to one
graph now that no cut rule does;
the block SET and the block ORDER differ from the buffered route's, which
every manifest since SBM2 admits.

What works:

- Pack from TriG, N-Quads, N-Triples, Turtle, RDF/XML and JSON-LD. The same
  quads in the same order from either syntax give byte-identical blocks.
- One `.merkle` leaf sidecar per block, and an SBM7 manifest committing the
  source file's SHA-256 as each entry's blank-node scope under the
  `content-digest-shared` publication profile.
- Activation: full SHA-256, rebuilt Merkle leaves and root, an
  `IndexedBlockWireV4.decode` of every artifact, and a check that the block's
  graph set equals the manifest entry's summary.
- **SPARQL through `l4block-quad-query`** (landed 2026-09-03; see the next
  subsection).
- `tools/blockengine-ibk5-quad-smoke.sh` (wire version 10: the RDF 1.2
  fixture, the blob artifacts, the zone maps, the tamper tests),
- `tools/blockengine-ibk4-quad-smoke.sh` and
  `tools/blockengine-ibk4-w3c-trig-smoke.sh` (241 pass, 0 fail out of 241
  positive W3C TriG 1.1 tests).

What does NOT work yet:

- **No index sidecars.** SRI2, OLI2 and TLI1 are keyed by a block-local ID
  with no graph dimension, so they cannot describe an IBK4 artifact, and SBM7
  admits none. Every selected block is therefore read whole; there is no
  selective row access path. The graph-aware sidecars are the next piece of
  work.
- **The manifest is still written at the end.** Its entries are held in
  memory until then — one `Entry` and one TSV line per block — which is the
  one part of the packer that still grows with the source. On the full
  1,543,478,120-byte skosdex corpus that is 3,306 entries and about 141 MB of
  the 472,746,624-byte peak. A manifest written incrementally is the next
  step. (The BLOCKS themselves are no longer held: the IBK4 path publishes
  them during the ingest pass, and the streamed grammars — N-Quads, Turtle,
  N-Triples, TriG, RDF/XML, JSON-LD — no longer buffer the source either,
  except under the fall-back rules of `Syntax/RdfXmlChunkFold.lean` and
  `Syntax/JsonLdChunkFold.lean`.)
- **No compaction and no delta log.** There is no compacted SBM7 layout label.

### Querying an IBK4 generation

`l4block-quad-query COLLECTION-ROOT --query SELECT...` opens the activated
generation through `CURRENT`, decodes the blocks the planner selects, builds
the RDF DATASET they denote (default graph = the rows whose graph column is
`none`, one named graph per graph name), and evaluates the query with
`env.dataset` set to that dataset. `GRAPH <iri>`, `GRAPH ?g`, default-graph
patterns, `FROM`, `FROM NAMED`, SELECT, ASK and CONSTRUCT all work.

It is a SIBLING of `l4block-id-v3-query`, not an arm of it, and
`l4block-id-v3-query` still refuses SBM7 by layout. The reason is structural:
every selective access path in the IBK3 tool is driven by an SRI2, OLI2 or
TLI1 sidecar, and SBM7 admits none; and the IBK3 tool threads a `List Triple`
plus a resolved DLOG overlay, where an IBK4 generation yields a dataset and
carries no delta log. Revisit the split when the graph-aware sidecars land.

**Block selection** (`ShardManifest.quadEntriesForQuery`) is what makes this
less than a whole-store read. An entry survives unless one of two collectors
excludes it:

| Collector | Excludes an entry when | Gives up (keeps everything) when |
| --- | --- | --- |
| `queryQuadConstantPredicates?` | the entry's predicate is not one the pattern names | a triple pattern or path step has a variable predicate; a `{}` or empty BGP under a `GRAPH` clause; a non-`backendLocal` FILTER / OPTIONAL / BIND expression; a sub-SELECT, SERVICE, LATERAL or VALUES |
| `queryGraphNames?` | the entry's manifest `graphSet` meets none of the names the pattern reads | `GRAPH ?v`; the query carries `FROM` / `FROM NAMED`; the same expression and pattern forms as above |

Both are refused outright unless `Query.patternBoundedReads` holds. It is
`Query.expressionsOutsidePatternExistsFree` and not a DESCRIBE form. Section
18.6 evaluates an `EXISTS` in the projection, a GROUP BY key, a HAVING
condition or an ORDER BY condition against the ACTIVE GRAPH, and neither
collector reads those positions (the same guard `l4block-id-v3-query`
carries, [issue 638](https://github.com/danbri/factoidal/issues/638)). A
DESCRIBE answers every statement about the resources it names, which no
pattern selects, so it always reads the complete generation
(`docs/designissues/2026-10-10-sparql-describe.md` section 4).

Two rules that look small and are not:

- `GRAPH <g> { }` reads no row but still asks whether the dataset names `g`,
  so the graph collector adds `<g>` itself, and the predicate collector gives
  up on an empty group under a `GRAPH` clause. Without both, an entry that
  puts `g` into the dataset could be skipped and the query would answer zero
  rows instead of one.
- A query with `FROM` gets no graph-based selection at all. Section 13.2
  rebuilds the default graph out of the `FROM` graphs, so a default-graph
  pattern under `FROM <g>` reads `<g>` and not the default graph.

The mode line names the path:

```
l4block-quad-query shards=1 open-mode=ibk4-full-manifest(1) graphs=2 logical-read-bytes=554 fetched-bytes=554
```

`ibk4-full-manifest` is the indexed backend path
(`StoreDataset.indexedDatasetBackend`). `ibk4-full-manifest-reference` is the
same answer through the reference evaluator, taken when the generation has a
graph whose NAME is a blank node: `materialiseDatasetBackend` keeps only
graphs with a well-formed IRI name, so the delegating arms of the backend
seam would lose such a graph.

Gate: `tools/blockengine-ibk4-quad-smoke.sh`.

## Browser and WASM path

The same Lean decoder runs in the browser through the WASM dispatch
operations `scanIBK3Predicate` (one complete block, hex transport) and
`queryIBK3BlockSetPreview` (up to 8 blocks / 8 MiB / 100,000 rows, RDF kept
inside Lean). Hub posts 50 and 51 use them with an Origin Private File
System cache; the caller must check each block's byte length and SHA-256
against the manifest before decoding. This is the diagnostic worker, not the
bounded protocol worker of spec section 2.4.2.

**A whole GENERATION, not a hand-picked block set** (2026-09-03). Three
further operations let a host run SPARQL over a packed generation without
understanding any of its formats — it reads files by name and carries bytes,
and every decision stays in Lean (iron rule 7):

| Op | Answers |
|---|---|
| `storeManifestInspect(manifestHex)` | wire version, layout, blank-node profile, and per entry: key, bytes, SHA-256, chunk bytes, Merkle root, predicate, rows, block kind, blank-node scope, graph-name set, sidecar keys |
| `storeQueryPlan(manifestHex, sparql)` | the keys to fetch in manifest order, the same open mode the native tools print, and the byte and row totals |
| `storeQuery(manifestHex, sparql, artifactsJson)` + one blob region | the `queryDataset` envelope, with `shards` and `mode` before `kind` |

Block selection is `queryNativeConstantPredicates?` (IBK3) and
`quadEntriesForQuery` (SBM7 / IBK4) — the collectors the native tools use, so
the plan and the mode agree with `l4block-id-v3-query` and
`l4block-quad-query`. `storeQuery` checks every artifact's byte length and
SHA-256 against its manifest entry and refuses naming the key on a mismatch;
caps are 64 artifacts, 8388608 bytes and 100000 rows, each an explicit refusal.

Artifact bytes cross RAW through `l4_call_blob_c`: one buffer the host wrote
into the wasm heap, and `{"key","offset","len"}` windows Lean bounds-checks.
Hexadecimal cost 96 ms against 71 ms for one 118,769-byte block and a 49.5x
larger args document, so it is kept for diagnostics only.

Design record:
[`docs/designissues/2026-09-03-wasm-shardborough-store-ops.md`](../../docs/designissues/2026-09-03-wasm-shardborough-store-ops.md).
Gate: `bash tools/wasm-store-query-smoke.sh` (the wasm module against
generations the packer just wrote, rows compared with the native tools).
The wasm is not committed since 2026-10-09: install it with
`tools/fetch-builds.sh` or build it with `Wasm/build-wasm.sh` first.

**The call stack a large collection needs.** Several engine paths recurse
once per manifest entry and once per row. On a 3,286-block collection
`storeQueryPlan` alone overflows the default stack of Node, before any
artifact byte is read (measured 2026-09-05). The host route is a
`worker_threads` thread with a raised stack, and a store HANDLE lives on
that thread because a wasm instance does not cross a thread boundary:
`openStoreHandleOnWorker` in `npm/factoidal/bin/store-worker-host.mjs`.
A one-shot `factoidal query` still runs in process and only retries there.
Deno's worker shim does not raise the stack, so Deno re-executes itself
instead, which needs `--allow-run` and `--allow-env`. Design record:
[`docs/designissues/2026-09-05-store-handle-call-stack.md`](../../docs/designissues/2026-09-05-store-handle-call-stack.md).

## Serving

`factoidal serve STORE --port N [--host H]` (npm/factoidal) serves the
activated generation of a collection, with its delta log, over HTTP/1.1
(https://github.com/danbri/factoidal/issues/669 step 1; design record
[`docs/designissues/2026-10-10-store-serve.md`](../../docs/designissues/2026-10-10-store-serve.md)):

```bash
l4block-shard-pack data.nq COL/gen-1 ibk5 && l4block-shard-activate COL gen-1
node npm/factoidal/bin/factoidal.mjs serve COL --port 3030
# serve: listening on http://127.0.0.1:3030 for COL (layout quad-ibk5-…, N rows,
#        delta batches replayed: 0, write scope all-graphs)
curl -s 'http://127.0.0.1:3030/sparql?query=ASK%7B%7D'           # Protocol §2.1
curl -s -H 'content-type: application/sparql-update' \
     --data-binary 'INSERT DATA { <s> <p> <o> }' http://127.0.0.1:3030/sparql
curl -s http://127.0.0.1:3030/sparql                              # Service Description
curl -s 'http://127.0.0.1:3030/data?graph=http%3A%2F%2Fe%2Fg'      # Graph Store
```

What it serves: `/sparql` (also `/sparql/`, `/query`, `/update`) is SPARQL
1.1 Protocol query and update; a GET there with no query string is the
SPARQL 1.1 Service Description; `/data` is the Graph Store HTTP Protocol
(`--query-path`, `--gsp-path` move them). Results are negotiated: SPARQL
Results JSON (the default), XML, CSV and TSV for SELECT; JSON and XML for
ASK; Turtle and N-Triples for CONSTRUCT, DESCRIBE and the Graph Store.

Where the decisions are: the request framing and the response bytes in
`L4Factoidal/HTTP/Wire.lean`; routing, status codes, negotiation,
evaluation, the service description, the Graph Store and the delta-log batch
in `L4Factoidal/SPARQL/StoreEndpoint.lean`; the ops in
`Wasm/Ops/StoreServe.lean`. The host (`npm/factoidal/bin/serve.mjs`, on a
worker thread with a raised stack) moves bytes and is in both groups of
`tools/host-purity-lint.sh`.

Rules it enforces:

- **An update is durable before it is answered.** The server executes the
  update (or Graph Store write) with the reference semantics, writes the
  change as ONE DLB1 batch to the activated generation's `deltas.dlog`
  (append at the expected size, fsync), and only then answers. A
  WHERE-dependent update is stored too. The native tools read the batch:
  `l4block-delta-log --inspect`, `l4block-id-v3-query` and
  `l4block-shard-compact`.
- **Write scope by layout.** An IBK3 generation takes default-graph changes
  only and answers 501 to a named-graph change, because its log is
  replayed and compacted for the default graph only. A quad generation
  (IBK4, IBK5) takes every graph, but no native reader replays its log yet
  (https://github.com/danbri/factoidal/issues/770): `l4block-quad-query`
  answers the pre-update data.
- **After compaction, restart.** `l4block-shard-compact COL/gen-1 COL/gen-2`,
  `l4block-shard-activate COL gen-2`, then restart the server; a running
  server keeps the generation it opened.
- **One writer.** The append has no advisory lock
  (https://github.com/danbri/factoidal/issues/644).

Scores (2026-10-10, wasm sha256 `c7d88f17…`):

- W3C over a live socket, `lake exe l4protocol-live --cli
  ../../npm/factoidal/bin/factoidal.mjs --bin .lake/build/bin --work DIR
  <protocol, graph-store-protocol direct and indirect, service-description
  manifests>`: **50 pass, 0 fail (out of 50)** — protocol 34,
  graph-store-protocol 13, service-description 3. Each test gets its own
  IBK5 collection packed from its `ut:graphData`. The deprecated
  `http-rdf-update` suite is not replayed live (Markdown requests, seeded
  by runner glue).
- `node tests/store-serve/serve.mjs`: **19 pass, 0 fail, 1 expected failure
  (out of 20)**: FILTER NOT EXISTS, FILTER EXISTS, MINUS, OPTIONAL with
  FILTER and a sub-SELECT give the same non-empty rows through the server,
  `factoidal query` and the in-memory engine over the source file; update,
  query, compact, activate, restart, query; framing; write scope. The
  expected failure is issue 770.

Measured 2026-10-10 on this container (4 shared CPUs) with
`node tests/store-serve/measure.mjs COL http://www.wikidata.org/entity/Q287043 4000`
over `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl` packed as IBK3
(888,949 triples, 13 blocks, 24,928,958 verified bytes):

| Measurement | Value |
| --- | --- |
| start to first answer (read, verify, decode, index) | 6.9 to 8.0 s (three runs) |
| bound-subject SELECT, 1 row, 4,000 requests, one keep-alive connection | median 0.50 ms, p95 0.82 ms, max 19.2 ms |
| `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`, 20 requests | median 31.5 ms (26.1 to 36.9 ms over three runs) |
| `… FILTER(isIRI(?o))`, every row evaluated, 5 requests | median 420 ms |
| resident set after 100, 1,000 and 4,000 bound requests | 508.5 MB, 527.3 MB, 526.6 MB: +3.6 % after 100, flat from 250 to 4,000 |
| resident set after the scans | 658.7 MB (the wasm heap grows and does not shrink) |

The growth gate (at most 10 % after 1,000 requests) passed in three runs:
+3.4 %, +9.1 % and +3.6 % between request 100 and request 1,000. The 9.1 %
run was the outlier; the 4,000-request series shows the resident set flat
from request 250 on, so the rise is start-up, not a per-request leak.

## Corpus ladder, profiling and the census

- Corpus ladder (which files are used at which size rung, and the rules
  every rung follows): [`docs/20260901-corpus-ladder-catalogue.md`](../../docs/20260901-corpus-ladder-catalogue.md).
  Rungs 1 and 2 are in the repository (`formal/lean4/Harness/TestData/`,
  `examples/wikidata/subsets/lifesci-kgx/data/`).
- Profile one file for the ladder (bytes, SHA-256, engine-counted
  statements, predicate and object-kind histograms):
  `tools/corpus-profile.sh FILE`.
- Executability and row-agreement census of the W3C SPARQL
  QueryEvaluationTests through the persisted path (pack, activate, query,
  then compare the answer with the reference in-memory engine over the same
  file; NOT a pass/fail conformance result — that is `lake exe l4w3c`):
  `tools/w3c-persisted-census.sh`, results in
  [`docs/20260901-persisted-executability-census.md`](../../docs/20260901-persisted-executability-census.md).
  Measured 2026-09-03: default graph 535 executed, 535 matched, 0 differed
  (out of 535 eligible); named graphs 29 executed, 29 matched, 0 differed
  (out of 35 eligible `qt:graphData` entries; the 6 refusals all carry a
  relative IRI in the query text, which no query CLI resolves).
- Parser differential for the N-Quads path the browser uses:
  `tools/nquads-parser-differential.sh FILE.nq`.

## Against QLever, and the proposed wire version 11

[`docs/designissues/2026-10-11-shardborough-vs-qlever.md`](../../docs/designissues/2026-10-11-shardborough-vs-qlever.md)
measures both disk query paths (IBK3, IBK5) on the QLever reference instance
(olympics, 1,781,625 triples) with the 21 oracle queries, next to `l4qlvr` and
QLever, and proposes SBM11: one byte-ordered global dictionary, 64-bit term
ids with inline canonical numerics, sorted PSO/POS/SPO/OSP column blocks with
first/last-key metadata, and joins over ids. Rerun with
`bash tools/shardborough-cmp/pack.sh`, `bash tools/shardborough-cmp/run.sh`
and `bash tools/shardborough-cmp/profile.sh LAYOUT QUERY` (perf needed).
Measured 2026-10-11: 437 MB (IBK3) and 222 MB (IBK5) against 38.5 MB; q07
13.6 s (IBK3) and 62.1 s (IBK5) against 0.35 s for `l4qlvr` on QLever's
layout; 60 % to 90 % of query time is decoding terms and building the
in-memory index before evaluation.

SBM11 stage 2 (2026-10-12, https://github.com/danbri/factoidal/issues/788):
64-bit term ids and the global dictionary GDV1/GDX1, with round-trip
theorems, and `l4sbm11-dict-pack` (packer phases 1 and 2). Format bytes,
theorem names and measurements:
[`docs/designissues/2026-10-12-sbm11-stage2.md`](../../docs/designissues/2026-10-12-sbm11-stage2.md).
Gates for a change there: `tests/sbm11/dict_scaling.sh [--doubled]`,
`l4sbm11-dict-pack --check SOURCE OUTDIR` (failures=0),
`python3 tests/sbm11/dict_reference.py SOURCE` (same counts) and the
`sbm11-dict` case of `tests/stack/run.sh --canary`.

RDF 1.2 triple terms (2026-10-14, https://github.com/danbri/factoidal/issues/792
item 1): a triple term is a dictionary term, key class 7 (`7 len(sk) sk
len(pk) pk ok`: the keys of its parts, `len` a u32 little-endian, the object
key last and without a length, so a nested triple term is the suffix of its
parent's key) and id tag 9. The packers read N-Quads in RDF 1.2 mode;
`l4sbm11 query --sparql12` (and `serve ... --sparql12`) reads SPARQL 1.2. On
the id path a triple term with no variable and no blank node inside is a
constant; one with a variable or a blank node inside goes to the reference
fallback; the triple functions run as the reference evaluator's own
functions on decoded terms. `l4sbm11 update --sparql12` stores INSERT DATA
and DELETE DATA with triple terms and directional literals in a DLOG of
version 2 (below, "Delta log versions"; since 2026-10-14). `l4sbm11 canon`
reads RDF 1.2 through the source layer since 2026-10-14 (https://github.com/danbri/factoidal/issues/837); part (m)
asserts that `dump` and `canon` of the triple-term fixture are equal. Records: stage 2 record section 8
(key, tag, format names, theorems), stage 4 record section 14 (each query
path). Gates for a change there: `tests/sbm11/run.sh` part (m) (46 queries
against `l4factoidal query --sparql12`, compaction, three SPARQL 1.2 updates
with queries after each, the refusals),
`l4sbm11-dict-pack --nest-check N`, and the `sbm11-triple-term` case of
`tests/stack/run.sh --canary` (depth 300,000).

SBM11 stage 3 (2026-10-12, https://github.com/danbri/factoidal/issues/789):
the sorted permutations PSO, POS, SPO, OSP as PRB1 column-frame blocks with
PRM1 block metadata, the manifest `manifest.sbm11` (wire version 11), packer
phase 3 and the activation checks. Record with bytes, theorems and
measurements:
[`docs/designissues/2026-10-12-sbm11-stage3.md`](../../docs/designissues/2026-10-12-sbm11-stage3.md).
Gates for a change there: `tests/sbm11/stage3_check.sh SOURCE WORKDIR`
(dump equals the source as a set, four permutations equal, tampered copies
refused), `tests/sbm11/pack_scaling.sh`, and the `sbm11-perm` case of
`tests/stack/run.sh --canary`.

SBM11 stage 4 (2026-10-12, https://github.com/danbri/factoidal/issues/790):
SPARQL on term ids over a generation, `l4sbm11 query GEN 'SPARQL' | --file
Q.rq [--base IRI] [--explain] [--repeat N] [--reference-render]
[--reference]` and `l4sbm11 serve GEN`. The id fragment (BGP, FILTER,
one level of GRAPH, GROUP BY with COUNT, DISTINCT, ORDER BY, LIMIT/OFFSET,
and since 2026-10-13 top-level OPTIONAL, below) runs on ids with PRM1 block skipping and merge/hash joins; since issue 823
(below) also residual FILTERs, ASK, CONSTRUCT, SELECT expressions and
aggregates; every other query
runs the reference evaluator over the quads the `quadEntriesForQuery` guard
selects; stderr names the path (`path=ids` or `path=reference`). FILTER on
ids: term identity only where `valueCompare` is term identity (IRI, string,
language-tagged constants), STRSTARTS by dictionary rank ranges, everything
else by the reference evaluator on decoded terms, memoised by ids. Record:
[`docs/designissues/2026-10-12-sbm11-stage4.md`](../../docs/designissues/2026-10-12-sbm11-stage4.md).
Gates for a change there: `tests/sbm11/run.sh` (oracle 21, printer, ids
against the fallback, the gate fixture with the anti-pattern 34 queries,
`prm-check`, `frame-check`), `tests/sbm11/census.sh` (W3C census on SBM11),
the `sbm11-query` case of `tests/stack/run.sh --canary`; timings with
`tests/sbm11/bench.sh GEN`. A query tool that changes routing must keep
the `ref-*` gate queries on `path=reference`.

Read verification is an option (2026-10-12,
https://github.com/danbri/factoidal/issues/796; record: section 9 of the
stage 4 record). `l4sbm11 query|serve|scan|count|dump|dump-ids ...
--verify merkle|none`; in Lean, `Sbm11Gen.openGen v` and
`Sbm11Query.openSession v` take a `Sbm11Gen.Verify` (no library default).
`merkle`: every read is widened to its 65,536-byte chunks and each chunk is
checked by its Merkle proof (PRM1 too since issue 805); GDX1 is read whole
on the first dictionary access and checked by SHA-256. `none`:
exact `pread` ranges, no hashing, only the manifest and the file lengths are
checked at open; a byte changed after activation is NOT detected
(`tests/sbm11/run.sh` part (g) pins this). CLI default: `none` when a
`CURRENT` pointer names GEN (activation checked every file), else `merkle`;
`--explain` prints `plan: verify=...` and why. `verify`, `activate`,
`stats`, `prm-check`, `frame-check` always check. The format is unchanged:
the packer writes the roots and `.merkle` sidecars either way. Bench one
mode with `VERIFY=none tests/sbm11/bench.sh GEN`.

Merkle reads are linear (2026-10-14, https://github.com/danbri/factoidal/issues/854;
record: section 11.2 of `docs/designissues/2026-10-11-shardborough-vs-qlever.md`,
"Time: the Merkle proof of each chunk"). Under `--verify merkle` a reader admits each
65,536-byte chunk of a file once, by a Merkle proof against the root in the manifest.
Until 2026-10-14 the proof of a chunk was computed from all the leaves of the file
(`BlockMerkle.proofWith?`: `n - 1` node hashes for `n` chunks), so a pass over a file of
`n` chunks hashed `n * (n - 1)` nodes. `dump` and `export` of a generation of 400,000
statements (a dictionary of 2,274 chunks) took 37.0 s of CPU time before the repair and
12.0 to 13.7 s after. `BlockMerkle.Tree` keeps the levels of the tree, computed once for
a file; `PosixRangeIO.VerifiedChunkCache` holds it with the admitted chunks. A proof is
`log2 n` reads (`Tree.proof?_ofLeavesWith`: the same proof as `proofWith?`), and
`ChunkedArtifact.verifyChunkWith` still checks the chunk against the manifest root. Rules
for a new reader of a file under `merkle`:

- Read through `readVerifiedRangeCached?` or `readVerifiedChunkCached?` with a cache
  from `newChunkCache` (`newVerifiedChunkCache`). `readVerifiedRange?` has no cache: it
  builds the proof table of the file once for the call (`treeOfLeaves`). A tool that
  reads several ranges of one file builds the table once and calls
  `readVerifiedRangeTree?` (`l4block-shard-merkle-scan` does). Until 2026-10-14
  (https://github.com/danbri/factoidal/issues/859) `readVerifiedRange?` computed the
  proof of the whole tree for each chunk: 4.0 s of user time for 2,048 chunks, 0.63 s
  after.
- To free memory, clear the chunks and keep the cache (`dropChunkRange`,
  `dropChunksBefore`, `dropDictChunks`): they keep the tree. A reader that passes over a
  permutation file in order calls `dropChunksBefore` with the offset of the next block.
  `dropChunkRange` for the block just read also forgets the chunk that the next block
  starts in.
- A reader that drops chunks and needs them again hashes them again. The olympics
  export under `merkle` fetched 2,020 MB to read 182 MB, 8.7 s more CPU time than under
  `none`. `dump` keeps up to `chunkKeepBytes` (16 MiB) of dictionary chunks for each file
  and drops them all when its window of 256 pages is full and a file holds more: on the
  olympics generation (GDV1 is 9.2 MB) it fetches each chunk once.
- Peak RSS of `dump --verify merkle` (issue 859): 184, 238 and 390 MB at 100,000, 200,000
  and 400,000 statements before the repair (1.66 bytes per output byte, 719 per
  statement); after: 60 to 62 MB at 100,000 and 200,000 statements and 64 or 78 MB at
  400,000 (0.02 to 0.13 bytes per output byte, 9 to 54 per statement). On the olympics
  generation: 45.7 MB
  against 116 MB, and 9 to 11 percent more user time, which comes from the window of 256
  pages (the objects are read in any order). Under `--verify none` the window stays 4,096
  pages: 256 pages cost 16 to 20 percent there.

Gate: the rows `sbm11-dump-time` and `sbm11-export-nq-time` of
`tests/stack/lean_scaling.sh` (100,000, 200,000 and 400,000 statements; 4x the data takes
at most 5.25 times as long; before the repair 6.0 and 6.7), `sbm11-dump-memory` (the
same sizes; at most 0.75 byte of peak RSS per output byte; before the repair 1.66) and
`merkle-range-read-time` (the user time of `l4merkle-range-read read --reader leaves` over
a file of 512, 1,024 and 2,048 chunks; at most 5.25 times; before the repair 12.1), and
`tests/merkle-range/run.sh` (the three readers of `PosixRangeIO` against a digest that
Python computes, with a changed byte in each chunk in turn: 1,223 pass, 0 fail, out of
1,223). Other effects, before and after:
`verify` (the activation checks) of 400,000 statements 27.1 s and 4.7 s of CPU time;
`scan GEN spo` over 100,000 statements 6.3 s and 3.4 s of CPU time; the slowest of three
runs of DBpedia d19 under `merkle` 9.9 s and 3.5 s. The warm time of d19 (3.4 s) did not
change, and it is the same under `none`: the 1.9 s of term decoding in
https://github.com/danbri/factoidal/issues/825 is another cost.

PRM1 by key range (2026-10-13, https://github.com/danbri/factoidal/issues/805;
record: section 13 of the stage 4 record). A query process never reads a
PRM1 file whole: the first use of a permutation reads its 22-byte header
(`PrmRange.openM`: magic, permutation code, block count, file length), and
each scan asks the store for the entries of its key range
(`IdQuery.Store.blocksForRange perm key`, `Store.blockCount perm`; the
`metas` field that held the whole array is gone). The I/O store answers with
`PrmRange.rangeM`: a binary search (one 92-byte entry per probe) for the
first block whose last row is not below the key prefix, a second for the
first block from there whose first row is above it, and one read of the
entries between; the answer is kept per key in the session. Proved:
`PrmRangeTheorems.rangeM_bytes` (over positioned reads of a PRM1 file that
decodes, the answer is `IdQuery.metasFor` of the decoded entries),
`rangeM_array` (the in-memory store), `scanFoldM_tuples_prm` (L4e over that
store). DBpedia slice d01 (one subject), `--verify none`: 220.0 ms and
8,210,091 bytes read per process before, 12.0 ms and 27,795 bytes after;
the process time is now about the start-up of the binary (10.5 ms with no
arguments).
Gates for a change there: `l4sbm11 prm-check GEN` on olympics and the
DBpedia slice, `tests/sbm11/process-start.sh` (d01 under 50 ms; exit 2
without the DBpedia slice), `tests/sbm11/run.sh`, `census.sh` and
`threads.sh`. The query and serve paths (`Sbm11Query.openSession`) read
PRM1 by range; `Sbm11Gen.openGen` (`scan`, `count`, `dump`, `verify`,
`activate`) decodes every PRM1 file at open, as before.

SBM11 stage 5 (2026-10-12, https://github.com/danbri/factoidal/issues/791):
updates and compaction. `l4sbm11 update GEN ('SPARQL UPDATE' | --file U.ru)
[--base IRI] [--sparql12]` appends one DLB1 batch to `GEN/deltas.dlog` (format
unchanged; every operation of SPARQL 1.1 Update, see the next paragraph).
Every `query`, `serve` and `compact` open replays
the batches after `compacted.epoch` into an overlay over ids
(`Sbm11Query.openOverlaid`): a term without a base id gets a tag-14 id
(`Overlay.tagDelta`, never a base id); `IdQuery.scanFoldM` merges the
overlay's sorted inserts and deletes into each block that has overlay rows
in its range (`Overlay.mergeRows`, proved in `OverlayTheorems`), other
blocks take the stage 4 path. stderr names `delta batches N, entries M,
overlay inserts I, deletes D, ...`. `l4sbm11 compact GEN OUTDIR` writes a
new generation through the packer's phases 2 and 3
(`Harness/Sbm11PackLib.lean` `packBatches`, shared with `l4sbm11-pack`)
from two scans of the overlaid SPO permutation; unused terms are dropped,
so the result is byte-identical to a fresh pack of the updated quads; then
`l4sbm11 activate ROOT NAME`. Quad (named-graph) generations replay their
log. Record:
[`docs/designissues/2026-10-12-sbm11-stage5.md`](../../docs/designissues/2026-10-12-sbm11-stage5.md).
Gates for a change there: `tests/sbm11/run.sh` parts (h) (the gate fixture,
batch by batch, against `l4factoidal` over the state
`tests/sbm11/delta_apply.py` computes; fresh pack; compaction byte-identical)
and (i) (olympics: insert seen, delete not seen, q01 to q21 equal to a fresh
pack, compaction at most 1.2 times pack time), and the `sbm11-delta` case of
`tests/stack/run.sh --canary`. Trap: a column built by reading
`cs[0]!` out of an array and storing it back keeps a second reference, and
every push copies the column (q01 over the overlay: 40 ms for 7 blocks, 8 ms
after `IdQuery.colsOfRowsGo` took the columns as separate arguments).

UPDATE with a WHERE clause and with blank nodes (2026-10-14,
https://github.com/danbri/factoidal/issues/849 and
https://github.com/danbri/factoidal/issues/850; record: section 10 of the stage 5
record). `l4sbm11 update` takes every operation of SPARQL 1.1 Update: INSERT
DATA, DELETE DATA, DELETE WHERE, DELETE/INSERT ... WHERE with WITH, USING and
USING NAMED, CLEAR, DROP, CREATE, ADD, MOVE, COPY, and LOAD SILENT (which does
nothing; any other LOAD is an error, as in the reference runner). The request
is ONE log batch (section 2.2 of the Update specification). The operations run
in order, each on the generation plus the log plus the entries of the earlier
operations; an error in any operation writes nothing and exits 1. The WHERE
clause runs on the evaluator of `l4sbm11 query`: the id path when
`IdQuery.translate` accepts the pattern and the operation has no USING clause,
otherwise the reference evaluator over the quads the planner guard selects
(stderr: `op N: where path=ids` or `where path=reference reason=...`). The
delete and insert templates are instantiated from the same solution sequence by
the reference functions (`UpdateStore.modifyDeleteQuads`,
`modifyInsertQuads`, `deleteWhereQuads`); the batch holds the removes, then the
adds. A blank node of INSERT DATA or of an INSERT template gets a fresh label
`sbm11u<n>`, written to the batch: one label for each INSERT DATA label in the
request, one for each template label and solution. The counter `n` starts at
the number of labels with that prefix in the dictionary and the log and skips
every held label, so a label is never one the store holds
(`UpdateStoreTheorems.chooseGo_spec`, `drawMany_spec`; `labels` group of
`tests/sbm11/update_where.sh`). Traps: `l4sbm11 dump` and `export` read the
BASE of a generation, so `compact` first; the store holds no empty named graph,
so CREATE, and CLEAR of a graph, leave no trace
(https://github.com/danbri/factoidal/issues/855); a graph named by a blank node
cannot be named in a log entry
(https://github.com/danbri/factoidal/issues/856); until 2026-10-14 the batch
encoder used 64 bytes of memory for each byte of log
(https://github.com/danbri/factoidal/issues/857) and every open replayed the log
with one dictionary lookup for each term (40,000 entries: 3 s; 203,264 entries:
58 s; https://github.com/danbri/factoidal/issues/858): both are repaired, see
the next paragraph. A `get` of an `IO.Ref` array
before its `modify` copies the array at every push (the replay was quadratic
for that reason until 2026-10-14): read and push in one `modifyGet`. The
decoder of the entries of a version 1 batch took one stack frame for each entry
until 2026-10-14 (`parseNFramedDeltaEntries`, now a loop named by an `@[csimp]`
lemma): a batch of 48,000 entries overflowed a 512 KB stack at every open. Gates:
`tests/sbm11/update_where.sh` (differential: every request against
`l4factoidal update`, by compaction and dump, and 7 queries on the overlay;
`scaling`: compile time for n and 4n solutions, replay time for n and 8n
entries) and `tests/sbm11/w3c_update.sh` (the 94 W3C Update evaluation tests
through the store and through the reference; since 2026-10-15 the store is packed
from TriG and exported as TriG, and every named graph is compared, also one with
no triple: `compare --empty keep`), parts (r) and (s) of
`tests/sbm11/run.sh`; the stack case `sbm11-update-where` of
`tests/stack/run.sh`; proofs in `SPARQL/UpdateStoreTheorems.lean` and
`Storage/Sbm11/UpdateOverlayTheorems.lean`.

The update path at scale (2026-10-14, https://github.com/danbri/factoidal/issues/857,
https://github.com/danbri/factoidal/issues/851 and
https://github.com/danbri/factoidal/issues/858; record: section 11 of the stage 5
record). The reader and the writer of the log work on a `ByteArray` by position
(`Storage/DeltaLogBytes.lean`), proved equal to the list functions of
`Storage/DeltaLog.lean` (`DeltaLogBytesTheorems.lean`; `parseLogChecked`,
`parseLogCheckedV1` and `appendPlan?` are replaced by `@[csimp]`). A new reader of a
log uses `parseLogChecked` or `DeltaLogBytes.parseLogCheckedBA` and never holds a
whole log as a `List UInt8`. The replay at open looks the distinct terms of the log
up in dictionary order (`Session.prefillBaseIds`, `Dict.lookupWalkM`, proved equal to
`lookupM` for any order of keys in `DictFingerTheorems.lean`), keeps their ids in
`Session.baseIds` for `idOf`, and applies the entries in log order, so the ids of
terms the dictionary does not hold are the same as before. `SBM11_REPLAY_LOOKUP=each`
runs the old replay (one lookup for each occurrence of each term): the oracle of the
`replay` group of `tests/sbm11/update_where.sh`; use it to compare two replays, never
in production. Numbers (olympics, the 101,632-solution update, 203,264 entries, 36
MB): update 3.0 s and 158 MB (was 15.9 s and 2.3 GB); replay at open 3.5 to 4.0 s
reading 1.8 MB (the old replay on the same log: 43 s reading 4.5 GB); an open after
`compact` and `activate`: 0.3 ms and 17 MB. The size limit of the log:
`l4sbm11 update GEN REQUEST --max-overlay-entries N --max-overlay-bytes N`, or the
environment variables `SBM11_MAX_OVERLAY_ENTRIES` and `SBM11_MAX_OVERLAY_BYTES`
(the flags override them; off by default; a log that holds exactly N is within the
limit). A request that would take the log past a limit, and every request when the
log is already over it, exits 1, writes nothing and says to run `l4sbm11 compact` and
`l4sbm11 activate` and repeat the request. `l4sbm11 serve` prints `serve: overlay
size: ...` and whether the log is within the limit the environment sets. Nothing
compacts by itself (https://github.com/danbri/factoidal/issues/803 item 4; the
expected failure `xfail-auto-compaction`). Traps: a positioned read of the store is
`open`, `fstat`, `pread` and `close` of the file (four system calls), so count reads
before time (`strace -c -f`); a hash set or map that grows hashes every term again, so
size it for the entries; the cut of the overlay state into its four permutations does
not run in tasks (a state that two threads reach is never updated in place, and
`Run.sync` updates it: `skills/lean4-performance`, "Values that two threads can
reach"). Gates: `tests/stack/lean_scaling.sh --only
sbm11-update-memory,sbm11-open-log-memory,sbm11-replay-time` (these three rows), and
the groups `replay`, `limit` and `scaling` of `tests/sbm11/update_where.sh`.

Delta log tails (2026-10-14, https://github.com/danbri/factoidal/issues/843;
record: section 8 of the stage 5 record). Only a crash artifact at the end of
a log is a torn tail: the final frame is cut short, or it is complete and
fails its checksum. A frame that fails its checksum with bytes after it
(`damaged`) and a committed frame whose checksum verifies but whose body does
not decode (`undecodable`) are errors for every reader
(`Storage.classifyTail`, `parseLogChecked`; browser: `LogRead.error?`,
`mergeChecked`). Until then `l4sbm11 query`, `serve` and `compact` and the JS
`deltaLogMerge` used the batches before such a frame with exit 0 and no
message, and a compaction followed by activation lost it and every later
batch. A torn final frame keeps each reader's rule: SBM11 query, serve and
compaction use the batches before it (stderr: `torn final frame left out`);
the IBK3 paths, `StoreEndpoint` and the writers refuse the log until it is
removed. A new reader of the log uses `parseLogChecked`, never `parseLog` and
its tail. Gates: `tests/delta-log/run.sh`, the `#guard`s of `DeltaLog.lean`,
`BrowserLog.lean` and `Wasm/Ops/DeltaLog.lean`,
`npm/factoidal/test/delta-log.test.mjs`.

Delta log versions (2026-10-14, https://github.com/danbri/factoidal/issues/792
item 1; record: section 9 of the stage 5 record). A DLOG of header version 2
may hold RDF 1.2 terms (triple terms nested in the object position,
directional literals), encoded by `serializeDeltaTerm?`/`parseDeltaTerm`;
version 1 uses the shared `serializeTerm?`/`parseTerm`, which keep refusing
them (BLK0, IBK1, IBK2, PTD1, TLI1 are unchanged). `l4sbm11 update --sparql12`
creates a version 2 log, or sets a version 1 log to version 2 in place, before
the first batch with an RDF 1.2 term (`appendPlan?`); a log without one stays
version 1, byte for byte. The SBM11 tools read both versions; the IBK3, IBK4
and IBK5 readers refuse version 2 (`parseLogCheckedV1`); every reader refuses
another version at the header. A new reader of a delta log uses
`parseLogChecked` (SBM11) or `parseLogCheckedV1` (the other layouts). Gates:
`tests/sbm11/run.sh` part (m), `tests/delta-log/run.sh` (DLOG versions), the
`delta-log-triple-term` case of `tests/stack/run.sh --canary` (depth 300,000),
`DeltaLogCodecTheorems.lean`.

Delta log version 3 and graph slots (2026-10-15,
https://github.com/danbri/factoidal/issues/855 and
https://github.com/danbri/factoidal/issues/856; record: section 12.6 of the
stage 5 record). A log entry names a graph by a `DeltaGraphName`: an IRI or a
blank node. A DLOG of header version 3 holds the entries of version 2 and the
entries that name a graph by a blank node (graph tag 2; entry tags 5 and 6 for
DROP and CREATE); every entry that version 2 admits has the same bytes. A log
gets version 3 in place before the first batch with such an entry
(`appendVersion`, `AppendPlan.setVersion`) and keeps its version and its bytes
otherwise. The SBM11 tools read versions 1 to 3; the IBK3, IBK4 and IBK5 readers
refuse versions 2 and 3 (`v1Refusal?`); the readers before this change refuse
version 3 at the header. The replay keeps the graphs that the log created and
dropped (`Overlay.State.created`, `dropped`): the named graphs of the overlaid
generation are `Overlay.denoteNamed` over the graph list (`Session.hasNamedGraph`,
`Session.namedGraphIds`). CREATE adds a graph with no triple, CLEAR and DELETE
keep the graph, DROP removes it; CLEAR NAMED, CLEAR ALL, DROP NAMED and DROP ALL
act on every named graph, also one with no triple and one named by a blank node;
ADD, COPY and MOVE create a named destination. Compaction writes the named graphs
of the overlaid generation into the graph list. Gates: `tests/sbm11/update_where.sh`
group `graphs`, `tests/delta-log/run.sh` (DLOG versions), `OverlayTheorems`
(`named_*`), `DeltaLogCodecTheorems` (`parseLog_v3_of_frames`, `appendVersion_noV3`).

Queries over named graphs with no triple (2026-10-15,
https://github.com/danbri/factoidal/issues/855). The id path reads triples only,
and refuses every shape that can see a graph with no triple: a GRAPH group with no
triple pattern or with only a FILTER, MINUS, OPTIONAL inside GRAPH. (FROM and FROM
NAMED run on ids since 2026-10-23, issue 953: the id path then reads triple
patterns only, and a graph with no triple gives no row to a triple pattern.) The reference fallback (`selectedDataset`, also for the WHERE clause of
`l4sbm11 update`) puts every named graph of the overlaid generation that the
planner guard keeps into its dataset (`Session.namedGraphIds`), a graph with no
selected quad with no triple, so `GRAPH ?g { }` and FROM NAMED see it. The
reference for such a dataset is `l4sbm11-w3c query-source` and `update-source`:
`l4factoidal query` reads N-Quads, which cannot state a graph with no triple.
Gate: `tests/sbm11/named_graphs.sh`.

OPTIONAL on ids (2026-10-13, https://github.com/danbri/factoidal/issues/775;
record: section 10 of the stage 4 record). `{ base OPTIONAL { g1 } ...
OPTIONAL { gk } }` at the top level runs on `path=ids` when the base is a
group of the id fragment, each group is triple patterns of the default graph
and FILTERs over the group's own variables, a variable of a group that the
base does not bind occurs in no other group, and a FILTER beside the
OPTIONALs reads base variables only (`IdQuery.flattenOptional`; every other
OPTIONAL shape goes to the reference fallback). Each group's BGP is
evaluated, its FILTERs applied to its rows, then `OptJoin.leftOuterJoin`
(merge on a shared sort variable, else a hash index probed in left order);
an unbound variable is id 0 in its column (`OptJoin.unbound`): the renderer
leaves it out, ORDER BY puts it first, `COUNT(?x)` skips it
(`IdQuery.countItems`). Theorems: `Storage/Sbm11/OptJoinTheorems.lean`
(lemmas L5g, L5g′ of the end-to-end record; the `Table` step L5g″ is open
and tested by `#guard`s). Since issue 809 (next paragraph) the group's first
scan takes the left keys as candidates when the rule selects it.
DBpedia d11 (OPTIONAL): 48.7 s warm and 849 MB on the reference fallback
before; 17.2 ms warm and 25.6 MB on ids (2026-10-13). Gates: `tests/sbm11/run.sh` part (d), the 16
`ids-optional-*` and 6 `ref-optional-*` queries; a change that admits more
OPTIONAL shapes must move a `ref-optional-*` query to `ids-` only with a
gate query that the reference semantics decide. Trap: until 2026-10-13 the
reference evaluator evaluated a FILTER in an OPTIONAL group on the group's
row only (https://github.com/danbri/factoidal/issues/815). The Lean parser
now makes the group's FILTERs the LeftJoin condition, evaluated on the merged
row (SPARQL 1.1 section 18.2.2.5; `optionalGroup`, theorems in
`SPARQL/OptionalFilterScope.lean`); the F* engine still has the defect
(known-defects case `SPARQL-OPT-FILTER-SCOPE`). The id path still refuses a
group FILTER over a left-side variable (`IdQuery.flattenOptional` reads the
condition and throws), so such a query takes the reference fallback
(`ref-optional-filter-outer.rq`), which now answers section 18.2.2.5. Admitting
it on ids is open.

Inline VALUES on ids (2026-10-22, https://github.com/danbri/factoidal/issues/950;
record: section 17 of the stage 4 record). A VALUES block in the WHERE clause,
and a trailing VALUES block of a query that does not group (the parser joins
it with the WHERE pattern, `attachValues`), runs on `path=ids` when it is
outside GRAPH, the WHERE clause has no OPTIONAL, its variables are distinct,
and no FILTER reads one of its variables (`IdQuery.flattenWhere`; a trailing
VALUES block after GROUP BY goes to the reference post-processing on decoded
rows, `selectPost`). `IdQuery.resolveValuesM` makes each block an id table
(UNDEF is id 0, `OptJoin.unbound`); a term that has no id in the generation
gets a query-local id, tag 15 (`IdQuery.tagLocal`), one per distinct
`normalizeTerm`, which joins with no stored id and which `Store.withLocal`
decodes when the term reaches the answer. `IdJoin.joinIds` joins each block
with the table of the triple patterns (compatible: equal ids, or one side
id 0). `evalBgpM` drops the columns that `need` does not name, so
`runPlanM` adds the VALUES variables to `need`; without them the join has no
shared column and computes a cross product. Theorems:
`Storage/Sbm11/IdJoinTheorems.lean` (`join_decode`, `values_decode`, lemma
L5l; the `Table` step L5l″ is open and tested by `#guard`s). Gates: the 15
`ids-values-*` and 3 `ref-values-*` gate queries.

UNION on ids (2026-10-22, issue 950; record: section 18 of the stage 4
record). A chain `{ P1 } UNION ... UNION { Pk }` outside GRAPH runs on
`path=ids` when the WHERE clause has no OPTIONAL, each branch is a group of
the id fragment with a triple pattern and no VALUES or UNION inside, and no
FILTER outside the branches reads a branch variable (`IdQuery.flattenUnions`;
`whereVars` walks the UNION, `scopeVars` does not count its variables, so
`splitFilter` refuses such a FILTER). Each branch is evaluated with every
column kept, the tables are concatenated (`IdJoin.unionIds`, id 0 where a
branch lacks a variable), and the result is joined with the other rows
(`IdJoin.joinIds`). `l4sbm11 update` redirects the branch patterns under
`WITH` too (`redirectPlan`). Theorems: `union_decode`, `unionChain_decode`
(lemma L5m). Gates: 10 `ids-union-*` and 4 `ref-union-*` queries.

FROM and FROM NAMED on ids (2026-10-23, https://github.com/danbri/factoidal/issues/953;
record: section 19 of the stage 4 record). `IdQuery.datasetSpec` reads the
dataset clauses (a FROM IRI given twice is one graph; a FROM NAMED IRI given
twice is refused, because the reference then iterates that graph twice), and
`IdQuery.resolvePatIn` resolves each pattern under it, as `applyDataset`
builds the dataset from the store's named graphs. A default-graph pattern
reads: no graph when no FROM IRI names a graph of the store (`missing`); one
graph as `GRAPH <iri>`; several graphs as the RDF merge (`Pat.merge`:
`scanPatM` scans each graph with every variable of the pattern, concatenates,
removes duplicate rows, then projects; one row per triple of the merge, set
merge as `Graph.union`). `GRAPH <iri>` reads the graph only when a FROM NAMED
IRI names it; `GRAPH ?g` keeps the rows of the FROM NAMED graphs
(`Pat.gnames`). The streamed single-pattern paths take only plain patterns
(`Pat.plain`). Blank nodes are not renamed apart: one label is one blank node
across the store's graphs, as in the reference. Theorems (`IdDatasetTheorems`,
lemma L5n): `lookup_decode`, `from_default_decode`, `from_named_decode`,
`mergedRows_eq`. Gates: 23 `ids-from-*` and 1 `ref-from-*` queries.

BIND on ids (2026-10-23, https://github.com/danbri/factoidal/issues/953;
record: section 20 of the stage 4 record). A chain `Extend(... Extend(P, v1,
e1) ..., vk, ek)` outside GRAPH runs on `path=ids` when the WHERE clause has
no OPTIONAL, `P` is a group of the id fragment with no VALUES, UNION or BIND
inside (it may have no triple pattern), and each expression is EXISTS-free
with no aggregate and no `UUID()`, `STRUUID()` or `BNODE()` (their value
depends on the row index, which the id path does not keep in the reference's
order) (`IdQuery.flattenBinds`). The block is evaluated by itself
(`evalBindsM`): `P` on ids, then per row `IdQuery.refBinder` (the binder the
reference lowers a top-level BIND to) on the decoded terms of the variables
the expression reads, once per distinct tuple of their ids; a value gets the
store's id or a query-local id (tag 15, `termIdM`), an error leaves the
variable unbound (`extendM`). The block's rows are joined with the other rows
after the VALUES and UNION blocks. A FILTER of the top group that reads a
variable of a BIND block runs after every join (`Plan.lateFilters`); a FILTER
in an inner group that reads one is refused (bind10 shape). `l4sbm11 update`
redirects the block patterns under `WITH`. Theorems (`IdBindTheorems`, lemma
L5o): `lower_bind`, `refBinder_active`, `extend_decode`, `bind_decode`. Gates:
18 `ids-bind-*` and 6 `ref-bind-*` queries; `gate/ref-bind.rq` is now
`ids-bind-str.rq` and `gate12/ref-tt-bind.rq` is now `ids-tt-bind.rq`.

Property paths on ids (2026-10-23, https://github.com/danbri/factoidal/issues/954;
record: section 21 of the stage 4 record). A pattern `s path o` outside GRAPH
runs on `path=ids` when the WHERE clause has no OPTIONAL and no FROM
(`IdQuery.flattenWhere` collects `PathBlock`s). `IdQuery.evalIM` computes the reference's
`SPARQL.evalPath` on ids under a restriction (a constant endpoint, else the ids
the rows joined so far hold for an endpoint variable, `pathCands`): a step is a
PSO or POS scan with the restriction as candidates; a sequence restricts its
second part to the objects of its first; `^p` drops a pair whose new subject
is a literal, as the reference does (`isNotLiteral`). The pair rows are joined
after the BIND blocks; a FILTER of the top group over an endpoint variable runs
after every join. Theorems (`IdPathTheorems`, lemma L5p): `evalPath_decode`,
`pathRows_decode`, `pathPattern_decode`. Gates: `ids-path-*` and `ref-path-*`
queries.

Closures on ids (2026-10-23, issue 954; record: section 22 of the stage 4
record). `p*`, `p+`, `p?` run on ids too (`IdQuery.closureM`): the step pairs
reachable from the restriction are collected in rounds of scans with
candidates, then a worklist per start node (`IdPath.reachPlus`). The
worklist bound (pairs plus two) is proved sufficient for its list model
(`reachModel_some`); the rounds bound is a bound on the number of distinct ids,
and each round adds one; either loop fails the query, never truncates, if its
bound runs out. `p*` and `p?` add `(n, n)` for each node of the active graph, so
`?s p* ?o` with both ends variables scans the whole graph for its nodes, as
the reference semantics require. Trap: the reference's `pathFixpoint step
step` for `p+` stops on a length test that is not a fixpoint test when the
step relation has a pair twice (`(p1/p2)+`, `(p|q)+` can have one); the id
path computes that relation first and refuses with an error that starts with
`refused:`, and the harnesses (`runOne`, `Run.evalWhere`) then run the
reference evaluator. A refusal after reading must come before the first
`emit` (`resolveExtrasM` runs first in `runPlanM`). Theorems
(`IdPathClosureTheorems`, lemma L5q): `fixpoint_mem`, `star_mem`, `plus_mem`,
`reachModel_some`, `reachModel_mem`, `starFrom_mem`, `plusFrom_mem`.

Sideways information passing (2026-10-13,
https://github.com/danbri/factoidal/issues/809; record: section 11 of the
stage 4 record). The right scan of a join (merge or hash), and the first scan
of an OPTIONAL group, take the sorted distinct left values of their sort
variable as candidates when `16 × left rows < the scan's PRM1 estimate`
(`IdQuery.sipRule`, `scanForJoinM`); a block whose first and last rows bound
the join column away from every candidate is not read (`Sip.mayHold`); in a
block read, only the join column is decoded (`Sip.findWords`, nothing written
for a row that does not match) and the other columns at the found rows only
(`Sip.gatherWords`, a delta frame stops after the last found row). `l4sbm11
query --sip auto|always|off` (default auto; `always` for tests); `--explain`
prints `sideways ?v: K candidates, blocks skipped B, key values tested T,
rows gathered G` per scan and a `total: rows decoded ...` line. Theorems:
`Storage/Sbm11/SipTheorems.lean`, `SipScanTheorems.lean`,
`SemiJoinTheorems.lean` (lemmas L4g, L4h, L4i, L5h of the end-to-end record:
the scan with candidates is the full scan filtered; a join over it is the
same join). DBpedia d05 (2026-10-13, median of three rounds): rows decoded
4,000,148 to 3,164, warm 365 to 76 ms, peak RSS 83 to 27 MB. Gates: `tests/sbm11/run.sh` part
(l) (every `ids-*` gate query with `--sip always` on the gate fixture packed
with blocks of 2 rows; olympics q01 to q21 and `tests/sbm11/sip/*.rq` under
off, auto and always), `SBM11_SIP=always tests/sbm11/census.sh`, and the
`sbm11-query` case of `tests/stack/run.sh` (150,000 candidates over blocks
of 65,536 rows). Traps: a hash join over a reduced right side may change the
output row order (the hash side is chosen by size), so compare answers as
multisets; a candidate test that needs a correct start pointer is a proof
obligation, so the pointer is a hint that `Sip.startFor` checks and resets.

Id path coverage (2026-10-13, https://github.com/danbri/factoidal/issues/823;
record: section 12 of the stage 4 record). (1) A FILTER conjunct outside
`Expr.backendLocal` (REGEX, LANGMATCHES, casts, IRI(), hashes), or one over a
variable no pattern binds, is a residual conjunct (`FKind.residual`): the
reference FILTER (`IdQuery.residualHolds`, with the query's NOW, BASE and
extension functions) on the decoded terms, memoised by ids, after the joins
of the BGP; admitted when every variable it reads is bound by its group
(`scopeVars`) or by no pattern at all (`whereVars`). A FILTER beside the
OPTIONALs over a group variable runs after the left joins
(`Plan.postFilters`). (2) ASK, CONSTRUCT and a SELECT clause outside the id
projection (expressions, aggregates other than COUNT, HAVING, GROUP BY or
ORDER BY an expression, REDUCED) run the WHERE clause on ids, decode the rows
(`decodeRowsM`) and call the reference's own `selectPost`,
`formHasSolution`, or `formSolutions` with `constructGraphOf`
(`IdQuery.runPostM`; `--explain` prints `post: N WHERE solutions decoded;
reference ...`). `firstRowsOf` cuts the WHERE rows to 1 (ASK without
modifiers) or OFFSET + LIMIT (no grouping, ORDER BY, DISTINCT). EXISTS, NOT
EXISTS anywhere, FROM and DESCRIBE stay on the fallback. COUNT stays on
ids. Theorems: `Storage/Sbm11/IdPostTheorems.lean` (lemma L5i: the residual
FILTER is the reference FILTER for every active graph; `evalConstruct_eq`;
the first-rows cuts); open: L6a. W3C census: id path 230 to 438 of 605, 0
differed. DBpedia d18 (REGEX after a join) 59.6 ms warm, 23.8 MB on ids (the
fallback was killed at 13.9 GB); d19 (MAX, AVG per group over 326,365 joined
rows) 3.2 s, 151.5 MB on ids, 25.3 s and 832 MB on the fallback; most of
d19's time was `Session.termOf` decoding the rows (since 2026-10-15 d19 aggregates
on ids: 0.5 s, 51 MB, next paragraph). Gates: `tests/sbm11/run.sh`
parts (d), (h), (l) with the `ids-ask-*`, `ids-construct-*`, `ids-expr-*`,
`ids-agg-*`, `ids-filter-*` and `ref-*` queries; `tests/sbm11/census.sh`,
whose CONSTRUCT and DESCRIBE answers `compare_answers.py` now compares line
by line (blank node labels masked). Traps: a residual FILTER over a variable
bound outside its group must stay refused (inside the group it is unbound);
a gate query that answers nothing checks nothing (d18's first REGEX matched
no row); run the fallback for a measurement under `ulimit -v`.

Grouped aggregates on ids (2026-10-15, https://github.com/danbri/factoidal/issues/825;
record: sections 15 and 16 of the stage 4 record). A SELECT with GROUP BY
variables (or none) whose items are variables or non-DISTINCT COUNT, SUM, MIN,
MAX or AVG of a variable (`AggStream.aggPlan?`) no longer decodes its WHERE
solutions. `IdAgg.aggregateM` groups the id table in one pass (key: the ids of
the GROUP BY columns, in order of first row), steps the accumulators of
`AggStream` with a `Summary` for each distinct id (a `Cache`; `COUNT(?x)`
decodes nothing), decodes the first row of each group, and `IdQuery.runPostM`
gives the rows to the reference's own tail (`groupedTail`: ORDER BY,
projection, DISTINCT, OFFSET, LIMIT). The group columns must hold blank nodes,
IRIs, inline integers or inline booleans (tags 1, 2, 4, 5); any other id or an
unbound value sends the query to the decoded path. `--explain` prints `post: N
WHERE solutions aggregated on ids into G groups (D distinct ids decoded, R
values in the representative rows)`; `l4sbm11 query --no-agg-ids` turns the
plan off, and the two answer byte for byte. Theorems (`SPARQL/AggStream.lean`):
`evalAggregate_stream`, `evalAggregate_star`, `varView_ne_error`,
`selectPost_grouped`, `selectPost_aggPlan`; `IdAgg.Cache.getPure_list`;
`TermKeyFast.decodeKeySlice?_eq`; `RDF.isIri_eq_isIriFast` (`@[csimp]`). Open:
lemma L5k (the groups of the pass are those of `groupWhere`; tested). DBpedia
d19 (MAX and AVG per country, 326,365 joined rows, 2026-10-15): warm 3,008 to
507 ms, cold 2,967 to 546 ms, peak RSS 150.9 to 50.8 MB, answers byte-identical
to the build before and to `--reference`. Still decoded, each an expected
failure in `tests/sbm11/agg_ids.sh` that names
https://github.com/danbri/factoidal/issues/861: HAVING, DISTINCT aggregates,
GROUP_CONCAT, SAMPLE, expressions, literal or unbound group keys, the
variables of a representative row, and MIN and MAX over IRIs (every distinct IRI
is decoded). Against the other engines (same machine and day, 2026-10-15, record
`2026-10-12-three-engine-benchmark.md` section 11.10): d19 warm 511 ms, Virtuoso
(1 thread) 293 ms, QLever (1 CPU) 103 ms; the remaining cost is
https://github.com/danbri/factoidal/issues/862 (expected failure
`xfail-d19-warm-300ms`). Gates: `tests/sbm11/run.sh` parts (d), (h),
(l) with the `ids-agg-*` queries, part (m) with `ids-tt-agg-*`, and part (t)
(`agg_ids.sh`, with six DBpedia queries in `tests/sbm11/agg-dbpedia`);
`IdAggTests` (build-time `#guard`s);
`tests/sbm11/census.sh` prints how many id-path tests aggregate on ids (9 of
438). Traps: the gate prints `path=ids` for both paths, so `agg_ids.sh` checks
`aggregated on ids`; COUNT alone with GROUP BY variables is the older counted
path, so a gate query of the new path needs a second aggregate; a high-cardinality
grouping (hundreds of thousands of groups) takes its time in the dictionary
pages and the JSON output, so the pass gains nothing there and must not lose:
decode the representative rows through the same term cache as the aggregate
arguments (the page cache of 2,048 pages is emptied when full, and an
uncached decode of the same IRI for each group took 18.8 s against 12.6 s).

Parallel block scans (2026-10-12 and 2026-10-13,
https://github.com/danbri/factoidal/issues/799; record:
[`docs/designissues/2026-10-12-parallel-block-scans.md`](../../docs/designissues/2026-10-12-parallel-block-scans.md)).
`l4sbm11 query --threads N` cuts the selected blocks of a scan into
consecutive block ranges (`ParallelScan.chunksOf`, at most N ranges and at
most one per 8,192 estimated rows, `IdQuery.rangeCount`) and runs one Lean
task per range. Stage 1: the BGP scans of `evalBgpM` (`scanTableParM`; tables
appended in range order, `ParallelScanTheorems.parallel_acc_eq`). Stage 1b:
one pattern that streams (ranges render their rows; the parent emits the
OFFSET/LIMIT window; only when OFFSET + LIMIT is above the estimate, so that
both read the same blocks), counts (range group maps merged in range order,
`Groups.merge`) or orders with LIMIT (ranges keep their first OFFSET + LIMIT
rows, `finishM` orders the union); `ParallelMergeTheorems` proves the merges
as list lemmas. `--threads 1` is the single-thread code. A task makes its own
copies of the spec and FILTERs (`ScanSpec.fresh`) and its own page cache;
the tasks share loaded pages in `taskPages`. Gates: `tests/sbm11/threads.sh`
(gate fixture, gate fixture with 2-row blocks and the coverage of the three
divided paths, olympics, DBpedia d01 to d17 against the three-engine record;
byte counts compared with `SBM11_PAGES=1000000`), `SBM11_THREADS=4
tests/sbm11/census.sh`. Traps: a value two threads can reach is never
updated in place and its reference counts are atomic (skill
`lean4-performance`, section "Values that two threads can reach"); with the
default page limit, a query that touches more than 2,048 dictionary pages
loads pages again on every run, and its dictionary byte counts depend on the
order of the tasks. Numbers (4 threads against 1, 2026-10-13): DBpedia d13
0.31, d16 0.33, d10 0.57, d17 0.96; olympics q21 0.42, q19 0.65.

Activation's exact permutation check and the scan theorem (2026-10-12,
https://github.com/danbri/factoidal/issues/776; record: sections 9 and 10 of
[`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`](../../docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md)).
`l4sbm11 verify` and `activate` now also check exactly that POS, SPO and OSP
hold the quads of PSO (`Harness/Sbm11PermCheck.lean`). Since 2026-10-22
(https://github.com/danbri/factoidal/issues/810) the rows are re-keyed to PSO
rows and cut into segments: one per predicate for POS (POS and PSO both
start with the predicate), the whole permutation for SPO and OSP. Each
segment is sorted and compared row by row with the next PSO rows; a segment
above `SBM11_VERIFY_GROUP_ROWS` rows (default 131,072) is written as sorted
runs (compressed with the column encoder of the packer) in `GEN.verify-PID`
and merged. Sorting and comparing run in background tasks
(`SBM11_VERIFY_SPILLS`, default 6 runs sorted at once), in segment order.
stderr prints `exact permutation check: segments=... runs=... failures=...
temp-written-bytes=... temp-peak-bytes=...`. The check is proved to give
equal quad multisets (`PermSet.perms_same`, lemma L3b). Measured: olympics
temporary peak 4.2 MB for a 34.8 MB generation (the bucket method of
2026-10-12 wrote 171 MB); DBpedia 173 MB for 568 MB. Gate:
`tests/sbm11/perm_check_disk.sh` (peak at most half the generation), run
as part (w) of `tests/sbm11/run.sh`.
`SBM11_VERIFY_DIGEST=0` turns the digest comparison off (test support).
The scan (`IdQuery.scanFoldM`) is a `forIn` over `blocksFor` with the body
`scanBlockM` and pure per-block functions; `ScanFoldTheorems.scanFoldM_tuples`
proves it returns exactly the kept rows of an admitted permutation (no
overlay, `m = Id`). Keep the per-block functions pure when changing the scan,
and run the old-against-new `#guard`s of `ScanFoldTests.lean` (update
`OldForms` only when the output is meant to change). Gate:
`tests/sbm11/run.sh` part (j).

Format registry rows (wire version 11):

| Name | File | Status | Definition |
| --- | --- | --- | --- |
| GDV1, GDX1 | `dict.gdv1`, `dict.gdx1` | landed (stage 2); key class 7, triple terms, 2026-10-14 | `Storage/Sbm11/Dict.lean`, `TermKey.lean` |
| PRB1 | `<perm>.prb1` | landed (stage 3); column codecs 0 constant, 1 raw, 2 delta; 3 zstd reserved and refused | `Storage/Sbm11/Column.lean`, `Block.lean` |
| PRM1 | `<perm>.prm1` | landed (stage 3) | `Storage/Sbm11/Block.lean` |
| SBM11 manifest | `manifest.sbm11` (`"SBM0"` version 11) | landed (stage 3); the roles of stage 3, or the same roles with `GNL1` after the dictionary, 2026-10-15 | `Storage/Sbm11/Manifest.lean` |
| GNL1 | `graphs.gnl1` | landed 2026-10-15 (https://github.com/danbri/factoidal/issues/855, https://github.com/danbri/factoidal/issues/856): the dictionary ids of all named graphs of the dataset, a graph with no triple included, strictly increasing, tag 1 (blank node) or 2 (IRI); only in a generation that has a named graph | `Storage/Sbm11/GraphList.lean`, `GraphListTheorems.lean` |
| DLOG | `deltas.dlog` | version 1; version 2: RDF 1.2 terms (2026-10-14, https://github.com/danbri/factoidal/issues/792 item 1); version 3: a graph named by a blank node, graph tag 2 and entry tags 5 and 6 (2026-10-15, https://github.com/danbri/factoidal/issues/856). A log has the lowest version that admits all its entries | `Storage/DeltaLog.lean`, `DeltaLogBytes.lean`, `DeltaLogCodecTheorems.lean` |

## The source layer: the store takes a dataset, not a syntax (2026-10-14)

Owner rule, 2026-10-14 (CLAUDE.md, section "Shardborough is a persistent store
for very large data"): the store takes the RDF abstract syntax from one source
layer and gives it to one serialiser layer. A concrete syntax is named only at
those two edges. No file under `formal/lean4/L4Factoidal/Storage/` imports a
module of `L4Factoidal.Syntax`. Tracking:
https://github.com/danbri/factoidal/issues/837. Design record:
[`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](../../docs/designissues/2026-09-03-rdf-parsing-strategy.md)
section 3f.

**Modules.**

- `L4Factoidal/RDF/Format.lean`: `RdfFormat` (N-Triples, Turtle, N-Quads, TriG,
  RDF/XML, JSON-LD) is the only format table. `formatOfExtension` and
  `formatOfPath` map a file name to a format. `formatOfLabel` and `formatLabel`
  map the `--format` label.
- `L4Factoidal/RDF/Source.lean`: `Source.parseDocument` reads a whole text.
  `Source.Reader` and `Source.ByteReader` read chunks and give each quad to a
  consumer `Step`. `Source.Prepass` computes the blank node prefix for Turtle
  and TriG.
- `L4Factoidal/RDF/SourceJsonLd.lean`: the JSON-LD parser (`Source.withJsonLd`).
  The core wasm does not link it.
- `L4Factoidal/RDF/SourceTheorems.lean`: the theorems, below.
- Users of the layer: `Storage/PackStream.lean` (the IBK2 to IBK5 packers),
  `Wasm/Ops/Pack.lean` and `Wasm/Ops/Parse.lean` (wasm),
  `Harness/Sbm11PackLib.lean` (`l4sbm11-pack` through `fileRangeSource`,
  `l4sbm11 canon` through `streamRange`),
  `Harness/Sbm11DictPack.lean` (`l4sbm11-dict-pack`, through
  `Sbm11Pack.streamRange`), `Wasm/Cli.lean` (`l4factoidal parse FILE`: the strict
  route `streamStrictFile`, with `Source.Prepass` for Turtle and TriG),
  `Harness/PredicateShardPack.lean` (`l4block-shard-pack`). None of them has a
  format table: each one gets an `RdfFormat` from `formatOfLabel` or
  `formatOfPath`.
- `L4Factoidal/RDF/Sink.lean`: the serialiser layer, the other half of the source
  layer. `Sink.serializeDataset` writes a whole `Dataset`. `Sink.Writer` (`init`,
  `push`, `finish`) writes quads one at a time. `Sink.GraphChoice` says what a
  syntax with no graph name does with a quad in a named graph.
- `L4Factoidal/RDF/SinkJsonLd.lean`: the JSON-LD writer (`Sink.withJsonLd`). The
  core wasm does not link it.
- Users of the serialiser layer: `Harness/Sbm11Export.lean` (`l4sbm11 export`),
  `Harness/SourceConvert.lean` (`l4source-convert`), `Wasm/Cli.lean`
  (`l4factoidal parse FILE --out F`: `ntriples`, `trig`, `rdfxml` and `jsonld`
  through `Sink.serializeDataset`; `nquads` and `turtle` keep their older writers,
  see section 3g of the parsing strategy record).

**What each syntax does.**

| Syntax | Extensions | Reader | Phase 1 of `l4sbm11-pack` |
| --- | --- | --- | --- |
| N-Triples | `.nt` `.ntriples` | line stream; strict: a graph name is an error | K byte ranges cut at line starts, K workers |
| N-Quads | `.nq` `.nquads` | line stream | K byte ranges, K workers |
| Turtle | `.ttl` `.turtle` | chunk fold | K byte ranges cut at dot boundaries found by one read of the bytes (`SplitScan`), K workers |
| TriG | `.trig` | chunk fold | K byte ranges cut at dot boundaries, at the top level or inside a graph block, K workers |
| RDF/XML | `.rdf` `.xml` `.owl` `.rdfxml` | chunk fold: one child of `rdf:RDF` at a time (`RdfXmlChunkFold`); the whole document under the fall-back rule below | one worker |
| JSON-LD | `.jsonld` `.json-ld` | chunk fold: one top-level node object at a time (`JsonLdChunkFold`), for an array or `{"@context":C,"@graph":[...]}`; the whole document otherwise | one worker |

`l4sbm11-pack` and `l4sbm11 canon` read RDF 1.2 syntax, which includes RDF 1.1
syntax for these grammars. The format comes from `--format` or from the
extension. An unknown extension is an error that asks for `--format`: these two
commands have no default syntax. `l4block-shard-pack` keeps its older rule (an
unknown extension is Turtle) and reads RDF 1.1 for `ibk4` and RDF 1.2 for `ibk5`.
The `ibk2` and `ibk3` layouts read Turtle only.

**RDF/XML in chunks (2026-10-22,
https://github.com/danbri/factoidal/issues/838).** `Syntax/RdfXmlChunkFold.lean`
keeps the characters until the start tag of the document element is complete,
reads the prologue and that start tag with the XML parser's functions, then scans
the content of `rdf:RDF` for the end of each top-level item (element, comment,
processing instruction, CDATA section, text run), parses that item alone with
`XML.parseChildren` and the document's entity table, and gives each element to
`RdfXml.nodeElement` with the state the previous child left. The pack holds one
chunk and one item. Fall-back rule (the whole document goes to
`RdfXml.parseRdfXml`, as before): the prologue or the root start tag does not
parse that way or the text ends first; the document element is not `rdf:RDF`, or
is empty; XML 1.1; a general entity that is external or whose replacement text
holds `<` or `&`; a prologue of more than 8 Mi characters. Error messages can
differ from the whole reader's (another error can come first); acceptance and
the triples are measured equal: `tools/rdfxml-chunk-differential.sh` (308 files,
2432 agree, 0 differ (out of 2432) on 2026-10-22). Row
`sbm11-pack-rdfxml-memory`: 0.51 bytes of peak RSS per source byte at 25,000 to
100,000 statements (12.7 before, measured with the binary of the parent commit).

**Turtle and TriG in K workers (2026-10-22,
https://github.com/danbri/factoidal/issues/842).** `Syntax/TurtleSplitScan.lean`
reads the bytes once and gives dot boundaries near `size * k / K` and the units
that can hold a directive; the reader of each range after the first reads those
units with a step that keeps nothing (`Source.Reader.resume`), enters the TriG
graph block of its start, and starts its blank-node counter at the count the
scan made before the split (`[` and collection items), so the generation is the
same bytes for every K. A range that ends with another counter than the scan
counted makes the pack read the source again as one range
(`Sbm11Pack.withSplitRetry`). A source with `<<`, `~` or `{|` is one range. The
pack prints `split-scan-ms=`. Phase 1 at 880,000 quads: Turtle 11.3 to 13.2 s with 1
worker, 2.7 to 2.9 s with 4; TriG 11.8 to 12.8 s and 2.9 to 3.6 s. Record:
section 3m of `docs/designissues/2026-09-03-rdf-parsing-strategy.md`.

**Blank nodes.** A blank node label is local to one document (RDF 1.1 Concepts,
section 3.4). The reader keeps the blank nodes of one document apart: a label
that the document writes cannot equal a label that the reader mints. Turtle and
TriG mint `anon` + (the longest run of underscores in the document + 1
underscores) + a counter, so they need the pre-pass. RDF/XML mints `b<N>` and
writes each `rdf:nodeID` as `n<value>`. JSON-LD mints `_jld_anon` + the fewest
underscores for which no label of the document begins with the prefix (none,
unless a label of the document begins with `_jld_anon`) + a counter, and passes
an explicit `_:` label through
(`JSONLD.generated_ne_written`; until 2026-10-14 an explicit `_:_jld_anon0`
merged with the first generated node,
https://github.com/danbri/factoidal/issues/840).

**Export (2026-10-14).** `l4sbm11 export GEN --format F [--out FILE]
[--graph default|all|IRI] [--prefix LABEL=IRI]... [--verify merkle|none]` writes
the dataset of a generation. F is `ntriples`, `nquads`, `turtle`, `trig`, `rdfxml`
or `jsonld`. The command reads the SPO permutation block by block, in key order,
and gives each quad to `Sink.Writer`. `Harness/Sbm11Export.lean` names no syntax.
The text goes to standard output, or to `FILE.tmp-PID` that the command renames
when the document is complete: a failed export leaves no FILE. Exit status: 0,
1 (error), 2 (usage). A summary line with the quad count, the byte count and the
peak RSS goes to standard error.

| Syntax | What the writer writes | What it holds |
| --- | --- | --- |
| N-Triples, N-Quads | one line for each quad | one quad |
| Turtle | one statement for each subject; SPO order gives the triples of a subject in one run | the triples of one subject |
| TriG | the Turtle statements inside a block `GRAPH <name> { ... }` (`{ ... }` for the default graph). The writer closes the block and opens a new block each time the graph of the next quad is not the open graph | the triples of one subject and the name of the open graph |
| RDF/XML | one `rdf:Description` for each subject, written when the next subject starts. The start tag declares the namespaces of all the predicates, so the export first reads the predicate ids of the quads it keeps (id columns only) and gives their table to the writer. The text is the text of `graphToRdfXml` (`Sink.runList_rdfxml_eq`) | the triples of one subject (https://github.com/danbri/factoidal/issues/846) |
| JSON-LD | a flattened document in expanded form: for each subject, one node object for the default graph and one graph object `{"@id": g, "@graph": [node]}` for each named graph, in RFC 8785 form; `{"@id": g, "@graph": []}` for a named graph with no triple. No `@list` and no sort by `@id` (both need the whole dataset); a reader's node map merges the objects of one `@id` | the quads of one subject (https://github.com/danbri/factoidal/issues/847) |

The SPO order visits the subjects in dictionary order. A graph whose subjects
interleave with those of other graphs gets several TriG blocks. A TriG reader
reads the blocks of one name as one graph (the W3C tests `alternating_iri_graphs`
and `alternating_bnode_graphs`), and `tests/sbm11/export_roundtrip.sh` packs the
export again to check it.

Named graphs with no triple (2026-10-15,
https://github.com/danbri/factoidal/issues/855): the graph list GNL1 holds every
named graph. The scan marks the listed graphs that have a quad; after the last
quad each listed graph with no quad goes to `Sink.Writer.declare`. TriG writes
`GRAPH <g> {` `}` (also `GRAPH _:b {` `}`), JSON-LD a node object with an empty
`@graph`. N-Quads has no statement without a triple: the command writes the quads,
exits 0, and standard error says `N such graphs are not in the document (the first
is <g>)`. The summary line has `graphs-with-no-triple=N`. Gate:
`tests/sbm11/named_graphs.sh` (part (v) of `run.sh`).

N-Triples, Turtle and RDF/XML have no place for a graph name. When the generation
has a named graph (a listed graph, also one with no triple, or a quad in a named
graph), the command stops before it writes a byte and names
the first graph, unless `--graph` chooses: `default` writes the default graph,
`all` writes the union of the graphs (a triple that is in several graphs is
written once), an IRI writes the triples of that graph. N-Quads, TriG and JSON-LD
write every graph and refuse `--graph` (exit 2). RDF/XML and JSON-LD have no form
for an RDF 1.2 triple term: the export says so and exits 1. Turtle and TriG write
every IRI in full unless `--prefix LABEL=IRI` gives a namespace (the label
without its colon).

Memory. The export holds one block of the permutation, a window of 256
dictionary pages (`pageLimit`), the verified chunks of the block and the pages it
is reading (it drops them as it goes), and a 64 KiB output buffer. Measured
2026-10-14 (`tests/stack/lean_scaling.py`, rows `sbm11-export-*-memory`, peak RSS
at n, 2n and 4n statements): N-Quads 33 MB at 25,000 statements (10.7 MB out) and
34 MB at 100,000 (43.0 MB out); Turtle 46 and 45 MB; TriG 34 and 46 MB. The slope is
at most 0.39 byte of peak RSS per output byte (bound 0.75). At 400,000 statements
(172 MB of output) N-Quads peaks at 36 MB and Turtle at 38 to 46 MB. Repeated runs of
the same Turtle export differ by up to 10 MB. RDF/XML and JSON-LD (2,000, 4,000 and
8,000 statements) hold the dataset: 5.9 and 5.5 bytes per output byte, expected
failures. Time is linear since 2026-10-14 (https://github.com/danbri/factoidal/issues/854).
Before, N-Quads took 1.1 s for 25,000 statements, 5.5 s for 100,000 and 35 s for 400,000
(a ratio of 5 and 6.4 for 4x the data), and `l4sbm11 dump` took the same time. The cause
was the Merkle proof of each dictionary chunk (the paragraph "Merkle reads are linear",
after "Read verification is an option"), not the window of 256 pages. Rows `sbm11-dump-time`
and `sbm11-export-nq-time`: 3.9 for 4x the data after the repair. The stack case
`sbm11-export` of `tests/stack/run.sh` exports 600,001 quads with a 300,000-byte
literal as N-Quads, Turtle and TriG under a 512 KB stack.

**The W3C tests through the store (2026-10-14).**
`tests/sbm11/w3c_roundtrip.sh`, run by `tests/sbm11/run.sh` part (p), packs every
positive evaluation and syntax test of the W3C RDF suites (N-Triples, N-Quads,
Turtle, TriG, RDF/XML; RDF 1.1 and RDF 1.2) and of the JSON-LD toRdf manifest
with `l4sbm11-pack`, dumps the generation, and compares the dump with the result
file by dataset isomorphism (`l4sbm11-w3c compare`, which uses
`Dataset.isomorphicOutcome` and RDFC-1.0 canonical N-Quads where the bounded search
cannot decide; language tags compare in lower case, lexical forms exactly). It
reads the manifests, the base IRIs and the result files from `third_party/testing`.
It also parses each test in memory (`Source.parseDocument`) and compares the
result. For each suite it prints "store: N pass, M fail (out of T); parser: N pass,
M fail (out of T)". A test that the parser passes and the store fails is a
failure. A test that fails in both routes needs a row in
`tests/sbm11/w3c_roundtrip_xfail.tsv` with an open issue; the run fails when a
listed test passes. Nine empty documents (one or more of each syntax) pack to a
valid generation with no quad. Result, 2026-10-14: 1,281 pass, 0 fail, 18
expected-fail (out of 1,299), in about 40 s with 4 jobs. The 18 expected failures
are JSON-LD toRdf tests that need a document loader or a processing option that
the JSON-LD reader of the source layer does not take:
https://github.com/danbri/factoidal/issues/848. The first run found 21 store-only
failures: RDF 1.2 TriG documents with an annotation block `{| ... |}` (15 of 26
evaluation tests and 6 of 24 syntax tests of the TriG 1.2 suites). The TriG chunk
scanner read the braces of the annotation as graph block braces. The scanner now holds a `{` back for one character, and the theorems of
`TriGChunkFoldTheorems.lean` cover the change (`WellHeld`, `finish_held`).

**Gates.**

- `tests/sbm11/storage_layering.py`, run by `tests/sbm11/run.sh` part (n): fails
  when a file under `L4Factoidal/Storage/` imports or opens
  `L4Factoidal.Syntax`. It exits 2 when it reads no file.
- `tests/sbm11/syntax_independence.sh`, run by `tests/sbm11/run.sh` part (o):
  hand-written fixtures in `tests/sbm11/syntax/` write one dataset in several
  syntaxes. D1 (no blank nodes, six syntaxes) and D2 (D1 and two named graphs,
  three syntaxes) must give byte-identical generations, apart from the source
  length and digest in the manifest. D3 (blank nodes, six syntaxes) must give
  equal RDFC-1.0 canonical N-Quads. A generated dataset of 1 MB in four
  syntaxes crosses many 64 KiB chunks. Other cases: blank nodes of one document
  stay distinct, `--format` selection, strict N-Triples, `l4sbm11 verify` of
  every generation. It also checks that `l4sbm11-dict-pack` writes the
  dictionary files of the pack for every fixture in every syntax, and that
  `l4factoidal parse --format F --out nquads` gives the same N-Quads for one
  dataset in every syntax that writes it. Two RDF/XML cases check the scope of
  property elements: `lang-scope rdfxml` and `scope-paths rdfxml` (until
  2026-10-14 the first was an expected failure,
  https://github.com/danbri/factoidal/issues/841).
- `tests/sbm11/w3c_roundtrip.sh`, run by `tests/sbm11/run.sh` part (p): the W3C
  RDF tests through the store, described under "The W3C tests through the store".
- `tests/sbm11/quad_source.sh`, run by `tests/sbm11/run.sh` part (u): the producers and
  the packer entry, described under "The packer entry". The part also checks that
  `tests/sbm11/storage_layering.py` finds no syntax in `RDF/QuadSource.lean`.
- `tests/sbm11/export_roundtrip.sh`, run by `tests/sbm11/run.sh` part (q): packs
  D1, D2, D3 and D4, exports each in every syntax that can write it, packs the
  export, and compares the data files (D3: RDFC-1.0 canonical N-Quads). Also: an
  N-Quads export is `dump` byte for byte; `--out`, `--graph`, `--prefix`, the usage
  errors, the refusals (a named graph for a syntax with no graph name, a triple
  term for RDF/XML and JSON-LD), an empty generation in six syntaxes, and a
  generated dataset of 1 MB. 53 pass, 0 fail, 0 expected-fail (out of 53,
  2026-10-14). The RDF/XML export of D1 read back with `"Alice"@en` for
  `"Alice"` until 2026-10-14 (https://github.com/danbri/factoidal/issues/841);
  the RDF/XML export of the 1 MB set is a case now.
- `tools/pack-differential.sh OLD NEW`: packs every `.ttl`, `.nt`, `.nq` and
  `.trig` file of the W3C RDF 1.1 and 1.2 suites with an old and a new
  `l4block-shard-pack`, in `ibk3`, `ibk4` and `ibk5`, with the chunk route and
  the whole-source route (`L4_PACK_BUFFERED=1`), and compares the exit status
  and the generation hash.
- `tests/trig-pack/compare_w3c.sh` and `order_xfail.sh`: IBK4 and IBK5 agree
  across routes.
- `tests/stack/lean_scaling.sh` rows `sbm11-pack-ttl-memory`,
  `sbm11-pack-trig-memory`, `sbm11-pack-nt-vs-nq`, `sbm11-export-nq-memory`,
  `sbm11-export-ttl-memory`, `sbm11-export-trig-memory`, `sbm11-dump-time`,
  `sbm11-export-nq-time` (assertions) and
  `sbm11-pack-rdfxml-memory`, `sbm11-pack-jsonld-memory`,
  `sbm11-pack-ttl-workers`, `sbm11-pack-trig-workers`,
  `sbm11-export-rdfxml-memory`, `sbm11-export-jsonld-memory` (expected failures).
- `tests/sbm11/syntax_bench.sh`: packs one generated dataset in each syntax and
  prints the table below.

**Theorems** (`RDF/SourceTheorems.lean`; the axioms are `propext`,
`Classical.choice` and `Quot.sound`; `tools/lean-unbuilt-modules.py --gate`
passes):

- `whole_readAll`, `jsonld_readAll`: a whole reader gives `parseDocument` of
  the joined chunks, for every list of chunks.
- `rdfxml_readAll_of_notStreamed` (with `RdfXmlChunkFold.foldlM_inv` and
  `readAll_eq_whole_of_notStreamed`): the RDF/XML chunk fold, when it ends in
  its prologue or fall-back phase, gives `parseDocument` of the joined chunks.
- `nquads_readAll_eq_run`, `nquads11_readAll_eq_batch`,
  `nquads11_readAll_eq_parseNQuadsFast`: the N-Quads reader in RDF 1.1 mode gives
  the line walk of the joined text. They use
  `NQuadsFold.streamConsume11_eq_batch`.
- `turtleStep_collect`: the Turtle consumer with the consumer that collects
  triples is the accumulator step of `parseTurtle`.
- `prepass_chunks`, `underscores_chunks`: the pre-pass over any cut of the text
  gives `freshBnodePrefix` of the whole text.

**Gaps.** Each has an open issue and a test that fails or is marked as an
expected failure.

| Gap | Issue | Test |
| --- | --- | --- |
| Turtle chunk walk, N-Triples chunk boundary, N-Quads in RDF 1.2 mode, UTF-8 decoding in chunks: equality with the batch result is not proved | https://github.com/danbri/factoidal/issues/826 | `tests/known-defects/run.sh` rows SF-1 to SF-4 |
| TriG chunk walk against `parseTriG`; block order differs on a source whose graphs interleave | https://github.com/danbri/factoidal/issues/836 | `tests/trig-pack/order_xfail.sh` |
| RDF/XML chunk fold, children phase: equality with the whole-document reader is measured (`tools/rdfxml-chunk-differential.sh`), not proved | https://github.com/danbri/factoidal/issues/936 | `tests/known-defects/run.sh` row RX-1 |
| JSON-LD is read whole | https://github.com/danbri/factoidal/issues/839 | row `sbm11-pack-jsonld-memory` |
| The Lean JSON-LD writer (`fromRdf` node list) takes time quadratic in the number of triples | https://github.com/danbri/factoidal/issues/712 | row `jsonld-write` |
| Turtle and TriG read by K workers: equality with the single reader (after a renaming of the generated blank-node labels) is measured (`tools/split-read-differential.sh`), not proved | https://github.com/danbri/factoidal/issues/944 | `tests/known-defects/run.sh` row SR-1 |
| The JSON-LD reader of the source layer takes no document loader and no processing option (18 toRdf tests) | https://github.com/danbri/factoidal/issues/848 | `w3c_roundtrip_xfail.tsv`, 18 rows |
| No theorem relates the stream writers (`Sink.Writer`) to the batch writers | https://github.com/danbri/factoidal/issues/852 | `tests/known-defects/run.sh`, rows `SK-1`, `SK-2` |
| The RDF/XML export holds the whole graph | https://github.com/danbri/factoidal/issues/846 | row `sbm11-export-rdfxml-memory` |
| The JSON-LD export holds the whole dataset | https://github.com/danbri/factoidal/issues/847 | row `sbm11-export-jsonld-memory` |

Repaired on 2026-10-18 and removed from the table: the JSON-LD reader's stack
(https://github.com/danbri/factoidal/issues/844), the RDF/XML writer's quadratic
time (https://github.com/danbri/factoidal/issues/845) and the JSON-LD writer's stack
(https://github.com/danbri/factoidal/issues/853). The rows `rdfxml-write` and the
`*-stack` rows of `tests/stack/lean_scaling.py`, and the cases `jsonld-read-fanout`,
`jsonld-read-list` and `jsonld-write-fanout` of `tests/stack/run.sh`, assert them.

**Measured** (2026-10-14, `tests/sbm11/syntax_bench.sh`): one generated dataset
(110,000 subjects, 880,000 quads; `gen_multi.py`) packed from each syntax with
`l4sbm11-pack --workers 4` on 4 CPUs. The data files of
every generation equal those of the N-Triples pack (default graph) or the
N-Quads pack (named graphs). The full table, with the small set that holds
RDF/XML and JSON-LD, is in section 11.1 of
[`docs/designissues/2026-10-11-shardborough-vs-qlever.md`](../../docs/designissues/2026-10-11-shardborough-vs-qlever.md).

| Source (writer) | Source MB | Phase 1 workers | Wall s | Kquads/s | Peak RSS MB |
| --- | ---: | ---: | ---: | ---: | ---: |
| N-Triples (generator) | 84.4 | 4 | 8.8 | 100 | 204 |
| Turtle (generator) | 39.0 | 1 | 15.6 | 56 | 227 |
| Turtle (Lean writer) | 31.0 | 1 | 14.7 | 60 | 225 |
| N-Quads (generator) | 102.0 | 4 | 8.9 | 99 | 200 |
| TriG (generator) | 40.8 | 1 | 17.2 | 51 | 228 |
| TriG (Lean writer) | 84.4 | 1 | 27.7 | 32 | 225 |
| RDF/XML (Lean writer), 88,000 quads | 6.9 | 1 | 2.1 | 42 | 137 |
| JSON-LD (Lean writer), 88,000 quads | 7.4 | 1 | 2.0 | 44 | 135 |

The Lean writers for RDF/XML and JSON-LD are quadratic in the dataset (22 s and
44 s for 8.3 MB; issues 845 and 712 in the table above), so those two rows use
the small set. Three runs differ in wall
time by up to 20 % for the big set.

**To add a syntax.** (1) Add the constructor and its table entries in
`RDF/Format.lean`. (2) Add its reader to `RDF/Source.lean` (`Reader`,
`Reader.init`, `feed`, `finish`, `parseDocument`) and a `#guard` that cuts a
document at every position. (3) Add a theorem to `RDF/SourceTheorems.lean`, or
an issue and an expected-failure test for the half that is not proved. (4) Add
fixtures to `tests/sbm11/syntax/` and cases to `syntax_independence.sh`. (5) Add
a memory row to `tests/stack/lean_scaling.py`. (6) Time the reader against the
route it replaces on the same bytes (`tests/sbm11/syntax_bench.sh`); see rule 8
of "Rules when changing a format". (7) Add its writer to `RDF/Sink.lean`
(`Writer.init`, `push`, `finish` and `serializeDataset`), the fixtures it can
write to `tests/sbm11/export_roundtrip.sh`, and an export memory row. (8) Run
`tests/sbm11/w3c_roundtrip.sh` with the suites of the syntax. Do not name the
syntax in a file under `Storage/`.

**The packer entry: quads from any producer (2026-10-15).**
Owner, 2026-10-15, verbatim: "isn't packing (into shardborough?) done against
abstract rdf graph or dataset API not a text file format???". Tracking:
https://github.com/danbri/factoidal/issues/866. Record: section 11.4 of
[`docs/designissues/2026-10-11-shardborough-vs-qlever.md`](../../docs/designissues/2026-10-11-shardborough-vs-qlever.md).
Until 2026-10-15 the entry of phase 1 was a file path and a byte range
(`phase1Worker cfg source outDir w start stop runTerms`). The entry now takes
producers of RDF quads, and a file is one producer.

- **The producer.** `L4Factoidal/RDF/QuadSource.lean`: `QuadSource` has one field,
  `next : IO (Option Batch)`. A batch has two arrays: `quads`, each a `Triple` and an
  `Option Subject` (`none` is the default graph), and `graphs`, the names of the named
  graphs that the source declares, with or without a triple (RDF 1.1 Concepts section
  4: a named graph can be empty; 2026-10-15,
  https://github.com/danbri/factoidal/issues/855). A consumer takes the union: the
  named graphs are the declared names and the graph names of the quads. `next` gives
  the next batch and, at the end, `none` (again at every later call). A batch is never
  empty: it has a quad or a graph name. When a call throws, every later call throws. The module imports no syntax module and names none
  (`tests/sbm11/storage_layering.py` checks both). `QuadSource.ofStep` makes a producer
  from a state and an `IO` step; `ofPull` does the same from a pure step.
  `QuadSource.ofDataset ds batch` and `QuadSource.ofArray quads batch` are the producers
  of a `Dataset` and of an array. `foldBatches` and `drain` use a producer.
- **The entry.** `Sbm11Pack.packQuads sources outDir runTerms blockRows sortRowsMax
  sourceId` (`Harness/Sbm11PackLib.lean`). `sources` is an array of `IO QuadSource`, one
  for each phase-1 worker. Each worker opens its producer in its own thread and gives the
  batches to the phase-1 worker (`openPhase1`: `consume` takes a batch, `finish` returns
  the term runs and quad runs). Phases 2 and 3 are `packBatches`, as before. `sourceId`
  is the length and the SHA-256 of the source that the manifest records
  (`SourceId.noDocument`: 0 and the SHA-256 of the empty string).
- **The producers in the tree.**

| Producer | Code | Use |
| --- | --- | --- |
| a byte range of a file, in one of the six syntaxes | `fileRangeSource` (`Sbm11PackLib.lean`); `chooseFormat` and `readCfg` choose the syntax, `packQuads` names none; the source layer declares each TriG graph block (also `<g> { }`) and each named graph of a JSON-LD document (`Source.Decl`, `feedD`, `finishD`) | `l4sbm11-pack FILE OUT`: one producer for each byte range of N-Triples and N-Quads, one for any other syntax |
| an RDF `Dataset` in memory | `QuadSource.ofDataset`: declares every named graph of `Dataset.named` (`QuadSourceTheorems.ofDataset_graphs`) | `packQuads #[QuadSource.ofDataset ds 4096] ...`; `l4sbm11-pack FILE OUT --via-dataset` reads the whole document into a `Dataset` first |
| an array of quads | `QuadSource.ofArray`: declares no graph | cut an array into slices to use K workers |
| an HDT file | `GraphStore.quadSource` (`L4Factoidal/HDT/QuadSource.lean`): declares no graph | `l4sbm11-pack FILE.hdt OUT`, or `--format hdt` |

- **What the output depends on.** The generation is a function of the set of quads, the
  set of declared graph names and `sourceId`. It does not depend on the number of producers, on how the quads are divided
  among them, on the size of their batches, on the size of the term map, or on the order of
  the quads. `l4sbm11-quad-source selftest` packs each of seven datasets ten ways and compares
  every file of the other nine packs with the first; `--via-dataset` is byte-identical to the file route on
  every syntax fixture (`tests/sbm11/quad_source.sh`).
- **Open the producer in the worker.** `packQuads` takes `IO QuadSource`, not
  `QuadSource`. Lean marks the objects that a task closure reaches as shared between
  threads, and a shared object is copied at its first update. A producer keeps its state in
  a reference; a reference made before the task and used in it is copied at every update.
  Measured 2026-10-15 (the program is in section 11.4 of the record): 100 rounds of
  `swap`, `push` and `set` on an array of 5,000,000 numbers took 9,557 ms for a reference
  made before the task and 29 ms for a reference made in the task. `QuadSource.ofStep` also
  takes the state out of the reference (`swap`) while the step runs, so that the step holds
  the only reference.
- **Compaction.** `l4sbm11 compact` ends in the same code as the pack: `packCompacted`
  calls `packBatches` and writes the epoch files. Its default phase 1 works on ids and key
  bytes, with no RDF term. `l4sbm11 compact GEN OUT --via-quads` is the reference route:
  one SPO scan of the overlaid generation decodes each row to RDF terms and gives the quads
  to the phase-1 worker (`openPhase1`) as any producer does. The two routes give
  byte-identical files (`tests/sbm11/run.sh` parts (h), (i) and (m)). The reference route
  takes about twice as long on the olympics generation (section 11.4 of the record has
  the numbers), so the id route is the default.
- **To add a producer.** (1) Write an `IO QuadSource` in a module that is not under
  `Storage/` (for a store: `L4Factoidal/<Store>/QuadSource.lean`), with `ofStep`. A step
  that cannot read a structure of the store throws; it never puts a placeholder term in the
  quad. (2) For the command line, add the case to `Sbm11Pack.producersOf`. (3) Add a case
  to `tests/sbm11/quad_source.sh`: pack, `l4sbm11 verify`, `l4sbm11 dump`, and compare the
  dump with the dump of the source store by isomorphism (`l4sbm11-w3c compare`). Add a check
  that an id the reader cannot resolve is an error (`l4sbm11-quad-source hdt-errors` for the
  HDT producer). (4) For a pure producer, state the order of its batches as
  `QuadSourceTheorems.ofDataset_flatten` does.
- **Theorems** (`RDF/QuadSourceTheorems.lean`; the axioms are `propext`,
  `Classical.choice` and `Quot.sound`): `take_quads`, `take_size_le` and `take_short`
  describe one `Cursor.take` step. `ofDataset_flatten`: the batches of `ofDataset`, taken
  together in order, are `Dataset.quadList`. `datasetPull_batches_size`: each batch has at
  least one quad and at most `max 1 batch` quads. `quadList_eq_foldDataset`: that order is
  the order of `Source.foldDataset`. The statements are about the pure form (`Pull`);
  `tests/sbm11/quad_source.sh` checks that the batches of the producer are the batches of
  the pure form.

## Where the code is

- Codecs and pure validators: `formal/lean4/L4Factoidal/Storage/`
  (`IndexedBlockWireV3`, `PagedTermDictionary`, `SubjectRowIndexWireV2`,
  `TermLocalIndexWire`, `ShardManifest`, `DeltaLog`; theorems in the
  `*Theorems.lean` siblings).
- Host I/O, packing, activation, compaction, query CLIs:
  `formal/lean4/Harness/` (`PredicateShardPack`, `ShardActivate`,
  `IndexedBlockV3Query`, `DeltaLogTool`, `PosixRangeIO` — the one host
  `extern_lib`, `libl4blockhost`, for `pread`, append-with-fsync and atomic
  replace).
- WASM operations: `formal/lean4/Wasm/Ops/Block.lean`, dispatch table in
  `Wasm/Dispatch.lean`, native checks in `Wasm/native-smoke.sh`.
- The source layer (any syntax to quads): `formal/lean4/L4Factoidal/RDF/Source.lean`,
  `SourceJsonLd.lean`, `SourceTheorems.lean`, the format table
  `RDF/Format.lean`; tools `Harness/SourceConvert.lean` (`l4source-convert`),
  `Harness/Sbm11PackLib.lean`, `Harness/Sbm11DictPack.lean`; tests
  `tests/sbm11/storage_layering.py`, `tests/sbm11/syntax_independence.sh`,
  `tests/sbm11/syntax_bench.sh`, `tests/sbm11/w3c_roundtrip.sh` (with
  `Harness/Sbm11W3c.lean`, the tool `l4sbm11-w3c`), `tools/pack-differential.sh`.
- The producers of quads and the packer entry: `L4Factoidal/RDF/QuadSource.lean`
  (`QuadSource`, `ofDataset`, `ofArray`), `RDF/QuadSourceTheorems.lean`,
  `HDT/QuadSource.lean` (an HDT file), `Harness/Sbm11PackLib.lean` (`packQuads`,
  `fileRangeSource`, `openPhase1`), `Harness/Sbm11Compact.lean` (`--via-quads`); the tool
  `Harness/Sbm11QuadSource.lean` (`l4sbm11-quad-source`) and the test
  `tests/sbm11/quad_source.sh`.
- The serialiser layer (quads to any syntax): `formal/lean4/L4Factoidal/RDF/Sink.lean`,
  `SinkJsonLd.lean`; the export `Harness/Sbm11Export.lean` (`l4sbm11 export`);
  test `tests/sbm11/export_roundtrip.sh`.
- Design records, with status: [`docs/worknotes-index.md`](../../docs/worknotes-index.md).

## Rules when changing a format

1. The Lean definition is the format. Change `encode?`/`decode?` in the
   codec module, keep or extend the round-trip theorem in the sibling
   `*Theorems.lean`, and keep the encoder's `supported` equal to the
   decoder's admission (the 2026-09-02 rule: the encoder refuses exactly
   what the decoder would refuse, so the theorem has no side hypotheses).
2. A byte change is a new wire version. Bump the format name (IBK3 to
   IBK4, SBM6 to SBM7) rather than changing bytes under a name; the alpha
   allows repacking, it does not allow silent drift (spec section 10).
3. Rebuild the WASM mirrors after any change under `L4Factoidal/` that the
   dispatch operations can reach (`bash formal/lean4/Wasm/build-wasm.sh`,
   about ten minutes), then `node --test tests/hub/*_test.mjs`.
4. Re-run the lifecycle above on a rung-2 file and compare the packed block
   bytes with the committed hub blocks under
   `docs/web/hub/assets/blocks/lifesci-crossgraph/` (a codec change that
   keeps the format must reproduce them byte for byte).
5. A change to WHAT a derived index holds is a byte change, also when no codec
   function changed. The literal gram index folds each lexical form before it
   takes grams. On 2026-10-10 the fold changed from ASCII-only to Unicode
   (merge 1107b396, [issue 706](https://github.com/danbri/factoidal/issues/706)),
   the LGI1 and LGI2 files written before it stopped being supersets of the
   rows the Unicode `LCASE` keeps, and the files carry no fold identifier, so
   a reader could not tell. The merge left the names alone and recorded the
   question as an owner decision. Between that merge and the rename (same day)
   a reader that trusted such a file would have dropped rows without saying so.
   When a function an index or sidecar is derived from changes (a fold, a
   tokeniser, a key function, a bounding-box rule), rename the format in the
   SAME landing, make the old name an error that says what to do, and gate the
   change with an input that only the new function decides (for the literal
   index, a non-ASCII needle: `tests/local/data/unicode_label_sample.trig` and
   the `literal index under the Unicode fold` cases of `Wasm/native-smoke.sh`).
6. A gate that compares an index path with a scan proves nothing when the
   index path silently fell back to the scan. `l4block-literal-gate` reads
   `literalIndexes` from the `storeOpen` envelope and fails when the handle
   opened with sidecars retained fewer literal indexes than blocks.
7. A new byte value that the code before it refuses is an extension: the
   format keeps its name. All three must hold, each checked: (a) no byte
   value the older code admitted changes meaning; (b) the older code refuses
   the new value loudly, shown by running the binary built before the change
   on a generation that holds it; (c) a generation without the new value is
   byte-identical to one packed before the change. Otherwise rule 2 applies.
   Coordinator decision, 2026-10-14
   (https://github.com/danbri/factoidal/issues/792 item 1): SBM11 key class 7
   and id tag 9 (triple terms) kept the names GDV1 and SBM11. Measured: the
   `l4sbm11` of `origin/main` 1986fdf4 refuses a generation with a triple
   term at activation (`id with an unknown tag or a rank past the
   dictionary`, `refused failures=8`) and its `dump` stops (`unknown tag 9`);
   the olympics generation packed after the change has the same 10 artifacts
   and manifest as the stage 3 one (`cmp`). Trap, found on the way: the
   decision assumed that the older activation decodes every dictionary key,
   so that its decoder (which returns `none` for class 7) would refuse the
   generation. It does not: activation checks the order and the count of the
   keys only. Had the new terms kept tag 3, the older activation would have
   admitted the generation and failed only at the first query that decoded a
   triple term. Read what the older reader checks before relying on it.
   Coordinator decision, 2026-10-14 (the update part of the same item, and
   https://github.com/danbri/factoidal/issues/843): the delta-log codec for
   RDF 1.2 terms did NOT keep the DLOG version, because condition (b) fails:
   the readers of `cf55723e` replayed a log whose second batch held a tag-3
   entry, answered with batch 1 only, exit 0, and their compaction lost batches
   2 and 3. So rule 2 applies: a log that holds an RDF 1.2 term has header
   version 2, which those readers refuse at the header (measured: `l4sbm11
   query`, `serve`, `compact`, `update` and `l4block-delta-log --inspect` exit
   1 with `DLOG header is malformed or unsupported`), and a log without one
   stays version 1, byte for byte (`appendPlan?_v1`; `cmp` against the
   `cf55723e` writer). The shared term codec of BLK0, IBK1, IBK2, PTD1 and
   TLI1 was not extended; the delta log has its own.
   Coordinator decision, 2026-10-15
   (https://github.com/danbri/factoidal/issues/855): the graph list GNL1 kept
   the names SBM11 and `"SBM0"` version 11. A generation that has a named
   graph has an eleventh file and an eleventh manifest role; one that has no
   named graph has the ten files of stage 3, byte for byte (`cmp` against the
   packer of `e185eb00`). Measured: the `l4sbm11` of `e185eb00` refuses the
   manifest with eleven roles at `verify`, `activate`, `stats`, `dump`,
   `query`, `serve` and `compact` (exit 1), and its `update` refuses every
   request that reads the generation. Record: section 12 of
   [`docs/designissues/2026-10-12-sbm11-stage5.md`](../../docs/designissues/2026-10-12-sbm11-stage5.md).
   Coordinator decision, 2026-10-15
   (https://github.com/danbri/factoidal/issues/856): a log entry that names a
   graph by a blank node needs DLOG version 3, for the reason of the RDF 1.2
   terms (condition (b) fails for the readers before section 8). Measured: the
   `l4sbm11` of `e185eb00` refuses a version 3 log at `query`, `serve`, `compact`
   and `update` (exit 1, `the DLOG header is malformed or unsupported`; no
   compaction output, the log bytes unchanged), and its `l4block-delta-log
   --inspect` refuses it too.
   A log without such an entry keeps its version and its bytes
   (`appendVersion_noV3`, `serializeDeltaEntryPayloadWith?_v3_eq_v2`).
8. A change that moves a syntax to another reader needs a timing against the
   old route on the same bytes, not only a byte comparison. On 2026-10-14 the
   source layer gave `.nt` files to the strict N-Triples reader. Every
   generation was byte-identical to the one of the reader it replaced, and
   `tools/pack-differential.sh` agreed on 8,586 of 8,662 cases. Phase 1 took
   2,996 ms for 8.3 MB against 477 ms for the same quads as N-Quads text,
   because `readTriple12` computed `r5.length + 1` (the characters left in the
   chunk) for each statement. A timing of one dataset in every syntax
   (`tests/sbm11/syntax_bench.sh`) found it; the scaling row
   `sbm11-pack-nt-vs-nq` now gates it.

## Named graphs, replay cost and IBK limits (2026-10-18)

- Every named graph is kept by SBM11, also a graph with no triple and a graph
  named by a blank node: graph list GNL1 (`graphs.gnl1`, eleventh manifest
  role) and DLOG version 3 (graph slots; CREATE adds, CLEAR keeps, DROP
  removes). Issues 855 and 856, closed. Record: stage 5 record section 12.
- `l4factoidal query` loses these graphs:
  https://github.com/danbri/factoidal/issues/876 (expected failure in
  `tests/sbm11/named_graphs.sh`).
- The IBK4 and IBK5 stores REFUSE a graph with no triple (owner decision,
  2026-10-22, https://github.com/danbri/factoidal/issues/880): the pack of a
  source that declares one (2 of the 6 graphs of `d5.trig`), `CREATE GRAPH`
  and `CLEAR GRAPH` in `l4block-delta-log` exit 1 with a message that names the
  rule, and the log is unchanged. `l4block-delta-log --update` refuses EVERY
  update on an IBK4 or IBK5 collection (exit 1, no file changed): their query
  path `l4block-quad-query` does not replay the log
  (https://github.com/danbri/factoidal/issues/935; this also covers a DELETE
  that empties a graph, https://github.com/danbri/factoidal/issues/934). IBK3
  updates still commit and `l4block-id-v3-query` replays them. Use SBM11 for such data.
- The replay of a log of NEW terms costs 37 to 42 microseconds of CPU for
  each entry, against 15 to 18 for dictionary terms. Cause: overlay ids are
  `14 * 2^60 + n`, above 2^63, so a Lean `Nat` holds them as GMP numbers, and
  the per-permutation sort in `Session.withOverlay` spends 30 percent of the
  replay in `mpz_cmp`. https://github.com/danbri/factoidal/issues/879, row
  `sbm11-replay-insert-time` (expected failure). Any Shardborough id at or
  above 2^63 (tag 8 or more, including triple terms, tag 9) has the same
  cost wherever rows are compared or hashed.
- Code or machine? Build the older commit in a worktree with a copy of
  `formal/lean4/.lake/build` (Lake rebuilds only the changed modules: 510
  jobs, about 10 minutes for `l4sbm11` and `l4sbm11-pack`), then run both
  binaries interleaved on this machine. On 2026-10-18 this showed that a
  recorded 746 ms (2026-10-15) was a different machine state, not a code
  change. Remove the worktree in the same turn (2 GB).

## Cross-backend differential gate and Jena TDB2 reader (2026-10-13)

- `tests/stack/backend_diff.py`: every SELECT/ASK W3C SPARQL 1.1
  QueryEvaluationTest through the Lean reference, a Shardborough store,
  Jena TDB2 and Jena in-memory, compared by result equivalence; expected
  disagreements with issues in `tests/stack/backend_diff/expected.tsv`.
  Needs Jena (`SOTA_DL`), about 20 minutes.
- `l4factoidal tdb2-dump DB` and `--format tdb2`: read a Jena TDB2 database
  in place; `tests/tdb2/run.sh` compares with `tdb2.tdbdump`.
  `factoidal serve --tdb2 DB /ds` (npm) serves one read only.
- `l4block-id-v3-query` and `l4block-quad-query` take `--base IRI`: the base
  IRI of the query (SPARQL 1.1 section 4.1.1.1, RFC 3986 section 5.1), used
  for relative IRIs and `IRI()`; a `BASE` declaration in the query takes
  precedence. `serve` uses the request IRI as base
  (https://github.com/danbri/factoidal/issues/835).
- Record: `docs/designissues/2026-10-13-tdb2-format.md`
  (https://github.com/danbri/factoidal/issues/834).
