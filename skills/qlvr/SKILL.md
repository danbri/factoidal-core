---
name: qlvr
description: Factoidal/qlvr — read and query a QLever index from Lean. How to rebuild the reference QLever instance (olympics dataset, 1,781,625 triples, image pinned by digest) and its SPARQL JSON query oracle with tools/qlvr/build-instance.sh, where the byte-level format record is (docs/designissues/2026-10-11-qlever-index-format.md), how to probe an index with tools/qlvr/probe_index.py, how to answer SPARQL basic graph patterns from the index with l4qlvr query (side index, plan rules, tests against the oracle), and the rules for the Lean decoders (loops, not per-item recursion). Use for any QLever on-disk format question, for work on the Lean QLever reader, or when the oracle or the instance must be rebuilt. Tracking https://github.com/danbri/factoidal/issues/778.
---

# Factoidal/qlvr: a QLever index read from Lean

Owner, 2026-10-11, verbatim: "Can we build a medium sized qlever database
instance and work up enough Lean machinery (call it Factoidal/qlvr) to be able
to access its data on disk for query, or even create/edit? This may teach us
something about Lean." and "consider tail recursive approach".

Tracking: https://github.com/danbri/factoidal/issues/778.

## Files

| Path | What |
| --- | --- |
| `tools/qlvr/build-instance.sh` | rebuild the instance and the oracle (idempotent) |
| `tools/qlvr/Qleverfile` | the qlever control-script configuration (image pinned by digest) |
| `tools/qlvr/probe_index.py` | Python format probe: decodes vocabulary, permutation metadata, zstd column frames; `--scan IRI`, `--dump-block0 index.pso`, `--zstd-tsv OUT` (every column frame with libzstd's sha256), `--words OUT` (every word as QLever prints it) |
| `formal/lean4/L4Factoidal/Codec/Zstd.lean` | pure-Lean zstd decoder (RFC 8878, XXH64 checksum); `decompress`, `decompressStats` |
| `formal/lean4/Harness/QlvrZstdCheck.lean` | `l4qlvr-zstd-check vectors DIR`, `blocks INDEXDIR TSV`, `frame FILE SHA256` |
| `formal/lean4/Harness/TestData/zstd/` | 14 libzstd vectors with expected sha256 (`tools/qlvr/zstd_vectors.py` writes them) |
| `tools/qlvr/zstd_bench.py` | libzstd time on the same frame list, for the throughput comparison |
| `formal/lean4/L4Factoidal/Qlvr/*.lean` | the Lean reader: `Id`, `Format` (exact `%.13g`), `Fsst`, `Vocab` (`vocabWord`, `findWord`), `Perm` (block metadata, `.meta`, `decodeColumn`), `Term` (N-Triples with QLever's escaping), `Scan` (`scanCol0M`, `scanPredicate`, rendering) |
| `formal/lean4/L4Factoidal/Qlvr/{Sort,Side,Bgp,Query}.lean` | stage 4: byte order and merge sort; the side index (string to `VocabIndex`); permutation choice, block-skipping scans, merge and hash joins; the SPARQL fragment, constant folding, FILTER, GROUP BY with COUNT, ORDER BY, DISTINCT, LIMIT/OFFSET, SPARQL JSON |
| `formal/lean4/Harness/Qlvr.lean` | `l4qlvr stats INDEXDIR`, `scan INDEXDIR PRED-IRI`, `dump INDEXDIR`, `words INDEXDIR`, `side-index INDEXDIR`, `side-check INDEXDIR [STORED..]`, `query INDEXDIR ('SPARQL' \| --file Q.rq) [--explain] [--constants]`; permutation frames by `pread` |
| `tests/qlvr/queries.sh`, `compare_query.py`, `expected-refusals.tsv` | every oracle query through `l4qlvr query` against QLever's answer (multisets of solutions, numbers by value, ORDER BY keys in order); refusals listed with their issue are expected failures |
| `tests/qlvr/bench.sh` | Lean time and peak RSS against QLever's server time, per query, warm, median of 3 |
| `tests/qlvr/run.sh` | scans against the oracle, dump against the input N-Triples and against QLever's CONSTRUCT, every word against the probe, stats |
| `tests/qlvr/canon_nt.py`, `compare_scan.py` | the canonicaliser (QLever's documented normalisations) and the scan-to-oracle comparison used by `run.sh` |
| `tests/qlvr/queries/*.rq` | the 21 oracle queries (q19-q21: single bound-predicate scans for the Lean reader) |
| `tests/qlvr/instance.json` | manifest: image digest, QLever commit, dataset URL and sha256, triple counts, every index file with size and sha256, every oracle answer with row count and sha256 |
| `docs/designissues/2026-10-11-qlever-index-format.md` | the format record: each file, its byte layout, source `file:line` at the pinned commit, what the instance confirmed, and the stage 3 plan |
| `docs/designissues/2026-10-11-qlvr-performance.md` | the performance record: warm against process times, phase shares, the Lean zstd decoder against libzstd, the q07 kernel in Lean and in C, the remainder against QLever with source lines, what was changed and what it gave |
| `tests/qlvr/bench-warm.sh` | per query: QLever compute and HTTP, Lean process, Lean warm (`--repeat`), Lean warm with libzstd, decode times |
| `tests/qlvr/kernel.sh`, `formal/lean4/Harness/QlvrKernel.lean`, `tools/qlvr/bench/kernel.c` | the q07 kernel (two scans, merge join) in eight Lean forms (with `usize` and `usize-cstore`, 2026-10-12) and in C on the same dumped input; the checksums must agree |
| `docs/designissues/2026-10-12-lean-to-c-performance.md`, `tools/qlvr/bench/pipeline.sh`, `compare.py`, `c-audit.py` | the Lean-to-C record: C compiler options (O2, native, LTO, PGO) against the generated C, the per-iteration audit of the kernel and zstd loops, `word64U`/`pushCopyU`, the case for a column library |
| `formal/lean4/ffi/qlvr_zstd.c` | optional libzstd call-out, loaded with dlopen (`l4qlvr query --libzstd`, `l4qlvr zstd-diff`); the Lean decoder stays the default |
| `docs/designissues/2026-10-11-shardborough-vs-qlever.md` | Shardborough on the same instance and queries, against `l4qlvr` and QLever, and the proposed Shardborough layout with global term ids (scripts `tools/shardborough-cmp/`) |

Bulky data stays outside the repository, in `QLVR_WORK` (default
`/home/user/qlvr-work`): `instance/` (input N-Triples and index files),
`oracle/` (one `<query>.srj` per query), `qlever-src/` (QLever source at the
image commit), `logs/`.

## Rebuild

```
pip install qlever==0.6.0 zstandard
tools/qlvr/build-instance.sh              # data, index, server, oracle
tools/qlvr/build-instance.sh --manifest   # also rewrite tests/qlvr/instance.json
tools/qlvr/build-instance.sh --rebuild --manifest --stop
```

Needs a docker daemon. The script starts `dockerd` itself when it runs as
root and no daemon answers. The dataset comes from a pinned commit of
https://github.com/wallscope/olympics-rdf by `git clone`; the session proxy
refuses `github.com/.../raw/...` downloads of repositories that are not
attached, and `git clone` works. The script checks the zip and the N-Triples
sha256.

To read the QLever source at the image commit:
`git clone --depth 1 https://github.com/ad-freiburg/qlever /home/user/qlvr-work/qlever-src`,
then compare `.git/shallow` with `qlever_commit` in `tests/qlvr/instance.json`.
A newer image changes the commit; then rebuild, rerun the probe, and update
the format record.

## Facts that cost time to find

- The permutation files are not byte-reproducible: blocks are written
  concurrently. Vocabulary, `.meta` and patterns files are. Compare
  permutations by decoded content, never by sha256.
- Every column of every block is one zstd frame, and every zstd block in the
  instance is of type Compressed (Huffman literals, FSE sequences). A reader
  needs the full RFC 8878 decoder.
- Vocabulary words are FSST-compressed twice; decode with the second decoder
  of the pair first.
- The vocabulary is in ICU collation order: a byte-wise binary search is
  wrong. Use a scan or a side index for string-to-Id.
- `Int` and `Double` Ids lose the input datatype IRI; QLever prints them as
  `xsd:int` and `xsd:decimal`.

## Check the zstd decoder

```
python3 -I tools/qlvr/probe_index.py /home/user/qlvr-work/instance olympics --zstd-tsv /tmp/frames.tsv
cd formal/lean4 && lake build l4qlvr-zstd-check
.lake/build/bin/l4qlvr-zstd-check vectors Harness/TestData/zstd   # 14 pass, 0 fail (out of 14)
.lake/build/bin/l4qlvr-zstd-check blocks /home/user/qlvr-work/instance /tmp/frames.tsv
python3 -I tools/qlvr/zstd_bench.py /home/user/qlvr-work/instance /tmp/frames.tsv
```

2026-10-11: 1,860 pass, 0 fail (out of 1,860) column frames, 4,208 zstd
blocks; Lean 113 MB/s of output, libzstd 1,785 MB/s; peak RSS 21 MB. Numbers
and method: the format record, section "Column frames". `tests/stack/run.sh`
case `zstd-8mib` decodes a 9,600,000-byte frame under the canary stack.

What the zstd decoder taught about Lean (the loop rule in practice):

- Hot loops (Huffman literals, sequence decode and execution, match copy,
  XXH64) are top-level functions with a fuel `Nat` as first argument and
  every other piece of state as an argument, ending in an `if`/`else` chain
  whose last branch is the self-call. These compile to `goto _start`, and no
  tuple is allocated per item. Branches return `.error`/`.ok` directly; a
  `do` block with `←` inside such a loop would put the call under a bind.
- `copySlice src off dest ...` with the same `ByteArray` as `src` and `dest`
  shares it, so the destination is copied whole on every call. An
  overlapping match copy uses `extract` then `++` on the unique buffer, and
  doubles the copied run each step.
- Setup code (FSE and Huffman tables, at most 2,048 entries) uses `for` loops
  in `Except`; that is per table, not per byte.

## Run the Lean reader

```
cd formal/lean4 && lake build l4qlvr
.lake/build/bin/l4qlvr stats /home/user/qlvr-work/instance
.lake/build/bin/l4qlvr scan /home/user/qlvr-work/instance http://dbpedia.org/property/year
tests/qlvr/run.sh                        # from the repository root
tests/stack/run.sh --route native --canary   # includes case qlvr-dump
```

2026-10-11: scans 4 pass, 0 fail (out of 4); `tests/qlvr/run.sh` 8 pass, 0
fail (out of 8). Dump against the input: 1,680,959 lines equal, 100,666 equal
after normalisation (all `xsd:double` printed as `xsd:decimal`), 0
different; dump against QLever's CONSTRUCT: 1,781,625 equal, 0 different.
Dump 4.4-5.2 s, peak RSS 49 MB; QLever's CONSTRUCT over HTTP 3.3-3.9 s.
Numbers, method and the Lean lessons: the format record, section "Read from
Lean".

- The vocabulary lookup (`findWord`) is a binary search on the first byte
  and then a linear scan: up to 406,730 decodes for an IRI (355-637 ms).
  Stage 4 added the side index (below); `findWord` stays as the reference.
- A local `structure Id` shadows the `Id` monad in the namespace; write
  `_root_.Id`. `meta` is a keyword. UInt64 literals in bit expressions need
  a type ascription.
- `tests/qlvr/run.sh` part (e) needs the server on port 7019; without it the
  part is printed as not run and not scored.

## Query the index from Lean (stage 4)

```
cd formal/lean4 && lake build l4qlvr
.lake/build/bin/l4qlvr side-index /home/user/qlvr-work/instance   # writes /home/user/qlvr-work/instance.qlvr-side/
.lake/build/bin/l4qlvr query /home/user/qlvr-work/instance --file ../../tests/qlvr/queries/q07-join-three.rq --explain
tests/qlvr/queries.sh        # from the repository root: the 21 oracle queries
tests/qlvr/bench.sh          # needs the server on port 7019
tests/stack/run.sh --route native --canary   # includes case qlvr-join (q07)
```

2026-10-11: 21 pass, 0 fail, 0 refused (out of 21); `tests/qlvr/run.sh` 18
pass, 0 fail (out of 18); side index against the linear scan 1,120 pass, 0
fail (out of 1,120); side-index build 3.3 s, peak RSS 83 MB. Times, plan
rules, join choice and the Lean lessons: the format record, section "Basic
graph patterns from Lean (stage 4)".

- The fragment: SELECT (variables, `*`, `COUNT(*)`, `COUNT(?x)`), a BGP with
  FILTERs (`&& || ! = != < > <= >= sameTerm STRSTARTS STRENDS CONTAINS`),
  GROUP BY variables, ORDER BY variables, DISTINCT, LIMIT, OFFSET. Anything
  else exits 3 with `l4qlvr: refused: <reason>` before any file is read.
  A refused oracle query goes into `tests/qlvr/expected-refusals.tsv` with an
  issue; `queries.sh` fails when a listed query starts to be answered.
- Semantics are QLever's, because QLever is the oracle: numeric constants
  fold to `Int`/`Double` Ids (`1936` matches `"1936"^^xsd:int`), FILTER and
  ORDER BY compare Ids as `compareIds` does (words by vocabulary position,
  which is ICU collation order; numbers by value). This is not SPARQL 1.1
  section 15.1 order.
- The side index is ours, next to the index directory (`INDEXDIR.qlvr-side/`),
  checked against the vocabulary by word count, `words.external` size and the
  XXH64 of `words.external.offsets`. Rebuild it after the index changes;
  `l4qlvr query` refuses a stale one. Without one it falls back to
  `findWord` and says so on stderr.
- Code that is generic over the fetch monad (scans, the side-index search)
  loops with `for` over a range; a hand-written tail call in a generic monad
  goes through a closure and the tail-recursion audit reports it. Trees from
  the parser (FILTER, WHERE) are walked with an explicit stack, not
  recursion.
- `run.sh` part (f) rebuilds the side index (about 3 s) before part (g).

## Measure performance (2026-10-11)

```
tests/qlvr/bench-warm.sh                 # all 21 queries; needs the server on port 7019
tests/qlvr/kernel.sh                     # Lean against C on the q07 kernel
cd formal/lean4 && .lake/build/bin/l4qlvr zstd-diff /home/user/qlvr-work/instance
.lake/build/bin/l4qlvr query /home/user/qlvr-work/instance --file Q.rq --repeat 20 [--libzstd]
.lake/build/bin/l4qlvr serve /home/user/qlvr-work/instance < queries.txt
```

Numbers, method and causes: docs/designissues/2026-10-11-qlvr-performance.md.
Rules that the measurements gave:

- Compare warm with warm. A process per query cost 17 to 22 ms of start and
  load for every query; in stage 4 the setup was up to 96 ms of a query.
- In `q07`, after the changes, the Lean zstd decoder is 52 of 75 ms; with
  libzstd the query takes 23 ms against QLever's 19 to 21 ms.
- A `Nat` shift (`1 <<< n`) calls `lean_nat_shiftl` and GMP: use `UInt64`.
  Loop state that is a `Nat` is boxed and tested at each step; `UInt64`
  state made the zstd sequence loop 15 to 30 percent faster (218 to 249-282
  MB/s).
- An 8-byte Id in a `ByteArray` is 8 byte reads with `Nat` index
  arithmetic, and `ByteArray.push` is an out-of-line call: the same kernel is
  9 to 16 times C with `ByteArray` columns and 2.5 to 2.9 times C with one
  word per Id (`FloatArray` or `Array UInt64`).
- Avoid per-row work that the order of the data makes unnecessary: rows with a
  key prefix are one range (binary search), `COUNT(*)` is a sum of block
  counts, runs of a sorted group variable need one map update each.
- Check every output change against the form kept beside it:
  `--reference-render` and `tests/qlvr/run.sh` part (i); `zstd-diff` and part
  (j); a `cmp` of all 21 answers against the previous binary.

## Rules for the Lean decoders

Every decoder over input-proportional data (blocks, rows, bytes of a frame,
code bytes of a word, words of the vocabulary) is a loop or a tail call with
an accumulator, never one stack frame per item. Check with
`python3 tools/lean-tail-recursion-audit.py --gate` (read the exit code) and a
`tests/stack` case at a size above any wasm stack limit. Lake commands run
with `formal/lean4/` as the working directory.

A `@[csimp]` twin of a decoder (`cmpBytes` and `cmpBytesFast`) is in force only in the
modules that import the module of its theorem. After a full `lake build`, run
`python3 tools/lean-csimp-reach.py --gate` and read the exit code
(https://github.com/danbri/factoidal/issues/871; its first run found two qlvr modules that
lacked the import).
