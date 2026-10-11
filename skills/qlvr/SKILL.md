---
name: qlvr
description: Factoidal/qlvr — read a QLever index from Lean. How to rebuild the reference QLever instance (olympics dataset, 1,781,625 triples, image pinned by digest) and its SPARQL JSON query oracle with tools/qlvr/build-instance.sh, where the byte-level format record is (docs/designissues/2026-10-11-qlever-index-format.md), how to probe an index with tools/qlvr/probe_index.py, and the rules for the Lean decoders (loops, not per-item recursion). Use for any QLever on-disk format question, for work on the Lean QLever reader, or when the oracle or the instance must be rebuilt. Tracking https://github.com/danbri/factoidal/issues/778.
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
| `formal/lean4/Harness/Qlvr.lean` | `l4qlvr stats INDEXDIR`, `scan INDEXDIR PRED-IRI`, `dump INDEXDIR`, `words INDEXDIR`; permutation frames by `pread` |
| `tests/qlvr/run.sh` | scans against the oracle, dump against the input N-Triples and against QLever's CONSTRUCT, every word against the probe, stats |
| `tests/qlvr/canon_nt.py`, `compare_scan.py` | the canonicaliser (QLever's documented normalisations) and the scan-to-oracle comparison used by `run.sh` |
| `tests/qlvr/queries/*.rq` | the 21 oracle queries (q19-q21: single bound-predicate scans for the Lean reader) |
| `tests/qlvr/instance.json` | manifest: image digest, QLever commit, dataset URL and sha256, triple counts, every index file with size and sha256, every oracle answer with row count and sha256 |
| `docs/designissues/2026-10-11-qlever-index-format.md` | the format record: each file, its byte layout, source `file:line` at the pinned commit, what the instance confirmed, and the stage 3 plan |

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
  and then a linear scan: up to 406,730 decodes for an IRI (355-637 ms). A
  side index or the ICU collation subset is stage 4 work.
- A local `structure Id` shadows the `Id` monad in the namespace; write
  `_root_.Id`. `meta` is a keyword. UInt64 literals in bit expressions need
  a type ascription.
- `tests/qlvr/run.sh` part (e) needs the server on port 7019; without it the
  part is printed as not run and not scored.

## Rules for the Lean decoders

Every decoder over input-proportional data (blocks, rows, bytes of a frame,
code bytes of a word, words of the vocabulary) is a loop or a tail call with
an accumulator, never one stack frame per item. Check with
`python3 tools/lean-tail-recursion-audit.py --gate` (read the exit code) and a
`tests/stack` case at a size above any wasm stack limit. Lake commands run
with `formal/lean4/` as the working directory.
