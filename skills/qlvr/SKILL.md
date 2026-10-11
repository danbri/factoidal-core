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
| `tools/qlvr/probe_index.py` | Python format probe: decodes vocabulary, permutation metadata, zstd column frames; `--scan IRI`, `--dump-block0 index.pso` |
| `tests/qlvr/queries/*.rq` | the 18 oracle queries |
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

## Rules for the Lean decoders

Every decoder over input-proportional data (blocks, rows, bytes of a frame,
code bytes of a word, words of the vocabulary) is a loop or a tail call with
an accumulator, never one stack frame per item. Check with
`python3 tools/lean-tail-recursion-audit.py --gate` (read the exit code) and a
`tests/stack` case at a size above any wasm stack limit. Lake commands run
with `formal/lean4/` as the working directory.
