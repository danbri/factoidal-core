---
title: Shardborough (early stage)
description: The persisted RDF store of Factoidal, at an early stage — pack an RDF file into an immutable generation, activate it, query it, apply SPARQL Update through a delta log and compact — with output recorded from real runs.
layout: hub.njk
tests: tests/hub/hub_servers_test.mjs
---

# Shardborough (early stage)

[Hub](../) · the persisted store

**Early stage.** The formats change between wire versions, the npm
commands do not yet cover updates and compaction, and the query path
reads whole blocks into memory. Do not use it to keep data you cannot
rebuild.

A Shardborough *collection* is a directory. Each *generation* under it is
an immutable set of blocks and index sidecars with a manifest and Merkle
commitments. The file `CURRENT` names the activated generation. Updates go
to a delta log beside the generation; compaction writes a new generation
that includes them.

The runs below were made on 2026-10-20 with `@factoidal/core` 0.10.0 from
this repository (shown as `factoidal`) and the Lean native tools
(`l4block-*`, built with `lake build` in `formal/lean4`). `data.ttl` is
the four-line FOAF file of the [servers page](../servers/).

## Pack, activate, query: the npm command

```
$ factoidal pack data.ttl store/gen-1 --layout ibk5
packed 374 bytes of turtle into store/gen-1
20 artifacts, 4294 bytes, layout ibk5
5 rows
activate it with: factoidal activate store gen-1

$ factoidal activate store gen-1
activated gen-1: 19 artifacts verified, 2424 bytes

$ factoidal query store 'SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name'
mode ibk5-full-manifest(1), 1 artifact, 291 bytes read, plan declares 2 block rows
name
"Alice"
"Bob"
2 rows

$ factoidal inspect store
generation gen-1 (activated through CURRENT)
manifest manifest.sbm2, 1870 bytes, wire version 10
layout quad-ibk5-ptd2-lgi4-gbi1-merkle-v0
3 entries, 696 bytes, 5 rows

#  rows  bytes  kind  graphs   predicate                                        blobs
0  2     239    IBK5  default  http://www.w3.org/1999/02/22-rdf-syntax-ns#type  0
1  2     291    IBK5  default  http://xmlns.com/foaf/0.1/name                   0
2  1     166    IBK5  default  http://xmlns.com/foaf/0.1/knows                  0
```

The query read one block, the `foaf:name` block, 291 bytes.

`factoidal update` and `factoidal compact` are not wired in the npm
package yet:

```
$ factoidal update store 'INSERT DATA { <http://example.org/carol> <http://xmlns.com/foaf/0.1/name> "Carol" }'
factoidal update: not yet wired. The delta-log operations are stage 4 of the milestone.
This needs a WebAssembly operation from the Lean engine; see https://github.com/danbri/factoidal/issues/641.
(exit 3)
```

`factoidal serve STORE` does apply updates through the delta log; see the
[servers page](../servers/).

## The SBM11 layout: `--layout sbm11`

Since 0.17.0, `factoidal pack --layout sbm11` writes an SBM11 generation
(64-bit global term ids, a term dictionary and four sorted permutations,
each file with a Merkle sidecar). The files are the same, byte for byte,
as those of the native `l4sbm11-pack` (605 of 605 W3C census inputs).
`activate` checks the length, SHA-256 and Merkle root of every file before
it moves `CURRENT`; `inspect` and `query` read the store. IBK5 stays the
default layout (https://github.com/danbri/factoidal-core/pull/131,
https://github.com/danbri/factoidal/issues/1009). Run on 2026-10-27 with
`@factoidal/core` 0.18.0, the same `data.ttl`:

```
$ factoidal pack data.ttl store/gen-1 --layout sbm11
packed 187 bytes of turtle into store/gen-1
21 files, 2372 bytes, layout sbm11
activate it with: factoidal activate store gen-1

$ factoidal activate store gen-1
activated gen-1: 10 artifacts verified (21 files, 1218 bytes), layout sbm11

$ factoidal query store 'SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name'
path=ids, 9 reads, 635 bytes read
name
"Alice"
"Bob"
2 rows

$ factoidal inspect store
store store
generation gen-1 (activated through CURRENT)
manifest manifest.sbm11
layout sbm11
8 terms
generation directory holds 21 files, 2372 bytes
```

`factoidal serve` does not read an SBM11 store yet.

### Opening a store from Node

`openStoreHandle` opens a store for many queries. Times measured in the
pull requests on the londat store (142,314 quads, 1,046 blocks, a 753 kB
manifest; the 0.17.0 run: Apple M1, Node 22):

| `openStoreHandle` | before | after | change |
|---|---|---|---|
| 0.16.0 → 0.17.0, median of 7 | 1,485 ms | 562 ms | manifest decoded over bytes, arguments read in place, HACL* SHA-256 in `storeOpen` (https://github.com/danbri/factoidal-core/pull/135) |
| 0.17.0 → 0.18.0, scoped open, median of 9 | 305 ms | 198 ms | the manifest goes to the engine as bytes and is decoded once (https://github.com/danbri/factoidal-core/pull/141) |

An SBM11 store opens in about 5 ms. Tracking:
<https://github.com/danbri/factoidal/issues/1039>.

## Update through the delta log and compact: the native tools

The full cycle on an IBK3 (triples) generation:

```
$ l4block-shard-pack data.ttl n3store/gen-1 ibk3
l4block-shard-pack format=predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0 input=data.ttl triples=5 blocks=3 ...
$ l4block-shard-activate n3store gen-1
l4block-shard-activate root=n3store generation=gen-1 verified-logical-bytes=628 pointer=CURRENT

$ l4block-delta-log n3store --update 'INSERT DATA { <http://example.org/carol> <http://xmlns.com/foaf/0.1/name> "Carol" }'
l4block-delta-log committed path=n3store/gen-1/deltas.dlog seq=1 epoch=1 ops=1 bytes=171 sync=file retries=1

$ l4block-id-v3-query n3store --query 'SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name'
l4block-id-v3-query shards=1 open-mode=ibk3-paged-merkle(1) delta=base-plus-delta logical-read-bytes=267 fetched-bytes=275
l4block-id-v3-query rows=3 preview=[[("name", ... "Alice" ...)], [("name", ... "Bob" ...)], [("name", ... "Carol" ...)]]

$ l4block-shard-compact n3store/gen-1 n3store/gen-2
l4block-shard-compact source=n3store/gen-1 output=n3store/gen-2 format=ibk3 base-triples=5 delta-batches=1 compacted-triples=6 epoch=1 verified-logical-bytes=628
$ l4block-shard-activate n3store gen-2
l4block-shard-activate root=n3store generation=gen-2 verified-logical-bytes=727 pointer=CURRENT

$ l4block-id-v3-query n3store --query 'SELECT ?name WHERE { ?p <http://xmlns.com/foaf/0.1/name> ?name } ORDER BY ?name'
l4block-id-v3-query shards=1 open-mode=ibk3-paged-merkle(1) delta=base logical-read-bytes=366 fetched-bytes=374
l4block-id-v3-query rows=3 ...
```

On an IBK5 (quads) generation the same log append succeeds, but the
native quad query does not replay the log and compaction fails:

```
$ l4block-delta-log nstore --update 'INSERT DATA { ... "Carol" }'
l4block-delta-log committed path=nstore/gen-1/deltas.dlog seq=1 epoch=1 ops=1 bytes=171 sync=file retries=1
$ l4block-quad-query nstore --query 'SELECT ?name WHERE { ... }'
l4block-quad-query rows=2 ...
$ l4block-shard-compact nstore/gen-1 nstore/gen-2
l4block-shard-compact failure: source child artifact is missing, changed, or malformed
```

## Limits

- npm `update` and `compact` are not wired:
  <https://github.com/danbri/factoidal/issues/641>. Expected-failure test:
  `tests/hub/hub_servers_test.mjs`.
- Native readers and compaction do not replay the delta log of a quad
  generation: <https://github.com/danbri/factoidal/issues/770>.
- Query execution materialises the selected blocks (or the whole
  generation) in memory: <https://github.com/danbri/factoidal/issues/775>.
- No end-to-end theorem that a persisted query answers the same as the
  in-memory evaluator: <https://github.com/danbri/factoidal/issues/776>.
- A named graph with no triple is lost in IBK4 and IBK5 stores:
  <https://github.com/danbri/factoidal/issues/880>.
- SBM11 (above) is in the npm commands `pack`, `activate`, `inspect` and
  `query`, not yet in `serve`: <https://github.com/danbri/factoidal/issues/787>,
  <https://github.com/danbri/factoidal/issues/1009>.
