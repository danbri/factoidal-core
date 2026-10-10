# `factoidal serve`: a SPARQL 1.1 endpoint over a Shardborough collection

Date: 2026-10-10. Tracking: https://github.com/danbri/factoidal/issues/669
(step 1). Open gap: https://github.com/danbri/factoidal/issues/770.

## 1. What it is

`factoidal serve STORE --port N` serves the activated generation of a
collection, with its delta log, over HTTP/1.1:

| Path | Specification |
| --- | --- |
| `GET`/`POST /sparql` (also `/sparql/`, `/query`, `/update`) | SPARQL 1.1 Protocol §2.1 query, §2.2 update |
| `GET /sparql` with no query string | SPARQL 1.1 Service Description §2 |
| `/data`, `/data/...` | SPARQL 1.1 Graph Store HTTP Protocol (`?default`, `?graph=IRI`, direct identification under `/data`) |

## 2. Where each decision is

The Node host (`npm/factoidal/bin/serve.mjs`) accepts TCP connections and
moves bytes. It does not use Node's HTTP parser. Every decision is Lean:

| Decision | Module |
| --- | --- |
| Where a request ends: request line, header fields, `Content-Length`, chunked transfer coding, 413/431/501/505 refusals, persistence (RFC 9112 §2-§7, §9.3) | `L4Factoidal/HTTP/Wire.lean` `frameRequest` |
| The response bytes: status line, `content-length`, `connection: close`, no content for 204 and HEAD | `L4Factoidal/HTTP/Wire.lean` `formatResponse` |
| Routing, the protocol decoder, status codes, negotiation (results JSON, XML, CSV, TSV; Turtle, N-Triples), evaluation, the service description, the Graph Store | `L4Factoidal/SPARQL/StoreEndpoint.lean` `handle`, which calls `Protocol.decodeRequest`, `ProtocolService`, `GraphStoreService.serve`, `ServiceDescription.buildSd` |
| Which files a server reads; the open; one request; the commit | `formal/lean4/Wasm/Ops/StoreServe.lean` (`storeServeKeys`, `storeServeOpen`, `storeServeRequest`, `storeServeCommit`, `storeServeClose`) |

`tools/host-purity-lint.sh` checks `serve.mjs` and `serve-worker.mjs` in both
groups: no status code other than 500, no protocol header name, no artifact
suffix, no field read.

## 3. The served view

`storeServeOpen` verifies and decodes every block through `storeOpen` (the
same admission the store handle uses), drops the handle's sidecars, and
keeps the dataset and its indexed backend (`indexedDatasetBackend`). It
then replays the committed delta-log batches after the compacted epoch
(`openLog`: the same `parseLog`, `validBatchHistory` and
`replayBatchesSinceEpoch?` the native reader uses). A torn log suffix, a
malformed `compacted.epoch` or an invalid batch order refuses the open.

A query is evaluated through the indexed backend when it names no dataset of
its own, and through the reference evaluator otherwise, with `env.dataset`
set for EXISTS (CLAUDE.md anti-pattern 34). This is the routing
`queryParsedDatasetWith` uses for the store handle.

## 4. Updates and Graph Store writes

1. The request is executed by the reference semantics over the served view:
   `SPARQL.Update.applyUpdateIn` for an update, `GraphStoreService.serve` for
   a Graph Store PUT, POST or DELETE.
2. `datasetDelta old new` is the change as `DeltaEntry` values (adds and
   removes per graph, `clear` for a graph emptied, `drop` and `create` for
   graph existence). `#guard`s check that `applyDeltaEntries old` of it is
   set-equal to `new`.
3. `storeServeRequest` answers `append`: the DLB1 batch bytes (with the DLOG
   header when the log is empty), the file, and the size the file must have.
   The host appends with `appendSyncAtSize` (fsync) and reports the outcome;
   `storeServeCommit` then switches the view and answers the response, or
   answers 500 when the append failed. No response says "done" before the
   batch is durable.

Because the change comes from the reference semantics, a WHERE-dependent
update (`INSERT … WHERE`, `DELETE WHERE`) is stored. `SPARQL.UpdateDelta`
(what `l4block-delta-log` uses) refuses those. A batch the server writes is
read by `l4block-delta-log --inspect`, `l4block-id-v3-query` and
`l4block-shard-compact` like one that tool wrote.

## 5. Write scope

| Generation | Accepted changes | Why |
| --- | --- | --- |
| IBK3 (triples) | the default graph only; a named-graph change is 501 and nothing is stored | the native readers replay (`foldDeltaBatches … none`) and compact (`…-compacted-default-dlog-v1`) the default graph only |
| IBK4, IBK5 (quads) | every graph | the server is the only reader that replays the log (https://github.com/danbri/factoidal/issues/770) |

On open, an IBK3 generation's log is replayed for the default graph only,
so the server and the native IBK3 reader answer from the same data.

## 6. Gates (measured 2026-10-10)

- W3C, against the live server over TCP (`lake exe l4protocol-live`,
  `Harness/ProtocolLive.lean`): protocol 34, graph-store-protocol 13
  (direct 4, indirect 9), service-description 3: **50 pass, 0 fail (out of
  50)**. Each test gets its own collection, packed from its `ut:graphData`
  as an IBK5 quad generation. The deprecated `http-rdf-update` suite is not
  replayed live: its requests are Markdown in `rdfs:comment` and its
  in-memory runner seeds graphs from entry names, which is runner glue and
  not a request a client sends.
- `tests/store-serve/serve.mjs`: **19 pass, 0 fail, 1 expected failure
  (out of 20)**. FILTER NOT EXISTS, FILTER EXISTS, MINUS, OPTIONAL with
  FILTER and a sub-SELECT give equal, non-empty rows through the live server,
  `factoidal query` and the in-memory engine over the source file; an update
  through the server, a query, `l4block-shard-compact`, activation, a
  restart and the same query; framing (pipelining, chunked, a malformed
  request line); the write scope. The expected failure is the native quad
  reader after a server update (issue 770).

## 7. Costs and limits

- Open cost and memory are the store handle's: every block is decoded and
  indexed once. Measured on `examples/wikidata/subsets/lifesci-kgx/data/gene.ttl`
  (888,949 triples, 13 IBK3 blocks): see `skills/shardborough-storage/SKILL.md`
  § Serving.
- An update re-indexes the whole view and its diff is linear in the size of
  the graphs it changes. Replay at open applies each entry with
  `Graph.add`/`Graph.remove`, linear in the graph per entry.
- One engine instance, single-threaded; requests are served in order.
  Several processes must not serve one collection for writing: the append
  has no advisory lock (https://github.com/danbri/factoidal/issues/644).
- The retained-bytes cap of the store handle (128 MiB of artifact bytes)
  bounds the collection a server can open.
