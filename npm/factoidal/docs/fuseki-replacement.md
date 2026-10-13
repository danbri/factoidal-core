# Using `factoidal serve` in place of Apache Jena Fuseki

Status: 2026-10-13, `@factoidal/core` 0.10.0. Every row below was tested
with curl against the installed package, and is gated by
`test/fuseki-compat.test.mjs` (assertions for what works, expected failures
naming an issue for what does not).

## Command-line mapping

| Fuseki | factoidal |
|---|---|
| `fuseki-server --file data.ttl /ds` | `factoidal serve --file data.ttl /ds` |
| `fuseki-server --update --file data.ttl /ds` | the same; updates are always on |
| `fuseki-server --loc DB /ds` (TDB2) | `factoidal pack data.nq STORE/gen-1 --layout ibk5`, `factoidal activate STORE gen-1`, then `factoidal serve STORE --query-path /ds/sparql --gsp-path /ds/data` |
| `--port 3030` | `--port 3030` (the default is 3030 in both) |
| `--localhost` | the default; `--host 0.0.0.0` to listen on all addresses |
| `--mem /ds` | `--file` with an empty file |
| `--config config.ttl` | none: https://github.com/danbri/factoidal/issues/832 |

`--file` packs the file into a new collection in a temporary directory
(layout `ibk5`, so every graph accepts writes) and serves it. Updates go to
that directory and are lost when the process ends, as with
`fuseki-server --file`. For data that must persist, use the `STORE` form:
updates are appended to the collection's delta log and synced before the
response is sent.

## Endpoints

With `--file DATA /ds`, or `--query-path /ds/sparql --gsp-path /ds/data`:

| Path | Fuseki | factoidal serve |
|---|---|---|
| `/ds/sparql` | query and update | query and update; GET with no query string returns the Service Description |
| `/ds/query` | query | query and update (the same endpoint) |
| `/ds/update` | update | query and update (the same endpoint) |
| `/ds/data` | Graph Store read and write | Graph Store read and write (`?default`, `?graph=IRI`, or a path under `/ds/data`) |
| `/ds/get` | Graph Store read | Graph Store read; PUT, POST and DELETE answer 405 with `Allow: GET, HEAD, OPTIONS` |
| `/ds/data` with no graph parameter | the whole dataset | 405: https://github.com/danbri/factoidal/issues/829 |
| `/$/ping`, `/$/datasets`, `/$/stats`, `/$/server` | administration API | 404: https://github.com/danbri/factoidal/issues/831 |

Without `--query-path`, the endpoint is `/sparql` and also `/query` and
`/update`; the Graph Store is `/data`.

Conformance: W3C SPARQL 1.1 Protocol, Graph Store HTTP Protocol (direct and
indirect identification) and Service Description tests against the running
server over TCP (`lake exe l4protocol-live`): 50 pass, 0 fail (out of 50),
re-run 2026-10-13 after the endpoint aliases were added
(`docs/designissues/2026-10-10-store-serve.md` has the command).

## Content types (tested)

- Query results: `application/sparql-results+json`,
  `application/sparql-results+xml`, `text/csv`, `text/tab-separated-values`.
- CONSTRUCT and DESCRIBE: `text/turtle` and the other RDF types the engine
  negotiates.
- Query requests: GET `?query=`, POST `application/x-www-form-urlencoded`,
  POST `application/sparql-query`. Updates: POST
  `application/sparql-update` and form `update=`.
- Graph Store GET: `text/turtle`, `application/n-triples`. JSON-LD and
  RDF/XML answer 406: https://github.com/danbri/factoidal/issues/830.

## Storage

Fuseki keeps a dataset in memory (`--mem`, `--file`) or in TDB2 (`--loc`).
factoidal serves a Shardborough collection: immutable generations plus a
delta log. A triples generation (`--layout ibk3`) accepts writes to the
default graph only; a named-graph write answers 501. Use `ibk4` or `ibk5`
for named graphs. The npm command cannot yet fold the delta log into a new
generation (`factoidal compact` and `factoidal update` exit 3:
https://github.com/danbri/factoidal/issues/641); the native
`l4block-shard-compact` of the source tree does it. Updates through the
server work.
TDB2 databases cannot be read: export them with `tdb2.tdbdump` and pack the
N-Quads (https://github.com/danbri/factoidal/issues/834).

## Not supported

- Several datasets in one process, assembler configuration, jena-text
  indexes, inference models, `unionDefaultGraph`:
  https://github.com/danbri/factoidal/issues/832.
- Authentication, access control, HTTPS:
  https://github.com/danbri/factoidal/issues/833. Bind to 127.0.0.1 (the
  default) or put a reverse proxy in front.
- Fuseki's administration API and UI: https://github.com/danbri/factoidal/issues/831.
