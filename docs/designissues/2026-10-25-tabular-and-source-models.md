# One table type and one source description for the pipeline

Status: accepted by the owner on 2026-10-25 (PR https://github.com/danbri/factoidal-core/pull/111 merged; answers in section 6). No code yet.
Date: 2026-10-25. Base: `main` at `5fbd1ca`.
Tracking: https://github.com/danbri/factoidal/issues/1033; network retrieval records: https://github.com/danbri/factoidal/issues/1035.

Owner, 2026-10-25, verbatim:

> "Re pipes, cav and rml and sparql results share a tsbular data model, useful?
> Also do we have a datamodel for filenames, and input streams, abstracting from
> protocol/spec eg parser. Or db on disk, etc. In theory a URI can do everything
> but this needs thought."

> "If parsers and other components take extra args and settings find a way to
> expose that in api and keep it in provenance/pipeline, also consider their
> impact on proofs"

("cav" is read as CSV/CSVW.) The settings part is the subject of
`2026-10-25-pipeline-settings-and-provenance.md` (in progress on branch
`claude/pipeline-0.16`). This record covers tables and sources, and says where
each meets the settings and the evidence record.

## 1. What exists (survey of 2026-10-25)

Paths are under `formal/lean4/L4Factoidal/`.

### Tables: six types, no shared one

| Type | Cells | Missing value | Rows |
|---|---|---|---|
| `CSVW.Table` / `CSVW.Row` (CSVW/Dialect.lean:145,152) | strings; datatypes in the metadata, applied at conversion | empty string; `null` through `Inherited` | list, source line kept |
| RML `Record.table` (RML/Record.lean:38), `RVal {lexical, natural}` (RML/Value.lean:25) | lexical form + optional datatype IRI | cell dropped, column kept (`rml:null`) | list |
| SPARQL `SolutionSeq` = `List Binding` (SPARQL/Algebra.lean:162,165); `QueryResult` (SPARQL/Results.lean:62) | RDF terms | variable absent from the binding | list = multiset (SPARQL 1.1 §18.5) |
| Planner `Tuple`, `Plan.Row` (Planner/Capability.lean:54; Plan.lean:90) | RDF terms, positional | — | list |
| `Qlvr.Table` (Qlvr/Bgp.lean:171), reused by SBM11 | 8-byte term ids, columnar | not checked | `sortVar` records a sort |
| SBM11 `IdRow` (Storage/Sbm11/OptJoinTheorems.lean:472) | term ids | absent | list |

Conversions today: RML reads SPARQL results through `solutionText`
(RML/SparqlSource.lean), which turns each term into text and drops literal
datatypes. RML and the planner's FacadeX kind reuse the CSVW dialect reader.
There is no CSVW-to-bindings conversion and no bindings-to-CSVW conversion. The
dataflow wire `csv` (Dataflow/Wire.lean:36) has no working stage.

### Sources: no descriptor

| Where | What names or locates the input |
|---|---|
| `Dataflow.Document {bytes, mediaType, source}` (Dataflow/Stage.lean:72) | `source` is "path or URL", used as an id only |
| `RDF.parseDocument extra fmt mode base text` (RDF/Source.lean:232) | format enum, base IRI, RDF 1.1/1.2 mode; input is text |
| `Medium {readAt, size, writeObject, switchPointer}` (Storage/Medium.lean:48) | object names relative to a root that each host maps (directory, OPFS, URL prefix) |
| RML `LogicalSource {path, iterator, refFormulation, root, …}` (RML/Model.lean:33) | path + root; D2RQ and SQL sources refused |
| SERVICE `EvalEnv.services : List (Iri × Graph)` (SPARQL/Expr.lean:1649) | endpoint IRI as a lookup key |
| Planner `Capability.location : String`, `Described.kind : String` (Planner/Capability.lean:59) | untyped strings |
| npm `registerSbm11Source(source, reader)` | opaque string key |

A URI has two roles in this code. It is a NAME (SERVICE keys,
`Document.source`, the npm key, the IRI that provenance talks about) and it is
a LOCATOR (RML `path`, FacadeX `location`, REST `urlTemplate`, `sd:endpoint`,
the LWS URL prefix). The two are mixed in untyped strings. Evidence records name
no input source, time or checksum, and nothing emits PROV-O.

## 2. Proposal A: one table type

### The type

```lean
/-- A cell: an RDF term, or a lexical form with an optional datatype IRI
    (the CSVW "string value + datatype annotation" and the RML RVal). -/
inductive Cell
  | term (t : RDF.Term)
  | lexical (s : String) (datatype : Option Iri)

/-- A table: named columns and a multiset of rows. A row is a partial map
    from column names to cells (an absent column is SPARQL "unbound", CSVW
    "null", RML "rml:null"). `order` is the sort key list when the rows are
    ordered (ORDER BY, CSV row order); none when they are not. -/
structure Table where
  columns : List String
  rows    : List (List (String × Cell))
  order   : Option (List (String × Direction))
```

- Rows are a multiset, as in the SPARQL algebra (SPARQL 1.1 §18.5) and SQL.
  A set is the result of an explicit DISTINCT. This keeps SPARQL results
  without loss.
- "Missing" has one meaning: the column is absent from the row. The three
  current encodings (empty string, dropped cell, absent variable) map to it at
  the reader, where each format's own rule decides (CSVW `null`, RML
  `rml:null`).
- The cell keeps the difference between "already an RDF term" (SPARQL) and
  "text with an annotation, not yet a term" (CSV before the CSVW conversion).
  The CSVW cell rules (CSVW Tabular Data Model §6.4, Generating RDF §4.6)
  become one function `Cell → Option RDF.Term` that both CSVW and RML call.

### Conversions, each with a theorem

| Conversion | Theorem |
|---|---|
| `SolutionSeq ↔ Table` (columns = projected variables) | round trip both ways, rows equal as multisets |
| `CSVW.Table + metadata → Table` | each cell's `Cell.toTerm` equals the term the current CSVW conversion emits for that cell |
| RML `Record.table → Table` | as above, with `RVal` |
| SPARQL results formats (SRX, SRJ, CSV, TSV) `↔ Table` | the existing reader and writer round trips, restated over `Table`; CSV stays lossy (SPARQL 1.1 Query Results CSV and TSV §2), TSV and SRX are not |
| `Qlvr.Table` / `IdRow → Table` | decode by the dictionary; equal to the reference evaluator's `SolutionSeq` (already the claim of https://github.com/danbri/factoidal/issues/776) |

### What it gives

1. RML over SPARQL results without the text step, so literal datatypes are
   kept. Today `solutionText` drops them; this is a defect:
   https://github.com/danbri/factoidal/issues/1034.
2. A CSV-to-bindings path: a CSVW table can be a `VALUES` block or a SERVICE
   answer, and the planner's FacadeX kind and a SQL source (later) give the
   same type.
3. One dataflow wire `table` that replaces `csv` and is the output of SELECT
   (in place of `answer` for SELECT; ASK stays `answer`). The type check can
   then connect SELECT → CSVW writer, CSV reader → RML, SELECT → RML.
4. One place for the multiset rule. The 2026-09-08 duplicate-triple error
   (CLAUDE.md anti-pattern 37) was about sets; the table needs the opposite
   rule, multiset, stated once and tested by row count.

### Cost

The six types stay where they are fast (the id tables stay columnar). `Table`
is the denotation at stage boundaries and the target of the conversion
theorems, not a replacement inside the SBM11 executor.

## 3. Proposal B: a source description

### Names and locators are separate fields

A URI can name anything (RFC 3986 §1.1: "a resource"), but how to read it
depends on the scheme, the server, content negotiation, credentials, and
whether a local copy is wanted. HTTP itself separates the resource (named by a
URI) from a representation (bytes with a media type, RFC 9110 §3.2). DCAT 3 has
the same split: `dcat:Dataset` (the thing) and `dcat:Distribution` with
`dcat:accessURL`, `dcat:downloadURL`, `dcat:mediaType` and `spdx:checksum`
(how to get the bytes). So:

```lean
inductive Locator
  | file (path : String)                 -- host file system, relative to a root
  | http (url : String)                  -- GET, with negotiation settings
  | medium (root : String) (object : String) -- the Storage.Medium objects (OPFS, directory, URL prefix)
  | sparqlEndpoint (url : String)        -- SPARQL 1.1 Protocol
  | sbm11 (root : String) (generation : Option String)
  | inline                               -- bytes given by the caller

structure SourceDesc where
  name      : Option Iri          -- what the data is about / is called; used in provenance
  locator   : Locator             -- how the bytes were obtained
  mediaType : Option String       -- RFC 6838 media type, e.g. text/turtle
  settings  : Settings            -- base IRI, RDF 1.1/1.2 mode, CSVW dialect, encoding, ...
  checksum  : Option ByteArray    -- SHA-256 of the bytes read
  retrieved : Option String       -- xsd:dateTime of the read
```

- The parser stays a function of bytes, media type and settings. It does not
  see the locator. Reading is host IO (iron rule 11: pure I/O is the allowed
  realisation).
- `Dataflow.Document {bytes, mediaType, source}` becomes
  `{bytes, desc : SourceDesc}`. `source : String` is the current, untyped
  version of `name` plus `locator`.
- The planner's `Capability.location : String` and `Described.kind : String`
  become a `Locator` (plus the kind-specific description), so the catalog and
  the pipeline name sources the same way.
- RML `LogicalSource` maps to a `SourceDesc` plus its iterator and reference
  formulation; `rml:source` values become locators.

### Where the proof chain starts

A theorem about a parser is a statement about bytes. The step from a locator to
bytes cannot be proved; it is an assumption of the run. The evidence record
names it as an assumption, with the checksum: "the bytes read from
`locator` at `retrieved` have SHA-256 `checksum`". Each later step is then
proved or tested over those bytes, and a second run can check the assumption
again by comparing the checksum. This is the same shape as `ReadsWritten` in
`FileGenTheorems.store_written` (each positioned read returns the bytes the
packer wrote).

### Provenance in RDF

With the settings record (the other design record), each evidence record has
enough for PROV-O and DCAT terms:

- `prov:Activity` per node, `prov:used` → the input entity,
  `prov:wasGeneratedBy` from the output, `prov:startedAtTime`;
- the input entity is a `dcat:Distribution` with `dcat:accessURL` (from the
  locator), `dcat:mediaType`, `spdx:checksum`; `prov:wasDerivedFrom` → the
  `name` IRI;
- the node's settings and its status (proved, tested, assumed, unproved).

The graph is built in Lean (CLAUDE.md anti-pattern 36: no RDF decisions in the
JS). This is https://github.com/danbri/factoidal/issues/563. The Canary Wharf
hub page builds such a graph by hand today; its shape is the test oracle.

## 4. Network retrieval records

Owner, 2026-10-25, verbatim: "Any transactions with the global web also need
to go into the evidence pipeline system - if we dereference http or https at
least. maybe ftp, gopher and others, keep records of headers, ip addresses,
certs, timing etc etc. Treat this information as potentially high risk re
security/privacy." Tracking: https://github.com/danbri/factoidal/issues/1035.

### Scope

Every network read that the engine or a host makes for a pipeline step:
`Locator.http`, `Locator.sparqlEndpoint` (SERVICE and the Protocol client),
the LWS and Solid clients, and the fetches that a reader makes on its own
(JSON-LD remote contexts, CSVW metadata discovery, RML sources, GRDDL
transformations). HTTP and HTTPS first. A scheme with no record type (FTP,
Gopher, and the rest) is refused with an error that names the scheme. It is
not fetched without a record.

### The record

One `Retrieval` per request, redirects included, attached to the
`SourceDesc` it produced:

| Field | Content |
|---|---|
| request | method, URL (redacted as below), headers sent (redacted) |
| response | status, headers (redacted), body length, body SHA-256 |
| redirects | the chain of (status, Location), each with its own record |
| network | resolved remote IP address and port, protocol (HTTP/1.1, 2, 3) |
| TLS | see "TLS and certificate details" below |
| timing | start time (xsd:dateTime) and the durations of DNS, connect, TLS, first byte and total, the phases of W3C Resource Timing and of the HAR format |
| outcome | completed, refused (with the rule), or failed (with the error) |

### TLS and certificate details

Owner, 2026-10-25, verbatim: "Re recording tls, keep more of the crypto
details too, certs etc". For an HTTPS (or other TLS) exchange the record keeps:

- the negotiated protocol version (RFC 8446 for TLS 1.3), cipher suite, key
  exchange group (for example X25519), the server's signature algorithm, the
  ALPN protocol, the SNI host name sent, and whether the session was resumed;
- the full server certificate chain as sent, each certificate in DER (RFC
  5280), with its SHA-256 fingerprint, subject, issuer, serial number,
  validity period, subject alternative names, key type and size, and the
  SHA-256 of its SubjectPublicKeyInfo;
- the verification result: the trust anchor that the chain was verified to,
  the trust store's name and version, the host-name check, and each error;
- Certificate Transparency: the signed certificate timestamps received (RFC
  6962), from the certificate, the TLS extension or OCSP;
- revocation: the stapled OCSP response if one was sent (RFC 6960), with its
  status and times;
- the response's `Strict-Transport-Security` header (RFC 6797), already in the
  headers, noted with the TLS facts.

Never recorded: session keys, the master secret or any key log, the client's
private key, and the client certificate. Server certificates are public data,
but the chain and the SNI name show which hosts the user contacted, so they
are in the local record only. The shared subset keeps the leaf certificate's
SHA-256 fingerprint, as before.

The host performs the IO and reports these facts. Lean builds the record,
applies the redaction and decides what reaches the evidence (iron rule 11:
the host side is pure IO; the decisions are in the formal source).

### Security and privacy: default deny

The record can contain credentials, personal data and information about the
user's network. Rules:

1. Credentials never reach a record. The values of `Authorization`,
   `Proxy-Authorization`, `Cookie` and `Set-Cookie` are removed, and so are
   query parameters whose names are on a token list (for example `token`,
   `key`, `access_token`, `sig`). The header NAME stays, with the value
   replaced by `[removed]`, so the record still shows that a credential was
   sent. A secret is not hashed instead of removed, because the hash of a
   low-entropy secret can be reversed by trying candidates.
2. The local IP address, the local port and any client certificate are not
   recorded.
3. Two levels of record. The full redacted record goes to a local store with
   access control (a file the user owns, or browser storage), never to the
   package's shared state. Shared or published provenance (the PROV-O graph
   of section 3, a hub page, a pipeline record that someone shares) gets the
   SUBSET: URL (redacted), status, media type, body SHA-256, server
   certificate fingerprint, start time. Shared provenance gets more only when
   the caller opts in for that pipeline.
4. Retention: the local store has a limit (age or count) that the caller sets,
   with a default.
5. The response body is in the record only as its length and checksum. The
   body itself is the data, and it goes where the data goes.

### Proofs

A retrieval cannot be proved. The evidence names it as an assumption: "a GET
of URL U at time T returned status S and a body with SHA-256 H, from address
A, with server certificate F". Every later step is proved or tested over the
bytes with checksum H, as in section 3. Running the pipeline again and
comparing H checks the assumption.

### Tests that come with the first implementation

- A redaction test that fails if any of the listed header values, or a value
  of a listed query parameter, appears anywhere in a record or in the shared
  subset.
- An expected-failure case for each refused scheme, naming the issue.
- A record built from a recorded HTTPS exchange (a fixture), checked field by
  field.

## 5. Order of work (proposed)

1. `Table`, `Cell`, `SolutionSeq ↔ Table` with the round-trip theorem; `Cell.toTerm`
   shared by CSVW and RML. Expected-failure test for the RML datatype loss.
2. RML over `Table` (fixes the datatype loss); `table` wire; SELECT → `table`.
3. `SourceDesc` and `Locator`; `Document` carries it; checksum in the evidence
   record.
4. PROV-O and DCAT output of the evidence (issue 563).
5. Planner catalog locators.
6. Network retrieval records (section 4), with the redaction tests, before
   any new code path fetches over the network.

Each step lands with its tests; steps 1 and 3 do not depend on each other.

## 6. Owner answers (2026-10-25)

1. SELECT gives `table` instead of `answer`. Owner, verbatim: "select give
   table? Sure". ASK stays `answer`; CONSTRUCT and DESCRIBE give `dataset`
   (https://github.com/danbri/factoidal/issues/1026).
2. `SourceDesc.name` has no default. Owner, verbatim: "no default". When the
   caller gives no name, the field is empty; the locator is never copied into
   it.
3. Keep more TLS and certificate detail: "Re recording tls, keep more of the
   crypto details too, certs etc" (section 4, "TLS and certificate details").
