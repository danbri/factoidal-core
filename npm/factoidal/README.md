# @factoidal/core

> Release 0.9.0. The API surface is early and may change before 1.0. See
> [CHANGELOG.md](CHANGELOG.md).

RDF and SPARQL for JavaScript, in Node and in the browser, from one
WebAssembly module: the Lean 4 library `L4Factoidal`
([`formal/lean4`](https://github.com/danbri/factoidal-core/tree/main/formal/lean4))
compiled through C. The parsers, the SPARQL evaluator, the reasoners, the
validators and the store decoder are Lean code; the JavaScript in this
package shapes arguments and results and moves bytes. Since 0.9.0 the
package carries this one engine
([issue 713](https://github.com/danbri/factoidal/issues/713)); the F\*
engine builds are comparison artifacts of
[danbri/factoidal-builds](https://github.com/danbri/factoidal-builds).

The Lean library has no `sorry`, no user axioms and no `native_decide`, and
its W3C behaviour is pinned by build-time `#guard` cases
(`l4-assets/version.json`, `claims`). W3C suite scores, with dates and
commits, are at
[danbri.github.io/factoidal/test-results](https://danbri.github.io/factoidal/test-results/).

- **SPARQL 1.1 query and update in your process**, plus SPARQL 1.2 queries
  (triple terms, reified triples, annotations) with `{sparql12: true}`.
- **Every RDF 1.1 syntax**: Turtle, TriG, N-Triples, N-Quads, RDF/XML,
  JSON-LD; and the RDF 1.2 forms of the first four.
- **RDFC-1.0 canonicalization**: `canonicalize()` gives canonical N-Quads,
  stable under blank-node relabelling.
- **Reasoning**: RDFS, OWL 2 RL, core RDFS (ρdf), RDFS-Plus closures; OWL DL
  consistency and entailment by refutation; query-time entailment regimes.
- **Validation and mapping**: SHACL (Core, SHACL-SPARQL, SHACL 1.2 node
  expressions), ShEx (ShExJ and ShExC), RML, CSVW, RIF Core, XSLT 1.0,
  XPath 1.0, Schematron, JSON Schema, XForms, Content MathML.
- **A persisted store**: open a Shardborough generation (from disk, or over
  `fetch()` in a page) and query it, every block verified against the
  SHA-256 its manifest commits.
- **RDF/JS data model** (`DataFactory`, terms with `.equals`, `DatasetCore`).

## Install

```bash
npm install @factoidal/core
```

Node 22.12 or later (`index.js` gives the ES module `index.mjs` to
`require()`), Deno 2, or a browser with WebAssembly.

## Quickstart

Every engine call returns a Promise. The engine loads on the first call.

```js
import { parse, query, serialize, canonicalize } from "@factoidal/core";

// Parse any supported syntax into an RDF/JS DatasetCore.
const ds = await parse(`
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  _:a foaf:name "Alice" ; foaf:knows _:b .
  _:b foaf:name "Bob" .
`, { format: "turtle" });

// SELECT: bindings are Map<variableName, RDF/JS Term>, in SELECT order.
const rows = await query(ds, `
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?name WHERE { ?p foaf:name ?name } ORDER BY ?name
`);
for (const b of rows) console.log(b.get("name").value); // Alice, Bob

const yes = await query(ds, "ASK { ?s ?p ?o }");        // true
const c14n = await canonicalize(ds);                    // RDFC-1.0 N-Quads
const nq = await serialize(ds, { format: "nquads" });
```

CommonJS: `const factoidal = require("@factoidal/core")`. It is the same
module instance as the ES import, so `instanceof Dataset` holds across both.

### Parsing is strict

A syntax error, an undeclared prefix, or a relative IRI with no `baseIRI`
in effect rejects the whole parse with a `ParseError`:

```js
import { parse, ParseError } from "@factoidal/core";

const text = '<http://x/s> <http://x/p> "😀" .\nBOGUS .\n';
try {
  await parse(text);
} catch (err) {
  if (err instanceof ParseError) {
    console.log(err.line, err.column);   // 2 6
    console.log(text.slice(err.offset)); // " .\n": the error is here
  }
}
```

`line` is 1-based; `column` is 1-based and counts Unicode scalar values;
`offset` is a **UTF-16 code-unit index into the input string**, so
`text.slice(err.offset)` starts at the error even when a character outside
the Basic Multilingual Plane precedes it. RDF/XML and JSON-LD failures carry
a message only. Pass `{ baseIRI: "https://example.org/doc" }` to resolve
relative IRIs.

### Lenient parsing

`{ lenient: true }` recovers instead of rejecting
([issue 716](https://github.com/danbri/factoidal/issues/716)). The Turtle,
TriG, N-Triples and N-Quads parsers skip each bad statement and keep every
good one. `dataset.diagnostics` has one entry per skipped statement, in
document order:

```js
const text = '<http://x/a> <http://x/p> "1" .\n<http://x/b> <http://x/p> .\n' +
  '<http://x/c> <http://x/p> "3" .\n';
const ds = await parse(text, { format: "turtle", lenient: true });
console.log(ds.size);                 // 2
const [d] = ds.diagnostics;
console.log(d.line, d.column, d.class); // 2 27 unexpected-token
console.log(text.slice(d.offset));    // " .\n<http://x/c> ...": the error is here
```

Each diagnostic has `message`, `line`, `column` and `offset` (the same
conventions as `ParseError`) and a stable `class`: `undefined-prefix`,
`relative-iri`, `bad-iri`, `bad-escape`, `unterminated-string`,
`bad-literal`, `bad-blank-node`, `bad-prefixed-name`, `bad-directive`,
`bad-graph-name`, `rdf12-syntax`, `unclosed-group`, `nesting-limit`,
`unexpected-token`, `internal` or `too-many-errors`. In N-Triples and
N-Quads the parser resumes at the next line; in Turtle and TriG it resumes
after the end of the bad statement. A bad `@prefix` leaves that prefix
undefined. `{ lenient: true, maxErrors: n }` stops after `n` diagnostics and
adds one `too-many-errors` diagnostic. A document with no error gives the
strict result and no diagnostics (a theorem in the Lean source). RDF/XML and
JSON-LD parse strictly with `lenient`.

## In the browser

`browser.js` is an ES module with the same functions. On the first call it
imports `l4-assets/l4factoidal.js` and compiles `l4-assets/l4factoidal.wasm`
with `fetch()` and `WebAssembly.instantiateStreaming` (a server that does not
send `Content-Type: application/wasm` gets `WebAssembly.instantiate` over the
fetched bytes).

```html
<script type="module">
  import { parse, query } from "https://cdn.jsdelivr.net/npm/@factoidal/core@0.9.0/browser.js";
  const ds = await parse('<http://e/a> <http://e/p> "v" .', { format: "ntriples" });
  console.log(await query(ds, "SELECT * WHERE { ?s ?p ?o }"));
</script>
```

`setAssetsUrl(url)` names another directory holding the engine's three
files (`l4factoidal.js`, `l4factoidal.mjs`, `l4factoidal.wasm`); call it
before the first operation. A page under a Content-Security-Policy needs
`'wasm-unsafe-eval'` in `script-src`; nothing in the package evaluates
JavaScript source. `bundler` users: the
[`package.json`](package.json) `"browser"` condition maps
`@factoidal/core` to `browser.js`.

`tests/web-demos/npm_browser_smoke.sh` runs a parse, a SELECT, a
canonicalization, an XPath evaluation and a store query from a static page
in headless Chromium, and a second page over the core entry.

### The core engine: `@factoidal/core/core`

The full engine (`l4factoidal.wasm`) serves every function of this package.
`@factoidal/core/core` loads the core engine (`l4factoidal-core.wasm`): the
same Lean library with a dispatch table that reaches a subset of it, so the
linker drops the rest. It has the same exports and types as `@factoidal/core`
(in Node, `core.mjs`; in a browser or a bundler, its `browser` condition,
`core-browser.js`).

The core engine serves: `parse` and `serialize` for Turtle, TriG, N-Triples
and N-Quads (RDF 1.1 and 1.2) and RDF/XML, with `{lenient: true}`; `query`,
`update`, `openDataset` and `queryRaw` (SPARQL 1.1 and 1.2, extension
functions, SERVICE endpoints, the entailment regimes); `canonicalize`,
`graphs` and `canonicalHash`; `owlClosure`, `coreRdfsClosure`,
`rdfsPlusClosure` and the core-RDFS checks; `shaclValidate`. Every other
function (JSON-LD, the XML family, CSVW, RML, ShEx, the OWL DL refuter and
tableau, RIF, HDT, the store, VC and DID, the maths, Common Logic) rejects
with an error that names `@factoidal/core`, and `capabilities()` reports
`profile: 'core'` and `false` for it.

```js
import { parse, query, capabilities } from "@factoidal/core/core";
(await capabilities()).profile; // 'core'
```

Sizes (version 0.9.0 tree of 2026-10-10; gzip is `gzip -9`, brotli quality 11):

| Module | Raw | gzip | brotli |
|---|---:|---:|---:|
| `l4factoidal.wasm` (full, `@factoidal/core`) | 10.52 MB | 2.07 MB | 1.29 MB |
| `l4factoidal-core.wasm` (core, `@factoidal/core/core`) | 5.66 MB | 1.07 MB | 0.69 MB |
| the F\* engine bundle of 0.8.0 (`factoidal-npm-entry.js`), for comparison | 1.19 MB | 0.35 MB | 0.28 MB |

Each entry also loads about 68 KB (gzip) of JavaScript. The browser default
(`@factoidal/core`, `browser.js`) stays the full engine, so a page gets every
function unless it chooses the core entry. What each module is made of, by
Lean namespace: `docs/designissues/2026-10-10-npm-lean-only.md` § 9 in the
source repository.

### Bundlers and Content Security Policy

`@factoidal/core/api` builds the typed API over an engine you load
yourself, for a bundler build or a page with its own asset layout:

```js
import { createApi } from "@factoidal/core/api";
import { loadL4 } from "@factoidal/core/l4-assets/l4factoidal.js";

const factoidal = createApi(() => loadL4({
  // You decide where the wasm comes from.
  instantiateWasm: (imports) =>
    WebAssembly.instantiateStreaming(fetch("/assets/l4factoidal.wasm"), imports),
}));
const rows = await factoidal.query(ttl, "SELECT * WHERE { ?s ?p ?o }");
```

esbuild bundles this with `platform: 'browser'` when `node:module` is
marked external: the Emscripten glue imports it only when it runs under
Node. `test/bundler-esbuild.test.mjs` and
`tests/web-demos/bundler_csp_smoke.sh` (headless Chromium, CSP
`script-src 'self' 'wasm-unsafe-eval'`) are the checks.

### RDF/JS interop

```js
import { dataFactory } from "@factoidal/core";
const { namedNode, literal, quad, blankNode } = dataFactory;
const q = quad(blankNode("x"),
               namedNode("http://xmlns.com/foaf/0.1/name"),
               literal("Alice", "en"));
// Terms implement termType/value/language/datatype/.equals per the
// RDF/JS data-model spec; Dataset implements DatasetCore
// (add/delete/has/match/size/iteration).
```

## Blank nodes, labels and statement order

(Issue [683](https://github.com/danbri/factoidal/issues/683).)

- Each `parse()` call is one document. Each document's blank nodes get
  their own scope, so the same label in two documents is two nodes, also
  when `query([docA, docB], …)` merges them. On the Lean engine a label
  reads `p<k>_d<n>_<label>` (an anonymous `[ … ]` is `anon_<i>`); the text
  carries no meaning (RDF 1.1 Concepts §3.4) and may change between
  releases.
- A `Dataset`'s statement order, and the line order of `serialize()` and
  `toNQuads()`, is the engine's, not the document's. It is not part of the
  contract. Compare datasets with `canonicalize()` (isomorphism, RDF 1.1
  Concepts §3.6), not by line.

`test/parse-order.test.js` checks the three properties RDF fixes: each
`[ … ]` is its own node, the dataset is isomorphic to the labelled form of
the same graph, and two parses never share a node.

## SPARQL 1.2 queries

```js
const rows = await query(data,
  'SELECT ?s WHERE { ?who <http://e/says> <<( ?s <http://e/p> <http://e/o> )>> }',
  { sparql12: true, format: 'nquads12' });
```

`{sparql12: true}` (or `{version: '1.2'}`) reads the query with the Lean
SPARQL parser's 1.2 grammar (op `queryDataset12`; on a `DatasetHandle`,
`handle.query(q, {sparql12: true})`, op `datasetQuery12`). The data formats
`turtle12`, `ntriples12`, `nquads12` and `trig12` read RDF 1.2 terms.

## Entailment regimes

```js
await query(ttl, 'ASK { <http://e/a> a <http://e/D> }', { entail: 'RDFS' });
```

`entail` is `'none'` (default), `'RDFS'`, `'OWL-RL'`, `'x-rdfscore'` (the
core RDFS, ρdf, closure) or `'x-rdfsplus'` (RDFS-Plus: RDFS plus
`owl:sameAs`, `owl:inverseOf`, symmetric, transitive, functional and
inverse-functional properties, equivalent classes and properties). The
engine closes the default graph under the regime, then answers the query
(op `queryRaw`): SELECT, ASK, CONSTRUCT and DESCRIBE. Extension functions
and SERVICE registrations are not in scope on this path. `x-ikl-*` names are
refused ([issue 581](https://github.com/danbri/factoidal/issues/581)).

## Custom extension functions (SPARQL 1.1 §17.6)

Register your own functions by IRI (the
[Comunica model](https://comunica.dev/docs/query/advanced/extension_functions/));
sync or async both work. Built-in function families always win, and a call
to an IRI with no registered function is the error the specification
requires (unbound in SELECT/BIND position, row dropped in FILTER position).
Issue: [#463](https://github.com/danbri/factoidal/issues/463).

```js
import { query, registerExtensionFunction } from "@factoidal/core";

await registerExtensionFunction(
  "http://example.org/fn#isAdult",
  async ([age]) => Number(age.value) >= 18   // args are SRJ-style terms
);

const rows = await query(ds, `
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s WHERE { ?s <http://example.org/age> ?a
                    FILTER(fn:isAdult(?a)) }`);
```

Return a JS primitive (`boolean`/`number`/`string`), an SRJ-style term
object (`{type:'uri'|'literal'|'bnode', value, datatype?, 'xml:lang'?}`), or
a Promise of either; `null`/`undefined`/a thrown error is the §17.6 error.
Async functions run over the synchronous engine through a bounded,
memoised re-evaluation loop: within one query every call with the same
arguments sees one stable answer. The registry is the engine's, so a
registered function also reaches dataset handles and store queries. Every
call crosses into JavaScript, so a function in a FILTER runs once per row.
Design: [`docs/designissues/2026-09-04-lean-extension-functions.md`](../../docs/designissues/2026-09-04-lean-extension-functions.md).

## Dataset handles

`openDataset()` parses once and keeps the dataset indexed in the engine,
so repeated `query()`/`update()`/`serialize()` calls skip the re-parse and
the index build:

```js
import { openDataset } from "@factoidal/core";

const handle = await openDataset(`
  @prefix ex: <http://example.org/> .
  ex:alice ex:name "Alice" ; ex:knows ex:bob .
`, { format: "turtle" });

const rows = await handle.query("SELECT * WHERE { ?s ?p ?o }");
await handle.update('PREFIX ex: <http://example.org/> INSERT DATA { ex:carol ex:name "Carol" }');
const ttl = await handle.serialize({ format: "turtle" }); // uses the document's prefixes
await handle.close(); // every method rejects after this
```

`query`, `serialize` and `canonicalize` accept a handle for `data`;
`update(handle, …)` rejects with a `TypeError`, because `update()` answers a
fresh Dataset while `handle.update()` changes the handle.

## The persisted store

A **Shardborough** store is the on-disk format the Lean packer writes:
predicate-local IBK3, IBK4 or IBK5 blocks with their index sidecars, a
manifest that commits every artifact's SHA-256, and a `CURRENT` pointer to
the activated generation
([`skills/shardborough-storage`](../../skills/shardborough-storage/SKILL.md),
[`docs/shardborough-storage-spec.md`](../../docs/shardborough-storage-spec.md)).
The package carries one, the sample store (4,434 triples, IPTC NewsCodes,
CC BY 4.0; see `NOTICE`).

```js
import { openStore, queryStore, sampleStorePath } from "@factoidal/core";

const store = await openStore(sampleStorePath());   // reads CURRENT, verifies every block once
const rows = await store.query(`
  SELECT ?c ?l WHERE {
    ?c <http://www.w3.org/2004/02/skos/core#prefLabel> ?l
    FILTER(CONTAINS(LCASE(STR(?l)), "video")) } LIMIT 5`);
console.log(store.layout, store.rows);              // predicate-ibk3-…  4434
await store.close();

// One query: open only the blocks this query's plan names, query, close.
const n = await queryStore(sampleStorePath(), 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
```

`source` is a collection root path (Node), or a reader function from a
root-relative path to the file's bytes, which works in any runtime:

```js
// In a page: the store's files served under /store/.
const store = await openStore((path) => fetch("/store/" + path).then((r) => r.arrayBuffer()));
```

| `openStore(source, options)` option | effect |
|---|---|
| (none) | read every artifact the manifest declares |
| `{ sparql }` | read only the artifacts that query's plan names |
| `{ keys }` | read exactly these artifact keys |
| `{ generation }` | open that generation, not the one `CURRENT` names |

A `Store` is a store handle inside the engine (op `storeOpen`): the engine
decodes the manifest, chooses the blocks, checks each artifact's SHA-256
and indexes the rows; the JavaScript only reads the files it names. The
engine refuses a query whose plan needs a block the handle did not read, so
an answer never comes from part of a generation. `store.inspect()` answers
the decoded manifest; `listStores()` the open handles and the residency
caps (8 handles, 128 MiB of retained artifact bytes). The wasm module is
single-threaded: one query at a time.

What is not there yet: packing, activating, updating and compacting a store
from JavaScript ([issue 641](https://github.com/danbri/factoidal/issues/641));
use the native `l4block-*` tools. Large collections need a deeper call
stack than Node gives by default: see "A handle on a large store: the
worker route" below.

## The `factoidal` command

Installing this package puts a `factoidal` command on PATH. It reads a
**Shardborough** store — the on-disk format the Lean `l4block-*` tools
write — with no native binary: JavaScript reads the files and moves the
bytes, and the Lean engine running as WebAssembly makes every format
decision (parsing the manifest, choosing the blocks, verifying their
SHA-256, evaluating the SPARQL).

> This command is not the native `factoidal` binary of the repository
> (`bin/<platform>/factoidal`, which takes subcommands such as `shex` and
> `compact`). This one takes `version`, `sample-store`, `inspect`,
> `query`, `lws-serve`, `solid-serve` and `solid-client`.

### First query, with nothing else to download

The package carries an activated store, so a fresh install answers a
SPARQL query at once:

```console
$ npm install @factoidal/core
$ npx factoidal query "$(npx factoidal sample-store)" \
    'SELECT ?c ?l
     WHERE { ?c <http://www.w3.org/2004/02/skos/core#inScheme>
                <http://cv.iptc.org/newscodes/videocodec/> ;
                <http://www.w3.org/2004/02/skos/core#prefLabel> ?l .
             FILTER(langMatches(lang(?l), "en")) }
     LIMIT 4'
c                                               l
<http://cv.iptc.org/newscodes/videocodec/c001>  "Analogue Black and White"@en-gb
<http://cv.iptc.org/newscodes/videocodec/c002>  "PAL"@en-gb
<http://cv.iptc.org/newscodes/videocodec/c003>  "NTSC"@en-gb
<http://cv.iptc.org/newscodes/videocodec/c004>  "SECAM"@en-gb
```

`factoidal sample-store` prints the path; `--json` adds what was
recorded when the store was packed. From JavaScript:

```js
import { sampleStorePath, sampleStoreFacts } from '@factoidal/core/sample-store'
```

The store holds 4,434 triples in 13 predicate blocks: five IPTC
NewsCodes vocabularies, published by the IPTC under CC BY 4.0 and taken
from [danbri/skosdex](https://github.com/danbri/skosdex). See `NOTICE`.

### Any other store

```console
$ factoidal inspect ./mystore
store ./mystore
generation gen-1 (activated through CURRENT)
manifest manifest.sbm2, 2372 bytes, wire version 6
layout predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0
blank-node profile (none recorded)
term registry local-ibk3-ptd1-v0
fixed-chunk Merkle commitment yes
5 entries, 393775 bytes, 6455 rows
generation directory holds 42 files, 846592 bytes

#  rows  bytes   kind  graphs  predicate
0  1800  110085  IBK3  -       http://www.wikidata.org/prop/direct/P31
1  719   35535   IBK3  -       http://www.wikidata.org/prop/direct/P361
...

$ factoidal query ./mystore 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
mode ibk3-paged-merkle-full-manifest(5), 5 artifacts, 393775 bytes read, plan declares 6455 block rows
n
"6455"^^<http://www.w3.org/2001/XMLSchema#integer>
1 row
```

`STORE` is a collection root: the directory holding `CURRENT`. The plan
line goes to stderr, so stdout carries only the result; `--quiet`
removes it.

| Option | What it does |
|---|---|
| `--format table` | default; a human display of the results |
| `--format json` | SELECT prints the engine's SPARQL 1.1 Query Results JSON; ASK and CONSTRUCT print the operation's envelope |
| `--format nquads` | CONSTRUCT only: the graph the engine serialized |
| `--format turtle` | CONSTRUCT only: that graph through the engine's own Turtle writer |
| `--explain` | print the artifacts the query needs and the open mode, and stop |
| `--limit N` | print at most N table rows; the total is always named |
| `--file PATH` | read the query text from a file |
| `--generation NAME` | read that generation rather than the activated one |

Under Deno, run the file directly; `inspect` and `query` need only
`--allow-read`:

```console
$ deno run --allow-read node_modules/@factoidal/core/bin/factoidal.mjs query ./mystore 'ASK { ?s ?p ?o }'
```

### What the command answers for, and what it does not

* **Every artifact is verified.** The engine refuses the whole query
  when a block's bytes do not hash to the SHA-256 the manifest commits,
  and names the artifact.
* **Three caps.** One call reads at most 64 artifacts, 8388608 artifact
  bytes and 100000 rows. A query over any of them is refused before a
  single file is read, with the cap and the value named. Nothing is
  truncated.
* **Committed artifacts only.** A store carrying uncompacted delta-log
  updates is not served by this path; use the native `l4block-*` tools.
* **`pack`, `activate`, `update` and `compact` exit 3.** They need
  WebAssembly operations that do not exist yet
  (https://github.com/danbri/factoidal/issues/641).
* **Node's WebAssembly frame budget.** Some evaluator paths recurse once
  per row. Measured 2026-09-03 on a 6455-row store, `SELECT ?s ?p ?o
  WHERE { ?s ?p ?o }` overflows the stack under Node's default while
  `SELECT *`, or the same query with a `LIMIT`, does not, and Deno
  clears all of them. The command reports it and exits 1 rather than
  crashing; `node --stack-size=4000` clears it.

Measured 2026-09-03 on macOS arm64, the 6455-triple `sequence_variant`
store, `SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`, whole process
including start-up: 220 ms through this command, 33 ms through the
native `l4block-id-v3-query`.

### Holding a store open from `bin/store.mjs`

`openStore()` on the main entry (above) is a store handle. The command's
own module, `@factoidal/core/store` (`bin/store.mjs`), exposes the same
operations synchronously over an engine you loaded, which is what the
command and the worker route below use. Its `queryStore` is stateless. Every call transfers the artifacts again, and
the engine hashes, decodes and indexes them again. A process that answers
many questions against one generation — a chat bot, an MCP server, a
SPARQL endpoint — pays all of that for every question, and none of it
depends on the question.

A **store handle** holds that work. `openStoreHandle` verifies each
artifact against the SHA-256 the manifest commits, decodes each block and
indexes the rows, once. `handle.query()` then answers from what it
retained. Several stores can be open at the same time.

```js
import { loadEngine } from '@factoidal/core/bin/engine.mjs'
import { openStore, openStoreHandle, listStoreHandles } from '@factoidal/core/store'

const engine = await loadEngine()

// Two stores, open at once, held for the life of the process.
const skos = openStoreHandle(engine, openStore('./skos-store'))
const docs = openStoreHandle(engine, openStore('./docs-store'))

console.log(listStoreHandles(engine))
// { ok: true, handles: [ {handle:'s1', bytes:…, rows:…}, {handle:'s2', …} ],
//   bytes: …, rows: …, handleCap: 8, bytesCap: 134217728 }

const PREFIX = 'PREFIX skos: <http://www.w3.org/2004/02/skos/core#>'

function labelsMatching (handle, needle) {
  const answer = handle.query(`${PREFIX}
    SELECT ?c ?l WHERE {
      GRAPH ?g { ?c skos:prefLabel ?l }
      FILTER(CONTAINS(LCASE(STR(?l)), "${needle.toLowerCase()}"))
    } LIMIT 10`)
  return answer.srj.results.bindings
}

// Many questions, each a new search string. None of them re-reads a block.
for (const needle of ['water', 'forest', 'railway', 'volcano']) {
  console.log(needle, labelsMatching(skos, needle).length)
}
console.log(docs.query(`${PREFIX} SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }`))

skos.close()
docs.close()
```

`openStoreHandle(engine, store, options)` takes:

| option | effect |
|---|---|
| (none) | open every artifact the manifest declares |
| `{ sparql }` | open only the artifacts that query's plan names |
| `{ keys }` | open exactly these artifact keys |

`queryStoreHandle(engine, handle, sparql)`, `closeStoreHandle(engine,
handle)` and `listStoreHandles(engine)` are the same operations for a
caller that holds only the handle id.

**Measured 2026-09-04**, macOS arm64, Node 22, the 141-graph SKOS store,
`skos:prefLabel` block of 5,571,302 bytes and 45,806 rows, one
`CONTAINS` query per row, a DIFFERENT search string every time:

| | stateless `queryStore` | handle |
|---|---|---|
| first query (open + query) | 1376 ms | 1363 ms |
| second query, different search string | 1376 ms | 95 ms |
| tenth query, all different | 1382 ms | 103 ms |
| ten queries, total | 13962 ms | 2277 ms |

**What a handle buys.** It removes the per-query digest check, block
decode and index build. With the LGI3 or LGI4 literal index (below) a search is
also sub-linear rather than a scan, so a handle plus the index is what
makes repeated search on a large store interactive.

**Residency.** Retaining a decoded block costs memory. Measured on the
same store: 76 MiB resident with the engine loaded and no handle, 170 MiB
with the handle open — about 94 MiB for a 5.5 MB packed block, and
evaluation peaks higher again (346 MiB during the queries above). At
corpus scale the marginal figure is smaller, because that one is carrying
the fixed cost of the process: measured 2026-09-05 on a 7,315,251-quad
store, one handle over 257 blocks and 103,341,302 retained artifact bytes
peaked at 1,675,345,920 bytes resident — 16.2 bytes resident per retained
byte.

The caps are on ARTIFACT bytes, which is what the manifest declares: 8
open handles, and 134217728 (128 MiB) retained artifact bytes across all
of them. There is NO cap on the number of artifacts a handle retains; a
count bounds nothing that the bytes do not
(https://github.com/danbri/factoidal/issues/657). 128 MiB is half the
wasm32 address space divided by that measured multiplier, and it admits
the 257-block corpus-wide set above. A cap is a refusal naming the cap
and the value that tripped it; no handle is ever evicted to make room for
another. `listStoreHandles` is how a server sees its own residency.

**One call at a time.** The WebAssembly module is single-threaded. Two
`query()` calls cannot overlap; a server queues them.

### A handle on a large store: the worker route

Several engine paths recurse once per manifest entry and once per row.
Against a large collection that exceeds the default call stack of Node
and of Deno, and the failure is `Maximum call stack size exceeded`.
**Measured 2026-09-05**, macOS arm64, Node 22.22.2, on a 7,315,251-quad
collection of 3,286 blocks in 204 graphs: `storeQueryPlan` alone
overflows on plain `node`, before one artifact byte is read.
`node --stack-size=60000` clears the plan, the open and every query.

`openStoreHandleOnWorker` removes the flag. It holds the engine and the
handle on a `worker_threads` thread with `resourceLimits.stackSizeMb`,
the route `factoidal pack` already takes
([issue 649](https://github.com/danbri/factoidal/issues/649)). A handle
is state inside the wasm instance and an instance does not cross a
thread boundary, so the handle lives where the raised stack is, and
`query()` and `close()` are messages to it.

```js
import { openStoreHandleOnWorker, closeSharedStoreWorkerSession }
  from '@factoidal/core/store-worker'

// No runtime flag. One worker thread, shared by every handle opened
// this way, so a caller that opens several stores pays for one thread
// and one copy of the module.
const handle = await openStoreHandleOnWorker('/path/to/store', {
  sparql: 'SELECT ?c ?l WHERE { GRAPH <urn:g> { ?c ?p ?l } }'
})
const answer = await handle.query(`${PREFIX}
  SELECT ?c ?l WHERE { GRAPH <urn:g> { ?c skos:prefLabel ?l }
    FILTER(CONTAINS(LCASE(STR(?l)), "volcan")) } LIMIT 8`)
await handle.close()
await closeSharedStoreWorkerSession()
```

| option | effect |
|---|---|
| `{sparql}`, `{keys}` | the same artifact choice `openStoreHandle` takes |
| `{generation}` | open a generation that has not been activated |
| `{session}` | open into a session you started with `openStoreWorkerSession()` |
| `{ownWorker: true}` | give this handle its own thread and its own copy of the module |
| `{worker: false}` | open in this process, with no thread |

What it costs, all **measured 2026-09-05** on the same machine, against
the bundled sample store so the overhead is not lost in the query:

| | in process | on a worker |
|---|---|---|
| one-shot query (thread start + engine load + query) | 163 ms | 220 ms |
| handle open (thread start + engine load + open) | 124 ms | 236 ms |
| every query after the open | 1 ms | 1 ms |

So the thread and its second copy of the engine cost about 110 ms once,
and the message round trip is under a millisecond. Three further costs:
every call is asynchronous where the in-process handle is synchronous;
an extension function registered on the main thread's engine
(`bin/ext.mjs`) is not visible to the worker's engine; and the worker
keeps the process alive until `close()`.

**Deno takes a different route.** Deno's `node:worker_threads` shim
accepts `resourceLimits.stackSizeMb` and raises almost nothing with it —
measured by counting frames to the overflow inside the worker, Node
reaches 41,195 frames by default and 696,555 at `stackSizeMb` 64, where
Deno reaches 10,835 and 13,837. `openStoreHandleOnWorker` therefore
gives a Deno caller an in-process handle behind the same asynchronous
interface, and the process supplies the stack:

```
deno run --allow-read --v8-flags=--stack-size=65536 your-program.mjs
```

**A one-shot `factoidal query` pays none of this.** It builds no handle,
so it runs in process and only retries on a worker if the runtime runs
out of frames; under Deno it re-executes itself once with a raised V8
stack, which needs `--allow-run` and `--allow-env`. `--no-worker` turns
the retry off. See
[issue 653](https://github.com/danbri/factoidal/issues/653).

## Searching a store

### GeoSPARQL — six topological functions

The `geof:` functions below are built into the SPARQL engine and need no
import. They work through `query()` / `fn.query()` AND against a
persisted store through `factoidal query`, because both paths evaluate
in the same environment.

    geof:sfEquals   geof:sfDisjoint   geof:sfIntersects
    geof:sfTouches  geof:sfWithin     geof:sfContains

```sparql
PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
PREFIX geo:  <http://www.opengis.net/ont/geosparql#>
SELECT ?a WHERE {
  ?a :footprint ?w
  FILTER(geof:sfWithin(?w, "POLYGON((0 0,0 2,2 2,2 0,0 0))"^^geo:wktLiteral))
}
```

**What is NOT there**, stated so nobody plans around it: no
`geof:distance`, `geof:buffer`, `geof:envelope`, `geof:boundary`,
`geof:convexHull` or any other non-topological measure; no
`geof:relate` with a DE-9IM matrix; no coordinate reference system
handling beyond what the WKT literal carries; no GML literals. Geometry
comes from a WKT parser, so a shapefile, GeoJSON or GML source must be
converted to `geo:wktLiteral` before it is loaded.

### Full text: SPARQL's own functions, over a character-gram index

`CONTAINS`, `STRSTARTS`, `STRENDS` and `REGEX` (SPARQL 1.1 §17.4.3) are
the way to search text. There is no `text:query`-style extension and you
do not ask for the index: where the query shape allows it, the planner
uses the **LGI3** or **LGI4** literal index the packer writes beside each block
(LGI3 beside an IBK4 block, LGI4 beside an IBK5 block; they were named LGI1 and
LGI2 until 2026-10-10).

The index holds character 3-grams of the case-folded lexical form, folded with
the Unicode case mapping that `LCASE` uses, so `CONTAINS(LCASE(?x), "école")`
finds `École Normale` through the index. It is a
CANDIDATE FILTER rather than a decider — it answers a superset and the
engine re-evaluates your original `FILTER` on those rows, so the answer
is exactly the answer a scan gives. Tokens would not do: `CONTAINS` is a
substring test, and "underwater" contains "water" without being the
token "water".

Measured 2026-09-05, full skosdex corpus (7,315,251 quads, 3,286 blocks,
204 named graphs, 1.0 GB), through a store handle on plain `node`:

| search | rows | time |
|---|---|---|
| `water` | 5 | 645 ms |
| `glacier` | 0 | 670 ms |
| `bicycle` | 2 | 617 ms |

A miss costs what a hit costs, because both are index lookups rather than
scans. On a 45,806-row block the same search was about 180 ms of scan
before the index and 1.8 ms after it.

**It falls back to a scan**, silently and correctly, for: a needle under
3 characters, a variable needle, `REGEX`, `UCASE`, `!CONTAINS`,
`CONTAINS` under `||`, a filter on a variable not bound in object
position, and any block whose generation has no literal-index sidecar. A
generation packed before 2026-10-10 names LGI1 or LGI2, which were folded with
the ASCII-only fold and miss rows the Unicode `LCASE` keeps: the engine refuses
it, says so, and asks for a re-pack. The
index costs about 55% of the block bytes.

### Geometry: the GBI1 bounding-box index

The same construction for `geof:`. Each `geo:wktLiteral` object's
bounding box is indexed, and five of the six topological functions are
filtered by it — `sfIntersects`, `sfWithin`, `sfContains`, `sfTouches`,
`sfEquals`. Measured 74x to 94x against a scan, with a miss at 82x.

**`sfDisjoint` is refused and falls back to a scan**, deliberately: it
accepts exactly the rows a box can exclude, so a box test inverts and
would drop answers. A non-overlapping pair of boxes proves geometries
disjoint, but that saves work inside a scan rather than reducing the
candidate set.

### Wire version 10: large literals, RDF 1.2 terms, zone maps

A generation packed at wire version 10 (`--layout ibk5`) carries three
things earlier versions do not. Everything below is read by the command
and by `bin/store.mjs` without a flag; wire versions 9 and earlier are
read exactly as before.

**Out-of-line literals.** A literal whose lexical form is at most 65,536
UTF-8 bytes is stored inside the block. A longer one is stored as one
file beside it, `blob-<sha256 hex>.lit`, holding exactly those bytes; the
block keeps only the byte length and the SHA-256, and the manifest blob
table commits the file. The name is the content address, so the same
literal in twenty blocks is one file. `factoidal inspect` prints how many
such files a generation holds and their total size, and the plan a query
produces lists them under `blobKeys` beside `keys` and `sidecarKeys` — a
host reading a store itself must fetch all three. A blob that is missing
or whose bytes hash differently REFUSES the query; it is never answered
with a shortened literal.

Above 4,294,967,295 bytes the packer refuses the literal and names its
subject and predicate. That ceiling, and every other one, is stated in
`docs/designissues/2026-09-05-wire-version-10-scale.md` section 2.

**RDF 1.2 terms.** A triple term (`<<( :a :p :b )>>`) and a directional
language literal (`"..."@ar--rtl`) are stored and read back. Wire version
9 refuses both.

**Zone maps.** Each manifest entry carries the smallest and the largest
subject key and object key of its block, truncated to 64 bytes. A query
with a constant subject or object skips every block whose range cannot
hold it, from the manifest alone, with no block read. The plan reports
how many entries were dropped that way as `zoneExcluded`. Selectivity
depends on the source order: a subject-grouped or graph-grouped file
gives disjoint ranges per block, a shuffled one gives overlapping ranges
and a scan, which is correct and no worse than wire version 9.


## Linked Web Storage 1.0 and the Solid Protocol

Three new entry points serve two storage protocols over HTTP. Each is a
socket and nothing more: every protocol decision — status codes, `Link`
relations, `Last-Modified`, containment triples, the PATCH blank-node
refusal, Web Access Control, CORS — is made by the Lean engine and
reaches the host as a `{status, headers, body}` record.

| entry point | what it serves |
| --- | --- |
| `@factoidal/core/lws` | [Linked Web Storage 1.0 core](https://w3c.github.io/lws-protocol/lws10-core/), a Node `http` server |
| `@factoidal/core/solid/server` | [Solid Protocol v0.11.0](https://solidproject.org/TR/protocol) server conformance class |
| `@factoidal/core/solid/client` | Solid Protocol client conformance class, over `fetch` |

```js
import { listen } from '@factoidal/core/solid/server'
import { createSolidClient } from '@factoidal/core/solid/client'

const running = await listen({ port: 3000 })
const client = await createSolidClient({ baseIri: running.origin })
await client.replace('/notes/one', '<#it> <#p> "v" .', 'text/turtle')
const read = await client.read('/notes/one')
await running.close()
```

From the command:

```
factoidal lws-serve   DIR [--port N] [--base IRI]
factoidal solid-serve DIR [--port N] [--base IRI] [--owner WEBID]
factoidal solid-client <get|put|post|delete|discover> URL [--file PATH]
```

**State today.** The protocol operations live in the Lean engine and
reach this package through the WebAssembly dispatch ABI
(`lwsOpen`/`lwsStep`/`lwsClose`, `solidOpen`/`solidStep`/`solidClose`,
`solidClientRequest`/`solidClientResponse`). A module built before those
operations landed answers `unknown op`; each entry point reports that
through its `…OpsAvailable(engine)` probe and the commands exit 3 with
the reason. `DIR` is the storage directory and is not read or written
yet: the first slice keeps the resource tree in the engine handle.
Solid-OIDC token verification is a host job that is not built, so the
first slice serves public resources and unauthenticated writes.

Details: `lws/README.md`, `solid/server/README.md`,
`solid/client/README.md`, and the conformance ledger at
[`docs/lws-solid-conformance.md`](https://github.com/danbri/factoidal/blob/main/docs/lws-solid-conformance.md).


## Functional API (fn)

`@factoidal/core/fn` is a functional variant of the API above. `FnDataset`
is a frozen snapshot; operations are free functions that return new values;
RDFC-1.0 canonical hashes are a memoized identity, which is what lets a
dataflow graph skip recomputation. Design:
[`docs/designissues/2026-07-05-functional-dataset-api.md`](../../docs/designissues/2026-07-05-functional-dataset-api.md).

```js
const { parse, filter, hash, cell, derive, validate, shex } = require('@factoidal/core/fn');

const ds = await parse(`
  @prefix foaf: <http://xmlns.com/foaf/0.1/> .
  _:a foaf:name "Alice" ; a foaf:Person .
  _:b foaf:name "Bob".
`);
const people = filter(ds, (q) => q.predicate.value.endsWith('/type'));
const source = cell(ds);
const names = derive((d) => filter(d, (q) => q.predicate.value.endsWith('name')), source);
await names.get();             // computes; recomputes only when the content hash changes
await hash(ds);                // sha256 hex of the RDFC-1.0 canonical N-Quads
const { conforms, report } = await validate(ds, await parse(shapesTtl)); // SHACL
```

`fromDataset`/`toDataset` convert to and from the RDF/JS `Dataset`.
`union`/`difference`/`filter`/`mapQuads` are set algebra;
`query`/`entail`/`canonicalize`/`graphs`/`validate`/`shex`/`fromMapping`/
`fromCsvw`/`rif` wrap the functions of the main entry.

## API

| Function | Signature (informal) | Notes |
|---|---|---|
| `parse` | `(text, {format?, baseIRI?}) => Dataset` | `turtle`, `ntriples`, `nquads`, `trig`, `rdfxml`, `jsonld`, and `turtle12`, `ntriples12`, `nquads12`, `trig12`. One call is one document. Strict: a syntax error rejects with `ParseError`. `dataset.prefixes` is the declared map |
| `query` | `(data, sparql, {format?, entail?, sparql12?}) => Bindings[] \| boolean \| Dataset` | SELECT → `Map<var, Term>[]`; ASK → boolean; CONSTRUCT and DESCRIBE → Dataset. `data` is a Dataset, a string, `{text, format}`, an array of those, or a `DatasetHandle` |
| `update` | `(data, sparqlUpdate) => Dataset` | in memory; answers a fresh Dataset |
| `openDataset` | `(data, {format?, baseIRI?}) => DatasetHandle` | parse and index once (above) |
| `serialize` | `(data, {format, prefixes?, literalShorthand?}) => string` | `nquads`, `ntriples` (refuses a named graph), `turtle` (prefix-compacted, subject-grouped; named graphs flattened). `literalShorthand` (default `true`) prints numeric and boolean literals bare |
| `canonicalize` | `(data) => string` | RDFC-1.0 canonical N-Quads |
| `graphs` | `(Dataset) => Array<[iri, Dataset]>` | named graphs, default graph excluded; no engine call |
| `canonicalHash` | `(Dataset) => string` | RDFC-1.0 canonical N-Quads of one graph |
| `queryRaw` | `(dataText, sparql, {dataFormat?, entail?, output?}) => object \| string` | one call, serialized answer: `json` (parsed), `csv`, `tsv`, `xml`, `table`, `ntriples` |
| `queryHdt` | `(hdtBytes, sparql) => Bindings[] \| boolean` | SELECT/ASK over an HDT file's bytes |
| `openStore`, `queryStore`, `listStores` | see "The persisted store" | `Store`: `.query`, `.inspect`, `.close`, `.handle`/`.layout`/`.wireVersion`/`.rows`/`.bytes`/`.artifacts`/`.generation`/`.activated`/`.closed` |
| `sampleStorePath`, `sampleStoreFacts` | `() => string`, object | Node only |
| `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions` | see above | SPARQL 1.1 §17.6 |
| `registerServiceEndpoint`, `clearServiceEndpoints` | `(iri, data)` | `SERVICE <iri>` answers from this snapshot |
| `shaclValidate` | `(data, shapes) => {conforms, report: Dataset}` | SHACL Core, SHACL-SPARQL, SHACL 1.2 node expressions |
| `shexValidate` | `(data, schemaText, focus, shape?) => boolean` | ShExJ when the text starts with `{`, else ShExC; no `shape` = the schema's START |
| `owlClosure` | `(data, 'RDFS' \| 'OWL-RL') => Dataset` | input + derived triples, default graph |
| `coreRdfsClosure`/`rhoDfClosure`, `coreRdfsCheck`/`rhoDfFragmentCheck`, `rdfsPlusClosure` | `(data) => {ok, ntriples, …}` | ρdf closure, fragment check, RDFS-Plus closure |
| `tableauMaterialise` | `(data) => {dataset, addedCount, budgetHit}` | class-expression memberships; `budgetHit` true when the work budget ran out |
| `tableauDlInconsistent` | `(data) => {inconsistent, rlAlone}` | OWL DL clash after RL closure + materialisation |
| `owlIsConsistent`, `owlEntails` | `(data, {fuel?})`, `(premise, conclusion, {fuel?})` | three-valued: `true`, `false`, `null` (budget out, with `reason`) |
| `rmlMap` | `(mapping, sourceText, 'json' \| 'csv') => Dataset` | one logical source |
| `csvwToRdf` | `(csvText, metadataJson?, {mode?, base?, url?}) => Dataset` | CSV on the Web csv2rdf |
| `jsonldToRdf`, `jsonldFromRdf` | | JSON-LD 1.1 to and from RDF; a remote `@context` is not fetched |
| `rifEval` | `(data, rifXml) => Dataset` | RIF Core forward chaining |
| `xmlWellformed`, `xpathEval`, `xsltTransform`, `schematronValidate`, `jsonSchemaValidate`, `xformsRecalc`, `mathmlEval` | | XML 1.0, XPath 1.0, XSLT 1.0, Schematron, JSON Schema draft-07, XForms recalculation, Content MathML |
| `clParse`, `clSerialize`, `clAlphaNorm`, `clNormalize` | `(clifText) => {…}` | Common Logic (ISO/IEC 24707) and IKL; `clSerialize` reports `roundTripProved: false`, `clNormalize` reports `preserves: "satisfiability"` |
| `toanSummation`, `toanProduct`, `toanSimplify`, `toanDiff`, `toanSubst` | | symbolic algebra over Content MathML |
| `matrixDeterminant`, `matrixScalarProduct`, `matrixVectorProduct`, `matrixOuterProduct`, `sigmoidPoints`, `sigmoidFormulaMathml` | | exact rational matrices; sigmoid samples |
| `vcSha256Hex`, `vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical` | | VC Data Integrity `eddsa-rdfc-2022`; Ed25519 is HACL\*'s C code in the wasm module; no initialisation step |
| `vcCheckCredential`, `vcCheckCredentialSubject`, `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests`, `didKeyResolve` | | VCDM 2.0 checks; `did:key` (Ed25519) resolution |
| `capabilities` | `() => {…}` | which ops the loaded wasm serves |
| `loadEngine` | `() => engine` | the low-level handle, `call(op, args)`, for ops this layer does not wrap |
| `Dataset`, `DatasetHandle`, `Store`, `ParseError`, `dataFactory`, `version`, `engine` | | `engine` is `'lean4-wasm'` |

`./l4` and `./l4-core` are aliases of the main entry in 0.9.x and go in
0.10.0.

## Behaviour that differs from 0.8 (the F\* engine)

From the parity runs of issue 713
([design record](../../docs/designissues/2026-10-10-npm-lean-only.md),
section 6). No answer below was found wrong against a specification on
either engine; where one engine did less, the row says so.

- `ParseError.offset` is a UTF-16 index (0.8: UTF-8 bytes).
- DESCRIBE answers the Concise Bounded Description (0.8: the empty graph,
  [issue 702](https://github.com/danbri/factoidal/issues/702)).
- `shexValidate` answers a boolean (0.8: `null` outside its decidable
  fragment).
- `xmlWellformed` reads a DOCTYPE with an internal subset (0.8: `false` for
  any DOCTYPE).
- `xpathEval` is the full XPath 1.0 evaluator; node kinds include `root` and
  `namespace`; a non-finite number reads `Infinity` or `NaN`.
- `mathmlEval` evaluates `vector` and `matrix` too; an `undef` result has one
  fixed `reason` text.
- `rmlMap` reads the iteration format from the mapping's
  `rml:referenceFormulation` (RML Core); `sourceKind` is checked.
- `rifEval` has no `rounds` or `engineMs` members.
- `tableauMaterialise` adds `budgetHit`.
- `queryRaw` writes `table` and `ntriples` with N-Triples term syntax; CSV
  and TSV have no ASK encoding, so an ASK with those outputs is an error.
- Blank-node label text and N-Quads line order differ (see "Blank nodes,
  labels and statement order").

## Open shortfalls

Each has an open issue and an expected-failure test in `test/`:

- A failed `SERVICE` call without `SILENT` inside `EXISTS` does not fail the
  query, and an outer `SERVICE SILENT` does not cover a failed nested
  `SERVICE` (SPARQL 1.1 Federated Query §2.3, §3.2;
  [issue 735](https://github.com/danbri/factoidal/issues/735)). A failed
  call elsewhere fails the query (issue 717, fixed).
- Turtle output with literal shorthand on keeps an `@prefix xsd:` line when
  no printed term uses it
  ([issue 691](https://github.com/danbri/factoidal/issues/691)).
- `xmpp` `parseJid` does not apply the PRECIS profiles of RFC 8265 to a
  localpart: it accepts a disallowed code point and does not normalize to
  NFC ([issue 676](https://github.com/danbri/factoidal/issues/676)).

## Sizes

Measured on 2026-10-10 for 0.9.0 (the wasm that `Wasm/build-wasm.sh` built
from danbri/factoidal-core; `gzip -9` of each file):

| File | Raw | gzip -9 |
|---|---|---|
| `l4-assets/l4factoidal.wasm` (the whole Lean library) | 10,402,990 bytes | 2,042,240 bytes |
| `l4-assets/l4factoidal.mjs` (Emscripten glue) | 64,391 bytes | 18,307 bytes |
| `l4-assets/l4factoidal.js` (loader) | 13,460 bytes | 4,853 bytes |
| `lib/api.mjs` (the wrappers) | 111,836 bytes | 30,042 bytes |
| every JavaScript file `browser.js` loads, together | 230,293 bytes | 67,446 bytes |
| the tarball (`npm pack`, 161 files) | 12,042,704 bytes unpacked | 2,410,574 bytes |

A browser page that loads `browser.js` transfers about 2.1 MB with gzip, of
which 2.04 MB is the wasm. One dispatch table reaches the whole library, so
the linker removes no Lean module; a smaller wasm for the browser is stage 4
of [issue 713](https://github.com/danbri/factoidal/issues/713).

## Testing

- `npm test`: the package suite, against the wasm in `l4-assets/`. A
  function the wasm does not serve fails; it is not skipped.
- `tests/web-demos/npm_browser_smoke.sh` and
  `tests/web-demos/bundler_csp_smoke.sh`: `browser.js`, and an esbuild
  bundle under a strict Content-Security-Policy, in headless Chromium.
- `tests/engine-compare/run.sh PATH/TO/factoidal-npm-entry.js`: the same
  inputs through this package and through an F\* engine build (a
  factoidal-builds artifact). Exit 2 when the bundle is absent.
- The Lean library is gated on every landing by `lake build` (its
  `#guard` cases), `formal/lean4/Wasm/native-smoke.sh` and the W3C suites.

## Provenance & license

Built from [danbri/factoidal-core](https://github.com/danbri/factoidal-core)
(Apache-2.0). This package's JavaScript is a consumer layer (argument
shaping, RDF/JS conversion, file reading for the store) with no RDF or
SPARQL semantics of its own. `l4-assets/version.json` records the git
commit, toolchain and wasm digest of the engine build.
