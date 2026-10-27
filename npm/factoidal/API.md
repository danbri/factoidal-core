# @factoidal/core: API reference

This file was the package README until 0.10.0. The README is now a short
summary; this file keeps the full API description. It is not in the npm
tarball.

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

// Parse any supported syntax into a Dataset; its quads stay in the engine.
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
const xml = ds.toString("rdfxml");                      // RDF/XML, synchronous
ds.dispose();                                           // release the engine copy
```

CommonJS: `const factoidal = require("@factoidal/core")`. It is the same
module instance as the ES import, so `instanceof Dataset` holds across both.

### Parsing is strict

A syntax error, an undeclared prefix, or a relative IRI with no `baseIRI`
in effect rejects the whole parse with a `FactoidalError` (see "Errors"
below):

```js
import { parse, FactoidalError } from "@factoidal/core";

const text = '<http://x/s> <http://x/p> "😀" .\nBOGUS .\n';
try {
  await parse(text, { format: "ntriples" });
} catch (err) {
  if (err instanceof FactoidalError) {
    console.log(err.code);                        // parse.syntax
    console.log(err.position.line, err.position.column); // 2 6
    console.log(text.slice(err.position.offset)); // " .\n": the error is here
    console.log(err.spec); // https://www.w3.org/TR/rdf12-n-triples/#n-triples-grammar
  }
}
```

`line` is 1-based; `column` is 1-based and counts Unicode scalar values;
`offset` is a **UTF-16 code-unit index into the input string**, so
`text.slice(err.position.offset)` starts at the error even when a character
outside the Basic Multilingual Plane precedes it; `byteOffset` is the same
position in UTF-8 bytes. RDF/XML and JSON-LD failures have `position: null`.
Pass `{ baseIRI: "https://example.org/doc" }` to resolve
relative IRIs.

### Errors

Every function rejects (or throws) with `FactoidalError`. A `TypeError` is
thrown only when an argument has the wrong JavaScript type. The engine
decides the fields (`formal/lean4/Wasm/Ops/ErrorModel.lean`); the
JavaScript copies them:

| field | value |
|---|---|
| `code` | a stable code; the table is in README "Errors" and in `engineTables().errorCodes` |
| `position` | `{line, column, offset, byteOffset}` for a parse, query or update error, else `null` |
| `spec` | the URL of the specification section of the condition, or `null` |
| `cause` | the underlying error of a `host.io` failure |
| `format`, `formatInferred` | for a parse failure of text: the syntax read, and whether it was inferred |

The message is the engine's text. A query or an update that does not parse
has a `position` into the query text. A method of a disposed `Dataset`
rejects with `handle.disposed`.

### Lenient parsing

`{ lenient: true }` recovers instead of rejecting
([issue 716](https://github.com/danbri/factoidal/issues/716)). The Turtle,
TriG, N-Triples and N-Quads parsers skip each bad statement and keep every
good one. `dataset.diagnostics` has one entry per skipped statement, in
document order:

```js
import { parse } from "@factoidal/core";

const text = '<http://x/a> <http://x/p> "1" .\n<http://x/b> <http://x/p> .\n' +
  '<http://x/c> <http://x/p> "3" .\n';
const ds = await parse(text, { format: "turtle", lenient: true });
console.log(ds.size);                 // 2
const [d] = ds.diagnostics;
console.log(d.line, d.column, d.class); // 2 27 unexpected-token
console.log(text.slice(d.offset));    // " .\n<http://x/c> ...": the error is here
```

Each diagnostic has `message`, `line`, `column` and `offset` (the same
conventions as `FactoidalError.position`) and a stable `class`: `undefined-prefix`,
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

### Language tags that are not well-formed

RDF 1.2 Concepts section 3.4 requires a language tag that is well-formed per
BCP 47 section 2.2.9. A reader that meets a tag which its grammar reads and
which is not well-formed keeps the triple and adds one entry to
`dataset.warnings` (class `ill-formed-language-tag`; `line`, `column` and
`offset` of the tag's first character). The writers write the tag unchanged.
Owner decision of 2026-10-24
([issue 1004](https://github.com/danbri/factoidal/issues/1004),
[issue 1005](https://github.com/danbri/factoidal/issues/1005)). The RDF 1.2
readers still refuse a subtag of more than 8 characters, as the W3C test
`ntriples-langdir-bad-4` requires; read such a document as RDF 1.1.

```js
import { parse } from "@factoidal/core";

const ds = await parse('<http://x/s> <http://x/p> "v"@abcdefghijk .\n', { format: "ntriples" });
console.log(ds.warnings[0].class);   // ill-formed-language-tag
console.log(ds.toString("ntriples")); // ... "v"@abcdefghijk .
```

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
in headless Chromium.

### One engine

One wasm, `l4factoidal.wasm`, carries every capability of the package
(owner, 2026-10-20: "all this stuff goes into a single mod we call
Factoidal/core and a dingle wasm"). The duplicate smaller wasm and its
`./core` and `./core-browser` subpaths are gone since 0.10.0.

### Bundlers and Content Security Policy

`@factoidal/core/api` builds the typed API over an engine you load
yourself, for a bundler build or a page with its own asset layout:

```js browser
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
// RDF/JS data-model spec. A Dataset implements RDF/JS DatasetCore (size,
// add, delete, has, match, iteration) in the engine; an in-memory
// DatasetCore is in "@factoidal/core/rdfjs".
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
import { query } from "@factoidal/core";

const data = '<http://e/w> <http://e/says> <<( <http://e/a> <http://e/p> <http://e/o> )>> .\n';
const rows = await query(data,
  'SELECT ?s WHERE { ?who <http://e/says> <<( ?s <http://e/p> <http://e/o> )>> }',
  { sparql12: true, format: 'nquads12' });
console.log(rows[0].get("s").value); // http://e/a
```

`{sparql12: true}` (or `{version: '1.2'}`) reads the query with the Lean
SPARQL parser's 1.2 grammar (op `datasetQuery12`; also
`dataset.query(q, {sparql12: true})`). The data formats
`turtle12`, `ntriples12`, `nquads12` and `trig12` read RDF 1.2 terms.

## Entailment regimes

```js
import { query } from "@factoidal/core";

const ttl = '<http://e/a> a <http://e/C> . <http://e/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/D> .';
await query(ttl, 'ASK { <http://e/a> a <http://e/D> }', { entail: 'RDFS', format: 'turtle' }); // true
```

`entail` is `'none'` (default), `'RDFS'`, `'OWL-RL'`, `'x-rdfscore'` (the
core RDFS, ρdf, closure) or `'x-rdfsplus'` (RDFS-Plus: RDFS plus
`owl:sameAs`, `owl:inverseOf`, symmetric, transitive, functional and
inverse-functional properties, equivalent classes and properties). The
engine closes the default graph under the regime, then answers the query
(op `datasetQueryRaw`): SELECT, ASK, CONSTRUCT and DESCRIBE. Extension functions
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
import { parse, query, registerExtensionFunction } from "@factoidal/core";

const ds = await parse('<http://e/x> <http://example.org/age> 20 .', { format: "turtle" });

await registerExtensionFunction(
  "http://example.org/fn#isAdult",
  async ([age]) => Number(age.value) >= 18   // args are SRJ-style terms
);

const rows = await query(ds, `
  PREFIX fn: <http://example.org/fn#>
  SELECT ?s WHERE { ?s <http://example.org/age> ?a
                    FILTER(fn:isAdult(?a)) }`);
```

Return one of these, or a Promise of one; `null`/`undefined`/a thrown error
is the §17.6 error:

- A JS primitive (`boolean`/`number`/`bigint`/`string`). The engine chooses
  the datatype and the lexical form (`L4Factoidal.XSD.JsValue.jsLiteral`):
  `7` is `"7"^^xsd:integer`, `1e21` is `"1.0E21"^^xsd:double`, a string is an
  `xsd:string` literal (`'_:x'` too: it is never a blank node).
- An exact term, when the application chooses the datatype IRI and the
  lexical form. The engine keeps both as given and does not canonicalise
  (RDF 1.1 Concepts §3.3: an ill-typed literal is still a literal):
  - an RDF/JS term, duck-typed on `termType`: `Literal` (`value` and
    `datatype`, or `language` and optional `direction`), `NamedNode`,
    `BlankNode`, or a `Quad` (an RDF 1.2 triple term);
  - a plain object `{value, datatype}` (`datatype` an IRI string or a
    NamedNode) or `{value, language, direction?}`;
  - an engine term object (`{type:'uri'|'literal'|'bnode'|'triple', value,
    datatype?, 'xml:lang'?, 'its:dir'?}`).

  JavaScript only copies the components. The engine checks what RDF
  requires and nothing more: every IRI (datatype IRIs too) is absolute, a
  language tag is well-formed BCP 47, a direction is `ltr` or `rtl`, and a
  `datatype` given with a language tag is `rdf:langString` (no direction) or
  `rdf:dirLangString`. A term that fails a check is the §17.6 error for that
  call.

```js
import { registerExtensionFunction } from "@factoidal/core";
await registerExtensionFunction("http://example.org/fn#pad", () =>
  ({ value: "007", datatype: "http://www.w3.org/2001/XMLSchema#integer" }));
// BIND(fn:pad() AS ?x) binds ?x to "007"^^xsd:integer, not "7"
```

There is no registration option for a number policy: an application that
wants a different datatype or lexical form for a number returns the exact
term.
Async functions run over the synchronous engine through a bounded,
memoised re-evaluation loop: within one query every call with the same
arguments sees one stable answer. The registry is the engine's, so a
registered function also reaches dataset handles and store queries. Every
call crosses into JavaScript, so a function in a FILTER runs once per row.
Design: [`docs/designissues/2026-09-04-lean-extension-functions.md`](../../docs/designissues/2026-09-04-lean-extension-functions.md).

## Terms given as strings

Every API that takes an RDF term as a string reads it as one RDF 1.2
N-Triples term, with the engine's one term-string reader
(`L4Factoidal.RDF.TermJson.readTermString`): `<http://e/x>` is an IRI,
`_:x` a blank node, `"7"^^<http://www.w3.org/2001/XMLSchema#integer>` a
literal, `<<( <s> <p> <o> )>>` a triple term. The IRI must be absolute. A
string that is not one such term is an error. This holds for `Dataset.match`
and `has` (each position takes a term or a string), the ShEx `focus` and
`shape`, and the engine ops that take term objects (`{type:'nt', value}`).

Breaking changes in 0.10.0:

- `shexValidate` / `Dataset.validateShex`: `focus` and `shape` strings are
  N-Triples terms. Write `'<http://example.org/alice>'`, not
  `'http://example.org/alice'`; an RDF/JS term still works.
- `graphs(dataset)` answers `[name, Dataset]` pairs where `name` is a
  `NamedNode` or a `BlankNode`. It answered the bare `value` string, so the
  graph IRI `urn:g` and an RDF/JS blank node with the label `urn:g` gave the
  same string.

## Datasets

A `Dataset` is a handle into the engine: its quads are parsed and indexed
once and stay in the wasm memory. Every producer (`parse`, `openDataset`,
`csvwToRdf`, `rmlMap`, `jsonldToRdf`, `closure` and the closure functions,
`rifEval`, CONSTRUCT and DESCRIBE) answers one, and every consumer takes
one, so a pipeline moves no N-Quads text between its steps
(https://github.com/danbri/factoidal/issues/882).

```js
import { parse, csvwToRdf, closure } from "@factoidal/core";

const ds = await parse(`
  @prefix ex: <http://example.org/> .
  ex:alice ex:name "Alice" ; ex:knows ex:bob .
`, { format: "turtle" });

const rows = await ds.query("SELECT * WHERE { ?s ?p ?o }");
await ds.update('PREFIX ex: <http://example.org/> INSERT DATA { ex:carol ex:name "Carol" }');
console.log(ds.size);                                   // 3
const ttl = await ds.serialize({ format: "turtle" });   // uses the document's prefixes
const trig = ds.toString("trig");
const csv = await ds.query("SELECT ?s WHERE { ?s ?p ?o }", { output: "csv" });
for (const q of ds) console.log(q.subject.value);       // RDF/JS quads, read lazily
const copy = ds.clone();                                // independent of ds
ds.dispose();                                           // every method throws after this

const table = await csvwToRdf("id,name\n1,a\n", "", { mode: "minimal", url: "http://x/t.csv" });
const inferred = await closure(table, "rdfs");          // a new Dataset
console.log(inferred.size >= table.size);               // true
for (const d of [copy, table, inferred]) d.dispose();
```

Methods: `query(sparql, {sparql12?, version?, entail?, output?})`,
`update(text)` (in place; answers the Dataset), `validateShacl(shapes,
{format?, baseIRI?})`, `validateShex(schema, {focus, shape?})`,
`closure('rdfs' | 'owl-rl' | 'rho-df' | 'rdfs-plus')`, `canonicalize()`,
`serialize({format, version?, prefixes?, literalShorthand?,
useNativeTypes?, useRdfType?, rdfDirection?, rdfstar?})`, `toString(format)`
(synchronous), `toNQuads()`, `clone()`, `has(quad, {match?})`,
`match(s, p, o, g, {match?})` (a new Dataset), `add(quad)`, `delete(quad,
{match?})` (`match: 'value'` compares a literal object by value, see "Matching
literals by value"), `listItems(head, graph?)`, `containerItems(node,
graph?)`, `addList(items, graph?)` (see "RDF lists and containers"),
`toArray()`, iteration, `size`, `prefixes`,
`diagnostics`, `warnings`, `format`, `formatInferred`, `dispose()` and
`[Symbol.dispose]` (for `using` where the runtime has it). A Dataset that is
garbage collected without `dispose()` is released by a
`FinalizationRegistry`.

`serialize` formats: `nquads`, `ntriples` (refuses a named graph), `turtle`,
`trig`, `rdfxml`, `jsonld`, `rdfc` (RDFC-1.0 canonical N-Quads);
`version: '1.1'` refuses a dataset with an RDF 1.2 term. `formats()` gives
the engine's list with read and write support per RDF version. The functional
`update(data, text)` answers a NEW Dataset and leaves a Dataset argument
unchanged. Text input takes `{format}`; with no format the engine infers one
and reports it. An unknown option key rejects with a `FactoidalError` of
code `option.unknown`; the engine checks the keys (op `apiCheck`).

Query warnings. A SELECT answer can carry a non-enumerable `warnings`
array. A `FROM` or `FROM NAMED` IRI that names no graph of the dataset gives
a warning of class `dataset-iri-not-found` with `class`, `clause` (`FROM` or
`FROM NAMED`), `iri` and `message`. The rows do not change: the clause adds
no graph. The native `l4factoidal query` command writes the same warning to
standard error (https://github.com/danbri/factoidal/issues/1032, FROM IRI
that names no graph). This needs a wasm module built after 0.15.0; with the
0.15.0 wasm the answer has no `warnings` property.

```js
import { parse } from '@factoidal/core';
const ds = await parse('<http://e/s> <http://e/p> "x" <http://e/g> .\n', { format: 'nquads' });
const rows = await ds.query("SELECT * FROM <http://e/none> WHERE { ?s ?p ?o }");
console.log(rows.length, rows.warnings?.[0]?.class); // 0 'dataset-iri-not-found'
```

## Matching literals by value

`has`, `match` and `delete` of a Dataset compare terms by default (RDF 1.1
Concepts section 3.6; SPARQL 1.1 section 18.3): `"01"^^xsd:integer` is not
`"1"^^xsd:integer`. With `{match: 'value'}` as the last argument, a literal
object matches every object literal that is the same term or has the same
value under SPARQL 1.1 `=` (sections 17.3 and 17.4.1.7). The subject, the
predicate, the graph and an object that is not a literal match by term. The
engine decides the relation and keeps an index of the object literals by value
(https://github.com/danbri/factoidal/issues/1052, value-based matching).

`sameValue(a, b)` answers the relation for two terms: `true`, `false`, or
`null` for incomparable (the type error of `=`: two different literals of a
datatype with no value comparison, an ill-typed literal and another literal,
`xsd:integer` and `xsd:boolean`). It is synchronous and needs the engine
loaded (`await ready()` or any other call first). Two consequences of the
SPARQL operator: `"NaN"^^xsd:double` is not the same value as itself (the
value match still finds the same term), and the relation is not transitive
across `xsd:float` and `xsd:decimal` (F&O 3.1 section 4.2 rounds the decimal
to the float type first).

```js
import { parse, ready, sameValue, dataFactory as f } from '@factoidal/core';
await ready();
const xsd = (l) => f.namedNode('http://www.w3.org/2001/XMLSchema#' + l);
console.log(sameValue(f.literal('01', xsd('integer')), f.literal('1.0', xsd('decimal')))); // true
console.log(sameValue('"a"^^<http://e/dt>', '"b"^^<http://e/dt>'));                      // null

const ds = await parse('<http://e/s> <http://e/p> "01"^^<http://www.w3.org/2001/XMLSchema#integer> .\n',
  { format: 'ntriples' });
const q = f.quad(f.namedNode('http://e/s'), f.namedNode('http://e/p'), f.literal('1', xsd('int')));
console.log(ds.has(q), ds.has(q, { match: 'value' }));                                   // false true
console.log(ds.match(null, null, f.literal('1e0', xsd('double')), null, { match: 'value' }).size); // 1
ds.delete(q, { match: 'value' });
console.log(ds.size);                                                                     // 0
```

## Syntax names, IRIs and vocabularies

These functions are synchronous and need the engine loaded (`await ready()` or
any other call first). The engine decides each answer.

`syntaxFor(fileNameOrIri)` or `syntaxFor({fileName, mediaType})` gives the
syntax of a document, a `name` of `formats()`, or `null`
(https://github.com/danbri/factoidal/issues/1053). The table is the W3C
registrations: Turtle `text/turtle` `.ttl`, N-Triples `application/n-triples`
`.nt`, N-Quads `application/n-quads` `.nq`, TriG `application/trig` `.trig`,
RDF/XML `application/rdf+xml` `.rdf`, JSON-LD `application/ld+json` `.jsonld`.
The media type wins when it is given, and its parameters and letter case do not
change the answer. An unknown media type (`text/plain`) gives `null`; it does not
fall back to the name. The query and the fragment of an IRI are ignored.
`.owl` and `.xml` are not registered and give `null`. Each row of `formats()`
has the same `mediaTypes` and `extensions`.

`splitIri(iri)` gives `{namespace, localName}`
(https://github.com/danbri/factoidal/issues/1051 item 4). The local name is the
longest suffix of the IRI that is an XML NCName (the name an RDF/XML QName can
carry), and `''` when there is none; `namespace + localName` is the IRI.
`isNCName(text)` is the check of a prefix label or a local name.

`vocabularies()` gives the engine's vocabulary table, `[{prefix, namespace,
terms}]` (issue 1051 item 5): `rdf`, `rdfs`, `xsd` and `owl` with their term
local names (RDF 1.2 Schema, XSD 1.1 Part 2 built-in datatypes, OWL 2 reserved
vocabulary), and `foaf`, `dcterms`, `dc`, `schema` as namespaces only (no
terms). The prefixes are those of the Turtle writer. `memberIri(n)` gives the
container membership property `rdf:_n` (n >= 1) and `memberOrdinal(iri)` its
`n`, or `null`.

```js
import { ready, syntaxFor, splitIri, vocabularies, memberIri } from '@factoidal/core';
await ready();
syntaxFor('data.ttl');                                    // 'turtle'
syntaxFor({ fileName: 'a.nt', mediaType: 'text/turtle' }); // 'turtle'
splitIri('http://e/123abc');                               // { namespace: 'http://e/123', localName: 'abc' }
const rdf = vocabularies().find((v) => v.prefix === 'rdf');
rdf.namespace + 'type';                                    // rdf:type
memberIri(2).value;                                        // '...22-rdf-syntax-ns#_2'
```

## RDF lists and containers

A Dataset reads and builds RDF lists (`rdf:first` / `rdf:rest`, RDF 1.2 Schema
section 5.2) and reads containers (`rdf:_1`, `rdf:_2`, ..., section 5.1)
(https://github.com/danbri/factoidal/issues/1051 item 6). The engine walks the
list through its indexes, one lookup per node. The last argument `graph` is the
graph name; omitted, `null` or the DefaultGraph is the default graph.

- `ds.listItems(head, graph?)` gives the items in order; `rdf:nil` gives `[]`.
  A list that is not well formed is a FactoidalError with code `op.failed`; the
  message names the reason (`no-first`, `no-rest`, `branch` for two
  `rdf:first` or `rdf:rest`, `cycle`) and the node.
- `ds.containerItems(node, graph?)` gives `{kind, items}`: `items` is
  `[{ordinal, term}]` sorted by `n` (a gap in the numbers is kept), `kind` is
  `rdf:Bag`, `rdf:Seq` or `rdf:Alt` from the `rdf:type` of the node, or `null`.
- `ds.addList(items, graph?)` adds a new list on blank nodes that are fresh in
  the Dataset and gives its head; no items give `rdf:nil` and add nothing.
  A graph named by a blank node cannot be changed.

```js
import { parse, dataFactory as f } from '@factoidal/core';
const ds = await parse('@prefix : <http://e/> . :s :p ( :a "b" ) .', { format: 'turtle' });
const head = ds.match(null, null, null).toArray().find((q) => q.predicate.value === 'http://e/p').object;
ds.listItems(head).map((t) => t.value);   // ['http://e/a', 'b']
const h2 = ds.addList([f.literal('x'), f.literal('y')]);
ds.listItems(h2).length;                  // 2
```

## The persisted store

A **Shardborough** store is the on-disk format the Lean packer writes:
predicate-local IBK3, IBK4 or IBK5 blocks with their index sidecars, a
manifest that commits every artifact's SHA-256, and a `CURRENT` pointer to
the activated generation
([`skills/shardborough-storage`](../../skills/shardborough-storage/SKILL.md),
[`docs/shardborough-storage-spec.md`](../../docs/shardborough-storage-spec.md)).
`factoidal pack` and `factoidal activate` make one from an RDF file;
`sampleStorePath()` (and `factoidal sample-store`) packs a small built-in one.

```js
import { openStore, queryStore } from "@factoidal/core";
import { sampleStorePath } from "@factoidal/core/sample-store";
const root = sampleStorePath();   // packs a small built-in store under the temp directory

const store = await openStore(root);                 // reads CURRENT, verifies every block once
const rows = await store.query(`
  SELECT ?c ?l WHERE {
    ?c <http://www.w3.org/2004/02/skos/core#prefLabel> ?l
    FILTER(CONTAINS(LCASE(STR(?l)), "video")) } LIMIT 5`);
console.log(store.rows);                             // 15
console.log(store.layout);                           // quad-ibk5-ptd2-lgi4-gbi1-merkle-v0
await store.close();

// One query: open only the blocks this query's plan names, query, close.
const n = await queryStore(root, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }');
```

`source` is a collection root path (Node), or a reader function from a
root-relative path to the file's bytes, which works in any runtime:

```js browser
// In a page: the store's files served under /store/.
// (Browser example; the Node test checks its syntax only.)
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

## The durable update log

A SPARQL Update log that survives a page reload (hub post 18,
[issue 728](https://github.com/danbri/factoidal/issues/728)). In the browser
each log is an IndexedDB database; under Node it lives in the memory of the
process.

```js browser
import { deltaLogOpen, deltaLogAppend, deltaLogMerge, deltaLogInspect } from '@factoidal/core/browser';
const log = await deltaLogOpen('my-log');
const { seq, opCount } = await deltaLogAppend(log,
  'INSERT DATA { <http://example.org/a> <http://example.org/p> "v" }');
const nquads = await deltaLogMerge(log, '');          // base N-Quads + the log
const { batches, torn } = await deltaLogInspect(log);  // what the log holds
```

`deltaLogAppend` admits INSERT DATA, DELETE DATA, CLEAR DEFAULT, CLEAR GRAPH,
DROP GRAPH and CREATE GRAPH; any other form rejects and nothing is written.
Each update is one record: the engine writes its bytes (a DLB1 frame with
checksums) and, on merge, decodes the records in order. A torn last write (an
append that did not complete) is not applied. A damaged record, or a record
whose checksum verifies but whose entries the engine cannot decode, makes
`deltaLogMerge` and `deltaLogInspect` reject, because the records after it
would otherwise be lost without a message
([issue 843](https://github.com/danbri/factoidal/issues/843)). The page
stores the records and reads none of their bytes.

## The `factoidal` command

Installing this package puts a `factoidal` command on PATH. It reads a
**Shardborough** store — the on-disk format the Lean `l4block-*` tools
write — with no native binary: JavaScript reads the files and moves the
bytes, and the Lean engine running as WebAssembly makes every format
decision (parsing the manifest, choosing the blocks, verifying their
SHA-256, evaluating the SPARQL).

> This command is not the native `factoidal` binary of the repository
> (`bin/<platform>/factoidal`, which takes subcommands such as `shex` and
> `compact`). This one takes `version`, `sample-store`, `pack`, `activate`, `inspect`,
> `query`, `serve`, `lws-serve`, `solid-serve` and `solid-client`.

### First query

`factoidal sample-store` packs a small built-in store (15 triples held in
`sample-store.mjs`; no data file ships) and prints its path:

```console
$ npm install @factoidal/core
$ npx factoidal query "$(npx factoidal sample-store)" \
    'SELECT ?c ?l WHERE { ?c <http://www.w3.org/2004/02/skos/core#prefLabel> ?l }'
```

From JavaScript (Node): `import { sampleStorePath } from '@factoidal/core/sample-store'`.
Your own data: `factoidal pack data.ttl store/gen-1 && factoidal activate store gen-1`.

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

### Serving a store: `factoidal serve`

```console
$ factoidal serve ./mystore --port 3030
serve: listening on http://127.0.0.1:3030 for ./mystore (layout quad-ibk5-…, 6455 rows, delta batches replayed: 0, write scope all-graphs)
serve: query http://127.0.0.1:3030/sparql, graph store http://127.0.0.1:3030/data
http://127.0.0.1:3030
$ curl -s 'http://127.0.0.1:3030/sparql?query=SELECT%20(COUNT(*)%20AS%20%3Fn)%20%7B%3Fs%20%3Fp%20%3Fo%7D'
```

| Request | Answer |
| --- | --- |
| `GET`/`POST /sparql` with a query | SPARQL 1.1 Protocol §2.1; SPARQL Results JSON, XML, CSV or TSV by `Accept`; Turtle or N-Triples for CONSTRUCT and DESCRIBE |
| `POST /sparql` with an update | Protocol §2.2; the change is appended to the delta log and synced before the answer |
| `GET /sparql`, no query string | the SPARQL 1.1 Service Description of the endpoint |
| `/data?default`, `/data?graph=IRI`, `/data/...` | the Graph Store HTTP Protocol: GET, HEAD, PUT, POST, DELETE |

The engine decides the request framing, routing, status codes, negotiation
and what an update stores; `bin/serve.mjs` moves bytes and appends the batch
the engine hands it. A quad store (`--layout ibk5`, the default, or `ibk4`)
takes changes to every graph. An IBK3 store (`--layout ibk3`) takes changes
to the default graph only (a named-graph change answers 501), because its
delta log is replayed and compacted for that graph only. Fold the log into a new generation with `l4block-shard-compact`,
activate it and restart the server. W3C protocol, graph-store and
service-description tests over a live socket: 50 pass, 0 fail (out of 50).
Measured on 888,949 triples: about 7 s to open, 0.5 ms median for a
bound-subject SELECT, 31 ms for `COUNT(*)` over every triple, resident set
flat at 527 MB over 4,000 requests (`skills/shardborough-storage`, § Serving).

```js
import { listen, listenOnWorker } from '@factoidal/core/serve'
import { sampleStorePath } from "@factoidal/core/sample-store";
const root = sampleStorePath();   // packs a small built-in store under the temp directory
const running = await listen(root, { port: 0 })
await running.close()
// running.origin, running.served.info, await running.close()
// listenOnWorker(root, options): the same on a worker thread with a raised
// stack, which a large store needs (what `factoidal serve` uses)
```

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
import { loadEngine } from '@factoidal/core/engine'
import { openStore, openStoreHandle, listStoreHandles } from '@factoidal/core/store'

const engine = await loadEngine()

// Two stores, open at once, held for the life of the process.
import { sampleStorePath } from "@factoidal/core/sample-store";
const root = sampleStorePath();   // packs a small built-in store under the temp directory
const skos = openStoreHandle(engine, openStore(root))
const docs = openStoreHandle(engine, openStore(root))

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
import { sampleStorePath } from "@factoidal/core/sample-store";
const root = sampleStorePath();   // packs a small built-in store under the temp directory
const PREFIX = 'PREFIX skos: <http://www.w3.org/2004/02/skos/core#>'
const handle = await openStoreHandleOnWorker(root, {})
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
a 4,434-triple store (the test fixture `test/fixtures/sample-store`) so the overhead is not lost in the query:

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

### GeoSPARQL — six topological functions, distance and envelope

The `geof:` functions below are built into the SPARQL engine and need no
import. They work through `query()` / `fn.query()` AND against a
persisted store through `factoidal query`, because both paths evaluate
in the same environment.

    geof:sfEquals   geof:sfDisjoint   geof:sfIntersects
    geof:sfTouches  geof:sfWithin     geof:sfContains
    geof:distance   geof:envelope

`geof:distance(?a, ?b)` takes two points in the same reference system and
returns the planar distance in that system's coordinate units as an
`xsd:double`. With the GeoSPARQL 1.1 third argument, a unit of measure
IRI, it answers only when the unit is the unit of the first point's
reference system (`uom:degree` for CRS84 and EPSG:4326, `uom:metre` for
EPSG:3857 and EPSG:27700) and is an error otherwise; a geodesic distance
in metres between CRS84 points is not computed
(https://github.com/danbri/factoidal/issues/772). `geof:envelope(?g)` returns
the bounding box as a `geo:wktLiteral` `POLYGON`.

```sparql
PREFIX geof: <http://www.opengis.net/def/function/geosparql/>
PREFIX geo:  <http://www.opengis.net/ont/geosparql#>
SELECT ?a WHERE {
  ?a :footprint ?w
  FILTER(geof:sfWithin(?w, "POLYGON((0 0,0 2,2 2,2 0,0 0))"^^geo:wktLiteral))
}
```

**What is NOT there**, stated so nobody plans around it: no
`geof:buffer`, `geof:boundary`, `geof:convexHull` or any other
non-topological function beyond distance and envelope; no
`geof:relate` with a DE-9IM matrix; no coordinate reference system
handling beyond what the WKT literal carries; no GML literals. Geometry
comes from a WKT parser, so a shapefile, GeoJSON or GML source must be
converted to `geo:wktLiteral` before it is loaded.

### Full text: SPARQL's own functions, over a character-gram index

`CONTAINS`, `STRSTARTS`, `STRENDS` and `REGEX` (SPARQL 1.1 §17.4.3) are
the way to search text with an index. You do not ask for the index: where
the query shape allows it, the planner
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

### Full text by token: jena-text `text:query`

The engine also reads the jena-text property function, slice 1 of it:
exact tokens, every query token required, no score, no ranking.

```sparql
PREFIX text: <http://jena.apache.org/text#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT ?s WHERE { ?s text:query (rdfs:label "solar panel" 10) }
```

The object is `"terms"`, `( property "terms" )` or
`( property "terms" limit )`. A literal matches when its lexical form,
lowercased and split on every character that is not an ASCII letter or
digit, holds every query token, so `"panel"` matches `Solar Panel kit`
and does not match `panels`. Without a property every literal is
searched. The limit keeps the first matches in data order. It does not
use the literal index: it reads every candidate literal, about 17 ms per
10,000 literals on a native build (measured 2026-10-12; record:
`docs/designissues/2026-10-10-lean-geo-distance-fulltext.md`).

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

const running = await listen({ port: 0 })
const client = await createSolidClient({ baseIri: running.origin })
await client.replace('/notes/one', '<#it> <#p> "v" .', 'text/turtle')
const read = await client.read('/notes/one')
await running.close()
```

From the command:

```
factoidal lws-serve   DIR (--issuer IRI | --auth-config FILE | --insecure-no-auth) [--owner WEBID] [--port N] [--base IRI]
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


## An SBM11 store held in Linked Web Storage: `lwsSbm11Reader`

`openSbm11` (the Shardborough store, https://github.com/danbri/factoidal/issues/1009)
reads each file of a generation at an offset through a reader.
`lwsSbm11Reader(url, opts)` is a reader of a generation held as
[LWS 1.0](https://w3c.github.io/lws-protocol/lws10-core/) resources: one
resource per file under the container `url`, and the `CURRENT` pointer of a
collection root as one more resource (https://github.com/danbri/factoidal/issues/1010).
Give it to `openSbm11` as `reader` (or to `registerSbm11Source`):

```js browser
// In a dedicated worker: the engine asks for bytes synchronously, and the
// default transport there is a synchronous XMLHttpRequest.
import { openSbm11, lwsSbm11Reader } from '@factoidal/core/browser'

const storeUrl = 'https://storage.example/stores/tiny/'   // holds CURRENT and gen/...
const accessToken = 'an LWS access token'
const reader = lwsSbm11Reader(storeUrl, { auth: `Bearer ${accessToken}` })
const store = await openSbm11(storeUrl, { reader })
const answer = store.query('SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }')
console.log(answer.json, store.evidence)   // evidence: [{ resource, etag, lastModified, requests, partial, bytes }]
store.close()
reader.close()
```

How it reads. Each read is a GET with `Range: bytes=a-b` (RFC 9110 §14).
The answer is used as the range only when it is `206` with `Content-Range:
bytes a-b/N`; any other successful answer is taken as the whole file, kept in
memory, and later reads of that file are cut from it with no request. A
changed `ETag` between two reads of one file refuses the read, so the bytes of
two versions are never mixed. `factoidal lws-serve` answers `Range` with
`206` (the decision is Lean: `LWS/Binding.lean` `parseRange`,
`range_selection_exact`). The engine checks every length against the manifest
as for a directory.

Evidence. `store.evidence` lists each resource read with its `ETag` and
`Last-Modified`, the number of requests, how many were answered `206`, and
the bytes received, so an answer can say which bytes it came from.
`store.evidence` is `undefined` for a reader that records none (a directory).

Transport. The engine is inside WebAssembly and cannot wait for a promise, so
the reader needs a synchronous GET. In Node the default is a `fetch` in a
worker thread that this thread waits for (`Atomics.wait`), stopped by
`reader.close()`; the server must then run in another process or worker,
not on the thread that queries. In a browser worker the default is a
synchronous `XMLHttpRequest`; a window thread has neither, so pass
`opts.transport` (`(url, headers) => ({ status, header(name), bytes })`).
`opts.auth` is sent as the `Authorization` header; `opts.headers` adds more.

The storage medium. In Lean every reader is a `Medium`
(`L4Factoidal/Storage/Medium.lean`: `readAt`, `size`, `writeObject`,
`switchPointer`); the SBM11 session uses the two reads. Every host refuses
the two writes today. What a store relies on from a medium is the named
assumption `ReadsWritten`: the bytes read are the bytes written.

Not yet: writes to an LWS storage (packing a generation, switching
`CURRENT` with a conditional PUT), the Merkle check of each read, eviction of
in-memory copies.

## Packing an SBM11 generation in memory: `packSbm11`, `mapReader`

> `packSbm11` needs a wasm module built after 0.15.0 (the op
> `sbm11PackFiles`). The 0.15.0 wasm does not have it: there `packSbm11`
> rejects with `code: 'SBM11_NO_PACK_OP'`. `mapReader` works on any module
> that has the SBM11 query ops.

```js
import { packSbm11, mapReader, openSbm11 } from "@factoidal/core";

const files = await packSbm11(
  "<http://e/s> <http://e/p> <http://e/o> .", { syntax: "nquads" });
// files: Map from file name to Uint8Array (data files, .merkle sidecars,
// manifest.sbm11; no CURRENT)
const store = await openSbm11("mem", { reader: mapReader(files) });
console.log(store.query("SELECT * WHERE { ?s ?p ?o }").json);
store.close();
```

`packSbm11(text, { syntax, base? })`: `text` is a string or UTF-8 bytes;
`syntax` is `turtle`, `trig`, `nquads`, `ntriples`, `rdfxml` or `jsonld`
(required); `base` is the base IRI. It resolves to a `Map` from file name to
bytes: the files of one SBM11 generation, byte for byte the files that the
native `l4sbm11-pack` writes for the same quads (23 of 23 files for
`test/fixtures/sbm11-tiny`; all files of 605 of 605 W3C SPARQL 1.0 and 1.1
inputs). The engine names every file and computes every byte (Lean
`Storage/Sbm11/PackBytes.lean`), with one engine call per file.

`mapReader(files)` is a reader over files held in memory (a `Map` or a plain
object from file name to `Uint8Array`). Give it to `openSbm11(source,
{ reader })`. A read past the end of a file, or of a file that it does not
hold, answers null, and the engine refuses the read with the file name.

Limits: the whole document and every file are in memory at the same time.
Not yet: `factoidal pack` for SBM11, and a pack that streams its input
(https://github.com/danbri/factoidal/issues/1009, SBM11 in npm).

## Functional API (fn)

`@factoidal/core/fn` is a functional variant of the API above. `FnDataset`
is a frozen snapshot; operations are free functions that return new values;
RDFC-1.0 canonical hashes are a memoized identity, which is what lets a
dataflow graph skip recomputation. Design:
[`docs/designissues/2026-07-05-functional-dataset-api.md`](../../docs/designissues/2026-07-05-functional-dataset-api.md).

```js
import fn from '@factoidal/core/fn';
const { parse, filter, hash, cell, derive, validate } = fn;
const shapesTtl = '@prefix sh: <http://www.w3.org/ns/shacl#> . <http://e/S> a sh:NodeShape .';

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

`fromDataset` snapshots a `Dataset` (or an RDF/JS DatasetCore);
`toDataset` gives an in-memory RDF/JS DatasetCore.
`union`/`difference`/`filter`/`mapQuads` are set algebra;
`query`/`entail`/`canonicalize`/`graphs`/`validate`/`shex`/`fromMapping`/
`fromCsvw`/`rif` wrap the functions of the main entry.

## Explaining an entailment: `explain`

```js
import { explain } from "@factoidal/core";

const sources = `@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:alice ex:worksFor ex:acme .
ex:worksFor rdfs:domain ex:Employee .
ex:Employee rdfs:subClassOf ex:Person .`;
const description = `@prefix ex: <http://example.org/> .
_:x a ex:Person . _:x ex:worksFor ex:acme .`;
const r = await explain(sources, description, { profile: "rdfs" });
console.log(r.entailed); // true: _:x maps to ex:alice
// { profile, entailed, bundle, assumptions, rejection, entailedMeans }
```

`explain(sources, description, options)` asks whether the sources RDFS-entail
the description. The description is a graph; its blank nodes are variables
shared across its triples. Both arguments are a Dataset, text, `{text, format}`
or an array of those. Text is Turtle unless `format` (or `sourcesFormat` /
`descriptionFormat`) says otherwise. The description must be a default graph
only; a named graph rejects with a `FactoidalError`. `profile` is `'rdfs'`
(the only value). The call needs the full engine (op `explainGraph`).

- `entailed: true`: `bundle` holds the sources, the description, the
  blank-node `mapping`, the derivation `steps` (rule, conclusion, premise
  indexes) and one `support` index per description triple. The graph checker
  accepted the bundle.
- `entailed: false`: `bundle` is `null` and `rejection` is `noMatch` (with the
  `index` and `triple` that has no instance in the RDFS closure),
  `noJointMapping` (each triple has an instance, but no single mapping serves
  all of them) or `checkerRefused`. The verdict relies on the named
  assumption listed in `assumptions`; read that list with the verdict.
- `entailedMeans` is the engine's statement of what `entailed` is worth.

Blank-node labels in the output carry a scope prefix (`d0_` for the sources,
`d1_` for the description). Design: [issue 1002](https://github.com/danbri/factoidal/issues/1002).

## Stages as nodes: `stages`, `node`, `pipe`, `run`

```js
import { stages, node, pipe, run } from "@factoidal/core";

const sources = `@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:alice ex:worksFor ex:acme .
ex:worksFor rdfs:domain ex:Employee .
ex:Employee rdfs:subClassOf ex:Person .`;
const description = `@prefix ex: <http://example.org/> .
_:x a ex:Person . _:x ex:worksFor ex:acme .`;

const list = await stages();
console.log(list.length, list.filter((s) => s.status === "proved").length);

const p = pipe(
  await node("turtleDocumentReader"),
  await node("rdfsReasoner"),
  await node("rdfsExplainGraphStage", { description }),
);
const r = await run(p, sources);
for (const e of r.evidence) console.log(e.stage, e.status, e.contract);
console.log(r.evidence[2].artefact.entailed); // true
console.log(r.assumptions); // the union of the nodes' named assumptions
console.log(p.wellTyped, p.check.conversions); // the engine's type check
```

`stages()` answers the stage registry of the Lean library
(`L4Factoidal.Dataflow.registry`, op `stageList`, full engine), one element
per entry: `name` (the declaration, or the area when there is none),
`declaration`, `kind` (the interface type: `Stage`, `RdfReader`,
`SoundReasoner`, ...), `wireIn`, `wireOut` (wire types of
`formal/lean4/L4Factoidal/Dataflow/Wire.lean`), `params` (the inputs a node
supplies when it is made), `status` (`proved`, `tested`,
`assumed`, `missing`), `contract` (the contract declaration), `theorems`,
`assumptions` (the named assumptions), `tests`, `runnable` (false for
`missing`) and `bound` (this package has a function that runs it). The
same list is [docs/dataflow-inventory.md](../../docs/dataflow-inventory.md).

`node(name, params)` makes a node for one stage. The bound stages are the
six document readers (`turtleDocumentReader`, ...; text in, Dataset out),
`rdfsReasoner`, `owlRlReasoner`, `rhoDfReasoner` (closure of the default
graph), `shaclValidator` (`{shapes}`), `shippedEvaluator` (`{query}`; a
CONSTRUCT or DESCRIBE answer replaces the graph), the N-Triples, N-Quads,
Turtle, TriG and RDF/XML writers, `rdfcStage`, and `rdfsExplainGraphStage`
(`{description}`). `pipe(...nodes)` composes nodes and pipelines left to
right, and asks the engine to check it (op `pipelineCheck`, full engine):
`p.check` has `wellTyped` (each stage's output wire is the next stage's
input wire, or converts to it: a dataset with prefixes to its dataset, a
dataset to its default graph, a graph to the dataset with that default
graph), `mismatch` (the first stage whose output does not feed the next),
`conversions`, `assumptions` (the union of the stages' named assumptions),
`contract` (the theorem `L4Factoidal.Dataflow.Pipeline.guarantee_sound` and
each stage's contract) and `stages`. `p.assumptions` and `p.wellTyped` are
its fields. The guarantee of a well-typed pipeline is that theorem: when
every assumption of the union holds, a successful run satisfies the
composition of the stages' contracts. With an engine built before the op,
`p.check` and `p.wellTyped` are null and `p.assumptions` is the union of the
nodes' fields. `run(pipeline, input)` takes a wire value `{graph, evidence}` or the
graph itself, and answers `{graph, evidence, assumptions}`: `evidence` gets
one record `{stage, status, contract, assumptions, checked, artefact}` per
node (`artefact`: the explain result, the SHACL report, the written text,
...), and `assumptions` is the assumptions of the records on the input
wire, then the engine's union for the pipeline. `wellTyped` is the engine's
check (null without the op). `checked` is true exactly when the stage's status is
`proved`. `proved` on the result is true exactly when every record is
checked and the pipeline is well typed, and `uncheckedSteps` lists the stage
names of the records that are not checked. A run with a node whose stage is
`missing` (no contract, no suite) or not bound, or of a pipeline that is not
well typed, rejects with a `FactoidalError` before any node runs.

`run(pipeline, input, { unchecked: true })` is the explicit opt-in to run
stages that are not `proved` (`tested`, `assumed`) and `missing` stages that
this package has a function for. The option is on `run`, not on `node`, so
one call site decides, and a pipeline built by other code cannot opt in on
its own. A step that ran under the opt-in and is not checked has
`unchecked: true` and a `reason` in its record (the status and the named
assumptions, or `no contract`). A stage with no package function still
rejects with `op.unknown`. The opt-in also runs a pipeline that is not well
typed. The result's `proved` stays false whenever such a step ran or the
pipeline is not well typed: the path has no guarantee for it, and the result
says so.

```js
import { node, pipe, run } from "@factoidal/core";

const ttl = "<http://example.org/a> <http://example.org/p> <http://example.org/b> .";
const viaWriter = pipe(await node("turtleDocumentReader"), await node("turtleDocumentWriter"));
const out = await run(viaWriter, ttl, { unchecked: true });
console.log(out.proved);         // false: the writer is not proved
console.log(out.uncheckedSteps); // ["turtleDocumentWriter"]
console.log(out.evidence[1].reason);
```

Design: [issue 1002](https://github.com/danbri/factoidal/issues/1002).

### Node settings, output wires and the CSVW stage (after 0.15.0)

> These three need a wasm module built after 0.15.0 (the op
> `pipelineCheckNodes`, the wire `table`, the CSVW stage bound in the
> engine). With the 0.15.0 wasm: evidence records have no settings, the
> evaluator's output wire is the registry's `Answer`, and the CSVW stage is
> `missing` and not bound.

Settings. The params of `node()` are the node's settings. Each evidence
record carries `settings` (canonical form: keys sorted at every depth; the
defaults of absent settings that narrow the contract, for example `lenient:
false` and `entail: 'none'`; a Dataset value as `{nquadsSha256}`) and
`settingsDigest` (`sha256:` and the hex SHA-256 of the canonical text). The
node has the same fields, plus `outside`, `derived` and `settingsWire` (the
settings as sent to the engine). A setting outside the proved domain of a
proved stage (a lenient reader, an evaluator with `entail` other than
`none` or with `output`, a key that the stage's settings table does not
name) makes the node's status `unproved`. The record then has
`registryStatus` and `outside` (each setting and the reason), and `run()`
reports `proved: false`. A reader's `format` must name the stage's syntax
(`ttl12` selects RDF 1.2 mode, reported as `derived.mode`); an evaluator's
query must parse, else `node()` rejects. Design record:
[2026-10-25-pipeline-settings-and-provenance.md](../../docs/designissues/2026-10-25-pipeline-settings-and-provenance.md).

Output wire by query form. The output wire of a `shippedEvaluator` node
follows its query form: SELECT gives `Table`, ASK gives `Answer`, CONSTRUCT
and DESCRIBE give `Dataset` (`node.wireOut`; Lean `Dataflow.evalContract_wire`).
So reader, CONSTRUCT, CONSTRUCT is well typed; reader, SELECT, CONSTRUCT is
not (https://github.com/danbri/factoidal/issues/1026, CONSTRUCT wire).

CSVW stage. `node('CSVW (tabular data to RDF)', { metadata, mode, base,
url })` takes CSV text on its wire, runs `csvwToRdf` and gives a Dataset.
Its evidence status is `tested` (the W3C csv2rdf suite; there is no Lean
contract, so `checked` is false and `run()` needs `{ unchecked: true }`)
(https://github.com/danbri/factoidal/issues/975, CSVW as a pipeline stage).
`stages()` marks a stage `bound` only when the engine also reports it
runnable.

## API

| Function | Signature (informal) | Notes |
|---|---|---|
| `parse` | `(text, {format?, baseIRI?, lenient?, maxErrors?}) => Dataset` | `turtle`, `ntriples`, `nquads`, `trig`, `rdfxml`, `jsonld`, and `turtle12`, `ntriples12`, `nquads12`, `trig12`; no format: inferred and reported. One call is one document. Strict: a syntax error rejects with a `FactoidalError` (`parse.syntax`). `dataset.prefixes` is the declared map |
| `query` | `(data, sparql, {format?, baseIRI?, entail?, sparql12?, version?, output?}) => Bindings[] \| boolean \| Dataset \| string` | SELECT → `Map<var, Term>[]`; ASK → boolean; CONSTRUCT and DESCRIBE → Dataset; with `output` the results document (`json`, `xml`, `csv`, `tsv`, `table`, `ntriples`). `data` is a Dataset, a string, `{text, format}`, or an array of those |
| `update` | `(data, sparqlUpdate, {format?, baseIRI?}) => Dataset` | answers a NEW Dataset; `dataset.update()` changes one in place |
| `openDataset` | `(data, {format?, baseIRI?}) => Dataset` | a Dataset argument is cloned |
| `closure` | `(data, 'rdfs' \| 'owl-rl' \| 'rho-df' \| 'rdfs-plus') => Dataset` | the closure of the default graph |
| `serialize` | `(data, {format, version?, prefixes?, literalShorthand?, useNativeTypes?, useRdfType?, rdfDirection?, rdfstar?, inputFormat?, baseIRI?}) => string` | `nquads`, `ntriples` (refuses a named graph), `turtle`, `trig`, `rdfxml`, `jsonld`, `rdfc`; see "Datasets" |
| `formats` | `() => [{name, read11, read12, write11, write12, engine, mediaTypes, extensions}]` | the engine's list; `mediaTypes` and `extensions` are the W3C registrations (issue 1053) |
| `sameValue` | `(a, b) => boolean \| null` | SPARQL 1.1 `=` on two terms; `null` incomparable; synchronous after `ready()`; see "Matching literals by value" |
| `syntaxFor` | `(name \| {fileName?, mediaType?}) => string \| null` | the syntax of a file name or media type; synchronous; see "Syntax names, IRIs and vocabularies" |
| `splitIri` | `(iri) => {namespace, localName}` | the local name is the longest NCName suffix; synchronous |
| `isNCName` | `(text) => boolean` | XML NCName check; synchronous |
| `vocabularies` | `() => [{prefix, namespace, terms}]` | rdf, rdfs, xsd, owl terms; foaf, dcterms, dc, schema namespaces; synchronous |
| `memberIri` | `(n) => NamedNode` | `rdf:_n`; synchronous |
| `memberOrdinal` | `(iri) => number \| null` | the `n` of `rdf:_n`; synchronous |
| `canonicalize` | `(data, {format?, baseIRI?}) => string` | RDFC-1.0 canonical N-Quads |
| `graphs` | `(Dataset) => Array<[NamedNode \| BlankNode, Dataset]>` | named graphs, default graph excluded |
| `canonicalHash` | `(Dataset) => string` | SHA-256 (64 lowercase hex digits) of the RDFC-1.0 canonical N-Quads of one graph; graph names are dropped first. `canonicalize` answers the text |
| `queryRaw` | `(dataText, sparql, {dataFormat?, entail?, output?}) => object \| string` | one call, serialized answer: `json` (parsed), `csv`, `tsv`, `xml`, `table`, `ntriples` |
| `queryHdt` | `(hdtBytes, sparql) => Bindings[] \| boolean` | SELECT/ASK over an HDT file's bytes |
| `openStore`, `queryStore`, `listStores` | see "The persisted store" | `Store`: `.query`, `.inspect`, `.close`, `.handle`/`.layout`/`.wireVersion`/`.rows`/`.bytes`/`.artifacts`/`.generation`/`.activated`/`.closed` |
| `registerExtensionFunction`, `unregisterExtensionFunction`, `clearExtensionFunctions` | see above | SPARQL 1.1 §17.6 |
| `registerServiceEndpoint`, `clearServiceEndpoints` | `(iri, data)` | `SERVICE <iri>` answers from this snapshot |
| `shaclValidate` | `(data, shapes) => {conforms, report: Dataset}` | SHACL Core, SHACL-SPARQL, SHACL 1.2 node expressions |
| `shexValidate` | `(data, schemaText, focus, shape?) => boolean` | ShExJ when the text starts with `{`, else ShExC; no `shape` = the schema's START; `focus`/`shape` are RDF/JS terms or N-Triples term strings (`'<http://…>'`, `'_:b'`) |
| `owlClosure` | `(data, 'RDFS' \| 'OWL-RL') => Dataset` | input + derived triples, default graph |
| `explain` | `(sources, description, {profile?, format?}) => {entailed, bundle, assumptions, rejection, entailedMeans}` | RDFS entailment of a graph with shared blank nodes, with evidence; see "Explaining an entailment" |
| `stages`, `node`, `pipe`, `run` | `() => StageInfo[]`; `(name, params?) => Node`; `(...nodes) => Pipeline`; `(pipeline, input, {unchecked?}) => {graph, evidence, assumptions, proved, uncheckedSteps, wellTyped}` | registered Lean stages as nodes, evidence on the wires; see "Stages as nodes" |
| `coreRdfsClosure`/`rhoDfClosure`, `rdfsPlusClosure` | `(data) => Dataset` | ρdf closure, RDFS-Plus closure |
| `coreRdfsCheck`/`rhoDfFragmentCheck` | `(data) => {ok, fragment}` | ρdf fragment check |
| `tableauMaterialise` | `(data) => {dataset, addedCount, budgetHit}` | class-expression memberships; `budgetHit` true when the work budget ran out |
| `tableauDlInconsistent` | `(data) => {inconsistent, rlAlone}` | OWL DL clash after RL closure + materialisation |
| `owlIsConsistent`, `owlEntails` | `(data, {fuel?})`, `(premise, conclusion, {fuel?})` | contradiction/entailment search; indeterminate results use `null` and an explicit `reason` (see below) |
| `rmlMap` | `(mapping, sourceText, 'json' \| 'csv') => Dataset` | one logical source |
| `csvwToRdf` | `(csvText, metadataJson?, {mode?, base?, url?}) => Dataset` | CSV on the Web csv2rdf |
| `jsonldToRdf`, `jsonldFromRdf` | | JSON-LD 1.1 to and from RDF; a remote `@context` is not fetched. Option `rdfstar`: JSON-LD-star (`@triple`, `@reifies`, `@annotation` as RDF 1.2 triple terms and reifiers; also `serialize` with `format: "jsonld"`) |
| `rifEval` | `(data, rifXml) => Dataset` | RIF Core forward chaining |
| `xmlWellformed`, `xpathEval`, `xsltTransform`, `schematronValidate`, `jsonSchemaValidate`, `xformsRecalc`, `mathmlEval` | | XML 1.0, XPath 1.0, XSLT 1.0, Schematron, JSON Schema draft-07, XForms recalculation, Content MathML |
| `clParse`, `clSerialize`, `clAlphaNorm`, `clNormalize` | `(clifText) => {…}` | Common Logic (ISO/IEC 24707) and IKL; `clSerialize` reports `roundTripProved: false`, `clNormalize` reports `preserves: "satisfiability"` |
| `toanSummation`, `toanProduct`, `toanSimplify`, `toanDiff`, `toanSubst` | | symbolic algebra over Content MathML |
| `vcSha256Hex`, `vcEd25519SecretToPublic`, `vcEd25519Sign`, `vcEd25519Verify`, `vcEddsaCreateFromCanonical`, `vcEddsaVerifyFromCanonical` | | VC Data Integrity `eddsa-rdfc-2022`; Ed25519 is HACL\*'s C code in the wasm module; no initialisation step |
| `vcCheckCredential`, `vcCheckCredentialSubject`, `vcCheckNoDataLoss`, `vcCheckRelatedResourceDigests`, `didKeyResolve` | | VCDM 2.0 checks; `did:key` (Ed25519) resolution |
| `capabilities` | `() => {…}` | which ops the loaded wasm serves |
| `loadEngine` | `() => engine` | the low-level handle, `call(op, args)`, for ops this layer does not wrap |
| `Dataset`, `Store`, `FactoidalError`, `dataFactory`, `version`, `engine` | | `engine` is `'lean4-wasm'` |

`owlIsConsistent` checks the original default graph in a restricted OWL
fragment. It reports `true` only when a finite model checks against that
graph (the result then has no `reason`), and `false` only after a refutation
certificate checks against the graph's translated ontology. It returns `null`
for unsupported syntax (`unsupported-syntax`), for a search or check that
ran out of `fuel` (`budget-out`, the reason names the fuel), or when no
certificate checks (`incomplete-search`). Named graphs do not supply axioms
or declarations to the default graph. The existing whole-dataset RDF 1.2
term refusal still applies.

Supported logical forms are named atomic subclass/class assertions,
Thing/Nothing, named-individual sameAs/differentFrom, and
`owl:someValuesFrom` restrictions on an object property with a named class
(or Thing/Nothing) filler, used as the superclass of `rdfs:subClassOf` or as
the class of `rdf:type`, and `owl:TransitiveProperty`. The reader also admits
`owl:ObjectProperty` declarations, the nine built-in annotation properties,
declared annotation properties (on IRIs and blank nodes),
`rdfs:subPropertyOf` between annotation properties, annotated axioms
(`owl:Axiom` nodes whose annotated triple is in the graph), and ontology
headers with `owl:versionIRI`
(`docs/designissues/2026-10-24-owl-model-certificates.md`). Other
restrictions, other object/data property axioms, imports and equivalentClass
are unsupported.
`fuel` (default 20000) bounds the model search (rounds of existential
expansion) and the certificate checker (saturation rounds). Record:
`docs/designissues/2026-10-24-owl-model-certificates.md`.

`owlEntails` answers `false` (via `refutation`, reason `countermodel: ...`)
only when a checked finite model of the premise is not a model of the
conclusion. Its positive results remain on the separate legacy
closure/refutation path and do not gain this proof guarantee.
It reports `true` for closure/refutation results and `null` for unsupported
conclusions, incomplete search, budget exhaustion or detected punning.
Its limited punning check is not a general Direct Semantics proof; reader,
preprocessing and negated-goal soundness remain unfinished for this operation.
Treat `null` as unresolved, not as the opposite Boolean.

This changes the 0.11.0 verdict contract: earlier versions reported a
quiescent search as a model or countermodel. Consumers must handle `null`
even when increasing the fuel does not change the answer. See
[OWL verdict repair and assurance gaps](../../docs/20261021-owl-public-verdict-repair.md).

`./l4` and `./l4-core` are aliases of the main entry in 0.9.x and go in
0.10.0.

## Behaviour that differs from 0.8 (the F\* engine)

From the parity runs of issue 713
([design record](../../docs/designissues/2026-10-10-npm-lean-only.md),
section 6). No answer below was found wrong against a specification on
either engine; where one engine did less, the row says so.

- A parse error's `position.offset` is a UTF-16 index (0.8: UTF-8 bytes).
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
