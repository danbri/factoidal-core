// Run ONE deep-input case through the shipped WebAssembly module in Node.
//
// The wasm module carries the smallest stack we ship, so it is the route
// that fails first when a recursion is proportional to an input. Each case
// runs in its OWN node process: a stack overflow inside wasm aborts the
// instance, and a shared process would report every later case as broken.
//
//   node tests/stack/wasm_case.mjs <case-name> <fixture-dir>
//
// Prints one JSON line: {case, route:"wasm", ok, ms, detail}.
//
// A case in SEQ is a file of op/args pairs, called in order in this one process
// (a dataset handle lives in the module instance); the last answer is the case's.
// A case in CHECK also tests the answer: `ok` is true only when the engine answered
// ok:true and the check passes (the other cases only need the call to return).
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const [, , caseName, dir] = process.argv;
const ROOT = new URL('../../', import.meta.url);
const read = (f) => readFileSync(`${dir}/${f}`, 'utf8');
const readArgs = (f) => JSON.parse(read(f));

const CASES = {
  'xml-entities': () => ['parseToDatasetJson', readArgs('args-xml.json')],
  'xml-entities-attr': () => ['parseToDatasetJson', readArgs('args-xml-attr.json')],
  'xml-entities-dtd': () => ['parseToDatasetJson', readArgs('args-xml-dtd.json')],
  'xml-text-chain': () => ['parseToDatasetJson', readArgs('args-xml-text-chain.json')],
  'xml-markup-chain': () => ['parseToDatasetJson', readArgs('args-xml-markup-chain.json')],
  'xml-markup-chain-top': () => ['parseToDatasetJson', readArgs('args-xml-markup-chain-top.json')],
  'turtle-literal': () => ['parseToDatasetJson', readArgs('args-turtle-literal.json')],
  'turtle-collection': () => ['parseToDatasetJson', readArgs('args-turtle-collection.json')],
  'turtle-predicates': () => ['parseToDatasetJson', readArgs('args-turtle-predicates.json')],
  'nquads-one-subject': () => ['parseToDatasetJson', readArgs('args-nquads.json')],
  'nquads-long-literal': () => ['parseToDatasetJson', readArgs('args-nquads-long-literal.json')],
  'turtle-write-one-node': () => ['serializeTurtle', readArgs('args-turtle-write-one-node.json')],
  'turtle-write-subjects': () => ['serializeTurtle', readArgs('args-turtle-write-subjects.json')],
  'sparql-union': () => ['queryDataset', readArgs('args-sparql-union.json')],
  'sparql-nested': () => ['queryDataset', readArgs('args-sparql-nested.json')],
  'sparql-order-limit': () => ['queryDataset', readArgs('args-sparql-order-limit.json')],
  'manifest': () => ['storeManifestInspect', readArgs('manifest-args.json')],
  'rdfxml-collection': () => ['parseToDatasetJson', readArgs('args-rdfxml-collection.json')],
  'sparql-collection': () => ['updateDataset', readArgs('args-sparql-collection.json')],
  'sparql-replace-long': () => ['queryDataset', readArgs('args-sparql-replace-long.json')],
  'regex-replace-groups': () => ['queryDataset', readArgs('args-regex-replace-groups.json')],
  'rdfc-bnode-chain': () => ['canonicalizeToNQuads', readArgs('args-rdfc-bnode-chain.json')],
  'delta-log-decode': () => ['deltaLogDecode', readArgs('args-delta-log-decode.json')],
  'delta-log-merge': () => ['deltaLogMerge', readArgs('args-delta-log-merge.json')],
  'turtle-write-prefixes': () => ['serializeTurtleWith', readArgs('args-turtle-write-prefixes.json')],
  'turtle-read-triple-term': () => ['parseToDatasetJson', readArgs('args-turtle-read-triple-term.json')],
  'ntriples-read-triple-term': () => ['parseToDatasetJson', readArgs('args-ntriples-read-triple-term.json')],
  'nquads-read-triple-term': () => ['parseToDatasetJson', readArgs('args-nquads-read-triple-term.json')],
  'trig-read-triple-term': () => ['parseToDatasetJson', readArgs('args-trig-read-triple-term.json')],
  'construct-triple-term': () => ['queryDataset', readArgs('args-construct-triple-term.json')],
  'jsonld-read-fanout': () => ['jsonldToRdf', readArgs('args-jsonld-fanout.json')],
  'jsonld-read-list': () => ['jsonldToRdf', readArgs('args-jsonld-list.json')],
  'jsonld-write-fanout': () => ['jsonldFromRdf', readArgs('args-jsonld-write-fanout.json')],
};

// The handle rows of the Turtle writer with many prefixes (issue 864): a document
// handle opened, then written as Turtle.
const SEQ = {
  'turtle-write-prefixes-handle': () => readArgs('seq-turtle-write-prefixes-handle.json'),
  'turtle-write-prefixes-with': () => readArgs('seq-turtle-write-prefixes-with.json'),
};

// Every prefix of the table is used, so the Turtle has one `@prefix` line for each.
const N_PREFIXES = Number(process.env.STACK_TURTLE_PREFIXES || '100000');
const prefixLines = (res) => {
  if (!res || res.ok !== true || typeof res.turtle !== 'string') {
    throw new Error(`the engine did not answer ok:true with Turtle: ${JSON.stringify(res).slice(0, 160)}`);
  }
  const n = res.turtle.split('@prefix ').length - 1;
  if (n !== N_PREFIXES) throw new Error(`the Turtle has ${n} @prefix lines, expected ${N_PREFIXES}`);
};

// The Turtle reader reads one triple whose object is a triple term nested N_NEST deep
// (issue 865), so the N-Quads of the answer hold N_NEST occurrences of `<<(`.
const N_NEST = Number(process.env.STACK_TURTLE_NEST || '300000');
const nestedTerm = (res) => {
  if (!res || res.ok !== true || typeof res.nquads !== 'string') {
    throw new Error(`the engine did not answer ok:true with N-Quads: ${JSON.stringify(res).slice(0, 160)}`);
  }
  if (res.count !== 1) throw new Error(`the document has one triple, the engine counted ${res.count}`);
  const n = res.nquads.split('<<(').length - 1;
  if (n !== N_NEST) throw new Error(`the N-Quads hold ${n} triple terms, expected ${N_NEST}`);
};

// The N-Triples, N-Quads and TriG readers read one triple whose object is a triple term
// nested N_TERM deep, and a CONSTRUCT query answers it as N-Triples text (issue 867): the
// text of the answer holds N_TERM occurrences of `<<(`.
const N_TERM = Number(process.env.STACK_TERM_NEST || '300000');
const nestedTermRead = (res) => {
  if (!res || res.ok !== true || typeof res.nquads !== 'string') {
    throw new Error(`the engine did not answer ok:true with N-Quads: ${JSON.stringify(res).slice(0, 160)}`);
  }
  if (res.count !== 1) throw new Error(`the document has one triple, the engine counted ${res.count}`);
  const n = res.nquads.split('<<(').length - 1;
  if (n !== N_TERM) throw new Error(`the N-Quads hold ${n} triple terms, expected ${N_TERM}`);
};
const nestedTermConstruct = (res) => {
  if (!res || res.ok !== true || res.kind !== 'construct' || typeof res.nquads !== 'string') {
    throw new Error(`the engine did not answer ok:true with a construct answer: ${JSON.stringify(res).slice(0, 160)}`);
  }
  const n = res.nquads.split('<<(').length - 1;
  if (n !== N_TERM) throw new Error(`the answer holds ${n} triple terms, expected ${N_TERM}`);
};
// The markup entity chain referenced directly from the content of the document element
// (issue 871) has one triple for each level.
const N_MARKUP_TOP = Number(process.env.STACK_MARKUP_CHAIN_TOP || '10000');
const markupTop = (res) => {
  if (!res || res.ok !== true) {
    throw new Error(`the engine did not answer ok:true: ${JSON.stringify(res).slice(0, 160)}`);
  }
  if (res.count !== N_MARKUP_TOP) throw new Error(`the document has ${N_MARKUP_TOP} triples, the engine counted ${res.count}`);
};
const CHECK = {
  'xml-markup-chain-top': markupTop,
  'ntriples-read-triple-term': nestedTermRead,
  'nquads-read-triple-term': nestedTermRead,
  'trig-read-triple-term': nestedTermRead,
  'construct-triple-term': nestedTermConstruct,
  'turtle-write-prefixes': prefixLines,
  'turtle-write-prefixes-handle': prefixLines,
  'turtle-write-prefixes-with': prefixLines,
  'turtle-read-triple-term': nestedTerm,
};

const out = { case: caseName, route: 'wasm' };
try {
  const calls = SEQ[caseName] ? SEQ[caseName]() : (() => {
    const build = CASES[caseName];
    if (!build) throw new Error(`no wasm route for case '${caseName}'`);
    return [build()];
  })();
  const { loadL4 } = await import(new URL('docs/web/hub/assets/l4/l4factoidal.js', ROOT).href);
  const l4 = await loadL4();
  const t0 = performance.now();
  let res;
  for (const [op, args] of calls) res = l4.call(op, args);
  out.ms = Math.round(performance.now() - t0);
  if (CHECK[caseName]) CHECK[caseName](res);
  out.ok = true;
  out.detail = JSON.stringify(res).slice(0, 120);
} catch (e) {
  out.ok = false;
  out.detail = String(e && e.message ? e.message : e).slice(0, 300);
}
console.log(JSON.stringify(out));
