// factoidal/l4-core — the typed core API served by the Lean 4 engine
// (L4Factoidal compiled to wasm, dispatch ABI). Since 0.9.0 '../l4-core.js'
// is an alias of the main entry (it goes in 0.10.0); every case here runs
// through it. The differential case against the F* engine moved to
// tests/engine-compare/.
//
// Content comparisons sort N-Quads lines first: the line order of the
// engine's N-Quads text is not part of the contract.
//
// Blank-node labels are salted per document (`d<N>_`) by the Lean engine's
// IO entry, as the F* engine does, and the four envelope features of
// https://github.com/danbri/factoidal/issues/685 (parse-error position,
// prefixes on a handle, serialize options, bare literals) are real
// assertions below; the cases for the stage 2 functions (maths, VC, DID) and
// the wider envelope checks are in test/l4-parity-2.test.js.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const { xfail, LENIENT_ISSUE } = require('./helpers.js');

const l4core = require('../l4-core.js');

// The ops the loaded wasm serves (its `ops` reflection). Since 0.9.0 the
// wasm in l4-assets/ is the package's only engine, so it must serve every op
// a case uses: a missing op FAILS the case, naming the op (it is not a skip).
let leanOpsPromise = null;
function leanOps() {
  if (!leanOpsPromise) {
    leanOpsPromise = require('../index.js').loadEngine().then((eng) => eng.call('ops', []).ops);
  }
  return leanOpsPromise;
}

function skipUnlessAvailable(_t) {
  return false;
}

async function skipUnlessOps(_t, ...ops) {
  const have = await leanOps();
  const missing = ops.filter((op) => !have.includes(op));
  assert.deepEqual(missing, [], `the loaded Lean wasm lacks ${missing.join(', ')} (ops reflection)`);
  return false;
}

// Sort N-Quads text into a canonical line list (order-insensitive
// content comparison — the Lean engine's line order is not pinned to
// the F* engine's sorted order).
function sortedLines(nq) {
  return nq.split('\n').filter((l) => l.trim() !== '').sort();
}

// One binding row (Map<string, Term>) -> a stable string; a row LIST
// -> a sorted multiset key. Sorting each row's entries first makes the
// comparison independent of SRJ row-key order.
function rowKey(row) {
  return JSON.stringify(
    [...row.entries()]
      .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
      .map(([name, term]) => [
        name, term.termType, term.value,
        term.termType === 'Literal' ? term.datatype.value : '',
        term.termType === 'Literal' ? term.language : '',
      ]));
}
function rowMultiset(rows) {
  return rows.map(rowKey).sort();
}

const X = 'http://x/';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const RDFS_SUBCLASS = 'http://www.w3.org/2000/01/rdf-schema#subClassOf';
const XSD_INT = 'http://www.w3.org/2001/XMLSchema#integer';

const JOIN_NT =
  `<${X}alice> <${X}name> "Alice" .\n` +
  `<${X}alice> <${X}age> "30"^^<${XSD_INT}> .\n` +
  `<${X}bob> <${X}name> "Bob" .\n` +
  `<${X}bob> <${X}age> "24"^^<${XSD_INT}> .\n`;
const JOIN_Q =
  `SELECT ?s ?n ?a WHERE { ?s <${X}name> ?n . ?s <${X}age> ?a }`;

// ---------------------------------------------------------------------
// parse + serialize round-trips
// ---------------------------------------------------------------------

test('l4-core parse: ntriples/turtle/nquads/trig round-trip to N-Quads', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const cases = [
    { format: 'ntriples', text: `<${X}s> <${X}p> "c" .`,
      quad: `<${X}s> <${X}p> "c" .` },
    { format: 'turtle',
      text: `@prefix x: <${X}> . x:s x:p "c" .`,
      quad: `<${X}s> <${X}p> "c" .` },
    { format: 'nquads', text: `<${X}s> <${X}p> <${X}o> <${X}g> .`,
      quad: `<${X}s> <${X}p> <${X}o> <${X}g> .` },
    { format: 'trig',
      text: `<${X}g> { <${X}s> <${X}p> <${X}o> . }`,
      quad: `<${X}s> <${X}p> <${X}o> <${X}g> .` },
  ];
  for (const c of cases) {
    const ds = await l4core.parse(c.text, { format: c.format });
    assert.equal(ds.size, 1, `${c.format}: one quad parsed`);
    const nq = await l4core.serialize(ds, { format: 'nquads' });
    assert.deepEqual(sortedLines(nq), [c.quad],
      `${c.format}: round-trips through serialize({format:'nquads'})`);
  }
});

test('l4-core parse: turtle relative IRI resolves against baseIRI', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.parse(`<me> <${X}p> "c" .`,
    { format: 'turtle', baseIRI: 'http://base.example/dir/doc' });
  const nq = await l4core.serialize(ds, { format: 'nquads' });
  assert.deepEqual(sortedLines(nq),
    [`<http://base.example/dir/me> <${X}p> "c" .`]);
});

// Fragment-only relative IRIs went through the same String.toList /
// String.ofList resolution path that trapped on wasm32 until
// 2026-08-25 (skills/lean4-wasm-export/SKILL.md, trap 8).
test('l4-core parse: turtle fragment IRI resolves against baseIRI', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.parse(`<#me> <${X}p> "c" .`,
    { format: 'turtle', baseIRI: 'http://base.example/dir/doc' });
  const nq = await l4core.serialize(ds, { format: 'nquads' });
  assert.deepEqual(sortedLines(nq),
    [`<http://base.example/dir/doc#me> <${X}p> "c" .`]);
});

// ---------------------------------------------------------------------
// query
// ---------------------------------------------------------------------

test('l4-core query: SELECT returns a typed literal binding', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const rows = await l4core.query(
    `<${X}s> <${X}age> "30"^^<${XSD_INT}> .`,
    `SELECT ?a WHERE { ?s <${X}age> ?a }`, { format: 'ntriples' });
  assert.equal(rows.length, 1);
  const a = rows[0].get('a');
  assert.equal(a.termType, 'Literal');
  assert.equal(a.value, '30');
  assert.equal(a.datatype.value, XSD_INT);
});

test('l4-core query: SELECT with a two-pattern join', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const rows = await l4core.query(JOIN_NT, JOIN_Q, { format: 'ntriples' });
  assert.equal(rows.length, 2);
  const names = rows.map((r) => r.get('n').value).sort();
  assert.deepEqual(names, ['Alice', 'Bob']);
});

test('l4-core query: ASK true and false', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const data = `<${X}s> <${X}p> "c" .`;
  assert.equal(
    await l4core.query(data, 'ASK { ?s ?p ?o }', { format: 'ntriples' }),
    true);
  assert.equal(
    await l4core.query(data, `ASK { <${X}none> <${X}q> "zz" }`,
      { format: 'ntriples' }),
    false);
});

test('l4-core query: CONSTRUCT returns a Dataset', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const out = await l4core.query(
    `<${X}s> <${X}p> "c" .`,
    `CONSTRUCT { ?s <${X}q> ?o } WHERE { ?s <${X}p> ?o }`,
    { format: 'ntriples' });
  assert.equal(out.constructor.name, 'Dataset');
  assert.equal(out.size, 1);
  const nq = await l4core.serialize(out, { format: 'nquads' });
  assert.deepEqual(sortedLines(nq), [`<${X}s> <${X}q> "c" .`]);
});

test('l4-core query: accepts a Dataset instance as input', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.parse(JOIN_NT, { format: 'ntriples' });
  const rows = await l4core.query(ds, JOIN_Q);
  assert.equal(rows.length, 2);
});

// ---------------------------------------------------------------------
// update
// ---------------------------------------------------------------------

test('l4-core update: INSERT DATA then query sees the triple', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.update(
    `<${X}s> <${X}p> "c" .`,
    `INSERT DATA { <${X}a> <${X}b> <${X}c> }`, { format: 'ntriples' });
  assert.equal(ds.size, 2);
  const hit = await l4core.query(ds, `ASK { <${X}a> <${X}b> <${X}c> }`);
  assert.equal(hit, true);
});

// ---------------------------------------------------------------------
// serialize
// ---------------------------------------------------------------------

// This raised a raw WebAssembly.Exception on ANY non-empty graph until
// 2026-08-25. Not an engine bug: Lean's runtime built String.toList
// results with a heap-allocated list terminator on wasm32, and
// String.ofList then walked off the end of the heap
// (skills/lean4-wasm-export/SKILL.md, trap 8). Fixed by
// build-wasm.sh step 1b; real test since. The serializer
// prefix-abbreviates (ns1:s), so the content check is a round-trip
// back through parse, not a substring match.
test("l4-core serialize({format:'turtle'}) round-trips the graph",
  async (t) => {
    if (skipUnlessAvailable(t)) return;
    const ttl = await l4core.serialize(
      `<${X}s> <${X}p> <${X}o> .`,
      { format: 'turtle', inputFormat: 'ntriples' });
    assert.match(ttl, /http:\/\/x\//, 'namespace appears in the Turtle');
    const back = await l4core.parse(ttl, { format: 'turtle' });
    const nq = await l4core.serialize(back, { format: 'nquads' });
    assert.deepEqual(sortedLines(nq), [`<${X}s> <${X}p> <${X}o> .`]);
  });

test("l4-core serialize format:'ntriples' answers the default graph and refuses a named graph", async () => {
  const nt = await l4core.serialize(`<${X}s> <${X}p> "c" .`,
    { format: 'ntriples', inputFormat: 'ntriples' });
  assert.deepEqual(sortedLines(nt), [`<${X}s> <${X}p> "c" .`]);
  // N-Triples has no graph term: a quad in a named graph is refused, not flattened.
  await assert.rejects(
    () => l4core.serialize(`<${X}s> <${X}p> "c" <${X}g> .`,
      { format: 'ntriples', inputFormat: 'nquads' }),
    /named graph; use format 'nquads'/);
});

// ---------------------------------------------------------------------
// canonicalize
// ---------------------------------------------------------------------

test('l4-core canonicalize: isomorphic graphs get identical canonical text', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const g1 = `_:a <${X}p> _:b .\n_:b <${X}q> _:a .`;
  const g2 = `_:z <${X}p> _:y .\n_:y <${X}q> _:z .`;
  const c1 = await l4core.canonicalize(g1, { format: 'ntriples' });
  const c2 = await l4core.canonicalize(g2, { format: 'ntriples' });
  assert.equal(c1, c2);
  assert.match(c1, /_:c14n\d/);
});

// ---------------------------------------------------------------------
// closures and checks
// ---------------------------------------------------------------------

const RDFS_DATA =
  `<${X}A> <${RDFS_SUBCLASS}> <${X}B> .\n` +
  `<${X}i> <${RDF_TYPE}> <${X}A> .\n`;

test('l4-core coreRdfsClosure infers a type via subClassOf', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const r = await l4core.coreRdfsClosure(RDFS_DATA, { format: 'ntriples' });
  assert.equal(r.ok, true);
  assert.ok(r.ntriples.includes(`<${X}i> <${RDF_TYPE}> <${X}B> .`),
    'closure contains the rdfs9-derived type triple');
});

test('l4-core rhoDfClosure / rdfsPlusClosure return certified envelopes', async (t) => {
  if (skipUnlessAvailable(t)) return;
  // Same contract as index.js: {ok, ntriples} — the raw certified
  // result the theorem registry talks about, not a Dataset.
  const rho = await l4core.rhoDfClosure(RDFS_DATA, { format: 'ntriples' });
  assert.equal(rho.ok, true);
  assert.equal(typeof rho.ntriples, 'string');
  const plus = await l4core.rdfsPlusClosure(RDFS_DATA, { format: 'ntriples' });
  assert.equal(plus.ok, true);
  assert.equal(typeof plus.ntriples, 'string');
  assert.ok(plus.ntriples.includes(`<${X}i> <${RDF_TYPE}> <${X}B> .`));
});

test('l4-core coreRdfsCheck / rhoDfFragmentCheck report booleans', async (t) => {
  if (skipUnlessAvailable(t)) return;
  const inFrag = await l4core.coreRdfsCheck(
    `<${X}A> <${RDFS_SUBCLASS}> <${X}B> .`, { format: 'ntriples' });
  assert.equal(inFrag.ok, true);
  assert.equal(typeof inFrag.fragment, 'boolean');
  assert.equal(inFrag.fragment, true);
  const alias = await l4core.rhoDfFragmentCheck(
    `<${X}A> <${RDFS_SUBCLASS}> <${X}B> .`, { format: 'ntriples' });
  assert.equal(alias.fragment, true);
});

test("l4-core owlClosure mode 'OWL-RL' returns a Dataset superset", async (t) => {
  if (skipUnlessAvailable(t)) return;
  const ds = await l4core.owlClosure(RDFS_DATA, 'OWL-RL', { format: 'ntriples' });
  assert.equal(ds.constructor.name, 'Dataset');
  assert.ok(ds.size >= 2, 'closure keeps the input triples');
  const nq = await l4core.serialize(ds, { format: 'nquads' });
  assert.ok(sortedLines(nq).includes(`<${X}i> <${RDF_TYPE}> <${X}B> .`));
});

// ---------------------------------------------------------------------
// OWL DL consistency / entailment (three-valued; formal/lean4 issue 586)
// ---------------------------------------------------------------------

const OWL_NS = 'http://www.w3.org/2002/07/owl#';
const SUBCLASS_NT =
  `<${X}a> <${RDF_TYPE}> <${X}C> .\n` +
  `<${X}C> <${RDFS_SUBCLASS}> <${X}D> .\n`;
// A ⊑ ∃p.A keeps the tableau expansion changing, so a fuel-1 budget
// runs out mid-search — the fixture for the null verdict.
const CYCLIC_NT =
  `<${X}i> <${RDF_TYPE}> <${X}A> .\n` +
  `<${X}A> <${RDFS_SUBCLASS}> _:r .\n` +
  `_:r <${OWL_NS}onProperty> <${X}p> .\n` +
  `_:r <${OWL_NS}someValuesFrom> <${X}A> .\n`;

test('l4-core owlIsConsistent: true / false / null (budget-out)', async (t) => {
  if (await skipUnlessOps(t, 'owlIsConsistent')) return;
  const yes = await l4core.owlIsConsistent(SUBCLASS_NT, { format: 'ntriples' });
  assert.equal(yes.consistent, true);
  assert.equal(yes.reason, undefined);
  const no = await l4core.owlIsConsistent(
    `<${X}i> <${RDF_TYPE}> <${OWL_NS}Nothing> .`, { format: 'ntriples' });
  assert.equal(no.consistent, false);
  assert.match(no.reason, /contradiction/);
  const unk = await l4core.owlIsConsistent(CYCLIC_NT,
    { format: 'ntriples', fuel: 1 });
  assert.equal(unk.consistent, null);
  assert.match(unk.reason, /budget-out.*fuel 1 /);
  // The same graph at the default budget saturates under the
  // witness-depth cap: null was the budget speaking, not the graph.
  const settled = await l4core.owlIsConsistent(CYCLIC_NT, { format: 'ntriples' });
  assert.equal(settled.consistent, true);
});

test('l4-core owlEntails: closure yes / refutation no / budget-out null', async (t) => {
  if (await skipUnlessOps(t, 'owlEntails')) return;
  const yes = await l4core.owlEntails(
    SUBCLASS_NT, `<${X}a> <${RDF_TYPE}> <${X}D> .`, { format: 'ntriples' });
  assert.equal(yes.entailed, true);
  assert.equal(yes.via, 'closure');
  const no = await l4core.owlEntails(
    SUBCLASS_NT, `<${X}a> <${RDF_TYPE}> <${X}Zebra> .`, { format: 'ntriples' });
  assert.equal(no.entailed, false);
  assert.equal(no.via, 'refutation');
  assert.match(no.reason, /model/);
  const unk = await l4core.owlEntails(
    CYCLIC_NT, `<${X}a> <${RDF_TYPE}> <${X}Zebra> .`,
    { format: 'ntriples', fuel: 1 });
  assert.equal(unk.entailed, null);
  assert.equal(unk.via, 'refutation');
  assert.match(unk.reason, /budget-out/);
});

// ---------------------------------------------------------------------
// clParse — Common Logic Interchange Format (ISO/IEC 24707:2018) text,
// with the IKL `that`-operator extension. Lean-only: formal/fstar has
// no CL/IKL parser (see select.js's capability table for the
// consequence). `pureCL` is a DIALECT flag, not a validity signal.
// ---------------------------------------------------------------------

const PURE_CL_TEXT = "(uttered Bram 'I saw Jon watching Foxworth by the nut tree')";
const IKL_TEXT =
  "(witnessed Clud (that (saw Jon (that (cached Foxworth 'the beech hollow')))))";

test('l4-core clParse: pureCL true for CL text with no `that` operator', async (t) => {
  if (await skipUnlessOps(t, 'clParse')) return;
  const r = await l4core.clParse(PURE_CL_TEXT);
  assert.equal(r.ok, true);
  assert.equal(r.sentences, 1);
  assert.equal(r.pureCL, true);
  assert.equal(r.normalized, PURE_CL_TEXT);
});

test('l4-core clParse: pureCL false once the text uses IKL\'s `that` operator', async (t) => {
  if (await skipUnlessOps(t, 'clParse')) return;
  const r = await l4core.clParse(IKL_TEXT);
  assert.equal(r.ok, true);
  assert.equal(r.sentences, 1);
  assert.equal(r.pureCL, false);
  assert.equal(r.normalized, IKL_TEXT);
});

test('l4-core clParse: rejects a `that`-term used where a proposition is required', async (t) => {
  if (await skipUnlessOps(t, 'clParse')) return;
  // '(that S)' denotes a TERM (the proposition-as-object); using it
  // bare as a sentence needs the extra parens IKL's GUIDE spells out --
  // '((that S))' asserts it. The engine's message says exactly this.
  await assert.rejects(
    () => l4core.clParse(
      "(that (saw Jon (that (cached Foxworth 'the beech hollow'))))"),
    /'\(that S\)' is a term; to assert the proposition write '\(\(that S\)\)'/);
});

test('l4-core clParse: rejects a non-string argument', async (t) => {
  if (skipUnlessAvailable(t)) return;
  await assert.rejects(() => l4core.clParse(42), TypeError);
});

// ---------------------------------------------------------------------
// clSerialize / clAlphaNorm / clNormalize -- wired alongside clParse
// (owner instruction, 2026-08-26: "wire into js functional api").
// Lean-only, same reason as clParse. `clFiniteSat` is deliberately NOT
// wired here (see lib/api.js's comment next to the other three).
// ---------------------------------------------------------------------

test('l4-core clSerialize: round-trips CLIF text, surfacing roundTripProved as false (not hidden or defaulted)', async (t) => {
  if (await skipUnlessOps(t, 'clSerialize')) return;
  const r = await l4core.clSerialize(PURE_CL_TEXT);
  assert.equal(r.ok, true);
  assert.equal(r.sentences, 1);
  assert.equal(typeof r.clif, 'string');
  // roundTripProved is a real field, present and exactly `false` --
  // `clif_roundTrip` (CL/ClifAdequacy.lean) is an OPEN lemma.
  assert.equal('roundTripProved' in r, true);
  assert.equal(r.roundTripProved, false);
});

test('l4-core clSerialize: rejects a non-string argument', async (t) => {
  if (skipUnlessAvailable(t)) return;
  await assert.rejects(() => l4core.clSerialize(42), TypeError);
});

test('l4-core clAlphaNorm: two alpha-variant sentences normalise to the same text', async (t) => {
  if (await skipUnlessOps(t, 'clAlphaNorm')) return;
  const a = await l4core.clAlphaNorm('(forall (x) (Boy x))');
  const b = await l4core.clAlphaNorm('(forall (zz) (Boy zz))');
  assert.equal(a.ok, true);
  assert.equal(b.ok, true);
  assert.equal(a.clif, b.clif);
});

test('l4-core clAlphaNorm: rejects a non-string argument', async (t) => {
  if (skipUnlessAvailable(t)) return;
  await assert.rejects(() => l4core.clAlphaNorm(42), TypeError);
});

test('l4-core clNormalize: a `that`-term reduces to a head/tail pair, with preserves and noIntrusion surfaced', async (t) => {
  if (await skipUnlessOps(t, 'clNormalize')) return;
  const r = await l4core.clNormalize('(P (that (Q a)))');
  assert.equal(r.ok, true);
  assert.equal(r.thatCount, 1);
  assert.ok(Array.isArray(r.head) && r.head.length === 1);
  assert.ok(Array.isArray(r.tail) && r.tail.length === 1);
  // The reduction preserves SATISFIABILITY, not equivalence -- this
  // field says so rather than leaving the caller to assume equivalence.
  assert.equal(r.preserves, 'satisfiability');
  // noIntrusion IS the proof hypothesis CL.noIntrSs decides, not a
  // paraphrase of it; this simple non-quantified case holds.
  assert.equal(r.noIntrusion, true);
});

test('l4-core clNormalize: rejects a non-string argument', async (t) => {
  if (skipUnlessAvailable(t)) return;
  await assert.rejects(() => l4core.clNormalize(42), TypeError);
});

// ---------------------------------------------------------------------
// capabilities honesty
// ---------------------------------------------------------------------

test('l4-core capabilities: entry, shacl, tableau true (issue 713 stage 3)', async (t) => {
  if (await skipUnlessOps(t, 'tableauMaterialise', 'shaclValidate')) return;
  const caps = await l4core.capabilities();
  assert.equal(caps.entry, true);
  assert.equal(caps.shacl, true);
  assert.equal(caps.tableau, true);
  assert.equal(caps.owlClosure, true);
  assert.equal(caps.update, true);
  assert.equal(caps.canonicalize, true);
});

// Expected failure (skills/test-suites § Expected failures): the Lean
// parsers have no recovery mode, so parse(..., {lenient:true}) cannot skip
// a bad statement and report it.
xfail('l4-core parse({lenient:true}) keeps good statements and reports the bad one', LENIENT_ISSUE, async () => {
  const ttl = `<${X}a> <${X}p> "1" .\n<${X}b> <${X}p> .\n<${X}c> <${X}p> "3" .\n`;
  const caps = await l4core.capabilities();
  assert.equal(caps.parseDiagnostics, true);
  const ds = await l4core.parse(ttl, { format: 'turtle', lenient: true });
  assert.equal(ds.size, 2);
  assert.equal(ds.diagnostics.length, 1);
  assert.equal(ds.diagnostics[0].line, 2);
});

// ---------------------------------------------------------------------
// error pins — the exact texts api.js produces on this driver
// ---------------------------------------------------------------------

test('l4-core shaclValidate: a shapes graph with no shapes validates every data graph', async () => {
  // The shapes graph declares no sh:NodeShape or sh:PropertyShape, so
  // there is no focus node and the report conforms (SHACL 3.1 / 5).
  const r = await l4core.shaclValidate(`<${X}s> <${X}p> "c" .`,
    `<${X}sh> <${X}q> "s" .`, { format: 'ntriples' });
  assert.equal(r.conforms, true);
  assert.ok(r.report instanceof l4core.Dataset);
});

test("l4-core query({entail:'RDFS'}) answers over the RDFS closure", async () => {
  const rows = await l4core.query(
    `<${X}s> <${RDF_TYPE}> <${X}C> .\n<${X}C> <${RDFS_SUBCLASS}> <${X}D> .\n`,
    `SELECT ?c WHERE { <${X}s> <${RDF_TYPE}> ?c }`,
    { format: 'ntriples', entail: 'RDFS' });
  const classes = rows.map((r) => r.get('c').value);
  assert.ok(classes.includes(`${X}D`), classes.join(' '));
});

test('l4-core missing op: an operation the wasm lacks rejects naming the op', async () => {
  // parseDocument ({lenient:true}) is not in this wasm's op table.
  await assert.rejects(
    () => l4core.parse(`<${X}s> <${X}p> "c" .`, { format: 'ntriples', lenient: true }),
    /parseDocument.*no dispatch op/);
});

// ---------------------------------------------------------------------
// multi-document blank-node scoping
// ---------------------------------------------------------------------

// Two documents each using _:b0 must stay two nodes at merge, as the F*
// engine's per-document renaming (RDF.Dataset.Merge.rename_dataset_bnodes)
// keeps them. The Lean engine's IO entry applies the same renaming to every
// document it parses (Wasm/Ops/Parse.lean, parseToDatasetJsonScoped).
test('l4-core multi-document merge keeps blank-node labels document-scoped',
  async (t) => {
    if (skipUnlessAvailable(t)) return;
    if (await skipUnlessOps(t, 'parseToDatasetJson')) return;
    const d1 = `_:b0 <${X}p> "one" .`;
    const d2 = `_:b0 <${X}p> "two" .`;
    const rows = await l4core.query([d1, d2],
      `SELECT DISTINCT ?s WHERE { ?s <${X}p> ?o }`, { format: 'turtle' });
    assert.equal(rows.length, 2,
      'two documents each with _:b0 must contribute two distinct nodes');
  });

// ---------------------------------------------------------------------
// dataset handles (issues #344/#680/#681 on lib/api.js's side; the
// Lean engine's own gap is https://github.com/danbri/factoidal/issues/685)
// ---------------------------------------------------------------------

test('l4-core dataset handle: open, query, update, serialize, close', async (t) => {
  if (skipUnlessAvailable(t)) return;
  if (await skipUnlessOps(t, 'datasetOpen')) return;
  const h = await l4core.openDataset(JOIN_NT, { format: 'ntriples' });
  assert.equal(h.size, 4);
  assert.equal(h.closed, false);
  const rows = await h.query(JOIN_Q);
  assert.equal(rows.length, 2);
  assert.deepEqual(rowMultiset(rows), rowMultiset(
    await l4core.query(JOIN_NT, JOIN_Q, { format: 'ntriples' })));

  await h.update(
    `INSERT DATA { <${X}carol> <${X}name> "Carol" . ` +
    `<${X}carol> <${X}age> "40"^^<${XSD_INT}> . }`);
  assert.equal(h.size, 6);
  const rows2 = await h.query(JOIN_Q);
  assert.equal(rows2.length, 3);

  const nq = await h.serialize({ format: 'nquads' });
  assert.match(nq, /carol/);

  await h.close();
  assert.equal(h.closed, true);
  await assert.rejects(() => h.query(JOIN_Q), /closed/);
});

// The four envelope features of https://github.com/danbri/factoidal/issues/685.
// They were expected-failure cases until the Lean engine gained them
// (Wasm/Ops/Parse.lean, Wasm/Ops/Handles.lean); each is now a real assertion,
// and test/l4-parity-2.test.js holds the wider cases.

test('dataset-handle parse error carries a line/column position', async (t) => {
  if (skipUnlessAvailable(t)) return;
  if (await skipUnlessOps(t, 'datasetOpen')) return;
  await assert.rejects(
    () => l4core.openDataset('this is not turtle', { format: 'turtle' }),
    (err) => {
      assert.equal(err.name, 'ParseError');
      assert.equal(err.line, 1, 'a positioned error (a line member), same as the F* engine');
      assert.equal(typeof err.column, 'number');
      assert.equal(typeof err.offset, 'number');
      assert.equal(err.format, 'turtle');
      return true;
    });
});

test('dataset handle records prefixes from a Turtle open()', async (t) => {
  if (skipUnlessAvailable(t)) return;
  if (await skipUnlessOps(t, 'datasetOpen')) return;
  const h = await l4core.openDataset(`@prefix ex: <${X}> .\nex:s ex:p ex:o .`, { format: 'turtle' });
  try {
    assert.deepEqual({ ...h.prefixes }, { ex: X });
  } finally {
    await h.close();
  }
});

test('dataset handle serialize({format:"turtle", literalShorthand:false}) is supported', async (t) => {
  if (skipUnlessAvailable(t)) return;
  if (await skipUnlessOps(t, 'datasetSerializeWith')) return;
  const h = await l4core.openDataset(`<${X}s> <${X}p> "1"^^<${XSD_INT}> .`, { format: 'ntriples' });
  try {
    const ttl = await h.serialize({ format: 'turtle', literalShorthand: false });
    assert.match(ttl, /"1"\^\^xsd:integer/, `expected the quoted form; got: ${ttl}`);
  } finally {
    await h.close();
  }
});

test('dataset handle Turtle output prints small integers bare (literal shorthand) by default', async (t) => {
  if (skipUnlessAvailable(t)) return;
  if (await skipUnlessOps(t, 'datasetOpen')) return;
  const h = await l4core.openDataset(`<${X}s> <${X}p> "1"^^<${XSD_INT}> .`, { format: 'ntriples' });
  try {
    const ttl = await h.serialize({ format: 'turtle' });
    assert.ok(!ttl.includes('^^'),
      `expected the integer to print bare, same as the F* engine; got: ${ttl}`);
    assert.match(ttl, / 1 \./);
  } finally {
    await h.close();
  }
});
