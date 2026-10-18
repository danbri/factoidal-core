// RDF 1.2 triple terms in the canonicalisation and reasoning ops
// (https://github.com/danbri/factoidal/issues/873).
//
// RDF 1.2 Semantics: a triple term is a term; it is not asserted. The RDFS
// and OWL 2 RL closures accept it as an opaque object term: the asserted
// triple stays, derivations from asserted triples are made, and nothing is
// derived from the triple inside a triple term. RDFC-1.0 (W3C
// Recommendation 2024) and OWL 2 Mapping to RDF Graphs define no rule for a
// triple term, so canonicalizeToNQuads, owlIsConsistent and owlEntails
// refuse such input with a message that names the missing rule; their
// acceptance is an expected failure that names the issue.
// Design record: docs/designissues/2026-10-18-rdf12-terms-canon-and-closures.md.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const { xfail } = require('./helpers.js');

const ISSUE = 'https://github.com/danbri/factoidal/issues/873';
const RDF_TYPE = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type';
const SUBCLASS = 'http://www.w3.org/2000/01/rdf-schema#subClassOf';
const X = 'http://example.com/';

const TT_IRI = `<${X}z> <${X}says> <<( <${X}s> <${RDF_TYPE}> <${X}C> )>> .\n`;
const TT_BNODE = `<${X}z> <${X}says> <<( _:b1 <${RDF_TYPE}> <${X}C> )>> .\n`;
const DATA =
  TT_IRI + TT_BNODE +
  `<${X}C> <${SUBCLASS}> <${X}D> .\n` +
  `<${X}x> <${RDF_TYPE}> <${X}C> .\n`;

let enginePromise = null;
function engine () {
  if (!enginePromise) enginePromise = require('../index.js').loadEngine();
  return enginePromise;
}

const CLOSURES = [
  ['owlClosure RDFS', (eng) => eng.call('owlClosure', [DATA, 'RDFS']), 'nquads'],
  ['owlClosure OWL-RL', (eng) => eng.call('owlClosure', [DATA, 'OWL-RL']), 'nquads'],
  ['rhoDfClosure', (eng) => eng.call('rhoDfClosure', [DATA]), 'ntriples'],
  ['rdfsPlusClosure', (eng) => eng.call('rdfsPlusClosure', [DATA]), 'ntriples'],
];

for (const [name, run, key] of CLOSURES) {
  test(`${name} accepts a triple term and derives nothing from inside it`, async () => {
    const r = run(await engine());
    assert.equal(r.ok, true, JSON.stringify(r));
    const out = r[key];
    assert.ok(out.includes(`<${X}z> <${X}says> <<( <${X}s> <${RDF_TYPE}> <${X}C> )>> .`),
      'the asserted triple with an IRI-subject triple term is kept');
    assert.ok(out.includes(`<<( _:`), 'the asserted triple with a blank-node triple term is kept');
    assert.ok(out.includes(`<${X}x> <${RDF_TYPE}> <${X}D> .`), 'the asserted derivation is made');
    assert.ok(!out.includes(`<${X}s> <${RDF_TYPE}> <${X}D> .`), 'no s rdf:type D from inside the triple term');
    assert.ok(!out.includes(`<${X}s> <${RDF_TYPE}> <${X}C> .`), 'the triple inside a triple term is not asserted');
  });
}

// `eng.call` throws the error text of an {ok:false} envelope.
test('canonicalizeToNQuads refuses a triple term with the RDFC-1.0 rule named', async () => {
  const eng = await engine();
  assert.throws(() => eng.call('canonicalizeToNQuads', [TT_BNODE]), /RDFC-1\.0.*issues\/873/);
  // An RDF 1.1 dataset is canonicalised as before.
  const r = eng.call('canonicalizeToNQuads', [`_:x <${X}p> <${X}o> .\n`]);
  assert.equal(r.ok, true);
  assert.ok(r.nquads.includes('_:c14n0'));
});

test('owlIsConsistent and owlEntails refuse a triple term with the rule named', async () => {
  const eng = await engine();
  assert.throws(() => eng.call('owlIsConsistent', [DATA, '']), /OWL 2 Mapping to RDF Graphs.*issues\/873/);
  assert.throws(() => eng.call('owlEntails', [DATA, `<${X}x> <${RDF_TYPE}> <${X}D> .\n`, '']),
    /OWL 2 Mapping to RDF Graphs.*issues\/873/);
});

xfail('canonicalizeToNQuads gives canonical labels to blank nodes inside a triple term', ISSUE, async () => {
  const r = (await engine()).call('canonicalizeToNQuads', [TT_BNODE]);
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.ok(r.nquads.includes('<<( _:c14n0 '));
});

xfail('owlIsConsistent decides a graph with a triple term', ISSUE, async () => {
  const r = (await engine()).call('owlIsConsistent', [DATA, '']);
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.equal(r.consistent, true);
});

xfail('owlEntails decides a premise with a triple term', ISSUE, async () => {
  const r = (await engine()).call('owlEntails', [DATA, `<${X}x> <${RDF_TYPE}> <${X}D> .\n`, '']);
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.equal(r.entailed, true);
});

// RDF 1.2 Semantics: the IRIs inside a triple term are transparent, so
// owl:sameAs substitutes inside it (W3C rdf12 rdf-semantics `opaque-iri`,
// superman.ttl). The OWL 2 RL closure applies the OWL 2 Profiles §4.3 rule
// table, whose eq-rep-o replaces a whole object term only.
xfail('owlClosure OWL-RL substitutes owl:sameAs inside a triple term (opaque-iri)', ISSUE, async () => {
  const data =
    `<${X}clark> <${X}reports> <<( <${X}superman> <${X}can> <${X}fly> )>> .\n` +
    `<${X}clark> <http://www.w3.org/2002/07/owl#sameAs> <${X}superman> .\n`;
  const r = (await engine()).call('owlClosure', [data, 'OWL-RL']);
  assert.equal(r.ok, true, JSON.stringify(r));
  assert.ok(r.nquads.includes(`<${X}clark> <${X}reports> <<( <${X}clark> <${X}can> <${X}fly> )>> .`));
});
