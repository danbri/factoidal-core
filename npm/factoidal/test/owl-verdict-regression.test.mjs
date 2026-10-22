import test from 'node:test';
import assert from 'node:assert/strict';
import { owlIsConsistent, owlEntails } from '../index.mjs';

const OWL = 'http://www.w3.org/2002/07/owl#';
const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const RDFS = 'http://www.w3.org/2000/01/rdf-schema#';
const same = (a, b) => `<urn:${a}> <${OWL}sameAs> <urn:${b}> .\n`;
const different = (a, b) => `<urn:${a}> <${OWL}differentFrom> <urn:${b}> .\n`;
const options = { format: 'ntriples' };

for (const [name, input] of [
  ['sameAs and differentFrom', same('a', 'b') + different('a', 'b')],
  ['reversed differentFrom', same('a', 'b') + different('b', 'a')],
  ['self differentFrom', different('a', 'a')],
  ['transitive sameAs and differentFrom', same('a', 'b') + same('b', 'c') + different('a', 'c')],
]) {
  test(`OWL consistency rejects ${name}`, async () => {
    const answer = await owlIsConsistent(input, options);
    assert.equal(answer.consistent, false);
    assert.match(answer.reason, /contradiction/);
  });
}

for (const [name, input] of [
  ['sameAs alone', same('a', 'b')],
  ['differentFrom alone', different('a', 'b')],
  ['ordinary class membership', `<urn:a> <${RDF}type> <urn:C> .`],
]) {
  test(`OWL consistency does not claim a model for ${name}`, async () => {
    const answer = await owlIsConsistent(input, options);
    assert.equal(answer.consistent, null);
    assert.match(answer.reason, /incomplete-search/);
    assert.doesNotMatch(answer.reason, /budget-out/);
  });
}

test('OWL consistency catches a negative object property assertion', async () => {
  const input = `<urn:a> <urn:p> <urn:b> .\n` +
    `_:n <${RDF}type> <${OWL}NegativePropertyAssertion> .\n` +
    `_:n <${OWL}sourceIndividual> <urn:a> .\n` +
    `_:n <${OWL}assertionProperty> <urn:p> .\n` +
    `_:n <${OWL}targetIndividual> <urn:b> .\n`;
  assert.equal((await owlIsConsistent(input, options)).consistent, false);
});

test('OWL entailment still returns a closure consequence', async () => {
  const premise = `<urn:a> <${RDF}type> <urn:C> .\n` +
    `<urn:C> <${RDFS}subClassOf> <urn:D> .\n`;
  const answer = await owlEntails(premise, `<urn:a> <${RDF}type> <urn:D> .`, options);
  assert.equal(answer.entailed, true);
  assert.equal(answer.via, 'closure');
});

test('OWL entailment does not turn a quiescent search into a countermodel', async () => {
  const answer = await owlEntails(
    `<urn:a> <${RDF}type> <urn:C> .`,
    `<urn:a> <${RDF}type> <urn:D> .`, options);
  assert.equal(answer.entailed, null);
  assert.equal(answer.via, 'refutation');
  assert.match(answer.reason, /incomplete-search/);
});

test('OWL entailment reports an unsupported negation as indeterminate', async () => {
  const answer = await owlEntails('', '<urn:a> <urn:p> "value" .', options);
  assert.equal(answer.entailed, null);
  assert.equal(answer.via, 'closure');
  assert.match(answer.reason, /unsupported-conclusion/);
});

test('OWL budget exhaustion remains distinct from incomplete search', async () => {
  const premise = `<urn:i> <${RDF}type> <urn:A> .\n` +
    `<urn:A> <${RDFS}subClassOf> _:r .\n` +
    `_:r <${OWL}onProperty> <urn:p> .\n` +
    `_:r <${OWL}someValuesFrom> <urn:A> .\n`;
  const answer = await owlIsConsistent(premise, { ...options, fuel: 1 });
  assert.equal(answer.consistent, null);
  assert.match(answer.reason, /budget-out.*fuel 1 /);
});

// C and D name both classes and individuals. Their individual denotations
// can agree while C's class extension contains x and D's is empty.
const punning = `<urn:C> <${RDF}type> <${OWL}Class> .\n` +
  `<urn:C> <${RDF}type> <${OWL}NamedIndividual> .\n` +
  `<urn:D> <${RDF}type> <${OWL}Class> .\n` +
  `<urn:D> <${RDF}type> <${OWL}NamedIndividual> .\n` +
  same('C', 'D') + `<urn:C> <${OWL}disjointWith> <urn:D> .\n` +
  `<urn:x> <${RDF}type> <${OWL}NamedIndividual> .\n` +
  `<urn:x> <${RDF}type> <urn:C> .\n`;

test('OWL Direct Semantics punning is indeterminate before RDF closure', async () => {
  const answer = await owlIsConsistent(punning, options);
  assert.equal(answer.consistent, null);
  assert.match(answer.reason, /unsupported-punning/);
});

test('OWL entailment does not substitute sameAs into a punned class name', async () => {
  const answer = await owlEntails(punning, `<urn:x> <${RDF}type> <urn:D> .`, options);
  assert.equal(answer.entailed, null);
  assert.match(answer.reason, /unsupported-punning/);
});

test('OWL punning across premise and conclusion is indeterminate', async () => {
  const answer = await owlEntails(same('C', 'D'), `<urn:x> <${RDF}type> <urn:C> .`, options);
  assert.equal(answer.entailed, null);
  assert.match(answer.reason, /unsupported-punning/);
});
