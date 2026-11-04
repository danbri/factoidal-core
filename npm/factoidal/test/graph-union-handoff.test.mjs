// Public adapter/link regressions. Finite artifact behavior, not browser proof.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as core from '../index.mjs';

test('asDefaultGraph preserves first-occurrence order and collapses cross-graph duplicates', async () => {
  const ds = await core.parse('<urn:a> <urn:p> "A" .\n<urn:b> <urn:p> "B" <urn:g1> .\n<urn:a> <urn:p> "A" <urn:g1> .\n<urn:c> <urn:p> "C" <urn:g2> .', {format:'nquads'});
  const flat = core.asDefaultGraph(ds);
  try {
    assert.deepEqual([...flat].map(q=>q.object.value), ['A','B','C']);
    assert.ok([...flat].every(q=>q.graph.termType==='DefaultGraph'));
    assert.equal(ds.size,4); assert.deepEqual(core.graphs(flat),[]);
  } finally { flat.dispose(); ds.dispose(); }
});

test('projection keeps blank-node identities and literal language distinctions', async () => {
  const ds = await core.parse('_:shared <urn:p> "word"@en <urn:g1> .\n_:shared <urn:p> "word"@fr <urn:g2> .\n_:other <urn:p> <urn:o> <urn:g2> .', {format:'nquads'});
  const flat = core.asDefaultGraph(ds);
  try {
    const before=[...ds], after=[...flat];
    assert.deepEqual(after.map(q=>q.subject.value), before.map(q=>q.subject.value));
    assert.deepEqual(after.map(q=>q.object.language??''), ['en','fr','']);
    assert.equal(new Set(after.map(q=>q.subject.value)).size,2);
    assert.ok(before.every(q=>q.graph.termType==='NamedNode'));
  } finally { flat.dispose(); ds.dispose(); }
});

test('actual merge-to-union-to-registered-RDFS path retains distinct source blank nodes', async () => {
  const text='@prefix ex: <urn:ex:> . @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . ex:Contributor rdfs:subClassOf ex:Person . _:same a ex:Contributor .';
  const left=await core.parse(text,{format:'turtle'}), right=await core.parse(text,{format:'turtle'});
  const owned=[left,right];
  try {
    const merged=await core.datasetMerge(left,right); owned.push(merged);
    const flat=core.asDefaultGraph(merged); owned.push(flat);
    const sourceSubjects=[...flat].filter(q=>q.object.value==='urn:ex:Contributor').map(q=>q.subject.value);
    assert.equal(new Set(sourceSubjects).size,2);
    const result=await core.run(await core.node('rdfsReasoner'),flat); owned.push(result.graph);
    const rows=await core.query(result.graph,'SELECT ?s WHERE { ?s a <urn:ex:Person> }');
    assert.equal(rows.length,2);
    assert.deepEqual(new Set(rows.map(row=>row.get('s').value)),new Set(sourceSubjects));
    // The component's registry evidence is not a proof of this JS composition.
    assert.equal(result.evidence.at(-1).status,'proved');
  } finally { for(const ds of owned.reverse())ds.dispose(); }
});
