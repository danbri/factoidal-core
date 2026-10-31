import test from 'node:test';
import assert from 'node:assert/strict';
import * as core from '@factoidal/core';
import { runPipeline } from '../../docs/web/hub/data-compositor/pipeline.mjs';
import { nodeAssurance, wireAssurance } from '../../docs/web/hub/data-compositor/assurance.mjs';

test('Evidence labels preserve component status and never promote manual wires to proofs', async () => {
  const result=await runPipeline(core);
  const stages=new Map(result.stages.map(stage=>[stage.id,stage]));
  const rdfs=nodeAssurance(stages.get('closure'));
  assert.equal(rdfs.status,stages.get('closure').evidence.status);
  assert.equal(rdfs.checked,stages.get('closure').evidence.checked);
  assert.equal(rdfs.contract,stages.get('closure').evidence.contract);
  assert.equal(rdfs.graphWideProof,false);
  assert.equal(nodeAssurance(stages.get('csvw')).checked,false);
  assert.equal(nodeAssurance(stages.get('filter')).projection.stage,'xqueryEval');
  const merge=wireAssurance('turtle','merge',stages);
  assert.equal(merge.wholeWireProved,false);
  assert.equal(merge.graphWideProof,false);
  assert.equal(merge.checkedSubcomposition.wellTyped,true);
  assert.deepEqual(merge.checkedSubcomposition.issues,[]);
  assert.match(merge.checkedSubcomposition.scope,/adapters remain outside/);
  const filter=wireAssurance('query','filter',stages);
  assert.match(filter.note,/not a Table input wire/);
  assert.equal(filter.checkedSubcomposition,null);
  assert.equal(wireAssurance('xml','xslt',stages).wholeWireProved,false);
  assert.equal(nodeAssurance().status,'not-run');
});
