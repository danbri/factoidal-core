import test from 'node:test';
import assert from 'node:assert/strict';
import {DEFAULTS} from '../../docs/web/hub/data-compositor/fixtures.mjs';
import {pipelineSnapshot,encodePipelineDocument,decodePipelineDocument,MAX_PIPELINE_BYTES} from '../../docs/web/hub/data-compositor/pipeline-document.mjs';
const make=()=>pipelineSnapshot('rdf-to-html','My pipeline',DEFAULTS,[{id:'turtle',x:34,y:65}],{evidence:true});
test('pipeline files round-trip editable source and layout, without credentials or evidence',()=>{
  const doc=pipelineSnapshot('rdf-to-html','My pipeline',{...DEFAULTS,token:'secret',result:{proved:true}},make().layout,{evidence:true});
  assert.deepEqual(decodePipelineDocument(encodePipelineDocument(doc),'rdf-to-html'),make());
  assert.ok(!encodePipelineDocument(doc).includes('secret'));
  assert.ok(!Object.hasOwn(doc,'result'));
});
test('invalid/foreign documents fail without producing a partial loaded recipe',()=>{
  for(const mutate of [d=>d.version=9,d=>d.recipe='execute-javascript',d=>d.inputs.query=4,d=>d.inputs.minScore='Infinity',d=>d.inputs.token='secret',d=>d.credentials={},d=>d.layout[0].x=-1,d=>d.layout.push({...d.layout[0]}),d=>d.view.evidence='yes']){
    const doc=make();mutate(doc);assert.throws(()=>decodePipelineDocument(JSON.stringify(doc)),/Pipeline document/);
  }
  assert.throws(()=>decodePipelineDocument('{'));
  assert.throws(()=>decodePipelineDocument(' '.repeat(MAX_PIPELINE_BYTES+1)),/2 MiB/);
  assert.throws(()=>decodePipelineDocument(JSON.stringify({...make(),__proto__:null,extra:1})),/unknown/);
  assert.throws(()=>decodePipelineDocument(JSON.stringify(make()),'xml-signature'),/open this file/);
});
test('signature recipe saves source/stylesheet/example, not keys or verification results',()=>{
  const doc=pipelineSnapshot('xml-signature','Coverage',{source:'<a/>',stylesheet:'<xsl/>',mode:'preprocessed',publicKey:'ignored'});
  assert.deepEqual(decodePipelineDocument(encodePipelineDocument(doc)).inputs,{source:'<a/>',stylesheet:'<xsl/>',mode:'preprocessed'});
});
