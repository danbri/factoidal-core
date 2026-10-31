// Public artifact gate: requires a rebuilt engine; an older engine is a failure.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as core from '../index.mjs';
const query='SELECT ?name WHERE { <urn:person> <urn:name> ?name }';
const data = value => `<urn:person> <urn:name> "${value}" .`;
const options={dataFormat:'turtle',output:'xml-report'};

test('checked XML report preserves accepted text and feeds the actual XQuery consumer',async()=>{
  for(const name of ['Mina & <Chen>', '李明 · Zoë', 'line\\nfeed\\ttab\\rcarriage']) {
    const source=data(name);
    const report=await core.queryRaw(source,query,options);
    assert.equal(report.kind,'xml');
    assert.equal(report.xml,await core.queryRaw(source,query,{...options,output:'xml'}));
    const result=await core.xqueryEval('count(/*)',report.xml);
    assert.equal(result.xml,'1');
  }
});

test('XML refusal is explicit on every public query surface and never changes RDF values',async()=>{
  for(const character of ['\\u0000','\\u0001','\\u000B','\\uFFFE','\\uFFFF']) {
    const source=data('Mina'+character+'Chen');
    const dataset=await core.parse(source,{format:'turtle'});
    try {
      const before=await dataset.serialize({format:'ntriples'});
      for(const report of [await core.queryRaw(source,query,options),
        await core.query(dataset,query,{output:'xml-report'}),
        await dataset.query(query,{output:'xml-report'})]) {
        assert.equal(report.kind,'diagnostic');
        assert.equal(report.code,'XML_ADMISSION_REFUSED');
        assert.match(report.message,/invalid character/);
        assert.ok(!Object.hasOwn(report,'xml'));
      }
      await assert.rejects(core.queryRaw(source,query,{...options,output:'xml'}),/XML_ADMISSION_REFUSED/);
      await assert.rejects(dataset.query(query,{output:'xml'}),/XML_ADMISSION_REFUSED/);
      assert.equal(await dataset.serialize({format:'ntriples'}),before);
      assert.equal((await dataset.query(query)).length,1);
    } finally { dataset.dispose(); }
  }
});

test('empty SELECT and ASK admit XML; syntax errors and graph results remain errors',async()=>{
  for(const q of ['SELECT ?x WHERE { ?x <urn:missing> ?y }','ASK {}']) {
    const report=await core.queryRaw('',q,options);
    assert.equal(report.kind,'xml');
    assert.equal((await core.xqueryEval('count(/*)',report.xml)).xml,'1');
  }
  await assert.rejects(core.queryRaw('','SELECT WITHOUT',options),/query does not parse/);
  await assert.rejects(core.queryRaw('', 'CONSTRUCT {} WHERE {}',options),/answer is a graph/);
});

test('query node explicit outputs use transport wires and retain unproved status',async()=>{
  const dataset=await core.parse(data('Mina & <Chen>'),{format:'turtle'});
  try {
    for(const q of [query,'ASK {}']) {
      for(const output of ['xml-report','json','xml','table']) {
        const node=await core.node('shippedEvaluator',{query:q,output});
        assert.equal(node.wireOut,['xml-report','json'].includes(output)?'JSON':'String');
        assert.equal(node.status,'unproved');
        const run=await core.run(node,dataset,{unchecked:true});
        assert.equal(run.proved,false);
        assert.equal(run.evidence.at(-1).checked,false);
        if(output==='xml-report') assert.equal(run.graph.kind,'xml');
        else if(output==='json') assert.equal(typeof run.graph,'object');
        else assert.equal(typeof run.graph,'string');
      }
      const plain=await core.node('shippedEvaluator',{query:q});
      assert.equal(plain.wireOut,q===query?'Table':'Answer');
      assert.equal(plain.status,'proved');
      const run=await core.run(plain,dataset,{unchecked:true});
      assert.equal(q===query?Array.isArray(run.graph):typeof run.graph==='boolean',true);
    }
    const graphQuery='CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }';
    const plain=await core.node('shippedEvaluator',{query:graphQuery});
    assert.equal(plain.wireOut,'Dataset'); assert.equal(plain.status,'proved');
    for(const output of ['xml-report','json','xml'])
      await assert.rejects(core.node('shippedEvaluator',{query:graphQuery,output}),/answer is a graph/);
    const rendered=await core.node('shippedEvaluator',{query:graphQuery,output:'ntriples'});
    assert.equal(rendered.wireOut,'String'); assert.equal(rendered.status,'unproved');
    assert.equal(typeof (await core.run(rendered,dataset,{unchecked:true})).graph,'string');
  } finally { dataset.dispose(); }
});

test('actual compositor routes XML-invalid RDF to a diagnostic before a broken stylesheet',async()=>{
  const {runPipeline,DEFAULTS}=await import('../../../docs/web/hub/data-compositor/pipeline.mjs');
  const events=[];
  const result=await runPipeline(core,{
    turtle:DEFAULTS.turtle.replace('Mina Chen','Mina\\u0001Chen'),
    stylesheet:'<intentionally-broken',
  },e=>events.push(e));
  assert.equal(result.kind,'diagnostic'); assert.equal(result.html,null);
  assert.equal(result.diagnostic.code,'XML_ADMISSION_REFUSED');
  assert.equal(result.counts.selected,null);
  assert.ok(!events.some(e=>e.id==='xslt'&&e.status==='running'));
  assert.equal(result.stages.find(s=>s.id==='xml').evidence.admission.accepted,false);
});
