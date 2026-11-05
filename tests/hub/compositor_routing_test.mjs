import test from 'node:test';
import assert from 'node:assert/strict';
import { runPipeline } from '../../docs/web/hub/data-compositor/pipeline.mjs';
const core = await import(process.env.FACTOIDAL_COMPOSITOR_TEST_ENGINE || '@factoidal/core');

// Host routing controls: the real RDF/query pipeline runs, but the XML report
// transport is deliberately injected. These do NOT certify Lean admission.
function withReport(report) {
  const calls = [];
  return { calls, api: { ...core,
    engineTables: async () => ({ ...(await core.engineTables()), queryOutputs: ['xml-report'] }),
    queryRaw: async (...args) => {
      calls.push('queryRaw'); assert.equal(args[2].output, 'xml-report');
      return typeof report === 'function' ? report(...args) : report;
    },
    node: async (name, params) => { calls.push(name); return core.node(name, params); },
  } };
}

test('refused XML routes to text diagnostic and never invokes either XML consumer', async () => {
  const message = '<script>not markup</script> invalid XML character';
  const {api,calls} = withReport({kind:'diagnostic',code:'XML_ADMISSION_REFUSED',message});
  const events=[];
  // A malformed stylesheet would fail if the unselected branch ran.
  const result=await runPipeline(api,{stylesheet:'<broken'},event=>events.push(event));
  assert.equal(result.kind,'diagnostic'); assert.equal(result.html,null);
  assert.equal(result.diagnostic.message,message);
  assert.equal(result.proved,false);
  assert.equal(result.stages.find(s=>s.id==='xml').evidence.admission.accepted,false);
  assert.equal(calls.filter(x=>x==='queryRaw').length,1);
  assert.ok(!calls.includes('xqueryEval')); assert.ok(!calls.includes('xslt4Transform'));
  assert.deepEqual(events.filter(e=>e.status==='skipped').map(e=>e.id),['xslt','html']);
  assert.equal(events.at(-1).id,'report'); assert.equal(events.at(-1).status,'done');
  assert.equal(result.counts.selected,null); // unknown, not a fictitious empty answer
});

test('accepted XML is shared unchanged and routes only to the HTML branch',async()=>{
  let exact;
  const {api,calls}=withReport(async(data,query,options)=>{
    exact=await core.queryRaw(data,query,{...options,output:'xml'});
    return {kind:'xml',xml:exact};
  });
  const result=await runPipeline(api);
  assert.equal(result.stages.find(s=>s.id==='xml').evidence.admission.accepted,true);
  assert.equal(result.kind,'html'); assert.match(result.html,/Mina Chen/);
  assert.equal(result.stages.find(s=>s.id==='xml').text,exact);
  assert.equal(result.stages.find(s=>s.id==='diagnostic').status,'skipped');
  assert.equal(calls.filter(x=>x==='queryRaw').length,1);
  assert.equal(calls.filter(x=>x==='xqueryEval').length,1);
  assert.equal(calls.filter(x=>x==='xslt4Transform').length,1);
});

test('malformed reports and query errors are not converted into admission refusals',async()=>{
  for(const report of [null,{kind:'xml'},{kind:'diagnostic',code:'OTHER',message:'bad'}]) {
    const {api,calls}=withReport(report);
    await assert.rejects(runPipeline(api), /Unexpected Lean XML admission report/);
    assert.ok(!calls.includes('xslt4Transform'));
  }
  const error=new Error('query execution failed');
  const {api}=withReport(()=>{throw error;});
  await assert.rejects(runPipeline(api),e=>e===error&&e.stageId==='filter');
});
