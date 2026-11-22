// Run the Hub application's public GDSL recipe on the shipping Lean/Wasm.
// --require-gpu also requires actual WebGPU dispatch and exact CPU agreement.
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {loadEngine} from '../npm/factoidal/index.mjs';
import {resolveEngine} from '../npm/factoidal/bin/engine.mjs';
import {createPVGraphWasm,runPVGraph,createGsslResidentSession,example,listExamples}
  from '../npm/factoidal/gdsl.mjs';
import {buildSignalMixer} from '../docs/web/hub/gdsl-app/example.mjs';
import {sourceProvenance} from './pvgraph-evidence-provenance.mjs';

const requireGpu=process.argv.includes('--require-gpu');
const root=fileURLToPath(new URL('../',import.meta.url));
const head=execFileSync('git',['rev-parse','HEAD'],{cwd:root,encoding:'utf8'}).trim();
const loader=resolveEngine();
const report={schema:'gdsl-app-public-api-v1',status:'fail',requireGpu,
  provenance:sourceProvenance(head,loader.replace(/\.js$/,'.wasm')),
  runtime:{loader},cases:[],
  assurance:'Observed results from the public API and installed Wasm; device/compiler correctness and physical GPU speed are separate claims.'};
const record=(name,details={})=>report.cases.push({name,correct:true,...details});
let session=null;

const fixtures=[
  {name:'normal',gain:3,
    bindings:{a:[2,3,5,7,11,13,17,19],b:[1,4,1,5,9,2,6,5]},
    expected:{mixed:[7,13,16,26,42,41,57,62],cumulative:[7,20,36,62,104,145,202,264]}},
  {name:'empty',gain:3,bindings:{a:[],b:[]},expected:{mixed:[],cumulative:[]}},
  {name:'high-u32',gain:2,
    bindings:{a:[0xffffffff,0x80000000,0,1],b:[2,0xffffffff,0xffffffff,0xffffffff]},
    expected:{mixed:[0,0xffffffff,0xffffffff,1],cumulative:[0,0xffffffff,0xfffffffe,0xffffffff]}},
  ...[65,4097].map(n=>({name:'scan-'+n,gain:3,
    bindings:{a:new Uint32Array(n).fill(1),b:new Uint32Array(n).fill(2)},
    expected:{mixed:Array(n).fill(5),cumulative:Array.from({length:n},(_,i)=>5*(i+1))}}))
];

try{
  const engine=await loadEngine();
  const ops=new Set(engine.call('ops',[]).ops);
  for(const op of ['pvgraphBuild','pvgraphAdmit','pvgraphEvaluate','pvgraphGpuPlan'])
    assert.ok(ops.has(op),'installed runtime exposes '+op);
  record('installed-runtime-exports');

  if(requireGpu){
    const adapter=await globalThis.navigator?.gpu?.requestAdapter();
    assert.ok(adapter,'--require-gpu needs an actual WebGPU adapter');
    const info=adapter.info??{};
    report.adapter=Object.fromEntries(['vendor','architecture','device','description','isFallbackAdapter']
      .map(name=>[name,info[name]??null]));
    report.isSoftwareAdapter=info.isFallbackAdapter===true||
      /swiftshader|llvmpipe|lavapipe|software/i.test([info.vendor,info.device,info.description].join(' '));
    session=await createGsslResidentSession({adapter,byteBudget:16*1024*1024,inspectMaxWords:16384});
  }

  for(const fixture of fixtures){
    const {builder,pvgraph}=await buildSignalMixer({createPVGraphWasm,loadEngine,gain:fixture.gain});
    assert.deepEqual(await builder.admit(pvgraph),pvgraph);
    const reference=await builder.evaluate(pvgraph,fixture.bindings);
    assert.deepEqual(reference,fixture.expected,fixture.name+' independently specified answer');
    record('cpu-'+fixture.name,{wordsPerInput:fixture.bindings.a.length,
      inputWords:fixture.bindings.a.length+fixture.bindings.b.length,
      outputWords:reference.mixed.length+reference.cumulative.length});
    if(requireGpu){
      const observed=await runPVGraph({pvgraph,bindings:fixture.bindings,loadEngine,
        session,requireGPU:true,minWords:0,verifyWithLean:true});
      assert.equal(observed.status,'gpu-observed');
      assert.equal(observed.verifiedAgainstLeanWasm,true);
      assert.ok(observed.dispatches>=3,'map, zip and scan all dispatched');
      assert.deepEqual({...observed.outputs},reference,fixture.name+' GPU equals Lean');
      assert.equal(session.status().usedBytes,0);
      assert.equal(session.status().resourceCount,0);
      record('gpu-'+fixture.name,{wordsPerInput:fixture.bindings.a.length,
        inputWords:fixture.bindings.a.length+fixture.bindings.b.length,
        dispatches:observed.dispatches,timing:observed.timing,residentBytes:observed.residentBytes});
    }
  }

  const small=fixtures[0];
  const {pvgraph}=await buildSignalMixer({createPVGraphWasm,loadEngine,gain:small.gain});
  const automatic=await runPVGraph({pvgraph,bindings:small.bindings,loadEngine});
  assert.equal(automatic.status,'lean-reference');
  assert.match(automatic.reason,/small workload/);
  assert.deepEqual(automatic.outputs,small.expected);
  record('automatic-small-workload',{status:automatic.status,reason:automatic.reason});

  const failure=new Error('injected GPU compilation failure');
  const failedSession={status:()=>({byteBudget:1024*1024,usedBytes:0}),
    compile:async()=>{throw failure;},release(){assert.fail('no buffer was allocated');}};
  const fallback=await runPVGraph({pvgraph,bindings:small.bindings,loadEngine,
    session:failedSession,minWords:0});
  assert.equal(fallback.status,'lean-reference');
  assert.match(fallback.reason,/injected GPU compilation failure/);
  assert.deepEqual(fallback.outputs,small.expected);
  record('automatic-device-failure',{status:fallback.status});
  await assert.rejects(runPVGraph({pvgraph,bindings:small.bindings,loadEngine,
    session:failedSession,requireGPU:true,minWords:0}),error=>error===failure);
  record('required-gpu-never-silently-falls-back');

  await assert.rejects(runPVGraph({pvgraph,bindings:{a:[1],b:[1,2]},loadEngine}),
    /unequal zip input lengths/);
  await assert.rejects(runPVGraph({pvgraph,bindings:{a:[-1],b:[1]},loadEngine}),
    /exact u32/);
  record('malformed-inputs-refused');

  for(const meta of listExamples()){
    const recipe=await example(meta.id,loadEngine);
    const expected=engine.call('pvgraphEvaluate',[
      JSON.stringify(recipe.pvgraph),JSON.stringify(recipe.input)]).outputs;
    const result=await runPVGraph({pvgraph:recipe.pvgraph,bindings:recipe.input,loadEngine,
      session,minWords:0});
    assert.deepEqual({...result.outputs},expected);
    if(meta.id==='basic'){
      if(requireGpu)assert.equal(result.status,'gpu-observed');
    }else{
      assert.equal(result.status,'lean-reference');
      assert.equal(result.reason,'outside Lean GPU fragment');
      await assert.rejects(runPVGraph({pvgraph:recipe.pvgraph,bindings:recipe.input,
        loadEngine,session,requireGPU:true,minWords:0}),/operator requires Lean CPU fallback/);
    }
    record('existing-example-'+meta.id,{status:result.status,reason:result.reason,
      requiredGpuRefused:meta.id!=='basic'});
  }

  if(!globalThis.navigator?.gpu){
    await assert.rejects(runPVGraph({pvgraph,bindings:small.bindings,loadEngine,
      requireGPU:true,minWords:0}),/WebGPU adapter/);
    record('required-gpu-without-webgpu-refused');
  }
  if(session){
    assert.equal(session.status().usedBytes,0);
    assert.equal(session.status().resourceCount,0);
    report.resources=session.status();
  }
  report.status='pass';
}catch(error){
  report.error=error?.stack??String(error);
  process.exitCode=1;
}finally{
  if(session)session.close();
  report.caseCount=report.cases.length;
  console.log(JSON.stringify(report,null,2));
}
