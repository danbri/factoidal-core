// Execute the actual Hub event handlers against the source-built shipping API.
// This DOM host records display changes; it does not implement RDF, queries,
// placement, GPU kernels, or browser rendering. Run with Deno --unstable-webgpu
// and --require-gpu for the real-device lane; Node also checks CPU-only hosts.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {resolveEngine} from '../npm/factoidal/bin/engine.mjs';
import * as core from '../npm/factoidal/index.mjs';
import {mountGpuSparql} from '../docs/web/hub/gpu-sparql/app.mjs';
import {queries} from '../docs/web/hub/gpu-sparql/fixtures.mjs';

const requireGpu=process.argv.includes('--require-gpu');
const sourceRoot=fileURLToPath(new URL('../',import.meta.url));
const page=readFileSync(new URL('../docs/web/hub/gpu-sparql/index.njk',import.meta.url),'utf8');
class Element {
  constructor(tag){this.tagName=tag.toUpperCase();this.children=[];this.dataset={};this.attributes={};this.events=new Map();this.value='';this.disabled=false;this.files=[];this.text='';}
  set textContent(value){this.text=String(value);this.children=[];}
  get textContent(){return this.text+this.children.map(child=>child.textContent).join('');}
  append(...children){this.children.push(...children);}
  replaceChildren(...children){this.text='';this.children=[...children];}
  setAttribute(key,value){this.attributes[key]=String(value);}
  addEventListener(name,callback){const events=this.events.get(name)??[];events.push(callback);this.events.set(name,events);}
  async fire(name,extra={}){for(const callback of this.events.get(name)??[])await callback({target:this,preventDefault(){},...extra});}
}
function documentHost(){
  const elements=new Map();
  for(const match of page.matchAll(/<([a-z][a-z0-9-]*)\b[^>]*\bid="([^"]+)"[^>]*>/gi)){
    assert.ok(!elements.has(match[2]),'unique element ID '+match[2]);
    elements.set(match[2],new Element(match[1]));
  }
  const doc={defaultView:{location:new URL('http://localhost/factoidal/web/hub/gpu-sparql/')},
    body:new Element('body'),createElement:tag=>new Element(tag),
    getElementById(id){assert.ok(elements.has(id),'actual page contains #'+id);return elements.get(id);},
    querySelectorAll(selector){assert.equal(selector,'input, select, textarea, button');return [...elements.values()].filter(el=>['INPUT','SELECT','TEXTAREA','BUTTON'].includes(el.tagName));}};
  const $=id=>doc.getElementById(id);
  for(const [id,value] of Object.entries({'runtime-module':'/factoidal/npm/factoidal/browser.js',
    'runtime-assets':'','sample-size':'64','execution-mode':'auto','gpu-min-rows':'','gpu-max-pairs':'1000000'}))$(id).value=value;
  return {doc,$};
}
const state=documentHost();
let moduleLoads=0;
const ui=mountGpuSparql({document:state.doc,loadModule:async url=>{
  moduleLoads++;assert.equal(url,'http://localhost/factoidal/npm/factoidal/browser.js');return core;
}});
const {$}=state;
const loaded=resolveEngine();
const report={status:'fail',sourceCommit:execFileSync('git',['rev-parse','HEAD'],{cwd:sourceRoot,encoding:'utf8'}).trim(),
  workingTreeDirty:!!execFileSync('git',['status','--porcelain'],{cwd:sourceRoot,encoding:'utf8'}).trim(),
  runtime:{loader:loaded,sha256:createHash('sha256').update(readFileSync(loaded.replace(/\.js$/,'.wasm'))).digest('hex')},
  host:'DOM event test host; rendering and browser asset loading are separate checks',cases:[],requireGpu};
const record=(name,details={})=>report.cases.push({name,correct:true,...details});
async function runPreset(preset,execution,expectedCount,kind='select'){
  $('query-preset').value=preset;await $('query-preset').fire('change');
  assert.equal($('query-text').value,queries[preset].text);
  $('execution-mode').value=execution;
  const result=await ui.run(true);
  assert.ok(result,$('status').textContent);
  assert.equal(result.result.kind,kind);
  if(expectedCount!==undefined)assert.equal(result.result.count,expectedCount);
  assert.equal(result.comparison.equal,true,$('comparison').textContent);
  assert.equal($('status').dataset.kind,'success');
  assert.equal($('compare-cpu').disabled,false);
  assert.equal($('download-report').disabled,false);
  return result;
}
try{
  assert.equal(moduleLoads,0,'mounting the page loads no engine');
  await $('load-runtime').fire('click');
  assert.equal(moduleLoads,1);
  assert.match($('runtime-status').textContent,/Local runtime ready/);
  assert.equal(JSON.parse($('registry-json').textContent).name,'gpuSparqlStage');
  assert.equal($('runtime-module').disabled,true);
  record('local-runtime-and-shipping-registry');
  for(const [preset,total,kind] of [['people',50,'select'],['counts',8,'select'],['bag',64,'select'],['ask',undefined,'ask'],['construct',50,'graph']]){
    const result=await runPreset(preset,'cpu',total,kind);
    if(kind==='ask')assert.equal(result.result.value,true);
    record('cpu-'+preset,{kind,count:result.result.count,value:result.result.value});
  }
  $('sample-size').value='2048';await $('load-sample').fire('click');
  const auto=await runPreset('counts','auto',8);
  assert.equal(auto.options.execution,'auto');
  if(auto.execution?.device){
    const info=auto.execution.device;
    const software=info.isFallbackAdapter===true||/swiftshader|llvmpipe|lavapipe|software/i.test([info.vendor,info.device,info.description].join(' '));
    if(software)assert.equal(auto.execution.gpuJoins,0);
    report.adapter=info;
  }
  record('automatic-placement',{execution:auto.execution});
  $('sample-size').value='64';await $('load-sample').fire('click');
  if(requireGpu){
    assert.ok(globalThis.navigator?.gpu,'the device lane requires WebGPU');
    for(const [preset,total,kind] of [['people',50,'select'],['counts',8,'select'],['bag',64,'select'],['construct',50,'graph'],['ask',undefined,'ask']]){
      const result=await runPreset(preset,'gpu',total,kind);
      if(kind!=='ask'){
        assert.ok(result.execution.gpuJoins>0);
        assert.ok(result.execution.observed.some(phase=>phase.dispatches>0));
        assert.ok(Number($('gpu-joins').textContent)>0);
      }
      record('gpu-'+preset,{kind,count:result.result.count,gpuJoins:result.execution?.gpuJoins});
    }
  }else if(!globalThis.navigator?.gpu){
    $('execution-mode').value='gpu';
    assert.equal(await ui.run(),undefined);
    assert.equal($('status').dataset.kind,'error');
    assert.match($('status').textContent,/GPU|WebGPU|device/);
    assert.match($('result-json').textContent,/No answer/);
    record('required-gpu-refusal-without-device');
  }
  const nq='_:a <urn:p> "same" <urn:g> .\n_:b <urn:p> "same" <urn:g> .\n';
  const trig='@prefix ex: <urn:> .\nex:g { _:a ex:p "same" . _:b ex:p "same" . }';
  for(const [name,text] of [['input.nq',nq],['input.trig',trig]]){
    $('dataset-file').files=[new File([text],name)];
    await $('dataset-file').fire('change');
    assert.equal($('dataset-text').value,text);
    assert.equal($('dataset-format').value,'','file format detection remains in the engine');
    $('execution-mode').value='cpu';
    $('query-text').value='SELECT ?s ?o WHERE { GRAPH <urn:g> { ?s <urn:p> ?o } } ORDER BY ?s';
    let result=await ui.run(true);assert.ok(result,$('status').textContent);
    assert.equal(result.result.count,2);assert.equal(result.comparison.equal,true);
    assert.equal(JSON.parse(result.result.preview)[0][0][1].termType,'BlankNode');
    $('query-text').value='SELECT ?o WHERE { GRAPH <urn:g> { ?s <urn:p> ?o } } ORDER BY ?o';
    result=await ui.run(true);assert.equal(result.result.count,2);assert.equal(result.comparison.equal,true);
    assert.equal(JSON.parse(result.result.preview).length,2,'duplicate solutions remain in the comparison');
    record('file-detection-blank-nodes-and-bag-'+name,{quads:result.source.quads});
  }
  $('dataset-text').value='invalid RDF';await $('dataset-text').fire('input');
  assert.equal(await ui.run(),undefined);assert.equal($('status').dataset.kind,'error');
  assert.match($('result-json').textContent,/No answer/);
  assert.equal($('download-report').disabled,true);record('invalid-input-has-no-stale-result');
  const old=documentHost();
  const oldUi=mountGpuSparql({document:old.doc,loadModule:async()=>({...core,loadEngine:async()=>({call(){return{ops:[]};}})})});
  try{await oldUi.loadRuntime();assert.match(old.$('runtime-status').textContent,/missing datasetQueryGpuBegin/);record('stale-runtime-refusal');}
  finally{oldUi.dispose();}
  const remote=documentHost();let contacted=false;
  remote.$('runtime-module').value='https://cdn.example/browser.js';
  const remoteUi=mountGpuSparql({document:remote.doc,loadModule:async()=>{contacted=true;return core;}});
  try{await remoteUi.loadRuntime();assert.equal(contacted,false);assert.match(remote.$('runtime-status').textContent,/HTTP origin/);record('remote-module-refused-before-loading');}
  finally{remoteUi.dispose();}
  report.status='pass';
}catch(error){report.error=error?.stack??String(error);process.exitCode=1;}
finally{ui.dispose();console.log(JSON.stringify(report,null,2));}
