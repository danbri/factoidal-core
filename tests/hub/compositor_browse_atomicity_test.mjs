import test, {after} from 'node:test';
import assert from 'node:assert/strict';
import {rootedPath} from '../../docs/web/hub/data-compositor/pod-storage.mjs';

// Import the real custom element. These minimal browser interfaces only hold
// option values; navigation and destination selection execute production code.
const saved=new Map(['HTMLElement','customElements','Option'].map(key=>
  [key,Object.getOwnPropertyDescriptor(globalThis,key)]));
globalThis.HTMLElement=class {};
globalThis.customElements={define(){}};
globalThis.Option=class {constructor(text,value){this.text=text;this.value=value;}};
after(()=>{for(const [key,descriptor] of saved){if(descriptor)Object.defineProperty(globalThis,key,descriptor);else delete globalThis[key];}});
const {PipelineLibrary}=await import('../../docs/web/hub/data-compositor/pipeline-files.mjs');

const root='http://127.0.0.1:8091/pod/';
const original=root+'visible/';
const target=root+'next/';
function fixture(transport){
  const library=new PipelineLibrary();
  const oldOption=new Option(original+'old.json',original+'old.json');
  const files={children:[oldOption],replaceChildren(...items){this.children=items;}};
  const location={textContent:original};
  library.folder=original;
  library.selectedPod=()=>({url:root});
  library.transport=transport;
  library.$=selector=>{if(selector==='.pod-files')return files;if(selector==='.pod-location')return location;throw Error(selector);};
  return {library,files,location,oldOption};
}

test('failed browse preserves displayed folder, entries and subsequent save destination',async()=>{
  const failure=new Error('403 listing denied');
  const state=fixture(async(operation,args)=>{
    assert.equal(operation,'list');assert.equal(args.url,target);throw failure;
  });
  await assert.rejects(state.library.browse(target),error=>error===failure);
  assert.equal(state.library.folder,original);
  assert.equal(state.location.textContent,original);
  assert.deepEqual(state.files.children,[state.oldOption]);
  assert.equal(rootedPath(state.library.folder,'pipeline.json'),original+'pipeline.json');
});

test('pending browse preserves destination; success commits new folder and entries',async()=>{
  let resolve;
  const state=fixture(()=>new Promise(complete=>{resolve=complete;}));
  const pending=state.library.browse(target);
  assert.equal(state.library.folder,original);
  assert.equal(state.location.textContent,original);
  assert.deepEqual(state.files.children,[state.oldOption]);
  resolve({items:[{id:target+'new.json'}]});
  assert.match(await pending,/^1 item/);
  assert.equal(state.library.folder,target);
  assert.equal(state.location.textContent,target);
  assert.deepEqual(state.files.children.map(option=>option.value),[target+'new.json']);
  assert.equal(rootedPath(state.library.folder,'pipeline.json'),target+'pipeline.json');
});

test('invalid listing cannot partially change the folder or discard the old entries',async()=>{
  const state=fixture(async()=>({items:null}));
  await assert.rejects(state.library.browse(target),TypeError);
  assert.equal(state.library.folder,original);
  assert.equal(state.location.textContent,original);
  assert.deepEqual(state.files.children,[state.oldOption]);
});
