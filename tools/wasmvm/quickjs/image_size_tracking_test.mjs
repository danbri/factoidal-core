import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import {test} from 'node:test';
import assert from 'node:assert/strict';

const prelude=readFileSync(new URL('./prelude.js',import.meta.url),'utf8');
function sizeTransport(){
  const start=prelude.indexOf('  const imgWriteSize = ');
  const end=prelude.indexOf('  const updateImage = id => {',start);
  assert.ok(start>=0&&end>start);
  const commands=[],live=new Map();
  let limit=1;
  const context=vm.createContext({Set,DOMException,n:{query(id,op,size){
    assert.equal(op,163);
    if(commands.length>=limit)return -5;
    commands.push([id,size]);live.set(id,size);return '';
  }},failD(code){throw new DOMException('host refusal '+code,'QuotaExceededError');}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.transport={imgWriteSize,imgClearSize};',context);
  return {transport:context.transport,commands,live,setLimit(n){limit=n;}};
}

test('image size tracking is retained after a refused host clear',()=>{
  const h=sizeTransport(),t=h.transport,st={layoutSized:false};
  t.imgWriteSize(4,st,'37 23');
  assert.equal(st.layoutSized,true);
  assert.throws(()=>t.imgClearSize(4,st),/host refusal -5/);
  assert.equal(st.layoutSized,true);
  assert.equal(h.live.get(4),'37 23');
  assert.deepEqual(h.commands,[[4,'37 23']]);
  h.setLimit(2);
  t.imgClearSize(4,st);
  assert.equal(st.layoutSized,false);
  assert.equal(h.live.get(4),'');
  assert.deepEqual(h.commands,[[4,'37 23'],[4,'']]);
});
test('a refused replacement does not discard earlier acknowledged size tracking',()=>{
  const h=sizeTransport(),t=h.transport,st={layoutSized:false};
  t.imgWriteSize(4,st,'37 23');
  assert.throws(()=>t.imgWriteSize(4,st,'19 11'),/host refusal -5/);
  assert.equal(st.layoutSized,true);
  assert.equal(h.live.get(4),'37 23');
});

test('one URL changing from 1x to 2x to 1x clears and restores its layout dimensions',async()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  assert.ok(start>=0&&end>start);
  const commands=[], events=[], requests=[];
  let selected='';
  const context=vm.createContext({DOMException,devicePixelRatio:1,info:()=>0,viewport:()=>[800,600],
    n0:{attr:()=>null},wrap:()=>({getAttribute:()=>null}),resolveURL:s=>s,
    n:{query(_id,op,payload){
      if(op===195){assert.equal(payload,'request\x001\x00800\x00600');return selected;}
      assert.equal(op,163);commands.push(payload);return '';
    }},imgGen:0,imgStates:new Map(),imgFire:(_el,event)=>events.push(event),imgUndelay:()=>{},
    cspBlocksRequest:()=>false,corsSettings:()=>({}),elementFetch(url){
      requests.push(url);return Promise.resolve({status:200,bytes:new TextEncoder().encode('19 11')});
    }});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  for(const marker of ['1','0','1']){
    selected=marker+'b.png';context.update(4);
    await new Promise(resolve=>setImmediate(resolve));
  }
  assert.deepEqual(commands,['19 11','','19 11']);
  assert.deepEqual(requests,['b.png','b.png','b.png']);
  assert.deepEqual(events,['load','load','load']);
});

function mutationWatcher(htmlDocument=true){
  const start=prelude.indexOf('  const imgWatch = () => {');
  const end=prelude.indexOf('  noteImg = id => imgWatch();',start);
  assert.ok(start>=0&&end>start);
  const updates=[];
  const context=vm.createContext({Set,String,
    imgWatching:false,imgAttrs:new Set(['src','srcset','sizes','crossorigin','referrerpolicy']),
    n:{setAttr(){return 0;},removeAttr(){return 0;}},
    info(_id,k){return k===0?1:k===8?(htmlDocument?1:0):0;},
    htmlEl(){return true;},str(){return 'img';},updateImage(id){updates.push(id);}});
  vm.runInContext(prelude.slice(start,end)+'\n imgWatch();',context);
  return {n:context.n,updates};
}
test('null-namespace source removals trigger exactly the image source lifecycle',()=>{
  const h=mutationWatcher();
  h.n.removeAttr(4,'\0src');
  h.n.removeAttr(4,'\0srcset');
  h.n.removeAttr(4,'urn:other\0src');
  h.n.removeAttr(4,'\0SRC');
  assert.deepEqual(h.updates,[4,4]);
});
test('ordinary HTML attributes fold case while namespace and XML local names do not',()=>{
  const h=mutationWatcher();
  h.n.setAttr(4,'SRC','a.png');
  h.n.setAttr(4,'\0SRC','other.png');
  assert.deepEqual(h.updates,[4]);
  const x=mutationWatcher(false);
  x.n.setAttr(4,'SRC','other.png');
  x.n.setAttr(4,'src','a.png');
  assert.deepEqual(x.updates,[4]);
});
