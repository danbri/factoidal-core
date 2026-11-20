import {readFileSync} from 'node:fs';
import vm from 'node:vm';
import {test} from 'node:test';
import assert from 'node:assert/strict';

const prelude=readFileSync(new URL('./prelude.js',import.meta.url),'utf8');
function sizeTransport(){
  const start=prelude.indexOf('  const imgWriteSize = ');
  const end=prelude.indexOf('  const updateImage = (id, force = false) => {',start);
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
  let lazy=false;
  const timers=[];
  const context=vm.createContext({Set,String,imgPendingUpdates:new Set(),chk(){},register(f){return f;},
    imgWatching:false,imgAttrs:new Set(['src','srcset','sizes','crossorigin','referrerpolicy','loading']),
    n:{setAttr(){return 0;},removeAttr(){return 0;},timer(f){timers.push(f);return ''; }},
    info(_id,k){return k===0?1:k===8?(htmlDocument?1:0):0;},
    htmlEl(){return true;},str(){return 'img';},updateImage(id){updates.push([id,lazy]);}});
  vm.runInContext(prelude.slice(start,end)+'\n imgWatch();',context);
  return {n:context.n,updates,setLazy(v){lazy=v;},timerCount(){return timers.length;},flush(){for(const timer of timers.splice(0))timer();}};
}

function pictureMutationWatcher(){
  const start=prelude.indexOf('  const imgWatch = () => {');
  const end=prelude.indexOf('  noteImg = id => imgWatch();',start);
  assert.ok(start>=0&&end>start);
  const elements=new Map(), selected=new Map(), states=new Map(), updates=[];
  const add=(id,tag,parent=-1)=>{
    elements.set(id,{tag,parent,children:[]});
    if(parent>=0)elements.get(parent).children.push(id);
  };
  const detach=id=>{
    const e=elements.get(id);
    if(e.parent>=0)elements.get(e.parent).children=elements.get(e.parent).children.filter(x=>x!==id);
    e.parent=-1;
  };
  const insert=(parent,node,child=-1)=>{
    detach(node);
    const kids=elements.get(parent).children, at=child<0?kids.length:kids.indexOf(child);
    kids.splice(at<0?kids.length:at,0,node);elements.get(node).parent=parent;return 0;
  };
  const remove=(parent,node)=>{elements.get(parent).children=elements.get(parent).children.filter(x=>x!==node);elements.get(node).parent=-1;return 0;};
  const replace=(parent,node,child)=>{remove(parent,child);return insert(parent,node,child);};
  const context=vm.createContext({Set,String,Promise,imgPendingUpdates:new Set(),imgAttrs:new Set(['src','srcset','sizes','crossorigin','referrerpolicy','loading']),
    imgWatching:false,imgStates:states,
    register:f=>f,chk(){},wrap:()=>({getAttribute:()=>null}),kids:id=>elements.get(id)?.children??[],
    htmlEl:()=>true,info(id,k){const e=elements.get(id);return k===0?1:k===1?(e?.parent??-1):k===8?1:0;},str:(id)=>elements.get(id)?.tag??'',
    imgSelection:id=>({url:selected.get(id)??''}),updateImage(id,force=false){updates.push([id,force]);states.set(id,{complete:false,url:selected.get(id)??''});},
    n:{setAttr(){return 0;},removeAttr(){return 0;},insert,remove,replace,timer(){return '';}}});
  vm.runInContext(prelude.slice(start,end)+'\n imgWatch();',context);
  return {n:context.n,add,selected,states,updates};
}
test('null-namespace source removals trigger exactly one image update per script turn',()=>{
  const h=mutationWatcher();
  h.n.removeAttr(4,'\0src');
  h.n.removeAttr(4,'\0srcset');
  h.n.removeAttr(4,'urn:other\0src');
  h.n.removeAttr(4,'\0SRC');
  assert.equal(h.timerCount(),1);
  h.flush();
  assert.deepEqual(h.updates,[[4,false]]);
});
test('ordinary HTML attributes fold case while namespace and XML local names do not',()=>{
  const h=mutationWatcher();
  h.n.setAttr(4,'SRC','a.png');
  h.n.setAttr(4,'\0SRC','other.png');
  assert.equal(h.timerCount(),1);
  h.flush();
  assert.deepEqual(h.updates,[[4,false]]);
  const x=mutationWatcher(false);
  x.n.setAttr(4,'SRC','other.png');
  x.n.setAttr(4,'src','a.png');
  x.flush();
  assert.deepEqual(x.updates,[[4,false]]);
});
test('a source write is observed after synchronous loading=lazy setup',()=>{
  const h=mutationWatcher();
  h.n.setAttr(4,'src','/image.png');
  h.setLazy(true);
  assert.equal(h.timerCount(),1);
  h.flush();
  assert.deepEqual(h.updates,[[4,true]]);
});
test('changing a deferred image to loading=eager schedules its request',()=>{
  const h=mutationWatcher();
  h.n.setAttr(4,'loading','lazy');
  h.setLazy(true);
  h.n.setAttr(4,'loading','eager');
  h.setLazy(false);
  assert.equal(h.timerCount(),1);
  h.flush();
  assert.deepEqual(h.updates,[[4,false]]);
});
test('loading=lazy defers a request until script demands image state',()=>{
  const start=prelude.indexOf('  const updateImage = (id, force = false) => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  assert.ok(start>=0&&end>start);
  const lazy=new Set(),calls=[];
  const context=vm.createContext({Set,String,imgLazy:lazy,wrap(){return {getAttribute(){return 'lazy';}};},
    imgSelection(){calls.push('selected');return null;}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  context.update(4);
  assert.deepEqual([...lazy],[4]);
  assert.deepEqual(calls,[]);
});

test('inserting an in-flight image into an empty picture invalidates its same-URL request',async()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(2,'img');
  h.selected.set(2,'green.png');h.states.set(2,{complete:false,url:'green.png',unitDensity:false});
  h.n.insert(1,2,-1);
  assert.deepEqual(h.updates,[]);
  await Promise.resolve();
  assert.deepEqual(h.updates,[[2,true]]);
});
test('inserting a cached same-URL image into an empty picture keeps its request',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(2,'img');
  h.selected.set(2,'green.png');h.states.set(2,{complete:true,url:'green.png',unitDensity:false});
  h.n.insert(1,2,-1);
  assert.deepEqual(h.updates,[]);
});
test('inserting an image into a sourced picture replaces a changed candidate immediately',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(3,'source',1);h.add(2,'img');
  h.selected.set(2,'blue.png');h.states.set(2,{complete:true,url:'green.png',unitDensity:false});
  h.n.insert(1,2,-1);
  assert.deepEqual(h.updates,[[2,true]]);
});
test('inserting an image into an ordinary container does not restart its request',()=>{
  const h=pictureMutationWatcher();h.add(4,'div');h.add(2,'img');
  h.selected.set(2,'green.png');h.states.set(2,{complete:false,url:'green.png',unitDensity:false});
  h.n.insert(4,2,-1);
  assert.deepEqual(h.updates,[]);
});
test('removing a source from a picture reselects the fallback image',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(3,'source',1);h.add(2,'img',1);
  h.selected.set(2,'green.png');h.states.set(2,{complete:true,url:'blue.png',unitDensity:false});
  h.n.remove(1,3);
  assert.deepEqual(h.updates,[[2,true]]);
});
test('changing a source candidate in a picture reselects its image',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(3,'source',1);h.add(2,'img',1);
  h.selected.set(2,'blue.png');h.states.set(2,{complete:true,url:'green.png',unitDensity:false});
  h.n.setAttr(3,'srcset','blue.png');
  assert.deepEqual(h.updates,[[2,true]]);
});
test('changing the selected density rechecks layout even when the URL is unchanged',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(2,'img');
  h.selected.set(2,'green.png');h.states.set(2,{complete:true,url:'green.png',unitDensity:true});
  h.n.insert(1,2,-1);
  assert.deepEqual(h.updates,[[2,true]]);
});
