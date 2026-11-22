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

test('Image constructor preserves its shared prototype with an immutable descriptor',()=>{
  const start=prelude.indexOf('    const ImageFactory = function Image(');
  const end=prelude.indexOf("def('Image', ImageFactory);",start)+"def('Image', ImageFactory);".length;
  assert.ok(start>=0&&end>start);
  const prototype={},attributes=[];
  let registered;
  const context=vm.createContext({named:{HTMLImageElement:{prototype}},scriptDocument:null,
    document:{createElement(name){assert.equal(name,'img');return Object.assign(Object.create(prototype),{setAttribute:(...args)=>attributes.push(args)});}},
    def(_name,value){registered=value;}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.imageFactory=ImageFactory;',context);
  const factory=registered,descriptor=Object.getOwnPropertyDescriptor(factory,'prototype');
  assert.equal(descriptor.value,prototype);
  assert.equal(descriptor.writable,false);
  assert.equal(descriptor.enumerable,false);
  assert.equal(descriptor.configurable,false);
  assert.equal(Reflect.set(factory,'prototype',{}),false);
  const image=new factory(17,23);
  assert.equal(Object.getPrototypeOf(image),prototype);
  assert.deepEqual(attributes,[['width','17'],['height','23']]);
});

test('one URL changing from 1x to 2x to 1x clears and restores its layout dimensions',async()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  assert.ok(start>=0&&end>start);
  const commands=[], events=[], requests=[], timers=[];
  let selected='';
  const context=vm.createContext({imgLazy:new Set(),layoutObserverInterfaces:()=>undefined,DOMException,devicePixelRatio:1,info:(_id,k)=>k===7?9:k===1||k===12?-1:0,viewport:()=>[800,600],
    n0:{attr:()=>null},wrap:()=>({getAttribute:()=>null}),resolveURL:s=>s,
    imgGen:0,imgStates:new Map(),imgAvailable:new Map(),imgFire:(_el,event)=>events.push(event),imgUndelay:()=>{},
    chk(){},register:f=>f,
    n:{query(_id,op,payload){
      if(op===195){assert.equal(payload,'request\x001\x00800\x00600');return selected;}
      assert.equal(op,163);commands.push(payload);return '';
    },timer(f){timers.push(f);return ''; }},
    cspBlocksRequest:()=>false,flushViolations(){},corsSettings:()=>({mode:'no-cors',credentials:'include'}),elementFetch(url){
      requests.push(url);return Promise.resolve({status:200,bytes:new TextEncoder().encode('19 11')});
    }});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  for(const marker of ['1','0','1']){
    selected=marker+'b.png';context.update(4);
    await new Promise(resolve=>setImmediate(resolve));
    for(const timer of timers.splice(0))timer();
  }
  assert.deepEqual(commands,['19 11','','19 11']);
  assert.deepEqual(requests,['b.png','b.png','b.png']);
  assert.deepEqual(events,['load','load','load']);
});

test('a completed plain-src image is available to another detached image in the same document',async()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  const requests=[],events=[],timers=[],states=new Map(),available=new Map();
  let mode='no-cors';
  const context=vm.createContext({imgLazy:new Set(),layoutObserverInterfaces:()=>undefined,DOMException,devicePixelRatio:1,info:(_id,k)=>k===7?9:k===1||k===12?-1:0,
    viewport:()=>[800,600],docURL:()=>'',resolveURL:s=>s,n0:{attr:(_id,name)=>name==='src'?'/cached.png':null},
    wrap:()=>({getAttribute:()=>null}),htmlEl:()=>true,str:()=>'',
    n:{query(_id,op,payload){if(op===195)return '0/cached.png';assert.equal(op,163);return '';},timer(f){timers.push(f);return ''; }},
    imgGen:0,imgStates:states,imgAvailable:available,imgFire:(_el,type)=>events.push(type),imgUndelay:()=>{},
    chk(){},register:f=>f,cspBlocksRequest:()=>false,flushViolations(){},
    corsSettings:()=>({mode,credentials:mode==='no-cors'?'include':'same-origin'}),
    elementFetch(url){requests.push(url);return Promise.resolve({status:200,bytes:new TextEncoder().encode('37 23')});}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  context.update(1);
  await new Promise(resolve=>setImmediate(resolve));
  for(const timer of timers.splice(0))timer();
  context.update(2);
  assert.equal(states.get(2).w,37);
  assert.equal(states.get(2).h,23);
  assert.deepEqual(requests,['/cached.png']);
  assert.deepEqual(events,['load']);
  for(const timer of timers.splice(0))timer();
  assert.deepEqual(events,['load','load']);
  mode='cors';
  context.update(3);
  await new Promise(resolve=>setImmediate(resolve));
  assert.deepEqual(requests,['/cached.png','/cached.png']);
});

test('a completed selected image is reused inside an empty picture',async()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  const events=[],timers=[],states=new Map(),available=new Map();
  available.set(JSON.stringify([9,'/cached-picture.png','no-cors','include']),{w:37,h:23});
  const context=vm.createContext({imgLazy:new Set(),layoutObserverInterfaces:()=>undefined,DOMException,devicePixelRatio:1,info:(id,k)=>k===7?9:k===1?(id===2?10:-1):k===12?-1:k===0?1:0,
    viewport:()=>[800,600],docURL:()=>'',resolveURL:s=>s,n0:{attr:(_id,name)=>name==='src'?'/cached-picture.png':null},
    wrap:()=>({getAttribute:()=>null}),htmlEl:()=>true,str:(id)=>id===10?'picture':'img',
    n:{query(_id,op,payload){if(op===195)return '0/cached-picture.png';assert.equal(op,163);return '';},timer(f){timers.push(f);return ''; }},
    imgGen:0,imgStates:states,imgAvailable:available,imgFire:(_el,type)=>events.push(type),imgUndelay:()=>{},
    chk(){},register:f=>f,cspBlocksRequest:()=>false,flushViolations(){},
    corsSettings:()=>({mode:'no-cors',credentials:'include'}),elementFetch(){assert.fail('completed picture image should be reused');}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  context.update(2);
  assert.equal(states.get(2).w,37);
  assert.equal(states.get(2).h,23);
  assert.equal(states.get(2).available,true);
  for(const timer of timers.splice(0))timer();
  assert.deepEqual(events,['load']);
});

test('a valid image response is accepted when its HTTP status is an error',async()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  const events=[],timers=[],states=new Map(),available=new Map();
  const context=vm.createContext({imgLazy:new Set(),layoutObserverInterfaces:()=>undefined,DOMException,devicePixelRatio:1,info:(_id,k)=>k===7?9:k===1||k===12?-1:0,
    viewport:()=>[800,600],docURL:()=>'',resolveURL:s=>s,n0:{attr:(_id,name)=>name==='src'?'/error-status.png':null},
    wrap:()=>({getAttribute:()=>null}),htmlEl:()=>true,str:()=>'div',
    n:{query(_id,op){if(op===195)return '0/error-status.png';assert.equal(op,163);return '';},timer(f){timers.push(f);return ''; }},
    imgGen:0,imgStates:states,imgAvailable:available,imgFire:(_el,type)=>events.push(type),imgUndelay:()=>{},
    chk(){},register:f=>f,cspBlocksRequest:()=>false,flushViolations(){},
    corsSettings:()=>({mode:'no-cors',credentials:'include'}),
    elementFetch:()=>Promise.resolve({status:404,bytes:new TextEncoder().encode('19 11')})});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  context.update(1);
  await new Promise(resolve=>setImmediate(resolve));
  assert.equal(states.get(1).complete,true);
  assert.equal(states.get(1).w,19);
  assert.equal(states.get(1).h,11);
  assert.deepEqual(events,['load']);
  assert.equal(available.has(JSON.stringify([9,'/error-status.png','no-cors','include'])),true);
});

test('a completed superseded fetch seeds availability without settling its stale element request',async()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  const src=new Map([[1,'/old.png'],[2,'/old.png']]),pending=[],timers=[],events=[];
  const states=new Map(),available=new Map();
  const context=vm.createContext({imgLazy:new Set(),layoutObserverInterfaces:()=>undefined,DOMException,devicePixelRatio:1,info:(_id,k)=>k===7?9:k===1||k===12?-1:0,
    viewport:()=>[800,600],docURL:()=>'',resolveURL:s=>s,n0:{attr:(id,name)=>name==='src'?src.get(id)??null:null},
    wrap:()=>({getAttribute:()=>null}),htmlEl:()=>true,str:()=>'',
    n:{query(id,op){if(op===195)return '0'+src.get(id);assert.equal(op,163);return '';},timer(f){timers.push(f);return ''; }},
    imgGen:0,imgStates:states,imgAvailable:available,imgFire:(_el,type)=>events.push(type),imgUndelay:()=>{},
    chk(){},register:f=>f,cspBlocksRequest:()=>false,flushViolations(){},
    corsSettings:()=>({mode:'no-cors',credentials:'include'}),
    elementFetch(url){return new Promise(resolve=>pending.push({url,resolve}));}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  context.update(1);
  src.set(1,'/new.png');context.update(1);
  assert.deepEqual(pending.map(x=>x.url),['/old.png','/new.png']);
  pending[0].resolve({status:200,bytes:new TextEncoder().encode('37 23')});
  await new Promise(resolve=>setImmediate(resolve));
  assert.equal(available.has(JSON.stringify([9,'/old.png','no-cors','include'])),true);
  assert.equal(states.get(1).url,'/new.png');
  assert.deepEqual(events,[]);
  context.update(2);
  assert.equal(states.get(2).w,37);
  assert.deepEqual(pending.map(x=>x.url),['/old.png','/new.png']);
});

test('decode waiters observe a replaced request on the DOM task source',()=>{
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  const timers=[];let rejected=0;
  const states=new Map([[4,{gen:0,url:'/old.png',waiters:[[()=>{},()=>rejected++]],layoutSized:false}]]);
  const context=vm.createContext({imgLazy:new Set(),layoutObserverInterfaces:()=>undefined,DOMException,devicePixelRatio:1,info:(_id,k)=>k===7?9:k===1||k===12?-1:0,
    viewport:()=>[800,600],resolveURL:s=>s,n0:{attr:()=>null},wrap:()=>({getAttribute:()=>null}),
    n:{query(_id,op){if(op===195)return '0/new.png';assert.equal(op,163);return '';},timer(f){timers.push(f);return ''; }},
    imgGen:0,imgStates:states,imgAvailable:new Map(),imgFire(){},imgUndelay(){},chk(){},register:f=>f,
    cspBlocksRequest:()=>false,flushViolations(){},corsSettings:()=>({mode:'no-cors',credentials:'include'}),
    elementFetch:()=>new Promise(()=>{})});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  context.update(4);
  assert.equal(rejected,0);
  assert.equal(timers.length,1);
  timers[0]();
  assert.equal(rejected,1);
});

function mutationWatcher(htmlDocument=true){
  const start=prelude.indexOf('  const imgWatch = () => {');
  const end=prelude.indexOf('  noteImg = id => imgWatch();',start);
  assert.ok(start>=0&&end>start);
  const updates=[];
  let lazy=false;
  const timers=[];
  const context=vm.createContext({Set,String,imgPendingUpdates:new Set(),isImg:()=>true,chk(){},register(f){return f;},
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
  const prepared=new Set(), delay=new Set(), timers=[];
  const readyState='loading';
  const add=(id,tag,parent=-1)=>{
    elements.set(id,{tag,parent,children:[]});
    if(parent>=0)elements.get(parent).children.push(id);
  };
  const children=id=>elements.get(id)?.children.slice()??[];
  const descendants=id=>children(id).flatMap(k=>[k,...descendants(k)]);
  const connectedId=id=>id===0||((elements.get(id)?.parent??-1)>=0&&connectedId(elements.get(id).parent));
  const detach=id=>{
    const e=elements.get(id);
    if(e.parent>=0)elements.get(e.parent).children=elements.get(e.parent).children.filter(x=>x!==id);
    e.parent=-1;
  };
  const insert=(parent,node,child=-1)=>{
    if(elements.get(node).tag==='fragment'){
      for(const id of children(node))insert(parent,id,child);
      return 0;
    }
    detach(node);
    const kids=elements.get(parent).children, at=child<0?kids.length:kids.indexOf(child);
    kids.splice(at<0?kids.length:at,0,node);elements.get(node).parent=parent;return 0;
  };
  const remove=(parent,node)=>{elements.get(parent).children=elements.get(parent).children.filter(x=>x!==node);elements.get(node).parent=-1;return 0;};
  const replace=(parent,node,child)=>{remove(parent,child);return insert(parent,node,child);};
  const context=vm.createContext({preparedImages:prepared,imgDelay:delay,descendants,connectedId,
    isImg:id=>elements.get(id)?.tag==='img',
    wrap:id=>({getAttribute:name=>name==='loading'?elements.get(id)?.loading??null:null}),
    get readyState(){return readyState;},Set,String,Promise,imgPendingUpdates:new Set(),imgAttrs:new Set(['src','srcset','sizes','crossorigin','referrerpolicy','loading']),
    imgWatching:false,imgStates:states,
    register:f=>f,chk(){},kids:id=>elements.get(id)?.children??[],
    htmlEl:()=>true,info(id,k){const e=elements.get(id);return k===7?0:k===0?(elements.get(id)?.tag==='fragment'?11:1):k===1?(e?.parent??-1):k===8?1:0;},str:(id)=>elements.get(id)?.tag??'',
    imgSelection:id=>({url:selected.get(id)??''}),updateImage(id,force=false){updates.push([id,force]);states.set(id,{complete:false,url:selected.get(id)??''});},
    n:{setAttr(){return 0;},removeAttr(){return 0;},insert,remove,replace,timer(f){timers.push(f);return '';}}});
  vm.runInContext(prelude.slice(start,end)+'\n imgWatch();',context);
  return {n:context.n,add,selected,states,updates,prepared,delay,flush(){for(const timer of timers.splice(0))timer();},setLoading(id,loading){elements.get(id).loading=loading;}};
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
function lazyImageHarness() {
  const start=prelude.indexOf('  const imgSelection = id => {');
  const end=prelude.indexOf('  const imgWatch = () => {',start);
  const lazy=new Set(),requests=[],timers=[],events=[],watches=[],available=new Map();
  let source='/image.png';
  const context=vm.createContext({imgLazy:lazy,DOMException,devicePixelRatio:1,
    info:(_id,k)=>k===7?9:k===1||k===12?-1:0,viewport:()=>[800,600],docURL:()=>'',resolveURL:s=>s,
    n0:{attr:(_id,name)=>name==='src'?source:null},
    wrap:()=>({getAttribute:name=>name==='loading'?'lazy':null}),htmlEl:()=>true,str:()=>'',
    n:{query(_id,op){if(op===195)return source?'1'+source:'';assert.equal(op,163);return '';},
      timer(f){timers.push(f);return ''; }},
    imgGen:0,imgStates:new Map(),imgAvailable:available,imgFire:(_el,type)=>events.push(type),imgUndelay(){},
    chk(){},register:f=>f,cspBlocksRequest:()=>false,flushViolations(){},
    corsSettings:()=>({mode:'no-cors',credentials:'include'}),
    layoutObserverInterfaces:()=>({watchLazyImage(){watches.push('observe');},forgetLazyImage(){watches.push('unobserve');}}),
    elementFetch(url){requests.push(url);return new Promise(()=>{});}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.update=updateImage;',context);
  return {update:context.update,lazy,requests,timers,events,watches,available,setSource(value){source=value;}};
}

test('an unavailable lazy image waits for an intersection before requesting its bytes',()=>{
  const h=lazyImageHarness();
  h.update(4);
  assert.deepEqual([...h.lazy],[4]);
  assert.deepEqual(h.watches,['observe']);
  assert.deepEqual(h.requests,[]);
  h.update(4,true);
  assert.deepEqual([...h.lazy],[]);
  assert.deepEqual(h.watches,['observe','unobserve']);
  assert.deepEqual(h.requests,['/image.png']);
});

test('an empty lazy image reports an error and clears its deferred request',async()=>{
  const h=lazyImageHarness();
  h.update(4);
  h.setSource('');
  h.update(4);
  await Promise.resolve();
  assert.deepEqual([...h.lazy],[]);
  assert.deepEqual(h.watches,['observe','unobserve']);
  assert.deepEqual(h.events,['error']);
  assert.deepEqual(h.requests,[]);
});

test('a completed image is reused before waiting on a lazy intersection',()=>{
  const h=lazyImageHarness();
  h.available.set(JSON.stringify([9,'/image.png','no-cors','include']),{w:40,h:20});
  h.update(4);
  assert.deepEqual([...h.lazy],[]);
  assert.deepEqual(h.watches,[]);
  assert.deepEqual(h.requests,[]);
  for(const timer of h.timers)timer();
  assert.deepEqual(h.events,['load']);
});

test('the internal observer resumes an intersecting image with zero intersection area',()=>{
  const start=prelude.indexOf('    let lazyImages;');
  const end=prelude.indexOf('    return { IntersectionObserver,',start);
  let deliver;
  const updates=[],id=4,target={};
  const context=vm.createContext({imgLazy:new Set([id]),nodeId:()=>id,
    IntersectionObserver:class {constructor(callback){deliver=callback;}},
    addIntersectionTarget(_observer,el){assert.equal(el,target);},
    removeIntersectionTarget(){},
    updateImage(node,force){updates.push([node,force]);}});
  vm.runInContext(prelude.slice(start,end)+'\n globalThis.watch=watchLazyImage;',context);
  context.watch(target);
  deliver([{target,isIntersecting:false,intersectionRatio:0}]);
  assert.deepEqual(updates,[]);
  deliver([{target,isIntersecting:true,intersectionRatio:0}]);
  assert.deepEqual(updates,[[id,true]]);
});

test('connecting a prepared subtree starts eager and lazy images but only eager images hold load',()=>{
  const h=pictureMutationWatcher();
  h.add(0,'document');h.add(1,'fragment');h.add(2,'section',1);h.add(3,'img',2);
  h.add(4,'section');h.add(5,'img',2);h.setLoading(5,'lazy');
  h.prepared.add(3);h.prepared.add(5);
  h.n.insert(4,1,-1);
  assert.deepEqual([...h.prepared],[3,5]);
  assert.deepEqual([...h.delay],[]);
  h.n.insert(0,4,-1);
  assert.deepEqual([...h.prepared],[]);
  assert.deepEqual([...h.delay],[3]);
  h.flush();
  assert.deepEqual(h.updates,[[3,false],[5,false]]);
  h.n.insert(0,2,-1);
  h.flush();
  assert.deepEqual(h.updates,[[3,false],[5,false]]);
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
test('source attribute mutation refreshes only following image siblings and preserves namespace case',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(2,'img',1);h.add(3,'source',1);h.add(4,'img',1);
  for(const id of [2,4]){h.selected.set(id,'blue.png');h.states.set(id,{complete:true,url:'green.png',unitDensity:false});}
  h.n.setAttr(3,'srcset','blue.png');
  assert.deepEqual(h.updates,[[4,true]]);
  h.updates.length=0;
  h.n.setAttr(3,'\0SRCSET','ignored.png');
  assert.deepEqual(h.updates,[]);
});
test('changing the selected density rechecks layout even when the URL is unchanged',()=>{
  const h=pictureMutationWatcher();h.add(1,'picture');h.add(2,'img');
  h.selected.set(2,'green.png');h.states.set(2,{complete:true,url:'green.png',unitDensity:true});
  h.n.insert(1,2,-1);
  assert.deepEqual(h.updates,[[2,true]]);
});
