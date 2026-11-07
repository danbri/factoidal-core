import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { Worker } from 'node:worker_threads';
import { createScriptSession } from './session.mjs';
import { createQuickJS } from './quickjs.mjs';
import { createLeanDOM } from './lean-dom.mjs';
import { createPageScripts } from './page-scripts.mjs';

const leanModuleURL = new URL('../../.build/web-render/engines/web-render.mjs', import.meta.url).href;
const wasmBytes = await readFile(new URL('../../.build/script-engine/qjs-wasi-reactor.wasm', import.meta.url));
const { default: createModule } = await import(leanModuleURL);
const engine = await createModule();
const source = '<!doctype html><div id="parent">before<span id="child">Old</span>after</div><p id="other">Outside</p>';
function inspect(commands = [], html = source) {
  const pointer = engine.ccall('web_document_call','number',['string','string','number','number'],
    [html,JSON.stringify({op:'inspect',url:'https://example.test/',commands}),1,1]);
  try { const result=JSON.parse(engine.UTF8ToString(pointer));assert.equal(result.error,undefined);return result; }
  finally { engine.ccall('web_render_free',null,['number'],[pointer]); }
}

test('QuickJS synchronous capability retains heap isolation and propagates exceptions', async () => {
  const vm = await createQuickJS(wasmBytes);
  try {
    await vm.bind('__echo', text => text);
    assert.equal(vm.evaluate('__echo("𐀀 café")',{stringResult:true}),'𐀀 café');
    await vm.bind('__throws', () => { throw Error('capability refused'); });
    assert.throws(()=>vm.evaluate('__throws("input")'),/capability refused/);
    assert.throws(()=>vm.evaluate('__echo()'),/Invalid host capability call/);
    assert.equal(vm.evaluate('typeof process + "/" + typeof fetch',{stringResult:true}),'undefined/undefined');
  } finally { vm.dispose(); }
});

test('actual Lean snapshots expose only own attributes before and after refresh', async () => {
  const html = source + '<p id="named" constructor="ctor-value" __proto__="proto-value" tostring="string-value" data-real="kept"></p>';
  const session = createScriptSession({wasmBytes,leanModuleURL,
    workerFactory:()=>new Worker(new URL('./worker.mjs',import.meta.url))});
  try {
    const batch = await session.start({nodes:inspect([],html).nodes,document:{source:html,url:'https://example.test/'},budgetMs:1000,
      source:`
        const absent=document.getElementById('child'),present=document.getElementById('named');
        function check(){
          for(const name of ['toString','constructor','__proto__'])
            if(absent.getAttribute(name)!==null)throw Error('inherited attribute leaked: '+name);
          for(const [name,value] of [['constructor','ctor-value'],['__proto__','proto-value'],['tostring','string-value'],['data-real','kept']])
            if(present.getAttribute(name)!==value)throw Error('real attribute lost: '+name);
        }
        check();
        absent.setAttribute('data-ok','yes');
        check();
        if(absent.getAttribute('data-ok')!=='yes')throw Error('successful attribute lost');
        console.log('own attributes passed');`});
    assert.deepEqual(batch.logs,['own attributes passed']);
    assert.equal(batch.commands.length,1);
  } finally { session.reset(); }
});

test('invalid Lean DOM mutation throws a named guest Error at the call without committing a command', async () => {
  const session = createScriptSession({wasmBytes,leanModuleURL,
    workerFactory:()=>new Worker(new URL('./worker.mjs',import.meta.url))});
  try {
    const batch = await session.start({nodes:inspect().nodes,document:{source,url:'https://example.test/'},budgetMs:1000,
      source:`
        const child=document.getElementById('child');let rejected=false;
        try{child.setAttribute('bad name','rejected');}
        catch(error){
          if(!(error instanceof Error)||error.name!=='InvalidCharacterError')throw Error('DOM error name lost');
          rejected=true;
        }
        if(!rejected||child.getAttribute('bad name')!==null)throw Error('invalid mutation became visible');
        child.setAttribute('data-ok','accepted');`});
    assert.deepEqual(batch.commands,[{op:'setAttribute',nodeId:inspect().nodes.find(n=>n.attributes.id==='child').id,name:'data-ok',value:'accepted'}]);
    const child=inspect(batch.commands).nodes.find(n=>n.attributes.id==='child');
    assert.equal(Object.hasOwn(child.attributes,'bad name'),false);
    assert.equal(child.attributes['data-ok'],'accepted');
  } finally { session.reset(); }
});

test('oversized actual Lean response rejects before committing synchronous mutation history', async () => {
  const html='<div>'.repeat(36)+'<p id="target">Old</p>'+'</div>'.repeat(36);
  const target=inspect([],html).nodes.find(n=>n.attributes.id==='target').id;
  const requests=[];
  const observed={...engine,ccall(name,...args){
    if(name==='web_document_call')requests.push(JSON.parse(args[2][1]).commands);
    return engine.ccall(name,...args);
  }};
  const vm=await createQuickJS(wasmBytes);
  try {
    await vm.bind('__mutate',await createLeanDOM({source:html,url:'https://example.test/'},observed));
    vm.evaluate(`let rejected=false;try{__mutate(JSON.stringify({op:'setTextContent',nodeId:${target},value:'x'.repeat(65536)}));}
      catch(error){if(!(error instanceof Error)||!/result exceeds budget/.test(error.message))throw error;rejected=true;}
      if(!rejected)throw Error('oversized response accepted');
      __mutate(JSON.stringify({op:'setTextContent',nodeId:${target},value:'small'}));`);
    assert.equal(requests.length,2);
    assert.equal(requests[0][0].value.length,65536,'negative control must reach the actual oversized response');
    assert.deepEqual(requests[1],[{op:'setTextContent',nodeId:target,value:'small'}]);
  } finally { vm.dispose(); }
});

test('actual Lean WASM makes ancestor text and connected ID lookup current inside one QuickJS turn', async () => {
  const initial = inspect();
  const session = createScriptSession({wasmBytes,leanModuleURL,
    workerFactory:()=>new Worker(new URL('./worker.mjs',import.meta.url))});
  try {
    const batch = await session.start({nodes:initial.nodes,document:{source,url:'https://example.test/'},budgetMs:1000,
      source:`
        const p=document.getElementById('parent'),c=document.getElementById('child');
        c.textContent='New';
        if(p.textContent!=='beforeNewafter')throw Error('ancestor text stayed stale');
        c.setAttribute('id','renamed');
        if(document.getElementById('child')!==null || document.getElementById('renamed')!==c)throw Error('ID lookup stayed stale');
        c.addEventListener('click',()=>{});
        p.textContent='Replacement';
        if(document.getElementById('renamed')!==null || c.isConnected)throw Error('removed child remained connected');
        if(p.textContent!=='Replacement')throw Error('replacement stayed stale');
        if(document.getElementById('other').textContent!=='Outside')throw Error('unrelated node changed');
        if(typeof __factoidalDOM!=='undefined')throw Error('raw capability leaked');
        console.log('same-turn Lean DOM passed');`});
    assert.deepEqual(batch.logs,['same-turn Lean DOM passed']);
    assert.deepEqual(batch.listeners,[]);
    assert.equal(batch.commands.length,3);
    const final = inspect(batch.commands);
    assert.equal(final.nodes.find(n=>n.attributes.id==='parent').textContent,'Replacement');
    assert.equal(final.nodes.some(n=>n.attributes.id==='renamed'),false);
  } finally { session.reset(); }
});

// Issue 1271: the guest API that Lean checks, in one turn and across many turns.
const page = '<!doctype html><body><ul id="list"><li class="a">one</li></ul><svg id="chart"></svg><p id="out">x</p></body>';
const lean = commands => inspect(commands, page);
const session = () => createScriptSession({wasmBytes,leanModuleURL,workerFactory:()=>new Worker(new URL('./worker.mjs',import.meta.url))});

test('actual Lean: createElement, createElementNS, appendChild, queries, classList and style', async () => {
  const s = session();
  try {
    const start = lean([]);
    const batch = await s.start({nodes:start.nodes,next:start.next,document:{source:page,url:'https://example.test/'},budgetMs:1000,source:`
      const list = document.getElementById('list');
      const item = document.createElement('LI');
      item.textContent = 'two';
      list.appendChild(item);
      const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
      rect.setAttribute('width', '10');
      document.querySelector('#chart').appendChild(rect);
      const out = document.getElementById('out');
      out.classList.add('b'); out.classList.toggle('c'); out.style.backgroundColor = 'red';
      console.log(document.querySelectorAll('ul li').length, item.parentNode === list, list.children.length,
        rect.namespaceURI, item.tagName, out.className, out.style.backgroundColor, document.querySelector('li.a').textContent);
      try { document.querySelector('ul > li'); } catch (error) { console.log(error.name); }
      list.removeChild(list.firstElementChild);
      console.log(list.textContent);`});
    assert.deepEqual(batch.errors, []);
    assert.deepEqual(batch.logs, ['2 true 2 http://www.w3.org/2000/svg LI b c red one', 'SyntaxError', 'two']);
    const final = lean(batch.commands);
    const out = final.nodes.find(n => n.attributes.id === 'out');
    assert.equal(out.attributes.class, 'b c');
    assert.equal(out.attributes.style, 'background-color: red');
    assert.equal(final.nodes.find(n => n.attributes.id === 'list').textContent, 'two');
    assert.equal(final.nodes.filter(n => n.tagName === 'rect' && n.namespace === 'svg').length, 1);
  } finally { s.reset(); }
});

test('actual Lean: a long animation stays within the history bound through compaction', async () => {
  const s = session(), start = lean([]);
  const compact = async commands => {
    const pointer = engine.ccall('web_document_call','number',['string','string','number','number'],
      [page,JSON.stringify({op:'compactCommands',url:'https://example.test/',commands}),1,1]);
    try { const answer = JSON.parse(engine.UTF8ToString(pointer)); assert.equal(answer.error, undefined); return answer.commands; }
    finally { engine.ccall('web_render_free',null,['number'],[pointer]); }
  };
  let frames = 0, done;
  const finished = new Promise(resolve => { done = resolve; });
  const runtime = createPageScripts({ session: s, compact, frameInterval: 0,
    onBatch: async (batch, kind) => { if (kind === 'frame' && ++frames === 1500) done(); } });
  try {
    await runtime.start({nodes:start.nodes,next:start.next,document:{source:page,url:'https://example.test/'},budgetMs:1000,source:`
      let n = 0; const out = document.getElementById('out');
      function step() { n++; out.setAttribute('data-frame', String(n)); out.textContent = 'frame ' + n; if (n < 1500) requestAnimationFrame(step); }
      requestAnimationFrame(step);`});
    await finished;
    assert.ok(runtime.stats.compactions >= 1, 'the history was compacted');
    assert.ok(runtime.commands.length <= 1024, `history ${runtime.commands.length}`);
    const out = lean(runtime.commands).nodes.find(n => n.attributes.id === 'out');
    assert.equal(out.attributes['data-frame'], '1500');
    assert.equal(out.textContent, 'frame 1500');
  } finally { runtime.stop('test end'); }
});
