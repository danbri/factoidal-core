// The shared engine of the Hub's Textnaut page and notebook (docs/web/hub/textnaut/engine-core.mjs)
// on the published Wasm engine, in Node: layout, the engine's CPU pixels, Textnaut's grid, links,
// page scripts on BubblePopJS, and the refusal of another site. NOT RUN (skipped) with no engine
// in docs/web/hub/html-webgpu/runtime/ (tools/fetch-builds.sh --set foafnaut-web) or $HUB_RUNTIME.
import test from 'node:test';
import assert from 'node:assert/strict';
import {hasRuntime,nodeHost,ORIGIN} from './_textnaut_host.mjs';
import {createEngineCore,classifyInput} from '../../docs/web/hub/textnaut/engine-core.mjs';

const BASE=`${ORIGIN}/factoidal/web/hub/notebook/`;
const skip=hasRuntime()?false:'no engine runtime (docs/web/hub/html-webgpu/runtime)';

test('classifyInput: markup, addresses and objects', () => {
  assert.deepEqual(classifyInput('<p>hi</p>',BASE),{html:'<p>hi</p>',url:BASE});
  assert.deepEqual(classifyInput('../foafnaut/pages/index.html',BASE),{url:`${ORIGIN}/factoidal/web/hub/foafnaut/pages/index.html`});
  assert.deepEqual(classifyInput('index.html',BASE),{url:`${BASE}index.html`});
  assert.deepEqual(classifyInput('https://example.org/',BASE),{url:'https://example.org/'});
  assert.deepEqual(classifyInput('plain words',BASE),{html:'plain words',url:BASE});
  assert.deepEqual(classifyInput({html:'<b>x</b>',url:'a.html'},BASE),{html:'<b>x</b>',url:`${BASE}a.html`});
  assert.throws(()=>classifyInput(42,BASE));
});

let core;
const engine=async()=>core??=createEngineCore(await nodeHost());

test('render: layout, primitives and CPU pixels of pasted HTML', {skip}, async () => {
  const e=await engine();
  const out=await e.open('a','<h1>Cell</h1><p>A <a href="../foafnaut/pages/index.html">link</a> here.</p>',{width:320,height:200,base:BASE});
  assert.equal(out.width,320);
  assert.ok(out.height>=40&&out.height<=200,`content height ${out.height}`);
  assert.ok(out.counters.primitives>0);
  assert.ok(out.counters.glyphRuns>=3);
  assert.equal(out.links.length,1);
  assert.equal(out.drawing,'cpu');
  assert.equal(out.rgba.length,out.width*out.height*4);
  assert.ok(out.rgba.some((v,i)=>i%4!==3&&v<128),'some dark pixels: the text is drawn');
  for(const k of ['layoutMs','drawMs','prepareMs','totalMs','engineMs'])assert.equal(typeof out.timing[k],'number',k);
  const link=e.linkAt('a',out.links[0].x+2,out.links[0].y+2);
  assert.equal(link.url,`${ORIGIN}/factoidal/web/hub/foafnaut/pages/index.html`);
  assert.equal(e.linkAt('a',1,1),null);
});

test('textnaut: grid of a page of this site, numbered links', {skip}, async () => {
  const e=await engine();
  const out=await e.textGrid('b','../foafnaut/pages/index.html',{cols:72,base:BASE});
  assert.equal(out.grid.cols,72);
  assert.ok(out.counters.rows>5);
  assert.ok(out.grid.targets.length>3,'the demo index has links');
  assert.match(out.text,/\[1\]/);
  assert.ok(out.grid.targets.every(t=>t.startsWith(ORIGIN)||/^[a-z]+:/.test(t)));
  assert.equal(typeof out.timing.cellsMs,'number');
});

test('another site is refused with a reason (no proxy)', {skip}, async () => {
  const e=await engine();
  await assert.rejects(e.open('c','https://example.org/',{base:BASE}),/another site/);
});

test('scripts: BubblePopJS runs the page, timers settle, a click changes it', {skip}, async () => {
  const e=await engine();
  const html='<p id=x>before</p><p><a href="#" id=b>more</a></p><script>document.getElementById("x").textContent="after "+(1+2);let n=0;'+
    'document.getElementById("b").addEventListener("click",e=>{e.preventDefault();n++;document.getElementById("x").textContent="clicked "+n});'+
    'setTimeout(()=>document.body.append("timer"),50)</script>';
  const out=await e.open('d',html,{width:320,height:160,base:BASE,scripts:true,draw:false});
  assert.equal(out.scripts.engine,'bubblepop');
  const grid=await e.textGrid('d2',html,{cols:40,base:BASE,scripts:true});
  assert.match(grid.text,/after 3/);
  assert.match(grid.text,/timer/);
  const link=out.links[0];
  const clicked=await e.click('d',link.x+2,link.y+2);
  assert.equal(clicked.changed,true);
  assert.equal(typeof clicked.frame.timing.layoutMs,'number');
});

test('views are bounded', {skip}, async () => {
  const e=await engine();
  for(let i=0;i<30;i++)await e.open(`v${i}`,`<p>${i}</p>`,{width:100,height:40,base:BASE,draw:false});
  assert.ok(e.views<=24);
});

// Every cell background of the grid is a colour the engine painted at that place (core finding
// 2026-11-15: shaped glyphs' bounds, in font units, were read as page boxes and painted large
// dark blocks over the demo index's text).
test('grid backgrounds agree with the engine\'s own pixels', {skip}, async () => {
  const e=await engine();
  const pages=['../foafnaut/pages/index.html',
    {html:'<style>body{margin:8px;font-family:sans-serif}.a{background:#fde;padding:8px;border-radius:6px}.b{background:#123;color:#fff;padding:4px}</style>'+
      '<h1>Boxes</h1><div class="a"><p>Pink box with <a href="x.html">a link</a>.</p></div><p class="b">Dark band of text</p><p>Plain text after.</p>'}];
  for(const [i,page] of pages.entries()){
    await e.textGrid(`bg${i}`,page,{cols:80,base:BASE});
    const check=await e.gridCheck(`bg${i}`);
    assert.equal(check.available,true);
    assert.ok(check.checked>0,`page ${i}: some cells have a background (${check.coloured})`);
    assert.equal(check.mismatches,0,`page ${i}: ${JSON.stringify(check.examples)}`);
  }
});
