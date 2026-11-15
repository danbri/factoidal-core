// docs/web/hub/notebook.md: its cells, run through the reactive runtime the page uses with an
// `nb` that records what each cell asks for, and that content given to the engine in Node
// (engine-core.mjs, the module the page's worker runs). The page itself, with its canvas and its
// grid, is checked in headless Chrome by hub_textnaut_notebook_chrome.mjs.
import test from 'node:test';
import assert from 'node:assert/strict';
import {extractObservableCells,HUB_PAGE_DIR,runReactivePost} from './_helpers.mjs';
import {analyzeCell} from '../../docs/web/hub/reactive-cells.mjs';
import {hasRuntime,nodeHost,ORIGIN} from './_textnaut_host.mjs';
import {createEngineCore} from '../../docs/web/hub/textnaut/engine-core.mjs';

const cells=extractObservableCells('notebook.md',HUB_PAGE_DIR);
const BASE=`${ORIGIN}/factoidal/web/hub/notebook/`;
const skip=hasRuntime()?false:'no engine runtime (docs/web/hub/html-webgpu/runtime)';

test('the cells: named data cells and an nb library cell that imports the helper', () => {
  const names=cells.map(c=>analyzeCell(c).name);
  for(const n of ['card','bars','counter','nb'])assert.ok(names.includes(n),`cell ${n}`);
  const nb=cells[names.indexOf('nb')];
  assert.match(nb,/import\(new URL\("\.\.\/notebook\/cells\.mjs", location\.href\)\.href\)/);
  // Every anonymous cell is one call of the helper.
  for(const c of cells.filter(c=>!analyzeCell(c).name))assert.match(c.trim(),/^nb\.(render|foafnaut|textnaut|sideBySide|timingTable)\(/);
  for(const mode of ['render','foafnaut','textnaut','sideBySide'])assert.ok(cells.some(c=>c.includes(`nb.${mode}(`)),`a cell uses nb.${mode}`);
});

/** The page's cells on the page's runtime, with an `nb` that records each call. */
async function calls(){
  const seen=[];
  const record=mode=>(input,options)=>{seen.push({mode,input,options});return {mode};};
  const fake={render:record('render'),foafnaut:record('foafnaut'),textnaut:record('textnaut'),sideBySide:record('sideBySide'),timingTable:()=>({})};
  const page=runReactivePost(cells.map(c=>/^nb = /.test(c.trim())?'nb = fake':c),{fake});
  for(const name of page.names)await page.value(name);
  return seen;
}

test('each engine cell gives the helper markup or an address of this site', async () => {
  const seen=await calls();
  assert.ok(seen.length>=5);
  for(const {input} of seen){
    if(input.startsWith('<'))assert.ok(input.length>40);
    else assert.match(input,/^\.\.\/foafnaut\/pages\/[a-z-]+\.html$/);
  }
});

test('the engine lays out every cell\'s input, and the script cell runs on BubblePopJS', {skip}, async () => {
  const core=createEngineCore(await nodeHost());
  const seen=await calls();
  for(const [i,{mode,input,options}] of seen.entries()){
    if(mode==='textnaut'){
      const out=await core.textGrid(`t${i}`,input,{cols:options?.cols??80,base:BASE});
      assert.ok(out.counters.rows>5&&out.counters.links>3,`textnaut cell ${i}`);
      continue;
    }
    const out=await core.open(`c${i}`,input,{width:options?.width??360,height:options?.height??400,base:BASE,scripts:mode==='foafnaut'});
    assert.ok(out.counters.primitives>0,`cell ${i} (${mode}) has primitives`);
    assert.ok(out.rgba.some((v,k)=>k%4!==3&&v<160),`cell ${i} (${mode}) draws something dark`);
    if(mode==='foafnaut'){
      const grid=await core.textGrid(`g${i}`,input,{cols:40,base:BASE,scripts:true});
      assert.match(grid.text,/0 clicks/,'the page script ran before the first frame');
      const count=out.links.find(l=>l.href==='#');
      const clicked=await core.click(`c${i}`,count.x+2,count.y+2);
      assert.equal(clicked.changed,true,'a click on Count runs the page handler');
      const link=(await core.click(`c${i}`,out.links.find(l=>l.href!=='#').x+2,out.links.find(l=>l.href!=='#').y+2)).link;
      assert.equal(link?.url,`${ORIGIN}/factoidal/web/hub/foafnaut/pages/index.html`);
    }
  }
});
