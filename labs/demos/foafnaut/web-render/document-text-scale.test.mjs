import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import createModule from '../.build/web-render/engines/web-render.mjs';

const engine=await createModule();
const html='<style>body{margin:0;font-size:7px;line-height:7px}div{width:48px}</style><div>AA BB</div>';
function wasm(source,options){
 const pointer=engine.ccall('web_document_call','number',['string','string','number','number'],[source,JSON.stringify(options),120,100]);
 assert.ok(pointer);
 try{return JSON.parse(engine.UTF8ToString(pointer));}
 finally{engine.ccall('web_render_free',null,['number'],[pointer]);}
}
function native(source,options){
 const directory=mkdtempSync(join(tmpdir(),'factoidal-text-scale-'));
 try{
  const input=join(directory,'page.html'),request=join(directory,'request.json');
  writeFileSync(input,source);writeFileSync(request,JSON.stringify(options));
  const result=spawnSync(fileURLToPath(new URL('../.build/web-render/web-render-native',import.meta.url)),[input,'120','100','--document',request],{encoding:'utf8',timeout:5000,maxBuffer:8*1024*1024});
  assert.equal(result.status,0,result.error?.message??result.stderr);
  return JSON.parse(result.stdout);
 }finally{rmSync(directory,{recursive:true});}
}

test('native and WASM text zoom reflow the same Lean scene at unchanged viewport and CSS width',()=>{
 const normal=wasm(html,{textScalePercent:100}),large=wasm(html,{textScalePercent:200});
 for(const [percent,scene] of [[100,normal],[200,large]]){
  assert.equal(scene.error,undefined);
  assert.equal(scene.width,120);assert.equal(scene.height,100);
  assert.deepEqual(native(html,{textScalePercent:percent}),scene);
 }
 assert.deepEqual(normal.webRender.glyphRuns.map(run=>run.glyphs.map(g=>g[2])),[[0,0],[0,0]]);
 assert.deepEqual(large.webRender.glyphRuns.map(run=>run.glyphs.map(g=>g[2])),[[0,0],[14,14]]);
 assert.deepEqual(large.webRender.glyphRuns.map(run=>run.size),[14,14]);
 assert.ok(normal.webRender.boxes.some(box=>box[3]===48&&box[4]===7));
 assert.ok(large.webRender.boxes.some(box=>box[3]===48&&box[4]===28));
});

test('native and WASM reject invalid text scales for layout and font requests',()=>{
 for(const op of ['render','fontRequests'])for(const percent of [49,251,150.5,'150']){
  const options={op,textScalePercent:percent},result=wasm(html,options);
  assert.match(result.error,/textScalePercent/);
  assert.deepEqual(native(html,options),result);
 }
});
