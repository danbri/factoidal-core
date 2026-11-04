#!/usr/bin/env node
// Local development transport. Serves an explicit set of source/runtime files.
import {createServer} from 'node:http';
import {readFile,stat} from 'node:fs/promises';
import {dirname,resolve} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {stripTypeScriptTypes} from 'node:module';
import {createHash} from 'node:crypto';
const here=dirname(fileURLToPath(import.meta.url)),lab=resolve(here,'..');
const files=new Map();
for(const name of ['index.html','app.mjs','worker.mjs','style.css','shader-editor.mjs','shader-scalars.mjs']) files.set('/'+name,resolve(here,name));
for(const name of ['svg_engine.ts','gpu_transport.ts','render_plan.ts',
  '.build/engines/svg-engine.mjs','.build/engines/svg-engine.wasm',
  '.build/engines/render-plan.mjs','.build/engines/render-plan.wasm'])files.set('/lab/'+name,resolve(lab,name));
for(const name of ['gallery.svg','affine.svg','linear-paths.svg'])files.set('/fixtures/'+name,resolve(lab,'svg-fixtures',name));
files.set('/fixtures/solving-browser-scene.svg',resolve(here,'fixtures/solving-browser-scene.svg'));
const mime=p=>p.endsWith('.wasm')?'application/wasm':p.endsWith('.html')?'text/html; charset=utf-8':p.endsWith('.css')?'text/css; charset=utf-8':p.endsWith('.svg')?'image/svg+xml; charset=utf-8':'text/javascript; charset=utf-8';
export async function provenance(){
 const entries=[];
 for(const [url,path] of files){const b=await readFile(path);entries.push({url,bytes:b.length,sha256:createHash('sha256').update(b).digest('hex')});}
 const source=[];
 for(const name of ['SVG.lean','SVGPath.lean','Graphics.lean','RenderPlan.lean']){
  try{const b=await readFile(resolve(lab,name));source.push({file:name,sha256:createHash('sha256').update(b).digest('hex')});}catch(e){if(e.code!=='ENOENT')throw e;}
 }
 return {format:'factoidal-browser-webgpu-provenance-v1',scope:'Local warm artifacts, not a published release; hashes identify bytes, not proof of correspondence to current source.',renderer:'Lean SVG/WGSL + Lean render plan + raw browser WebGPU; canvas presents GPU readback',generatedAt:new Date().toISOString(),node:process.version,files:entries,source};
}
export function makeServer(){return createServer(async(req,res)=>{
 const headers={'Cache-Control':'no-store','X-Content-Type-Options':'nosniff',
  'Content-Security-Policy':"default-src 'none'; script-src 'self' 'wasm-unsafe-eval'; style-src 'self'; connect-src 'self'; worker-src 'self'; img-src 'self' blob:; base-uri 'none'; frame-ancestors 'none'; form-action 'none'"};
 try{
  if(!['GET','HEAD'].includes(req.method)){res.writeHead(405,headers);res.end();return;}
  const host=req.headers.host??'';
  if(!/^(127\.0\.0\.1|localhost)(:\d+)?$/.test(host)){res.writeHead(403,headers);res.end('Loopback host required');return;}
  const u=new URL(req.url,'http://127.0.0.1'),name=u.pathname==='/'?'/index.html':u.pathname;
  if(name==='/provenance.json'){res.writeHead(200,{...headers,'Content-Type':'application/json'});res.end(req.method==='HEAD'?undefined:JSON.stringify(await provenance(),null,2));return;}
  const path=files.get(name);if(!path){res.writeHead(404,headers);res.end('Not found');return;}
  let body=await readFile(path);
  if(path.endsWith('.ts'))body=Buffer.from(stripTypeScriptTypes(body.toString('utf8'),{mode:'strip'}));
  res.writeHead(200,{...headers,'Content-Type':mime(path),'Content-Length':body.length});res.end(req.method==='HEAD'?undefined:body);
 }catch(e){console.error(e.message);res.writeHead(500,headers);res.end('Local runtime asset unavailable. See server log.');}
});}
if(process.argv[1]&&import.meta.url===pathToFileURL(resolve(process.argv[1])).href){
 const port=Number(process.argv[2]??8097);if(!Number.isInteger(port)||port<0||port>65535)throw Error('Port must be 0..65535');
 for(const path of files.values())await stat(path);
 const server=makeServer();server.listen(port,'127.0.0.1',()=>console.log(`Lean SVG + browser WebGPU: http://127.0.0.1:${server.address().port}/`));
}
