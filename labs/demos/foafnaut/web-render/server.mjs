#!/usr/bin/env node
// Local source/runtime transport. No HTML parser, CSS cascade or layout here.
import {createServer} from 'node:http';
import {readFile,stat} from 'node:fs/promises';
import {dirname,resolve} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {stripTypeScriptTypes} from 'node:module';
import {createHash} from 'node:crypto';
import {fetchResourceBytes,ResourceError} from './resource-broker.mjs';
import {createFontBroker} from '../tools/font-broker.mjs';
const here=dirname(fileURLToPath(import.meta.url)),lab=resolve(here,'..'),files=new Map();
for(const name of ['index.html','app.mjs','engine.mjs','style.css','navigation.mjs','resource-client.mjs','resource-broker.mjs','document-client.mjs'])files.set('/'+name,resolve(here,name));
for(const name of ['default.html','mvp.html','boxes.html','flow.html','links.html','graph.nt','scripted.html'])files.set('/fixtures/'+name,resolve(here,'fixtures',name));
for(const name of ['gpu_transport.ts','render_plan.ts'])files.set('/lab/'+name,resolve(lab,name));
for(const name of ['web-render.mjs','web-render.wasm'])files.set('/lab/.build/web-render/engines/'+name,resolve(lab,'.build/web-render/engines',name));
for(const name of ['render-plan.mjs','render-plan.wasm'])files.set('/lab/.build/engines/'+name,resolve(lab,'.build/web-render/engines',name));
for(const name of ['session.mjs','worker.mjs','quickjs.mjs','guest.mjs','lean-dom.mjs'])files.set('/script-engine/'+name,resolve(here,'script-engine',name));
files.set('/lab/.build/script-engine/qjs-wasi-reactor.wasm',resolve(lab,'.build/script-engine/qjs-wasi-reactor.wasm'));
files.set('/source-witness.json',resolve(lab,'.build/web-render/source-witness.json'));
const headers={'Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Content-Security-Policy':"default-src 'none'; script-src 'self' 'wasm-unsafe-eval'; worker-src 'self'; style-src 'self'; connect-src 'self'; img-src 'self' blob:; base-uri 'none'; frame-ancestors 'none'; form-action 'none'"};
const mime=path=>path.endsWith('.wasm')?'application/wasm':path.endsWith('.html')?'text/html; charset=utf-8':path.endsWith('.css')?'text/css; charset=utf-8':path.endsWith('.json')?'application/json':'text/javascript; charset=utf-8';
export function makeServer(){const fontBroker=createFontBroker();return createServer(async(req,res)=>{
 try{
  if(!/^(127\.0\.0\.1|localhost)(:\d+)?$/.test(req.headers.host??'')){res.writeHead(403,headers);res.end('Loopback host required');return;}
  const u=new URL(req.url,'http://127.0.0.1'),name=u.pathname==='/'?'/index.html':u.pathname;
  if(req.method==='GET'&&name==='/resource'){
    if((req.headers.origin&&req.headers.origin!==`http://${req.headers.host}`)||req.headers['sec-fetch-site']==='cross-site'){res.writeHead(403,headers);res.end('Same-origin resource request required');return;}
    const maxBytes=Number(u.searchParams.get('maxBytes')??1048576);
    if(!Number.isSafeInteger(maxBytes)||maxBytes<1||maxBytes>16777216)throw new ResourceError('Invalid resource byte limit',400);
    const controller=new AbortController();res.on('close',()=>{if(!res.writableEnded)controller.abort();});
    const resource=await fetchResourceBytes(u.searchParams.get('url'),{maxBytes,signal:controller.signal});
    console.log(JSON.stringify({type:'resource-fetch',requestedURL:resource.requestedURL,url:resource.url,bytes:resource.bytes.length,contentType:resource.contentType}));
    res.writeHead(200,{...headers,'Content-Type':'application/octet-stream','Content-Disposition':'attachment','Content-Length':resource.bytes.length,'X-Factoidal-Content-Type':resource.contentType,'X-Factoidal-Resource-URL':resource.url,'X-Factoidal-Network-Capability':'native-loopback-broker'});res.end(resource.bytes);return;
  }
  if(req.method==='POST'&&name==='/font-data'){
    if(req.headers.origin!==`http://${req.headers.host}`||!(req.headers['content-type']??'').startsWith('application/json')){res.writeHead(403,headers);res.end('Same-origin JSON required');return;}
    const chunks=[];let size=0;for await(const chunk of req){size+=chunk.length;if(size>1572864){res.writeHead(413,headers);res.end('Font request too large');return;}chunks.push(chunk);}
    let request;try{request=JSON.parse(Buffer.concat(chunks).toString('utf8'));}catch{res.writeHead(400,headers);res.end('Invalid JSON');return;}
    const data=JSON.stringify(await fontBroker(request));if(Buffer.byteLength(data)>16777216)throw new ResourceError('Font response too large',413);
    res.writeHead(200,{...headers,'Content-Type':'application/json'});res.end(data);return;
  }
  if(req.method==='POST'&&name==='/events'){
    if(req.headers.origin!==`http://${req.headers.host}`||!(req.headers['content-type']??'').startsWith('application/json')){res.writeHead(403,headers);res.end('Same-origin JSON required');return;}
    const chunks=[];let size=0;for await(const chunk of req){size+=chunk.length;if(size>16384){res.writeHead(413,headers);res.end('Event too large');return;}chunks.push(chunk);}
    let event;try{event=JSON.parse(Buffer.concat(chunks).toString('utf8'));}catch{res.writeHead(400,headers);res.end('Invalid JSON');return;}
    if(!event||typeof event!=='object'||Array.isArray(event)||event.type!=='link-click'||typeof event.href!=='string'||Buffer.byteLength(event.href,'utf8')>2048||!Number.isSafeInteger(event.sourceNode)||event.sourceNode<0||event.sourceNode>1048576||![event.x,event.y].every(n=>Number.isFinite(n)&&n>=0&&n<=4096)){res.writeHead(400,headers);res.end('Invalid link event');return;}
    const record={type:'lean-link-click',sourceNode:event.sourceNode,href:event.href,x:event.x,y:event.y};
    console.log(JSON.stringify(record));
    res.writeHead(200,{...headers,'Content-Type':'application/json'});res.end(JSON.stringify({ok:true}));return;
  }
  if(!['GET','HEAD'].includes(req.method)){res.writeHead(405,headers);res.end();return;}
  if(name==='/provenance.json'){
    const entries=[];for(const [url,path]of files){const data=await readFile(path);entries.push({url,bytes:data.length,sha256:createHash('sha256').update(data).digest('hex')});}
    res.writeHead(200,{...headers,'Content-Type':'application/json'});res.end(JSON.stringify({format:'factoidal-web-render-local-v1',renderer:'Lean HTML/DOM/CSS/layout/common scene + existing Lean SVG WGSL + raw WebGPU transport',files:entries},null,2));return;
  }
  const path=files.get(name);if(!path){res.writeHead(404,headers);res.end('Not found');return;}
  let body=await readFile(path);if(path.endsWith('.ts'))body=Buffer.from(stripTypeScriptTypes(body.toString('utf8'),{mode:'strip'}));
  res.writeHead(200,{...headers,'Content-Type':mime(path),'Content-Length':body.length});res.end(req.method==='HEAD'?undefined:body);
 }catch(error){console.error(error);if(res.destroyed)return;res.writeHead(error instanceof ResourceError?error.status:500,{...headers,'Content-Type':'text/plain; charset=utf-8'});res.end(error instanceof ResourceError?error.message:`Local renderer request failed: ${error.message??error}`);}
});}
if(process.argv[1]&&import.meta.url===pathToFileURL(resolve(process.argv[1])).href){
 for(const path of files.values())await stat(path);
 const port=Number(process.argv[2]??8099),server=makeServer();
 server.listen(port,'127.0.0.1',()=>console.log(`Lean HTML/CSS WebGPU: http://127.0.0.1:${server.address().port}/`));
}
