import {createServer} from 'node:http';
import {readFile} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
if(!process.env.FACTOIDAL_RENDER_MODULE)throw Error('Set FACTOIDAL_RENDER_MODULE to the actual built renderer .mjs');
const engine=resolve(process.env.FACTOIDAL_RENDER_MODULE);
const paths=new Map(['engine.mjs','engine-core.mjs','engine-worker.mjs','tests/browser-check.mjs','tests/browser-nonreturning.mjs'].map(name=>['/'+name,resolve(root,name)]));
paths.set('/',resolve(root,'tests/browser-page.html'));paths.set('/lab/.build/web-render/engines/web-render.mjs',engine);paths.set('/lab/.build/web-render/engines/web-render.wasm',engine.replace(/\.mjs$/,'.wasm'));
const server=createServer(async(req,res)=>{const path=paths.get(new URL(req.url,'http://localhost').pathname);if(!path){res.writeHead(404);res.end();return;}
 try{const body=await readFile(path);res.writeHead(200,{'Content-Type':path.endsWith('.wasm')?'application/wasm':path.endsWith('.html')?'text/html':'text/javascript','Cache-Control':'no-store'});res.end(body);}catch(error){res.writeHead(500);res.end(String(error));}});
server.listen(0,'127.0.0.1',()=>console.log('BROWSER_WORKER_TEST_URL=http://127.0.0.1:'+server.address().port+'/'));
