// A local server for the Hub's Textnaut page and notebook: the 11ty build's pages (--site DIR,
// made by `npx @11ty/eleventy --output=DIR` in docs/) with the files of this checkout over them,
// so an edit to a module shows at the next reload with no build: the Hub modules of
// docs/web/hub/{textnaut,notebook,foafnaut}/, the demo pages and fonts, grid.mjs made from
// labs/demos/foafnaut/textnaut/grid.ts as the build makes it, and the engine from
// docs/web/hub/html-webgpu/runtime/ ($HUB_RUNTIME; tools/fetch-builds.sh --set foafnaut-web).
//
//   node tests/hub/hub-dev-server.mjs --site DIR [--port 8090]
//   then open http://127.0.0.1:8090/factoidal/web/hub/textnaut/ and .../web/hub/notebook/
//
// Also imported by the headless check (hub_textnaut_notebook_chrome.mjs): `serve(site, port)`.
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {siteFile,emitGrid} from './_textnaut_host.mjs';

const TYPES={'.html':'text/html; charset=utf-8','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.css':'text/css',
  '.json':'application/json','.svg':'image/svg+xml','.png':'image/png','.ttf':'font/ttf','.xml':'application/xml','.xsl':'application/xml','.txt':'text/plain'};
const typeOf=f=>TYPES[path.extname(f)]??'application/octet-stream';
const OVERLAY=/^\/factoidal\/web\/hub\/(textnaut|notebook|foafnaut)\/[^/]+\.mjs$|^\/factoidal\/web\/hub\/foafnaut\/(pages|fonts)\/|^\/factoidal\/web\/hub\/html-webgpu\/runtime\//;

export function serve(site,port=0){
  const server=http.createServer((req,res)=>{
    let pathname;
    try{pathname=decodeURIComponent(new URL(req.url,'http://x').pathname);}catch{res.writeHead(400);res.end();return;}
    const send=(status,type,body)=>{res.writeHead(status,{'content-type':type,'cache-control':'no-store'});res.end(body);};
    if(pathname==='/factoidal/web/hub/textnaut/grid.mjs'){
      try{send(200,'text/javascript',emitGrid());}catch(error){send(500,'text/plain',String(error));}
      return;
    }
    let file=OVERLAY.test(pathname)?siteFile(pathname):undefined;
    if(!file&&site&&pathname.startsWith('/factoidal/')){
      let f=path.join(site,pathname.slice('/factoidal/'.length));
      if(f.startsWith(site)&&fs.existsSync(f)&&fs.statSync(f).isDirectory())f=path.join(f,'index.html');
      if(f.startsWith(site)&&fs.existsSync(f))file=f;
    }
    if(!file){send(404,'text/plain','not found');return;}
    send(200,typeOf(file),fs.readFileSync(file));
  });
  return new Promise(resolve=>server.listen(port,'127.0.0.1',()=>resolve({server,origin:`http://127.0.0.1:${server.address().port}`})));
}

if(process.argv[1]===fileURLToPath(import.meta.url)){
  const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
  const site=opt('--site');
  if(!site)console.error('no --site: only the overlay files are served (build docs/ with eleventy for the pages)');
  const {origin}=await serve(site&&path.resolve(site),Number(opt('--port',8090)));
  console.log(`${origin}/factoidal/web/hub/textnaut/\n${origin}/factoidal/web/hub/notebook/`);
}
