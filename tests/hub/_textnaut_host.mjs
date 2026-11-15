// The Hub's site for the Node tests of the Textnaut page and the notebook (and the local server,
// hub-dev-server.mjs): where each published path of /factoidal/web/hub/ comes from in this
// checkout. One table, so the tests and the server read the same files the 11ty build copies
// (docs/.eleventy.js passthroughs).
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import {createRequire} from 'node:module';
import {fileURLToPath,pathToFileURL} from 'node:url';

export const ROOT=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..','..');
const require=createRequire(import.meta.url);
export const {emitGrid}=require(path.join(ROOT,'docs/web/hub/textnaut/emit-grid.cjs'));

/** [published prefix, directory in the checkout], longest first. */
export const SITE_MAP=[
  ['/factoidal/web/hub/foafnaut/pages/',path.join(ROOT,'labs/demos/foafnaut/pages')],
  ['/factoidal/web/hub/foafnaut/fonts/noto-sans/',path.join(ROOT,'third_party/fonts/noto-sans')],
  ['/factoidal/web/hub/html-webgpu/runtime/',process.env.HUB_RUNTIME??path.join(ROOT,'docs/web/hub/html-webgpu/runtime')],
  ['/factoidal/web/hub/',path.join(ROOT,'docs/web/hub')],
];
export const RUNTIME_DIR=SITE_MAP[2][1];
export const hasRuntime=()=>fs.existsSync(path.join(RUNTIME_DIR,'web-render.wasm'))&&fs.existsSync(path.join(RUNTIME_DIR,'web-render.mjs'));

/** The checkout file of a published path, or undefined. */
export function siteFile(pathname){
  for(const [prefix,dir] of SITE_MAP){
    if(!pathname.startsWith(prefix))continue;
    const file=path.join(dir,decodeURIComponent(pathname.slice(prefix.length)));
    if(file.startsWith(dir)&&fs.existsSync(file)&&fs.statSync(file).isFile())return file;
    return undefined;
  }
  return undefined;
}

/** grid.mjs as the build makes it, written once to a temporary file; its file URL. */
let gridFile;
export function gridModuleURL(){
  if(!gridFile){
    gridFile=path.join(fs.mkdtempSync(path.join(os.tmpdir(),'hub-grid-')),'grid.mjs');
    fs.writeFileSync(gridFile,emitGrid());
  }
  return pathToFileURL(gridFile).href;
}

export const ORIGIN='https://hub.test';
/** The engine host of engine-core.mjs over this checkout, drawing with the engine's CPU pixels. */
export async function nodeHost(){
  const {default:createModule}=await import(pathToFileURL(path.join(RUNTIME_DIR,'web-render.mjs')).href);
  return {
    createModule:options=>createModule({...options,locateFile:name=>path.join(RUNTIME_DIR,name)}),
    origin:ORIGIN,
    fontURL:`${ORIGIN}/factoidal/web/hub/foafnaut/fonts/noto-sans/NotoSans-Regular.ttf`,
    async fetchBytes(url){
      const u=new URL(url);
      const file=u.origin===ORIGIN?siteFile(u.pathname):undefined;
      if(!file)throw Error(`HTTP 404 ${url}`);
      return {url,bytes:new Uint8Array(fs.readFileSync(file)),contentType:''};
    },
    gpu:async()=>undefined,
    grid:()=>import(gridModuleURL()),
  };
}
