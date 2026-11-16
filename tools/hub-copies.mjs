#!/usr/bin/env node
// Hub copies: unpack the snapshots of the pages in labs/demos/foafnaut/realpages/hub-copies.json
// into the built site, for docs/web/hub/foafnaut/copies.mjs (the Hub reads no other site; it
// shows these openly licensed pages from its copies, with their licence and attribution).
//
//   node tools/hub-copies.mjs --realpages DIR --out SITE/web/hub/foafnaut/copies [--list FILE] [--max-mb 60]
//
// DIR is third_party/realpages of a danbri/factoidal-builds checkout: <site>/<id>-<YYYYMMDD>.zip,
// made by labs/demos/foafnaut/realpages/snapshot.ts. The newest zip of each id is used; a page
// with none is left out and named on standard error. Out: index.json ({copies, urls}) and one
// file per response body, <id>/<n>.bin. The .bin name makes the server send the bytes as
// application/octet-stream, so no copied page runs as a page of this site if opened directly;
// the Hub gives the engine the recorded Content-Type instead. Responses from the hosts in a
// page's `drop` list are left out. Needs `unzip`.
import fs from 'node:fs';import path from 'node:path';import os from 'node:os';import {execFileSync} from 'node:child_process';

const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const here=path.dirname(new URL(import.meta.url).pathname);
const listFile=opt('--list',path.join(here,'../labs/demos/foafnaut/realpages/hub-copies.json'));
const realpages=opt('--realpages'),out=opt('--out'),maxBytes=Number(opt('--max-mb','60'))*1048576;
if(!realpages||!out){console.error('usage: hub-copies.mjs --realpages DIR --out DIR [--list FILE] [--max-mb 60]');process.exit(2);}

const list=JSON.parse(fs.readFileSync(listFile,'utf8'));
const zips=[];
for(const site of fs.readdirSync(realpages,{withFileTypes:true}))if(site.isDirectory())
  for(const f of fs.readdirSync(path.join(realpages,site.name)))if(f.endsWith('.zip'))zips.push(path.join(realpages,site.name,f));
const newest=id=>zips.filter(z=>new RegExp(`^${id.replace(/[-]/g,'\\-')}-\\d{8}\\.zip$`).test(path.basename(z))).sort().at(-1);

fs.rmSync(out,{recursive:true,force:true});fs.mkdirSync(out,{recursive:true});
const urls={},copies=[];let total=0,missing=0;
const header=(e,name)=>(e.headers??[]).find(([k])=>k.toLowerCase()===name)?.[1];
for(const page of list.pages){
  const zip=newest(page.id);
  if(!zip){console.error(`hub-copies: no snapshot for ${page.id} (${page.url})`);missing++;continue;}
  const tmp=fs.mkdtempSync(path.join(os.tmpdir(),'hub-copy-'));
  try{
    execFileSync('unzip',['-q','-o',zip,'-d',tmp]);
    const m=JSON.parse(fs.readFileSync(path.join(tmp,'manifest.json'),'utf8'));
    const drop=new Set(page.drop??[]);
    fs.mkdirSync(path.join(out,page.id));
    let n=0,kept=0;
    for(const e of m.entries){
      let u;try{u=new URL(e.url);}catch{continue;}
      u.hash='';const key=u.href;
      if(urls[key]||drop.has(u.hostname))continue;
      const location=header(e,'location');
      if(e.status>=300&&e.status<400&&location){urls[key]={id:page.id,location:new URL(location,key).href};continue;}
      if(e.status!==200||!e.body)continue;
      const bytes=fs.readFileSync(path.join(tmp,e.body));
      if(total+bytes.length>maxBytes){console.error(`hub-copies: past ${maxBytes} bytes, ${key} left out`);continue;}
      const file=`${page.id}/${++n}.bin`;
      fs.writeFileSync(path.join(out,file),bytes);total+=bytes.length;kept++;
      urls[key]={id:page.id,file,type:header(e,'content-type')??''};
    }
    // The page's own address answers even when the document came by a redirect.
    if(!urls[page.url]){const doc=m.entries.find(e=>e.status===200&&e.body);if(doc)urls[page.url]=urls[new URL(doc.url).href];}
    copies.push({id:page.id,url:page.url,title:page.title,lang:page.lang,licence:page.licence,attribution:page.attribution,fetched:m.fetched_at,snapshot:path.relative(realpages,zip),responses:kept});
    console.log(`hub-copies: ${page.id} ${kept} responses from ${path.relative(realpages,zip)}`);
  }finally{fs.rmSync(tmp,{recursive:true,force:true});}
}
fs.writeFileSync(path.join(out,'index.json'),JSON.stringify({note:'Hub copies of openly licensed pages (tools/hub-copies.mjs); each with its licence and attribution.',copies,urls})+'\n');
console.log(`hub-copies: ${copies.length} pages, ${Object.keys(urls).length} addresses, ${(total/1048576).toFixed(1)} MB${missing?`, ${missing} without a snapshot`:''}`);
