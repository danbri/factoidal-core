// host_parity_test.ts: the same pages through every host's path must give the same results
// (record: docs/designissues/2026-11-14-engine-integration.md, sections 7 and 8).
//
// The WPT score is measured by one host, the runner (tests/browser-wpt/testharness-run.ts). A page a
// person sees goes through another: the window (run_html.ts), Textnaut, or the Hub. Whatever only the
// runner does for a page is a pass the browser does not have. This check runs the fixtures of
// tests/browser-integration (original pages that use features together, as testharness.js tests)
// through each path and fails when
//
//   - a subtest fails that tests/browser-integration/expected.json does not list (`known`: fails in
//     every host today; `hosts.<path>`: fails or is missing in that host only, a known divergence);
//   - the tree a render replays (parse, then the session's commands) is not the tree the page's
//     scripts see, or a box of the render is not the box the scripts read (the prepared path);
//   - a block the window drew is not where the page's style sheet puts it (the window's shot);
//   - a host builds by hand a request that docs/web/hub/foafnaut/page-load.mjs makes for every host.
//
// A listed failure that passes is reported and does not fail the check: remove it from the list.
//
// Paths: `runner` (the runner's own page path, engineBackend), `prepared` (prepareHTML of the window
// and Textnaut, a session started and moved as run_html.ts does, one render), `window` (run_html.ts
// itself, off screen, with a shot), `textnaut` (textnaut.ts --dump). The Hub's worker runs in a
// browser only: it is checked here by its source, and in Chrome by the hub_*_check.mjs files.
//
// Needs the native engine library (WEB_RENDER_LIB, or .build/web-render/engines/libweb-render.dylib);
// the window path also needs .build/native/libnative-window.dylib and a GPU. Run:
//   deno test --no-check --allow-read --allow-write --allow-net --allow-run --allow-env --allow-ffi host_parity_test.ts
import {strict as assert} from "node:assert";

const lab=new URL(".",import.meta.url).pathname,root=new URL("../../../",import.meta.url).pathname;
const library=Deno.env.get("WEB_RENDER_LIB")??`${lab}.build/web-render/engines/libweb-render.dylib`;
const windowLibrary=`${lab}.build/native/libnative-window.dylib`;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const fixtures=`${root}tests/browser-integration/`;
type Subtest={name:string;status:string;message?:string|null};
type Expected={fixtures:Record<string,{subtests:string[];known:Record<string,string>;hosts:Record<string,Record<string,string>>;
  painted:{name:string;rgb:number[];box:number[];area?:number;known?:string}[]}>};
const expected=JSON.parse(await Deno.readTextFile(`${fixtures}expected.json`)) as Expected;

// ---- the fixture server: the pages, WPT's testharness.js and this repository's report script ----
const types:Record<string,string>={html:"text/html; charset=utf-8",css:"text/css",js:"text/javascript",mjs:"text/javascript",
  json:"application/json",png:"image/png"};
function serve() {
  let port=0;
  const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen:a=>{port=a.port;}},async request=>{
    const path=decodeURIComponent(new URL(request.url).pathname);
    const file=path==="/resources/testharnessreport.js"?`${root}tests/browser-wpt/testharnessreport.js`:
      path.startsWith("/resources/")?`${root}third_party/testing/wpt-scripting${path}`:
      path.startsWith("/integration/")&&!path.includes("..")?`${fixtures}pages/${path.slice(13)}`:undefined;
    if(!file)return new Response("not found",{status:404});
    try{return new Response(await Deno.readFile(file),{headers:{"content-type":types[file.split(".").pop()??""]??"application/octet-stream"}});}
    catch{return new Response("not found",{status:404});}
  });
  return {origin:()=>`http://127.0.0.1:${port}`,stop:()=>server.shutdown()};
}

// ---- the paths ---------------------------------------------------------------------------------
const deno=Deno.execPath(),base=["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","-A","--unstable-ffi"];
async function run(args:string[],seconds:number,env:Record<string,string>={}) {
  const child=new Deno.Command(deno,{args,cwd:lab,env,stdout:"piped",stderr:"piped"}).spawn();
  const timer=setTimeout(()=>{try{child.kill("SIGKILL");}catch{/* ended */}},seconds*1000);
  const out=await child.output();clearTimeout(timer);
  return {code:out.code,stdout:new TextDecoder().decode(out.stdout),stderr:new TextDecoder().decode(out.stderr)};
}
const statusNames=["PASS","FAIL","TIMEOUT","NOTRUN","PRECONDITION_FAILED"];
/** The subtests in a host's page console lines (`page: __wpt_result {...}`). */
function resultsOf(text:string):Subtest[] {
  const out:Subtest[]=[];
  for(const line of text.split("\n")){
    const at=line.indexOf("__wpt_result ");if(at<0)continue;
    try{const r=JSON.parse(line.slice(at+13));out.push({name:r.name,status:statusNames[r.status]??String(r.status),message:r.message});}catch{/* a cut line */}
  }
  return out;
}
type Parity={harness:string;subtests:Subtest[];errors?:string[];rects?:Record<string,number[]>|null;dom?:string[][]|null;
  painted?:Record<string,number[]>;replayed?:string[][];commands?:number};
async function enginePath(which:"runner"|"prepared",url:string):Promise<Parity> {
  const r=await run([...base,"host_parity_paths.ts",which,url,"--native-engine",library],180);
  const line=r.stdout.split("\n").findLast(l=>l.startsWith("__parity "));
  assert(line,`${which}: no answer (exit ${r.code}): ${r.stderr.slice(-600)}`);
  return JSON.parse(line.slice(9));
}
async function windowPath(url:string,shot:string):Promise<{subtests:Subtest[];log:string}|undefined> {
  const r=await run([...base,"--unstable-webgpu","run_html.ts","--url",url,"--shot",shot,"--offscreen","--no-splash","--no-state",
    "--watch-sweep","7","--native-engine",library],120);
  // No GPU in this launch context (exit 2), or a window that never showed a frame (no display, a
  // missing part of the build): the path is not run, and the caller says so. A window that showed
  // the page and then failed is a failure.
  if(r.code===2||/GPU BLOCKED/.test(r.stderr)||(r.code!==0&&!r.stdout.includes('"native-html-presented"'))){
    console.log(`host parity: the window did not show the page (exit ${r.code}): ${r.stderr.trim().split("\n").slice(-2).join(" | ").slice(0,300)}`);
    return undefined;
  }
  assert.equal(r.code,0,`run_html.ts ended with ${r.code}: ${r.stderr.slice(-600)}`);
  return {subtests:resultsOf(r.stdout),log:r.stdout};
}
async function textnautPath(url:string):Promise<Subtest[]> {
  const r=await run(["run","--no-check","--no-prompt","-A","--import-map=textnaut/import_map.json","textnaut/textnaut.ts","--dump","--verbose","--width","100",url],
    120,{TEXTNAUT_NATIVE:library});
  return resultsOf(r.stderr);
}

// ---- a PNG's pixels (8-bit RGBA or RGB, not interlaced), for the window's shot --------------------
async function pngPixels(file:string):Promise<{width:number;height:number;rgba:Uint8Array}> {
  const bytes=await Deno.readFile(file),view=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  let at=8,width=0,height=0,channels=4;const idat:Uint8Array[]=[];
  while(at<bytes.length){
    const length=view.getUint32(at),type=String.fromCharCode(...bytes.subarray(at+4,at+8)),data=bytes.subarray(at+8,at+8+length);
    if(type==="IHDR"){width=view.getUint32(at+8);height=view.getUint32(at+12);
      assert.equal(data[8],8,"PNG bit depth");channels=data[9]===6?4:data[9]===2?3:0;assert(channels,"PNG colour type");assert.equal(data[12],0,"PNG interlace");}
    else if(type==="IDAT")idat.push(data);
    at+=12+length;
  }
  const packed=new Blob(idat as BlobPart[]).stream().pipeThrough(new DecompressionStream("deflate"));
  const raw=new Uint8Array(await new Response(packed).arrayBuffer()),stride=width*channels,rgba=new Uint8Array(width*height*4);
  const line=new Uint8Array(stride),above=new Uint8Array(stride);
  for(let y=0;y<height;y++){
    const filter=raw[y*(stride+1)],row=raw.subarray(y*(stride+1)+1,(y+1)*(stride+1));
    for(let x=0;x<stride;x++){
      const a=x>=channels?line[x-channels]:0,b=above[x],c=x>=channels?above[x-channels]:0;
      const p=a+b-c,pa=Math.abs(p-a),pb=Math.abs(p-b),pc=Math.abs(p-c);
      const predicted=filter===0?0:filter===1?a:filter===2?b:filter===3?(a+b)>>1:(pa<=pb&&pa<=pc?a:pb<=pc?b:c);
      line[x]=(row[x]+predicted)&255;
    }
    for(let x=0;x<width;x++){
      rgba[(y*width+x)*4]=line[x*channels];rgba[(y*width+x)*4+1]=line[x*channels+1];rgba[(y*width+x)*4+2]=line[x*channels+2];
      rgba[(y*width+x)*4+3]=channels===4?line[x*channels+3]:255;
    }
    above.set(line);
  }
  return {width,height,rgba};
}
/** The box of the pixels of one colour (each channel within 6), in rows and columns that hold at
least 4 of them, and their count: [x, y, width, height, count], or undefined when there are none. */
function colourBox(image:{width:number;height:number;rgba:Uint8Array},rgb:number[],bgra=false) {
  const rows=new Uint32Array(image.height),columns=new Uint32Array(image.width);
  const [r,g,b]=bgra?[rgb[2],rgb[1],rgb[0]]:rgb;
  for(let y=0;y<image.height;y++)for(let x=0;x<image.width;x++){
    const i=(y*image.width+x)*4;
    if(Math.abs(image.rgba[i]-r)<=6&&Math.abs(image.rgba[i+1]-g)<=6&&Math.abs(image.rgba[i+2]-b)<=6){rows[y]++;columns[x]++;}
  }
  const first=(a:Uint32Array)=>a.findIndex(n=>n>=4),last=(a:Uint32Array)=>a.findLastIndex(n=>n>=4);
  if(first(rows)<0||first(columns)<0)return undefined;
  let count=0;for(let y=first(rows);y<=last(rows);y++)count+=rows[y];
  return [first(columns),first(rows),last(columns)-first(columns)+1,last(rows)-first(rows)+1,count];
}

// ---- the check ---------------------------------------------------------------------------------
/** The subtests of one path against the list: what failed that is not listed, and what is listed and passed. */
function judge(path:string,fixture:string,subtests:Subtest[]) {
  const want=expected.fixtures[fixture],listed={...want.known,...(want.hosts[path]??{})};
  const got=new Map(subtests.map(s=>[s.name,s]));
  const unexpected:string[]=[],nowPass:string[]=[];
  for(const name of want.subtests){
    const s=got.get(name),status=s?.status??"MISSING";
    if(status==="PASS"){if(name in listed)nowPass.push(name);}
    else if(!(name in listed))unexpected.push(`${name}: ${status}${s?.message?` (${s.message})`:""}`);
  }
  for(const s of subtests)if(!want.subtests.includes(s.name))unexpected.push(`${s.name}: a subtest that expected.json does not name`);
  if(nowPass.length)console.log(`host parity: ${path} ${fixture}: ${nowPass.length} listed failures pass now; remove them from expected.json:\n  ${nowPass.join("\n  ")}`);
  return unexpected;
}

const engine=exists(library);
if(!engine)console.log(`NOT RUN: host_parity_test.ts needs the native engine library (${library})`);

for(const fixture of Object.keys(expected.fixtures)) {
  Deno.test({name:`host parity: ${fixture} gives the listed results in the runner's path and the browser hosts' path`,ignore:!engine,
    sanitizeOps:false,sanitizeResources:false},async()=>{
    const server=serve();
    try{
      const url=`${server.origin()}/integration/${fixture}`;
      const runner=await enginePath("runner",url),prepared=await enginePath("prepared",url);
      const problems=[...judge("runner",fixture,runner.subtests).map(p=>`runner: ${p}`),...judge("prepared",fixture,prepared.subtests).map(p=>`prepared: ${p}`)];
      // The tree of the render (parse and replay of the commands) is the tree the scripts see.
      assert(prepared.dom&&prepared.replayed,"the prepared path gave no tree");
      assert.deepEqual(prepared.replayed,prepared.dom,"the tree a render replays differs from the tree the page's scripts see");
      // Each box the scripts read is the box of the render.
      for(const [id,rect] of Object.entries(prepared.rects??{})){
        const box=prepared.painted?.[id];
        if(!box){if(rect[2]*rect[3]>0)problems.push(`prepared: #${id} has the box [${rect}] for scripts and no box in the render`);continue;}
        if(box.some((v,i)=>Math.abs(v-rect[i])>0.02))problems.push(`prepared: #${id} is [${rect}] for scripts and [${box.map(v=>Math.round(v*100)/100)}] in the render`);
      }
      assert.deepEqual(problems,[]);
    }finally{await server.stop();}
  });
  Deno.test({name:`host parity: ${fixture} in Textnaut`,ignore:!engine,sanitizeOps:false,sanitizeResources:false},async()=>{
    const server=serve();
    try{assert.deepEqual(judge("textnaut",fixture,await textnautPath(`${server.origin()}/integration/${fixture}`)),[]);}
    finally{await server.stop();}
  });
  Deno.test({name:`host parity: ${fixture} in the window, with what it drew`,ignore:!engine||!exists(windowLibrary),sanitizeOps:false,sanitizeResources:false},async()=>{
    const server=serve(),shot=await Deno.makeTempFile({suffix:".png"});
    try{
      const shown=await windowPath(`${server.origin()}/integration/${fixture}`,shot);
      if(!shown){console.log("NOT RUN: host parity in the window needs the window to show a frame (a GPU)");return;}
      const problems=judge("window",fixture,shown.subtests);
      // What was drawn: each block of one colour, in CSS pixels from the header's corner.
      const image=await pngPixels(shot),want=expected.fixtures[fixture].painted;
      // The surface is BGRA or RGBA by platform: the header's colour says which.
      // The first entry is the plain strip at the top of the page: the others are measured from it.
      const header=want[0],bgra=!colourBox(image,header.rgb)&&!!colourBox(image,header.rgb,true);
      const origin=colourBox(image,header.rgb,bgra);
      if(!origin)problems.push(`window: nothing drawn in the colour of the top strip, rgb(${header.rgb})`);
      else {
        const scale=origin[2]/header.box[2];
        for(const block of want){
          const found=colourBox(image,block.rgb,bgra);
          const css=found?[(found[0]-origin[0])/scale,(found[1]-origin[1])/scale+header.box[1],found[2]/scale,found[3]/scale]:undefined;
          const ok=!!css&&css.every((v,i)=>Math.abs(v-block.box[i])<=1.5)&&(block.area===undefined||Math.abs(found![4]/(scale*scale)-block.area)<=block.area*0.04);
          const said=`${block.name}: drawn ${css?`[${css.map(v=>Math.round(v*10)/10)}]${block.area===undefined?"":` area ${Math.round(found![4]/(scale*scale))}`}`:"nowhere"}, the sheet says [${block.box}]${block.area===undefined?"":` area ${block.area}`}`;
          if(ok&&block.known)console.log(`host parity: window ${fixture}: listed as not drawn right, and it is now: ${block.name}; remove 'known' from expected.json`);
          if(!ok&&!block.known)problems.push(`window: ${said}`);
        }
      }
      assert.deepEqual(problems,[]);
    }finally{await server.stop();await Deno.remove(shot).catch(()=>{});}
  });
}

// ---- the hosts' sources: the shared steps are used, not written again -----------------------------
Deno.test("host parity: the hosts take their page steps from page-load.mjs",async()=>{
  const hub=await Deno.readTextFile(`${root}docs/web/hub/foafnaut/browser-worker.mjs`);
  const win=await Deno.readTextFile(`${lab}run_html.ts`);
  // The Hub fetches the linked sheets, and every request that lays the page out has the same fields.
  assert(/loadStyleSheets\(facts\.stylesheets,/.test(hub),"the Hub's prepare does not fetch the linked style sheets");
  for(const op of ["render","nodeAt","printLayout"]){
    const uses=hub.split("\n").filter(line=>line.includes(`op:'${op}'`)&&!line.includes("print-probe.html"));
    assert(uses.length>0,`the Hub makes no ${op} request`);
    for(const use of uses)assert(use.includes("pageLayoutFields(")||use.includes("printOptions()"),`a ${op} request of the Hub is built without pageLayoutFields: ${use.trim().slice(0,160)}`);
  }
  assert(/const layout=\{\.\.\.pageLayoutFields\(/.test(hub),"the Hub's script session layout is built without pageLayoutFields");
  assert(/return \{\.\.\.pageLayoutFields\(doc\),textScalePercent:printPercent\(\)/.test(hub),"the Hub's print request is built without pageLayoutFields");
  // A script fetch is answered with the server's type and X-Content-Type-Options, never with a made-up type.
  for(const [name,source] of [["the Hub",hub],["the window",win]] as const){
    assert(source.includes("fetchedAnswer("),`${name} does not answer script fetches through fetchedAnswer`);
    assert(!/contentType:\s*["']["']/.test(source),`${name} answers a fetch with an empty Content-Type of its own`);
  }
});
