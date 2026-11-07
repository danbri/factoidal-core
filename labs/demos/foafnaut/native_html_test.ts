// Real published Lean module + file/HTTP inputs. GPU/window qualification is a
// separate desktop check; these tests never create a native window or adapter.
import {strict as assert} from "node:assert";
import {pathToFileURL} from "node:url";
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,loadFontFile,navigationURL,prepareHTML,readSource} from "./native_html_document.ts";
import {requestRenderPlan} from "./render_plan.ts";
import {startCompileWorker} from "./native_html_compile.ts";
import {READBACK_COMMANDS} from "./native_html_session.ts";

let engine=await loadHTML();
const html=(body:string,css="")=>`<!doctype html><style>body{margin:0;font-family:monospace;font-size:14px;line-height:20px}${css}</style>${body}`;
const facts={maxUniformBufferBindingSize:65536,maxStorageBufferBindingSize:134217728,maxTextureDimension2D:4096,maxBufferSize:268435456};

Deno.test("published Lean default file reflows and picks its own link",async()=>{
  const document=await prepareHTML(engine,new URL("./native-html/default.html",import.meta.url).href);
  const wide=document.compile(1280,800),narrow=document.compile(480,800);
  assert.equal(wide.abi,"lean-svg-v1");assert(wide.data.length>0);
  assert.notDeepEqual(wide.webRender.links,narrow.webRender.links);
  const link=wide.webRender.links[0] as [number,string,number,number,number,number];
  const target=engine.hit(wide,link[2]+link[4]/2,link[3]+link[5]/2);
  assert.equal(navigationURL(target!.href,document.baseURL,document.url),new URL("./native-html/next.html",import.meta.url).href);
  assert.equal(target?.sourceNode,link[0]);
  const plan=await requestRenderPlan("svg-offscreen","rgba8unorm",wide,facts);
  assert.equal(plan.uniform.bindingType,"read-only-storage");
  assert.equal(plan.uniform.bytes,wide.data.length*4);
  assert(plan.commands.includes("copyTextureToBuffer"));assert(plan.commands.includes("unmap"));
});

Deno.test("published Lean owns session history and the key table",()=>{
  let h=engine.historyPush({entries:[],index:0},"a");
  assert.equal(h.canBack,false);
  h=engine.historyPush(h.history,"b");h=engine.historyPush(h.history,"c");
  assert.deepEqual(h.history,{entries:["a","b","c"],index:2});
  const back=engine.command(6,100,h.history);
  assert.equal(back.action,"back");assert.equal(back.url,"b");assert.equal(back.canForward,true);
  assert.equal(engine.command(7,100,h.history).url,null,"forward at the end loads nothing");
  const reload=engine.command(8,100,back.history);
  assert.equal(reload.url,"b");assert.deepEqual(reload.history,back.history);
  assert.deepEqual(engine.historyPush(back.history!,"d").history,{entries:["a","b","d"],index:2},"push keeps no forward entry");
  assert.equal(engine.keyCommand("mac","command","ArrowLeft"),6);
  assert.equal(engine.keyCommand("mac","command","]"),7);
  assert.equal(engine.keyCommand("other","alt","ArrowRight"),7);
  assert.equal(engine.keyCommand("other","command","ArrowRight"),null);
});
Deno.test("published Lean owns zoom, selection and copied text",async()=>{
  const dir=await Deno.makeTempDir({prefix:"factoidal-native-select-"});
  try{
    await Deno.writeTextFile(dir+"/page.html",html('<p>Hello big world</p><p>Second <b>para</b></p>'));
    const document=await prepareHTML(engine,inputURL(dir+"/page.html",true));
    assert.deepEqual(engine.command(1,100),{action:"zoomIn",textScalePercent:110});
    assert.deepEqual(engine.command(2,100),{action:"zoomOut",textScalePercent:90});
    assert.deepEqual(engine.command(3,200),{action:"zoomReset",textScalePercent:150});
    assert.equal(engine.command(5,100).action,"selectAll");
    assert.equal(engine.pointerUp([10,10,11,10]),"click");
    assert.equal(engine.pointerUp([10,10,60,10]),"select");
    const plain=document.compile(400,200),big=document.compile(400,200,{textScalePercent:200});
    assert.notDeepEqual(plain.data,big.data,"zoom did not change the Lean scene");
    assert.equal(document.selectedText(400,200,{selection:"all"}),"Hello big world\nSecond para");
    assert.equal(document.selectedText(400,200),"");
    const run=(plain.webRender.glyphRuns as {text:string;glyphs:number[][]}[]).find(r=>r.text==="big")!;
    const [x,y]=[run.glyphs[0][1],run.glyphs[0][2]],end=run.glyphs.at(-1)!;
    assert.equal(document.selectedText(400,200,{selection:[x,y+2,end[1]+end[3],y+2]}),"big");
    const marked=document.compile(400,200,{selection:"all"});
    assert.equal(marked.primitiveCount,plain.primitiveCount+2,"one highlight for each selected line");
  }finally{await Deno.remove(dir,{recursive:true});}
});

Deno.test("actual files use Lean base and external stylesheet resolution",async()=>{
  const dir=await Deno.makeTempDir({prefix:"factoidal-native-html-"});
  try{
    await Deno.mkdir(dir+"/assets");await Deno.mkdir(dir+"/pages");
    const source=html('<base href="../assets/"><link rel="stylesheet" href="theme.css"><a href="next.html">AA BB CC</a>');
    await Deno.writeTextFile(dir+"/pages/index.html",source);
    await Deno.writeTextFile(dir+"/assets/theme.css","a{color:red;font-size:20px;line-height:24px}");
    const document=await prepareHTML(engine,inputURL(dir+"/pages/index.html",true));
    assert.equal(document.source,source);assert.equal(document.baseURL,pathToFileURL(dir+"/assets/").href);
    const artifact=document.compile(240,200);
    assert(artifact.webRender.links.every(row=>navigationURL(row[1] as string,document.baseURL,document.url)===pathToFileURL(dir+"/assets/next.html").href));
    assert(artifact.data.length>0);
    await Deno.writeTextFile(dir+"/assets/theme.css","a{color:blue;font-size:10px;line-height:14px}");
    const changed=(await prepareHTML(engine,inputURL(dir+"/pages/index.html",true))).compile(240,200);
    assert.notDeepEqual(changed.data,artifact.data,"external CSS bytes did not change the Lean scene");
  }finally{await Deno.remove(dir,{recursive:true});}
});

Deno.test("actual HTTP redirect, CSS and link retain final document base",async()=>{
  const seen:string[]=[];
  const source=html('<link rel="stylesheet" href="theme.css"><a href="next.html">A link</a>');
  const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen:()=>{}},request=>{
    const path=new URL(request.url).pathname;seen.push(path);
    if(path==="/redirect")return new Response(null,{status:302,headers:{location:"/pages/index.html"}});
    if(path==="/pages/index.html")return new Response(source);
    if(path==="/pages/theme.css")return new Response("a{color:#2050b0}");
    return new Response("missing",{status:404});
  });
  try{
    const origin=`http://127.0.0.1:${server.addr.port}`;
    const document=await prepareHTML(engine,origin+"/redirect");
    assert.equal(document.source,source);assert.equal(document.url,origin+"/pages/index.html");
    const artifact=document.compile(240,160);
    assert(artifact.webRender.links.every(row=>navigationURL(row[1] as string,document.baseURL,document.url)===origin+"/pages/next.html"));
    assert.deepEqual(seen,["/redirect","/pages/index.html","/pages/theme.css"]);
    await assert.rejects(()=>readSource(origin+"/missing"),/HTTP 404/);
  }finally{await server.shutdown();}
});

Deno.test("XML pages run their XSLT stylesheet in Lean, and refusals are visible",async()=>{
  for(const [name,title] of [["books-xslt1","Web standards reading (XSLT 1.0)"],["books-xslt4","Web standards reading (XSLT 4.0)"],["books-svg","Web standards reading as a chart"]]){
    const document=await prepareHTML(engine,new URL(`./pages/${name}.xml`,import.meta.url).href);
    assert.equal(document.title,title);
    const artifact=document.compile(640,480);
    assert(artifact.primitiveCount>0);
    assert(artifact.webRender.links.some(row=>row[1]==="index.html"));
  }
  const dir=await Deno.makeTempDir({prefix:"factoidal-native-xslt-"});
  const page=dir+"/p.xml",sheet=dir+"/s.xsl",url=pathToFileURL(page).href;
  const xsl=(body:string,version="1.0")=>`<xsl:stylesheet version="${version}" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">${body}</xsl:stylesheet>`;
  try{
    await Deno.writeTextFile(page,'<?xml version="1.0"?><?xml-stylesheet type="text/xsl" href="s.xsl"?><r/>');
    await assert.rejects(()=>prepareHTML(engine,url),/NotFound|No such file/);
    await Deno.writeTextFile(sheet,xsl('<xsl:template match="/"><p>x</p></xsl:template>',"9.0"));
    await assert.rejects(()=>prepareHTML(engine,url),/unsupported XSLT version/);
    await Deno.writeTextFile(sheet,xsl('<xsl:template name="f"><xsl:call-template name="f"/></xsl:template><xsl:template match="/"><xsl:call-template name="f"/></xsl:template>'));
    await assert.rejects(()=>prepareHTML(engine,url));
    await Deno.writeTextFile(sheet,xsl('<xsl:template name="f"><xsl:call-template name="f"/></xsl:template><xsl:template match="/"><xsl:call-template name="f"/></xsl:template>',"3.0"));
    await assert.rejects(()=>prepareHTML(engine,url));
    // The engine must still work after a refused stylesheet.
    assert((await prepareHTML(engine,new URL("./pages/books-xslt1.xml",import.meta.url).href)).compile(640,480).primitiveCount>0);
    await Deno.writeTextFile(page,'<?xml version="1.0"?><?xml-stylesheet type="text/xsl" href="file:///etc/hosts"?><r/>');
    await assert.rejects(()=>prepareHTML(engine,url));
    assert.throws(()=>navigationURL("file:///etc/hosts","https://example.test/p.xml","https://example.test/p.xml"),/Remote HTML cannot/);
  }finally{await Deno.remove(dir,{recursive:true});}
});

Deno.test("scripts are refused, and unsupported CSS and layout are not",async()=>{
  const dir=await Deno.makeTempDir({prefix:"factoidal-native-html-refusal-"});
  const path=dir+"/page.html",url=pathToFileURL(path).href;
  try{
    await Deno.writeTextFile(path,html('<script>throw Error("must not execute")</script><p>Text</p>'));
    await assert.rejects(()=>prepareHTML(engine,url),/does not execute scripts/);
    await Deno.writeTextFile(path,html('<script type="application/ld+json">{"name":"inert"}</script><p>Text</p>'));
    assert((await prepareHTML(engine,url)).compile(240,160).data.length>0);
    // CSS we can not use is dropped, as in any browser: the page still shows.
    await Deno.writeTextFile(path,html("<p>Text</p>","p{font-family:Arial}.a > b{color:red}@media (max-width:1px){p{color:red}}"));
    assert((await prepareHTML(engine,url)).compile(240,160).data.length>0);
    await Deno.writeTextFile(path,html('<div style="display:grid">Unsupported grid</div>'));
    assert((await prepareHTML(engine,url)).compile(240,160).data.length>0);
  }finally{await Deno.remove(dir,{recursive:true});}
});

Deno.test("a live frame paints the same data as a full frame, with one probe",()=>{
  const source=html("<h1>Live</h1><p>frame</p>");
  const full=engine.compile(source,400,300,{}),live=engine.compile(source,400,300,{live:true});
  assert.equal(full.checks.length,6);
  assert.equal(live.checks.length,1);
  assert.deepEqual(live.data,full.data);
  assert.deepEqual(live.tiles,full.tiles);
  assert.equal(live.wgsl,full.wgsl);
  assert.deepEqual(live.checks[0],full.checks.find(p=>p.x===200&&p.y===150));
});

Deno.test("the bytes Lean sends are the floats of the text form, exactly",async()=>{
  for(const name of ["index.html","settings.html"]){
    const source=await Deno.readTextFile(new URL("./pages/"+name,import.meta.url));
    const options={url:"file:///"+name,resources:[]};
    const bytes=engine.compile(source,800,600,options),text=engine.compile(source,800,600,{...options,binary:false});
    assert.ok(bytes.data instanceof Float32Array&&Array.isArray(text.data));
    assert.equal(bytes.data.length,text.data.length);
    assert.deepEqual([...bytes.data],[...new Float32Array(text.data)]);
  }
});

Deno.test("the first website renders from its mirror, with its links",async()=>{
  const root=new URL("../../../third_party/testing/old-web/info.cern.ch/",import.meta.url);
  const pages:string[]=[];
  const walk=async(dir:URL,path:string)=>{for await(const entry of Deno.readDir(dir)){
    if(entry.isDirectory)await walk(new URL(entry.name+"/",dir),path+entry.name+"/");else pages.push(path+entry.name);
  }};
  await walk(root,"");
  assert(pages.length>=23);
  for(let index=0;index<pages.length;index++){
    const path=pages[index];
    // One engine would run out of memory on the whole set: a known render leak.
    if(index%10===9)engine=await loadHTML();
    const frame=(await prepareHTML(engine,new URL(path,root).href)).compile(1000,800);
    assert(frame.data.length>0,path);
  }
});

Deno.test("a font file draws the page through Lean alone, and no text stops it",async()=>{
  const fonts=await loadHTML();
  const page=html("<h1>World Wide Web</h1><p>office AVATAR</p><p style='font-size:13.5px'>fractional size</p><p>שלום سلام ∑ 你好</p>");
  const options={url:"https://example.test/",resources:[]};
  const bitmap=fonts.compile(page,800,500,options);
  const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url);
  assert.deepEqual(await loadFontFile(fonts,font.pathname,"Noto Sans"),{family:"Noto Sans",glyphs:3884});
  const first=fonts.compile(page,800,500,options);
  assert.notDeepEqual(first.data,bitmap.data);
  assert.ok(first.primitiveCount<bitmap.primitiveCount,"one primitive for each glyph, not for each bitmap cell");
  assert.deepEqual(fonts.compile(page,800,500,options).data,first.data,"the held words draw the same page");
  assert.throws(()=>fonts.fontLoad("not base64!","x","y"),/invalid base64/);
  assert.throws(()=>fonts.fontLoad(btoa("not a font at all"),"x","y"),/font\.file/);
});

Deno.test("resource size, resource count, cancellation and URL schemes are bounded",async()=>{
  const dir=await Deno.makeTempDir({prefix:"factoidal-native-html-limits-"});
  try{
    const path=dir+"/page.html",url=pathToFileURL(path).href;
    await Deno.writeTextFile(path,"x".repeat(1048577));
    await assert.rejects(()=>readSource(url),/exceeds 1 MiB/);
    await Deno.writeTextFile(path,html(Array.from({length:17},(_,n)=>`<link rel="stylesheet" href="${n}.css">`).join("")));
    await assert.rejects(()=>prepareHTML(engine,url),/16 external stylesheets/);
    const controller=new AbortController();controller.abort();
    await assert.rejects(()=>prepareHTML(engine,url,controller.signal),/abort/i);
    await Deno.writeFile(path,new Uint8Array([0x63,0x61,0x66,0xe9]));
    assert.equal((await readSource(url)).source,"café");
    const css="/*"+"x".repeat(1048572)+"*/";
    await Deno.writeTextFile(path,html(Array.from({length:5},(_,n)=>`<link rel="stylesheet" href="${n}.css">`).join("")));
    for(let n=0;n<5;n++)await Deno.writeTextFile(dir+`/${n}.css`,css);
    await assert.rejects(()=>prepareHTML(engine,url),/stylesheets exceed 4 MiB/);
    assert.throws(()=>inputURL("javascript:alert(1)"),/file, HTTP and HTTPS/);
    assert.throws(()=>inputURL("https://name:secret@example.invalid/"),/Credentials/);
    assert.throws(()=>inputURL("file://remotehost/private/file.html"),/Remote file URL hosts/);
    assert.throws(()=>navigationURL("file:///etc/passwd","https://example.test/","https://example.test/"),/Remote HTML cannot/);
    assert.throws(()=>navigationURL("local.css","file:///etc/","https://example.test/"),/Remote HTML cannot/);
  }finally{await Deno.remove(dir,{recursive:true});}
});
Deno.test("the interactive FOAF graph runs as a browser page through Lean",async()=>{
  const engine=await loadHTML(),shell={scale:1,tabs:[{title:"FOAF graph"}]};
  const rdf=await Deno.readTextFile(new URL("./pages/foaf-demo.ttl",import.meta.url));
  const start=engine.graphStart(rdf,1000,680,shell);
  assert.ok(start.commands.includes("render")&&start.commands.includes("startClock"));
  const position=(model:string)=>JSON.parse(model).positions as number[][];
  const [x,y]=position(start.model)[3];
  // Window pixels of an app point: the chrome is above, and the app is 1000 by 700 inside.
  const top=65,screenY=(v:number)=>Math.round(v*(680-top)/700+top);
  const press=engine.graphEvent(start.model,2,x,screenY(y),1000,shell);
  assert.equal(JSON.parse(press.model).selection,4);
  const moved=engine.graphEvent(press.model,3,x-30,screenY(y),1000,shell);
  assert.notDeepEqual(position(moved.model)[3],[x,y]);
  // A node may not cover another: a drag stops at the last legal position.
  let crowded=moved.model;
  const target=position(crowded)[0];
  for(let i=1;i<=40;i++){
    const [px,py]=position(crowded)[3];
    crowded=engine.graphEvent(crowded,3,Math.round(px+(target[0]-px)/4),screenY(py+(target[1]-py)/4),1000,shell).model;
  }
  const stopped=position(crowded)[3];
  assert.ok(Math.abs(stopped[0]-target[0])>100||Math.abs(stopped[1]-target[1])>60,`node 3 covers node 0: ${stopped} ${target}`);
  const held=engine.graphEvent(crowded,3,target[0],screenY(target[1]),1000,shell);
  assert.deepEqual(position(held.model)[3],stopped);
  // It can still move away.
  const freed=engine.graphEvent(held.model,3,x,screenY(y),1000,shell);
  assert.notDeepEqual(position(freed.model)[3],stopped);
  const page=engine.graphPage(crowded);
  assert.match(page,/<svg/);
  assert.ok(engine.compile(page,1000,680,{url:"foafnaut:graph",resources:[],shell}).primitiveCount>100);
  assert.deepEqual(engine.shellLink("foafnaut:graph"),{go:"command",name:"graph",argument:""});
});

Deno.test("compile in a worker answers what the main-thread engine answers, and every readback command is filtered by name",async()=>{
  const document=await prepareHTML(engine,new URL("./native-html/default.html",import.meta.url).href);
  const request=document.request(640,400,{textScalePercent:125});
  const local=engine.compile(request.source,640,400,request.options);
  const client=await startCompileWorker();
  try{
    const remote=await client.compile(request.source,640,400,request.options);
    assert.equal(remote.artifact.wgsl,local.wgsl);
    assert.deepEqual([...remote.artifact.data],[...local.data]);
    assert.deepEqual(remote.artifact.checks,local.checks);
    // A Lean error comes back as an error and does not stop the worker.
    await assert.rejects(client.compile("",0,0,{}));
    assert(client.alive);
  }finally{client.terminate();}
  const plan=await requestRenderPlan("svg-offscreen","rgba8unorm",local,facts);
  // Commands left after the filter draw and submit; none of them reads the window back.
  const kept=plan.commands.filter(command=>!READBACK_COMMANDS.has(command));
  assert(kept.includes("draw")&&kept.includes("submit"));
  assert(plan.commands.filter(command=>READBACK_COMMANDS.has(command)).length>=3);
});
