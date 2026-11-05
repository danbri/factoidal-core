// Real published Lean module + file/HTTP inputs. GPU/window qualification is a
// separate desktop check; these tests never create a native window or adapter.
import {strict as assert} from "node:assert";
import {pathToFileURL} from "node:url";
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,navigationURL,prepareHTML,readSource} from "./native_html_document.ts";
import {requestRenderPlan} from "./render_plan.ts";

const engine=await loadHTML();
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
    assert.deepEqual(engine.command(3,200),{action:"zoomReset",textScalePercent:100});
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

Deno.test("unsupported scripts, fonts and layout fail explicitly",async()=>{
  const dir=await Deno.makeTempDir({prefix:"factoidal-native-html-refusal-"});
  const path=dir+"/page.html",url=pathToFileURL(path).href;
  try{
    await Deno.writeTextFile(path,html('<script>throw Error("must not execute")</script><p>Text</p>'));
    await assert.rejects(()=>prepareHTML(engine,url),/does not execute scripts/);
    await Deno.writeTextFile(path,html('<script type="application/ld+json">{"name":"inert"}</script><p>Text</p>'));
    assert((await prepareHTML(engine,url)).compile(240,160).data.length>0);
    await Deno.writeTextFile(path,html("<p>Text</p>","p{font-family:Arial}"));
    await assert.rejects(()=>prepareHTML(engine,url),/ASCII bitmap font profile/);
    await Deno.writeTextFile(path,html('<div style="display:grid">Unsupported grid</div>'));
    await assert.rejects(async()=>{(await prepareHTML(engine,url)).compile(240,160);},/Lean HTML/);
  }finally{await Deno.remove(dir,{recursive:true});}
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
    await Deno.writeFile(path,new Uint8Array([255]));
    await assert.rejects(()=>readSource(url),/UTF|decode|valid/i);
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
