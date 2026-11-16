// Origin isolation, checks C1 to C5 (issue 518, docs/designissues/2026-11-16-origin-isolation.md).
// Each check fails when the leak it names exists. A check listed in OPEN is a known fault: it is
// reported and does not fail the run, and it fails once it passes, so that it leaves the list.
// The fixtures are original: two invented origins and marker strings, no page content.
//
// The engine is the native library: FOAFNAUT_ENGINE, else .build/web-render/engines/libweb-render.dylib
// (build-web-render.sh --native); with neither it says NOT RUN. The calls go to the library's
// web_document_call directly, so an installed release (~/.foafnaut/current/foafnaut/libweb-render.dylib)
// can be checked too.
// Run: deno test --allow-read --allow-ffi --allow-env origin_isolation_test.ts
import {strict as assert} from "node:assert";

const here=new URL(".",import.meta.url).pathname;
const library=Deno.env.get("FOAFNAUT_ENGINE")??`${here}.build/web-render/engines/libweb-render.dylib`;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

/** Checks that fail today; each has an engine fix to come (issue 518). */
const OPEN=new Set<string>(Deno.env.get("ORIGIN_ISOLATION_OPEN")?.split(",").filter(Boolean)??["C1","C2","C4"]);

type Turn={session:number;logs:string[];errors:string[];navigations?:{nodeId:number;url:string}[];
  netRequests?:{id:number;method:string;url:string;resolve?:boolean}[];fetches?:{id:number;url:string;kind:string}[]};
type Call=(html:string,request:Record<string,unknown>)=>Turn&Record<string,unknown>;

function engine(path:string):Call{
  const lib=Deno.dlopen(path,{web_document_call:{parameters:["buffer","buffer","u32","u32"],result:"pointer"},
    web_render_free:{parameters:["pointer"],result:"void"}} as const);
  const c=(t:string)=>new TextEncoder().encode(t+"\0");
  return (html,request)=>{
    const p=lib.symbols.web_document_call(c(html),c(JSON.stringify({op:"scriptSession",...request})),1,1);
    if(!p)throw new Error("engine allocation failed");
    try{
      const r=JSON.parse(new Deno.UnsafePointerView(p).getCString());
      if(r?.error)throw new Error(`engine: ${r.error}`);
      return r;
    }finally{lib.symbols.web_render_free(p);}
  };
}
const b64=(bytes:Uint8Array)=>{let s="";for(const x of bytes)s+=String.fromCharCode(x);return btoa(s);};
const A="http://a.isolation.test",B="http://b.isolation.test";

/** A check: `leak` answers what leaked (empty when nothing did). */
async function check(t:Deno.TestContext,name:string,what:string,leak:()=>string[]|Promise<string[]>){
  await t.step(`${name}: ${what}`,async()=>{
    const found=await leak();
    if(OPEN.has(name)){
      if(found.length)console.log(`KNOWN OPEN ${name}: ${found.slice(0,3).join("; ")}`);
      else assert.fail(`${name} passes now: take it out of OPEN`);
      return;
    }
    assert.deepEqual(found,[],`${name} leaks`);
  });
}

Deno.test({name:"origin isolation checks C1 to C5",ignore:!exists(library)},async t=>{
  const call=engine(library);
  const start=(html:string,url:string,extra:Record<string,unknown>={})=>call(html,{action:"start",url,resources:[],engine:"bubblepop",...extra});
  const settle=(s:number)=>call("",{action:"settle",session:s,budgetMs:1000});
  const close=()=>call("",{action:"close"});

  // C1: the page's realm with any import call. A guest script engine (fixtures/isolation/import-probe.wat)
  // logs the text of every text node it can name, and tries to change each of another document.
  await check(t,"C1","no foafnaut_dom import reads or writes a node of a cross-origin frame's document",()=>{
    // Precondition, on BubblePopJS: the frame is one the page may not reach.
    let r=start(`<!doctype html><iframe src="${B}/f.html"></iframe><script>
      const f=document.querySelector('iframe');f.onload=()=>console.log('contentDocument '+f.contentDocument);</script>`,`${A}/p.html`,{navigations:true});
    r=call("",{action:"frame",session:r.session,node:r.navigations![0].nodeId,url:`${B}/f.html`,source:"<p>C1-FRAME-TEXT</p>"});
    assert.deepEqual(r.logs,["contentDocument null"],"the frame must be cross-origin to the page");
    close();
    call("",{action:"load",moduleBase64:b64(Deno.readFileSync(`${here}fixtures/isolation/import-probe.wasm`))});
    let s=call(`<!doctype html><p>C1-PAGE-TEXT</p><iframe src="${B}/f.html"></iframe><script>0</script>`,
      {action:"start",url:`${A}/p.html`,resources:[],navigations:true});
    const logs=[...s.logs];
    s=call("",{action:"frame",session:s.session,node:s.navigations![0].nodeId,url:`${B}/f.html`,source:"<p>C1-FRAME-TEXT</p>"});
    logs.push(...s.logs);
    s=call("",{action:"advance",session:s.session,ms:200});
    logs.push(...s.logs);
    close();
    assert.ok(logs.some(l=>l.endsWith(" text C1-PAGE-TEXT")),`the probe ran: ${logs.slice(0,4)}`);
    return logs.filter(l=>l.includes("C1-FRAME-TEXT")||/^wrote \d+ 0$/.test(l)||/^doc [1-9]\d* text X$/.test(l));
  });

  // C2: a canvas that has drawn an image of another origin is not origin-clean: no read-back.
  await check(t,"C2","getImageData and toDataURL refuse a canvas with another origin's image",()=>{
    // a 2x2 PNG of one colour, rgb(200,30,40)
    const png=Uint8Array.from(atob("iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAAEUlEQVR4nGM4IafxH4QZYAwASIgINVKfBLYAAAAASUVORK5CYII="),c=>c.charCodeAt(0));
    const read=(src:string)=>{
      call("",{op:"imageLoad",key:src,sha256:"c2-"+src,imageBase64:b64(png)});
      const s=start(`<!doctype html><canvas id=c width=2 height=2></canvas><img id=i src="${src}"><script>
        const x=c.getContext('2d');x.drawImage(i,0,0);
        try{console.log('pixel '+Array.from(x.getImageData(0,0,1,1).data).join(','))}catch(e){console.log('getImageData '+e.name)}
        try{console.log('dataURL '+c.toDataURL().slice(0,22))}catch(e){console.log('toDataURL '+e.name)}</script>`,`${A}/p.html`);
      close();
      return s.logs;
    };
    assert.deepEqual(read(`${A}/own.png`),["pixel 200,30,40,255","dataURL data:image/png;base64,"],"an image of the page's origin is read back");
    return read(`${B}/secret.png`).filter(l=>!["getImageData SecurityError","toDataURL SecurityError"].includes(l));
  });

  // C3: a cross-origin answer that fails the CORS check gives the page the same failure,
  // whatever the answer held (two runs).
  await check(t,"C3","a refused cross-origin answer gives a failure that does not depend on the answer",()=>{
    const page=`<!doctype html><script>
      fetch('${B}/d1').then(r=>console.log('fetch '+r.status),e=>console.log('fetch failed '+e.name+': '+e.message));
      const x=new XMLHttpRequest();x.open('GET','${B}/d2');
      x.onprogress=e=>console.log('progress '+e.loaded);
      x.onerror=e=>console.log('xhr error '+e.loaded+' '+e.total);
      x.onloadend=()=>{let h;try{h=x.getAllResponseHeaders()}catch(e){h=e.name}console.log('xhr '+x.status+' ['+x.statusText+'] ['+x.responseText+'] ['+h+'] '+x.responseURL)};
      x.send();
      fetch('${B}/d3',{mode:'no-cors'}).then(r=>r.text().then(t=>console.log('no-cors '+r.type+' '+r.status+' ['+t+'] '+[...r.headers].length)),e=>console.log('no-cors failed '+e.message));
      </script>`;
    const run=(status:number,statusText:string,body:string,fields:[string,string][])=>{
      let s=start(page,`${A}/p.html`,{network:true});
      const logs=[...s.logs];
      for(let round=0;round<4&&s.netRequests?.length;round++){
        s=call("",{action:"net",session:s.session,results:s.netRequests.map(w=>w.resolve?{id:w.id,addresses:["93.184.216.34"]}:
          {id:w.id,status,statusText,headers:[["content-type","text/plain"],...fields],bodyBase64:btoa(body)})});
        logs.push(...s.logs);
      }
      logs.push(...settle(s.session).logs);
      close();
      return logs;
    };
    const ok=run(200,"OK","C3-ALLOWED",[["access-control-allow-origin","*"]]);
    assert.ok(ok.includes("xhr 200 [OK] [C3-ALLOWED] [access-control-allow-origin: *\r\ncontent-type: text/plain\r\n] "+B+"/d2")||ok.some(l=>l.includes("[C3-ALLOWED]")),
      `an answer that passes CORS reaches the page: ${ok}`);
    const one=run(200,"C3-TEXT-ONE","C3-BODY-ONE",[["x-c3","one"]]);
    const two=run(404,"C3-TEXT-TWO-LONGER","C3-BODY-TWO-LONGER-STILL",[["x-c3","two-two"]]);
    const leaks=one.filter(l=>/C3-|x-c3/.test(l)).concat(two.filter(l=>/C3-|x-c3/.test(l)));
    if(JSON.stringify(one)!==JSON.stringify(two))leaks.push(`the two runs differ: ${JSON.stringify(one)} / ${JSON.stringify(two)}`);
    return leaks;
  });

  // C4: rules the prelude states are also kept by the engine. The prelude runs in the page's
  // realm, so a page can change what its checks call (here URL.prototype.origin).
  await check(t,"C4","a Worker's script of another origin is refused by the engine, not only by the prelude",()=>{
    const s=start(`<!doctype html><script>
      Object.defineProperty(URL.prototype,'origin',{get(){return 'same'},configurable:true});
      try{const w=new Worker('${B}/w.js');w.onmessage=e=>console.log('worker '+e.data);w.onerror=()=>console.log('worker error')}catch(e){console.log('Worker '+e.name)}
      </script>`,`${A}/p.html`);
    const asked=(s.fetches??[]).filter(f=>!f.url.startsWith(A+"/")).map(f=>`asked the host for ${f.url}`);
    if(s.fetches?.length){
      const r=call("",{action:"fetched",session:s.session,results:s.fetches.map(f=>({id:f.id,status:200,url:f.url,contentType:"text/javascript",source:"postMessage('C4-RAN')"}))});
      asked.push(...r.logs.filter(l=>l.includes("C4-RAN")));
    }
    close();
    return asked;
  });
  await check(t,"C4d","document.domain changes no access: a same-site frame of another origin stays out of reach",()=>{
    let s=start(`<!doctype html><iframe src="http://b.site.isolation.test/f.html"></iframe><script>
      try{document.domain='site.isolation.test'}catch(e){console.log('domain '+e.name)}
      Object.defineProperty(Document.prototype,'domain',{get(){return 'site.isolation.test'},set(v){},configurable:true});
      document.domain='site.isolation.test';
      const f=document.querySelector('iframe');f.onload=()=>console.log('contentDocument '+f.contentDocument);</script>`,
      "http://a.site.isolation.test/p.html",{navigations:true});
    const logs=[...s.logs];
    s=call("",{action:"frame",session:s.session,node:s.navigations![0].nodeId,url:"http://b.site.isolation.test/f.html",source:"<p>C4-FRAME</p>"});
    logs.push(...s.logs);
    close();
    assert.ok(logs.includes("domain SecurityError"),`the setter refuses: ${logs}`);
    return logs.filter(l=>l.startsWith("contentDocument")&&l!=="contentDocument null");
  });

  // C5: what one origin leaves for the next page, and the history of links.
  await check(t,"C5","window.name does not survive into the next page; :visited answers as :link",()=>{
    const s=start(`<!doctype html><script>window.name='C5-NAME';console.log('set ['+window.name+']')</script>`,`${A}/p.html`);
    assert.deepEqual(s.logs,["set [C5-NAME]"]);
    const next=start(`<!doctype html><script>console.log('name ['+window.name+']')</script>`,`${B}/next.html`);
    const leaks=next.logs.filter(l=>l!=="name []");
    const v=start(`<!doctype html><style>a{color:rgb(0,0,255)} a:visited{color:rgb(255,0,0)}</style>
      <a id=v href="${A}/p.html">self</a><a id=u href="${A}/c5-never">never</a><script>
      console.log(getComputedStyle(v).color+' '+getComputedStyle(u).color+' '+v.matches(':visited')+' '+document.querySelectorAll(':visited').length)</script>`,`${A}/p.html`);
    close();
    leaks.push(...v.logs.filter(l=>l!=="rgb(0, 0, 255) rgb(0, 0, 255) false 0"));
    return leaks;
  });
});
