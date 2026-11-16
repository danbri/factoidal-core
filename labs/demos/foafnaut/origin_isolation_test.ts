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

/** Checks that fail on this tree's engine; each has an engine fix to come (none now).
An engine from before the C1, C2 and C4 fixes (release 1b2fc90d578e) needs
ORIGIN_ISOLATION_OPEN=C1,C2,C2b,C2c,C2d,C4. */
const OPEN=new Set<string>(Deno.env.get("ORIGIN_ISOLATION_OPEN")?.split(",").filter(Boolean)??[]);

type Turn={session:number;logs:string[];errors:string[];navigations?:{nodeId:number;url:string}[];
  netRequests?:{id:number;method:string;url:string;resolve?:boolean}[];fetches?:{id:number;url:string;kind:string}[]};
type Call=(html:string,request:Record<string,unknown>)=>Turn&Record<string,unknown>;

function engine(path:string):Call{
  const lib=Deno.dlopen(path,{web_document_call:{parameters:["buffer","buffer","u32","u32"],result:"pointer"},
    web_render_free:{parameters:["pointer"],result:"void"}} as const);
  const c=(t:string)=>new TextEncoder().encode(t+"\0");
  return (html,request)=>{
    const p=lib.symbols.web_document_call(c(html),c(JSON.stringify(request.op?request:{op:"scriptSession",...request})),1,1);
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

  // C2: a canvas that has drawn an image of another origin is not origin-clean: no read-back,
  // through any path that carries the flag (HTML §4.12.5.6), and no image bytes in the realm.
  // a 2x2 PNG of one colour, rgb(200,30,40)
  const pngB64="iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAAEUlEQVR4nGM4IafxH4QZYAwASIgINVKfBLYAAAAASUVORK5CYII=";
  const png=Uint8Array.from(atob(pngB64),c=>c.charCodeAt(0));
  const hold=(key:string)=>call("",{op:"imageLoad",key,sha256:"c2-"+key,imageBase64:b64(png)});
  const run=(html:string)=>{const s=start(html,`${A}/p.html`);const logs=[...s.logs];logs.push(...settle(s.session).logs);close();return logs;};
  // the read-backs of canvas c, each logged as its pixels or the exception's name
  const reads=`
    const tryLog=(w,f)=>{try{console.log(w+' '+f())}catch(e){console.log(w+' '+e.name)}};
    tryLog('getImageData',()=>Array.from(c.getContext('2d').getImageData(0,0,1,1).data).join(','));
    tryLog('toDataURL',()=>c.toDataURL().slice(0,22));
    tryLog('toBlob',()=>{c.toBlob(()=>{});return 'called'});`;
  const refused=["getImageData SecurityError","toDataURL SecurityError","toBlob SecurityError"];
  await check(t,"C2","getImageData, toDataURL and toBlob refuse a canvas with another origin's image",()=>{
    const read=(src:string,extra="")=>{
      hold(src);
      return run(`<!doctype html><canvas id=c width=2 height=2></canvas><img id=i src="${src}"><script>${extra}
        c.getContext('2d').drawImage(i,0,0);${reads}</script>`);
    };
    assert.deepEqual(read(`${A}/own.png`),["getImageData 200,30,40,255","toDataURL data:image/png;base64,","toBlob called"],"an image of the page's origin is read back");
    // the engine decides, not the prelude: what the page says of origins changes nothing
    const spoof=`Object.defineProperty(URL.prototype,'origin',{get(){return '${A}'},configurable:true});
      try{Object.defineProperty(location,'origin',{get(){return '${B}'},configurable:true})}catch(e){}`;
    const leaks=(got:string[])=>[...got.filter(l=>!refused.includes(l)),...refused.filter(r=>!got.includes(r)).map(r=>`missing: ${r}`)];
    return [...leaks(read(`${B}/secret.png`)),...leaks(read(`${B}/secret2.png`,spoof))];
  });
  await check(t,"C2c","the flag goes with the pixels: canvases, patterns, ImageBitmaps, OffscreenCanvas; it stays until new dimensions",()=>{
    hold(`${B}/secret.png`);
    const logs=run(`<!doctype html><canvas id=d width=2 height=2></canvas><canvas id=c width=2 height=2></canvas><img id=i src="${B}/secret.png"><script>
      const x=d.getContext('2d');x.drawImage(i,0,0);
      const log=(w,f)=>{try{console.log(w+' '+f())}catch(e){console.log(w+' '+e.name)}};
      const fresh=()=>{const e=document.createElement('canvas');e.width=2;e.height=2;return e};
      const px=e=>Array.from(e.getContext('2d').getImageData(0,0,1,1).data).join(',');
      { const e=fresh();e.getContext('2d').drawImage(d,0,0);log('canvas',()=>px(e)); }
      { const e=fresh(),g=e.getContext('2d'),p=g.createPattern(d,'repeat');g.fillStyle=p;log('fillStyle',()=>px(e)); }
      { const e=fresh(),g=e.getContext('2d');g.strokeStyle=g.createPattern(i,'repeat');log('strokeStyle',()=>px(e)); }
      { const o=new OffscreenCanvas(2,2),g=o.getContext('2d');g.drawImage(i,0,0);log('offscreen',()=>Array.from(g.getImageData(0,0,1,1).data).join(','));
        o.convertToBlob().then(()=>console.log('convertToBlob ok'),e=>console.log('convertToBlob '+e.name));
        const b=o.transferToImageBitmap(),e=fresh();e.getContext('2d').drawImage(b,0,0);log('transferToImageBitmap',()=>px(e)); }
      createImageBitmap(d).then(b=>{const e=fresh();e.getContext('2d').drawImage(b,0,0);log('createImageBitmap',()=>px(e))});
      { const e=fresh(),g=e.getContext('2d');g.drawImage(i,0,0);g.clearRect(0,0,2,2);g.putImageData(new ImageData(2,2),0,0);log('cleared',()=>px(e));
        e.width=3;log('resized',()=>px(e)); }
      </script>`);
    const want=["canvas SecurityError","fillStyle SecurityError","strokeStyle SecurityError","offscreen SecurityError",
      "transferToImageBitmap SecurityError","cleared SecurityError","convertToBlob SecurityError","createImageBitmap SecurityError"];
    // new dimensions clear the bitmap and the flag (HTML §4.12.5.6); an engine that keeps both
    // (setting width does not resize the bitmap yet) must keep refusing: either is safe
    const resized=logs.filter(l=>l.startsWith("resized ")&&l!=="resized 0,0,0,0"&&l!=="resized SecurityError");
    return [...logs.filter(l=>!want.includes(l)&&!l.startsWith("resized ")),...resized,...want.filter(w=>!logs.includes(w)).map(w=>`missing: ${w}`)];
  });
  await check(t,"C2b","an image element's request gives the page's realm no image bytes, of any origin",()=>{
    // a page that replaced Uint8Array saw every buffer the prelude wrapped, the image's bytes too
    let s=start(`<!doctype html><script>
      const U=Uint8Array;
      globalThis.Uint8Array=class extends U{constructor(...a){super(...a);
        if(a[0] instanceof ArrayBuffer&&a[0].byteLength>=8){const v=new U(a[0]);if(v[0]===137&&v[1]===80)console.log('PNG bytes '+a[0].byteLength)}}};
      </script><img id=i src="${B}/secret.png"><img id=d src="data:image/png;base64,${pngB64}"><img id=x src="data:image/png;base64,iVBO00PDR0BADBEEF00KGg"><script>
      i.onload=()=>console.log('load '+i.naturalWidth+' '+i.naturalHeight);
      d.onload=()=>console.log('data '+d.naturalWidth+' '+d.naturalHeight);x.onload=()=>console.log('corrupt loaded');x.onerror=()=>console.log('corrupt error')</script>`,`${A}/p.html`,{network:true});
    const logs=[...s.logs];
    for(let round=0;round<4&&s.netRequests?.length;round++){
      s=call("",{action:"net",session:s.session,results:s.netRequests.map(w=>w.resolve?{id:w.id,addresses:["93.184.216.34"]}:
        {id:w.id,status:200,statusText:"OK",headers:[["content-type","image/png"]],bodyBase64:pngB64})});
      logs.push(...s.logs);
    }
    logs.push(...settle(s.session).logs);
    close();
    const ok=["load 2 2","data 2 2","corrupt error"];
    assert.ok(ok.every(l=>logs.includes(l)),`the images load, a corrupt one fails: ${logs}`);
    return logs.filter(l=>!ok.includes(l));
  });
  await check(t,"C2d","an image of the page's origin that redirected to another origin is not origin-clean",()=>{
    // the engine's subresource op makes the request; the answer is a redirect to another origin
    const key=`${A}/redirect.png`;
    let out=call("",{op:"subresource",action:"start",kind:"image",url:key,documentURL:`${A}/p.html`,referrerPolicy:"",crossorigin:""}) as Record<string,any>;
    for(let i=0;i<6&&out.wire;i++){
      const w=out.wire;
      const answer=w.resolve?{addresses:["93.184.216.34"]}:w.url===key?{status:302,headers:[["location",`${B}/secret.png`]]}:
        {status:200,headers:[["content-type","image/png"]],bodyBase64:pngB64,url:w.url};
      out=call("",{op:"subresource",action:"answer",id:out.id,answer}) as Record<string,any>;
    }
    assert.ok(out.done?.opaque===true,`the answer is opaque: ${JSON.stringify(out)}`);
    hold(key);
    const got=run(`<!doctype html><canvas id=c width=2 height=2></canvas><img id=i src="${key}"><script>
      c.getContext('2d').drawImage(i,0,0);${reads}</script>`);
    return [...got.filter(l=>!refused.includes(l)),...refused.filter(r=>!got.includes(r)).map(r=>`missing: ${r}`)];
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
