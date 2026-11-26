// Engine sessions (docs/designissues/2026-11-26-foafnaut-engine-sessions.md): any number of
// engine states in one loaded native library (`web_session_new`). Checks:
//  1. two sessions hold separate state: a font held by one is not held by the other, and each
//     counts its own frame work (`frameWork`, `Engine.pages.work`);
//  2. a session that ended refuses calls, and the library still answers on other sessions;
//  3. three sessions used from three threads at the same time give the same answers, byte for
//     byte, as one session used alone. A data race in the engine or the shim would show as a
//     different answer or a crash; a pass does not show that there is none;
//  4. task sessions (web_session_new_task, WebSession.lean), called from this thread through
//     nonblocking FFI, three at once, give the same answers as one session alone;
//  5. a long call on one task session does not hold a short call on another: the short one,
//     sent after the long one, is answered first;
//  6. a task session that is ended answers the calls it had and refuses later ones;
//  7. a canceled task session refuses the calls it had not started, and the call in progress
//     stops at the engine's next check (before a render's paint), so three long calls cost one;
//  8. expected failure: a cancel does not stop a layout in progress
//     (https://github.com/danbri/factoidal-core/issues/1135);
//  9. a task session's layers answer carries the layout sections (issue 1124 stage B), decoded as
//     for the engine on this thread: the same boxes, glyph runs, links, pixel data and tile words.
// Needs the native library (`build-web-render.sh --native`); `WEB_RENDER_LIB=` names another.
// Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,loadHTMLSession} from "./native_html_engine.ts";
import {loadFontFile,prepareHTML} from "./native_html_document.ts";
import {answersOf} from "./fixtures/engine_sessions_answers.ts";

const lab=new URL("./",import.meta.url).pathname;
const library=(()=>{try{const e=Deno.env.get("WEB_RENDER_LIB");if(e)return e;}catch{/* no env permission */}
  return lab+`.build/web-render/engines/libweb-render.${Deno.build.os==="darwin"?"dylib":"so"}`;})();
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
Deno.test({name:"engine sessions: two sessions in one library hold separate state",ignore:noLibrary,fn:async()=>{
  const a=await loadHTML(library,"bytes",{session:true}),b=await loadHTML(library,"bytes",{session:true});
  assert(a.sessionOwn&&b.sessionOwn,"the library has no engine sessions");
  assert.deepEqual(await loadFontFile(a,font,"Noto Sans"),{family:"Noto Sans",glyphs:3884,fonts:1});
  // The font is held by a only: b answers the first font as the first it holds.
  const page="<p>Sessions hold their own fonts.</p>";
  const bytesOf=(scene:{data:unknown})=>{const d=scene.data as Float32Array;return new Uint8Array(d.buffer,d.byteOffset,d.byteLength);};
  const fa=a.compile(page,300,80,{checks:false}),fb=b.compile(page,300,80,{checks:false});
  assert.notDeepEqual(bytesOf(fa),bytesOf(fb),"a font held by one session drew in the other");
  assert.deepEqual(await loadFontFile(b,font,"Noto Sans"),{family:"Noto Sans",glyphs:3884,fonts:1});
  const fb2=b.compile(page,300,80,{checks:false});
  assert.deepEqual(bytesOf(fa),bytesOf(fb2),"the same font and page drew differently in two sessions");
  // Frame work is counted per session.
  const wa=a.frameWork(true)!,wb=b.frameWork(true)!;
  assert.equal(wa.layouts,1);assert.equal(wb.layouts,2);
  assert.equal(a.frameWork()!.layouts,0);assert.equal(b.frameWork()!.layouts,0);
  a.endSession();b.endSession();
}});

Deno.test({name:"engine sessions: an ended session refuses calls; the others still answer",ignore:noLibrary,fn:async()=>{
  const a=await loadHTML(library,"bytes",{session:true}),b=await loadHTML(library,"bytes",{session:true});
  a.endSession();a.endSession();
  assert.throws(()=>a.compile("<p>x</p>",100,40,{checks:false}),/session ended/);
  assert(b.compile("<p>still here</p>",100,40,{checks:false}).data.length>0);
  // The default session (no session argument) is not touched by either.
  const d=await loadHTML(library,"bytes");
  assert(!d.sessionOwn);
  assert(d.compile("<p>default</p>",100,40,{checks:false}).data.length>0);
  b.endSession();
}});

Deno.test({name:"engine sessions: three threads at once give the answers of one session alone",ignore:noLibrary,fn:async()=>{
  const pagesDir=lab+"pages/",rounds=3;
  const alone=await loadHTML(library,"bytes",{session:true});
  await loadFontFile(alone,font,"Noto Sans");
  const want=await answersOf(alone,pagesDir,rounds);
  alone.endSession();
  const workers=[0,1,2].map(()=>new Worker(new URL("./fixtures/engine_sessions_worker.ts",import.meta.url).href,{type:"module"}));
  try{
    const got=await Promise.all(workers.map(w=>new Promise<string[]>((resolve,reject)=>{
      w.onmessage=e=>e.data.error?reject(new Error(e.data.error)):resolve(e.data.answers);
      w.onerror=e=>{e.preventDefault();reject(new Error(e.message));};
      w.postMessage({library,font,pagesDir,rounds});
    })));
    for(const [i,answers] of got.entries())assert.deepEqual(answers,want,`thread ${i} answered differently from one session alone`);
  }finally{for(const w of workers)w.terminate();}
}});

Deno.test({name:"engine sessions: three task sessions at once give the answers of one session alone",ignore:noLibrary,fn:async()=>{
  const pagesDir=lab+"pages/",rounds=2;
  const alone=await loadHTML(library,"bytes",{session:true});
  await loadFontFile(alone,font,"Noto Sans");
  const want=await answersOf(alone,pagesDir,rounds);
  alone.endSession();
  const sessions=await Promise.all([0,1,2].map(()=>loadHTMLSession(library)));
  try{
    // The font helper awaits the answer: it takes a task session as it is.
    for(const s of sessions)assert.deepEqual(await loadFontFile(s as unknown as Parameters<typeof loadFontFile>[0],font,"Noto Sans"),{family:"Noto Sans",glyphs:3884,fonts:1});
    const got=await Promise.all(sessions.map(s=>answersOf(s,pagesDir,rounds)));
    for(const [i,answers] of got.entries())assert.deepEqual(answers,want,`task session ${i} answered differently from one session alone`);
  }finally{for(const s of sessions)await s.endSession();}
}});

Deno.test({name:"engine sessions: a long call on one task session does not hold a short call on another",ignore:noLibrary,fn:async()=>{
  const a=await loadHTMLSession(library),b=await loadHTMLSession(library);
  try{
    // A table of 6,000 rows (a long layout) on a, then a paragraph on b.
    const rows=Array.from({length:6000},(_,i)=>`<tr><td>${i}</td><td>row ${i} of a long table</td><td>${i*7%13}</td></tr>`).join("");
    const long=`<table>${rows}</table>`,short="<p>short</p>";
    const done:string[]=[];
    const t0=performance.now();
    const pa=a.compile(long,800,600,{checks:false}).then(()=>{done.push("long");return performance.now()-t0;});
    await new Promise(r=>setTimeout(r,20));
    const pb=b.compile(short,200,80,{checks:false}).then(()=>{done.push("short");return performance.now()-t0;});
    const [longMs,shortMs]=await Promise.all([pa,pb]);
    console.log(JSON.stringify({longMs:Math.round(longMs),shortMs:Math.round(shortMs)}));
    assert.deepEqual(done,["short","long"],`the short call waited for the long one (long ${Math.round(longMs)} ms, short ${Math.round(shortMs)} ms)`);
  }finally{await a.endSession();await b.endSession();}
}});

Deno.test({name:"engine sessions: an ended task session answers its calls and refuses later ones",ignore:noLibrary,fn:async()=>{
  const s=await loadHTMLSession(library);
  const sent=[s.compile("<p>one</p>",100,40,{checks:false}),s.compile("<p>two</p>",100,40,{checks:false})];
  s.close();
  await assert.rejects(()=>s.compile("<p>three</p>",100,40,{checks:false}),/session ended/);
  const [one,two]=await Promise.allSettled(sent);
  // Each call sent before close is answered: drawn, or refused by the closing session; none hangs.
  for(const r of [one,two])if(r.status==="rejected")assert.match(String(r.reason),/session ended/);
  await s.endSession();
  assert(s.ended);
  assert.equal(s.inFlight,0);
}});

// The library can cancel a task session (web_session_cancel, stage 4).
const canCancel=!noLibrary&&(()=>{try{const l=Deno.dlopen(library,{web_session_cancel:{parameters:["pointer"],result:"void",optional:true}} as const);
  const has=!!l.symbols.web_session_cancel;l.close();return has;}catch{return false;}})();
const longTable=(rows:number)=>`<table>${Array.from({length:rows},(_,i)=>`<tr><td>${i}</td><td>row ${i} of a long table</td><td>${i*7%13}</td></tr>`).join("")}</table>`;
// A shortfall is an expected failure that names its issue and fails the run when it passes.
const xfail=(name:string,issue:string,ignore:boolean,fn:()=>Promise<void>)=>Deno.test({name:`xfail: ${name} (${issue})`,ignore,fn:async()=>{
  let passed=false;
  try{await fn();passed=true;}catch(error){console.log(`xfail ${name} (${issue}): ${String(error).split("\n")[0]}`);}
  if(passed)throw new Error(`unexpected pass: flip to an assertion and close ${issue}`);
}});

Deno.test({name:"engine sessions: a canceled task session refuses the calls it had not started",ignore:!canCancel,fn:async()=>{
  const page=longTable(4000);
  // One long call alone, on a session of its own, for the time it takes.
  const probe=await loadHTMLSession(library);
  const t0=performance.now();await probe.compile(page,800,600,{checks:false});const oneMs=performance.now()-t0;
  await probe.endSession();
  const s=await loadHTMLSession(library);
  const t1=performance.now();
  const calls=[0,1,2].map(()=>s.compile(page,800,600,{checks:false}));
  await new Promise(r=>setTimeout(r,Math.min(50,oneMs/4)));
  s.cancel();
  const settled=await Promise.allSettled(calls);
  const allMs=performance.now()-t1;
  console.log(JSON.stringify({oneMs:Math.round(oneMs),threeCanceledMs:Math.round(allMs),results:settled.map(r=>r.status)}));
  // The second and third never started: refused.
  for(const r of settled.slice(1))assert.equal(r.status,"rejected","a call that had not started ran after the cancel");
  for(const r of settled)if(r.status==="rejected")assert.match(String(r.reason),/canceled|ended/);
  assert(allMs<2*oneMs+500,`three canceled calls took ${Math.round(allMs)} ms, one takes ${Math.round(oneMs)} ms`);
  await s.endSession();
  assert(s.ended);
}});

xfail("a cancel stops a layout in progress within 200 ms","https://github.com/danbri/factoidal-core/issues/1135",!canCancel,async()=>{
  const page=longTable(12000);
  const s=await loadHTMLSession(library);
  try{
    const call=s.compile(page,800,600,{checks:false}).catch(()=>undefined);
    await new Promise(r=>setTimeout(r,100));
    const t0=performance.now();s.cancel();await call;const afterMs=performance.now()-t0;
    assert(afterMs<200,`the call ended ${Math.round(afterMs)} ms after the cancel: the layout ran to its end`);
  }finally{await s.endSession();}
});

Deno.test({name:"engine sessions: a task session decodes the layout sections of a layers answer as the engine on this thread",ignore:noLibrary,fn:async()=>{
  const direct=await loadHTML(library,"bytes",{session:true});
  const s=await loadHTMLSession(library);
  try{
    await loadFontFile(direct,font,"Noto Sans");
    await loadFontFile(s as unknown as Parameters<typeof loadFontFile>[0],font,"Noto Sans");
    const shell={tabs:[{title:"t"}],active:0,address:"https://example.invalid/",cursor:0,focused:false,canBack:false,canForward:false,
      loading:false,scale:1,theme:"light",pages:1,scroll:900,pressed:""};
    const doc=await prepareHTML(direct,new URL("./pages/status.html",import.meta.url).href);
    const options={...doc.request(1600,1000).options,shell,checks:false};
    const a=direct.compileLayers(doc.source,1600,1000,options);
    const b=await s.compileLayers(doc.source,1600,1000,options);
    type Web={boxes:unknown[];glyphRuns:unknown[];links:unknown[];layoutSections?:boolean};
    const wa=a.page.webRender as unknown as Web,wb=b.page.webRender as unknown as Web;
    assert.equal(wb.layoutSections,true,"the task session's answer has layout sections");
    for(const key of ["boxes","glyphRuns","links"] as const){
      assert(wb[key].length>0,`no ${key}`);
      assert.deepEqual(wb[key],wa[key],`${key} differ`);
    }
    assert.deepEqual([...b.page.data as Float32Array],[...a.page.data as Float32Array],"pixel data");
    assert.deepEqual([...(b.page.tiles??[]) as Uint32Array],[...(a.page.tiles??[]) as Uint32Array],"tile words");
    assert.deepEqual(b.layers,a.layers,"layer places");
  }finally{direct.endSession();await s.endSession();}
}});
