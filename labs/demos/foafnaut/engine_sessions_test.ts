// Engine sessions (docs/designissues/2026-11-26-foafnaut-engine-sessions.md): any number of
// engine states in one loaded native library (`web_session_new`). Checks:
//  1. two sessions hold separate state: a font held by one is not held by the other, and each
//     counts its own frame work (`frameWork`, `Engine.pages.work`);
//  2. a session that ended refuses calls, and the library still answers on other sessions;
//  3. three sessions used from three threads at the same time give the same answers, byte for
//     byte, as one session used alone. A data race in the engine or the shim would show as a
//     different answer or a crash; a pass does not show that there is none.
// Needs the native library (`build-web-render.sh --native`); `WEB_RENDER_LIB=` names another.
// Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
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
