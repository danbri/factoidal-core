// First-compile cost of long words (issue 1268), on the Wasm engine and, when it is built,
// the native library:
// * the text of script, style, template, noscript and title is not shaped (SfntProfile.wordsOf):
//   a page with a 16,000-character JSON script costs about what the page costs without it;
// * a word of 10,000 characters with no space shapes in time linear in its length (the GSUB
//   and GPOS passes and the cluster ends were quadratic).
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const sans=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const url=new URL("./pages/long-words.html",import.meta.url).href;

// Each case uses its own letters, so no case finds its words in the memo of another.
const time=(engine:HTMLEngine,html:string)=>{const t=performance.now();engine.compile(html,800,600,{url});return performance.now()-t;};

async function counts(path?:string){
  const engine=await loadHTML(path);await loadFontFile(engine,sans,"Noto Sans");
  time(engine,"<!doctype html><p>warm up</p>");
  const plain=time(engine,"<!doctype html><p>alpha beta gamma</p>");
  const json=time(engine,`<!doctype html><script type="application/json">"${"q".repeat(16000)}"</script><p>alpha beta delta</p>`);
  assert(json<plain+50,`a page with a long JSON script: ${json} ms, without: ${plain} ms`);
  const short=time(engine,`<!doctype html><p>${"m".repeat(2500)}</p>`);
  const long=time(engine,`<!doctype html><p>${"n".repeat(10000)}</p>`);
  // Four times the characters: at most eight times the time (linear, with room for noise).
  assert(long<Math.max(40,short*8),`a 10,000-character word ${long} ms, 2,500: ${short} ms`);
  return {plainMs:Math.round(plain),jsonScriptMs:Math.round(json),word2500Ms:Math.round(short),word10000Ms:Math.round(long)};
}
Deno.test("long words: script text is not shaped; a 10,000-character word in linear time, Wasm engine",async()=>{console.log(JSON.stringify(await counts()));});
Deno.test({name:"long words: script text is not shaped; a 10,000-character word in linear time, native library",ignore:noLibrary,fn:async()=>{console.log(JSON.stringify(await counts(library)));}});
