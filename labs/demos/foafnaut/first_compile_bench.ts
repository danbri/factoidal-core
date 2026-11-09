// First-compile time of pages (issue 1268): a fresh engine with Noto Sans, then one compile
// of each page as its source stands (scripts are not run; their text is in the DOM).
// Usage: deno run --allow-read --allow-ffi first_compile_bench.ts [--engine PATH-to-dylib]
import {loadHTML} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
const args=Deno.args;
const enginePath=args.includes("--engine")?args[args.indexOf("--engine")+1]:undefined;
const sans=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const pages:[string,string,string][]=[
  ["foaf-explorer",new URL("./pages/foaf-explorer.html",import.meta.url).href,""],
  ["timers-and-clicks",new URL("./pages/timers-and-clicks.html",import.meta.url).href,""],
  ["json-script-1600",new URL("./pages/json-script.html",import.meta.url).href,
    `<!doctype html><script type="application/json">"${"x".repeat(1600)}"</script><p>A page with a JSON script.</p>`]];
const out:Record<string,number>={};
for(const [name,url,inline] of pages){
  const engine=await loadHTML(enginePath);await loadFontFile(engine,sans,"Noto Sans");
  const source=inline||Deno.readTextFileSync(new URL(url));
  const t=performance.now();engine.compile(source,1280,800,{url});out[name]=Math.round(performance.now()-t);
}
console.log(JSON.stringify({engine:enginePath??"wasm",firstCompileMs:out}));
