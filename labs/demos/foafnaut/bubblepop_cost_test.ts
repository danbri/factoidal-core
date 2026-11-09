// Cost ratchet for BubblePopJS (the JavaScript engine written in Lean): work that a page does
// element by element must take time in proportion to the elements, not to their square.
// Each case runs a page script at two sizes, n and 4n, and the larger must take less than
// 8 times as long (linear is 4, quadratic 16). The cases:
// - Array.prototype.push on a growing array (it copied the whole array at each push);
// - a[i] = v appending to an array;
// - charCodeAt over an ASCII string (it walked the string at each call).
// Times are the engine's own (`ns` of the start turn), the best of three runs.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env bubblepop_cost_test.ts
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

const cases:[string,(n:number)=>string][]=[
  ["push",n=>`var a=[];for(var i=0;i<${n};i++)a.push(i);document.title=String(a.length);`],
  ["index append",n=>`var a=[];for(var i=0;i<${n};i++)a[i]=i;document.title=String(a.length);`],
  ["charCodeAt",n=>`var s='x'.repeat(${n}),t=0;for(var i=0;i<s.length;i++)t+=s.charCodeAt(i);document.title=String(t);`],
];

Deno.test({name:"BubblePopJS: element-by-element work is linear",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const time=(src:string)=>{
    const page=`<!doctype html><title>cost</title><script>${src}</script>`;
    const runs=Array.from({length:3},()=>{
      const t=engine.scriptSession(page,{action:"start",url:"file:///cost.html",resources:[],engine:"bubblepop",instructionsPerMs:1e12}) as unknown as {ns:number;errors:string[]};
      assert.deepEqual(t.errors,[],src);
      return t.ns;
    });
    return Math.min(...runs);
  };
  const n=20000;
  for(const [name,make] of cases){
    const small=time(make(n)),large=time(make(4*n));
    const ratio=large/small;
    console.log(`${name}: ${n} in ${(small/1e6).toFixed(2)} ms, ${4*n} in ${(large/1e6).toFixed(2)} ms, ratio ${ratio.toFixed(2)}`);
    assert.ok(ratio<8,`${name}: ${4*n} elements took ${ratio.toFixed(1)} times as long as ${n} (linear is 4)`);
  }
  engine.scriptSession("",{action:"close"});
}});
