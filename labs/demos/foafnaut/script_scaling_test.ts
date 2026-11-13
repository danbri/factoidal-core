// Cost test: page-script work on many nodes (as WPT's legacy-encoding decode pages have, 7 000
// to 17 000 spans). The script reads the spans with querySelectorAll, reads two data-*
// attributes through dataset, keys a Map by numbers, walks a live getElementsByTagName list
// by index, and makes and aborts AbortControllers (testharness.js does that for each test).
// Two checks:
// - linear: the guest instructions at 4N stay under 6 times those at N (linear gives 4). A live
//   list that finds its nodes again at each list[i] and list.length is quadratic: on both
//   engines that loop ran out of steps at 1 000 elements before liveList kept its nodes
//   until the tree may change;
// - per node, on QuickJS-NG in WasmVM: the instructions one more node costs stay under
//   250 000 (now about 191 000). Without tools/wasmvm/quickjs/patches/0001-map-hash-mix.patch
//   and the prelude's dataset and AbortController changes, the same page less the live-list
//   loop cost about 297 000 a node, against 134 000 with them (number keys of a Map shared a
//   few hash buckets: about 65 000 instructions for each Map set at 7 000 keys, 1 800 after).
// Also: dataset is one object for each element ([SameObject]).
// Both script engines: QuickJS-NG in WasmVM (needs the guest: QUICKJS_WASM, else
// ~/working/qjs-wasm/qjs-wasmvm.wasm) and, with SCRIPT_ENGINE=bubblepop, BubblePopJS.
// FOAFNAUT_NATIVE_ENGINE names another native library (default: this tree's build).
// Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";

const lean=Deno.env.get("SCRIPT_ENGINE")==="bubblepop";
const library=Deno.env.get("FOAFNAUT_NATIVE_ENGINE")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=[Deno.env.get("QUICKJS_WASM")??"",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`].find(exists);

const page=(n:number)=>{
  const spans:string[]=[];
  for(let i=0;i<n;i++)spans.push(`<span data-cp="${(0x4e00+i).toString(16).toUpperCase()}" data-bytes="${(0x8140+i).toString(16).toUpperCase()}">${String.fromCodePoint(0x4e00+i)}</span>`);
  return `<!doctype html><meta charset=utf-8><body>${spans.join(" ")}<script>
const nodes = document.querySelectorAll('span'), seen = new Map();
let sum = 0, same = true;
for (let i = 0; i < nodes.length; i++) {
  const d = nodes[i].dataset;
  sum += parseInt(d.cp, 16) + d.bytes.length + nodes[i].textContent.length;
  same = same && nodes[i].dataset === d;
  seen.set(i, nodes[i]);
}
for (let i = 0; i < nodes.length; i++) if (seen.get(i) !== nodes[i]) same = false;
const live = document.getElementsByTagName('span');
for (let i = 0; i < live.length; i++) if (live[i] !== nodes[i]) same = false;
for (let i = 0; i < nodes.length; i += 10) { const c = new AbortController(); c.abort('done'); }
console.log('n=' + nodes.length + ' same=' + same + ' sum=' + sum);
</script>`;
};

Deno.test({name:`page-script work on N nodes is linear in N (${lean?"BubblePopJS":"QuickJS-NG in WasmVM"})`,
  ignore:!exists(library)||(!lean&&!guest),fn:async()=>{
  const engine=await loadHTML(library);
  if(!lean)engine.scriptLoad(await Deno.readFile(guest!));
  const run=(n:number)=>{
    const turn=engine.scriptSession(page(n),{action:"start",url:"file:///scaling.html",resources:[],instructionsPerMs:1e12,...(lean?{engine:"bubblepop"}:{})});
    engine.scriptSession("",{action:"close"});
    assert.equal(turn.errors?.length??0,0,`errors: ${turn.errors}`);
    assert.equal(turn.logs.length,1,`logs: ${turn.logs}`);
    return {instructions:turn.instructions,log:turn.logs[0]};
  };
  const small=run(1500),large=run(6000);
  const ratio=large.instructions/small.instructions;
  console.log(`instructions: ${small.instructions} at 1500 nodes, ${large.instructions} at 6000 (x${ratio.toFixed(2)}; linear 4)`);
  assert(ratio<6,`work at 4N is ${ratio.toFixed(2)} times the work at N: a path is no longer linear`);
  const perNode=(large.instructions-small.instructions)/4500;
  console.log(`instructions for each further node: ${Math.round(perNode)}`);
  if(!lean)assert(perNode<250000,`each further node costs ${Math.round(perNode)} guest instructions (limit 250 000)`);
  assert.match(small.log,/^n=1500 same=true sum=\d+$/);
  assert.match(large.log,/^n=6000 same=true sum=\d+$/);
}});
