// The DOM breadth APIs of page scripts (record docs/designissues/2026-11-08-dom-breadth.md):
// markup setters, Range (live under mutation), Selection, TreeWalker and NodeIterator with
// a filter, reflected attributes and getComputedStyle. One page runs on BubblePopJS and, with
// the guest module (QUICKJS_WASM, else ~/working/qjs-wasm/qjs-wasmvm.wasm), on QuickJS-NG in
// WasmVM; both must log the same lines, and the commands must replay (the engine checks).
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env dom_breadth_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=[Deno.env.get("QUICKJS_WASM")??"",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`].find(exists);

const page=`<!doctype html><body><div id=d><p id=a>Hello <b>big</b> world</p><p id=c>Second</p></div>
<ol id=o start=-3></ol><input id=i maxlength=" 12x" size=0><a id=l href="/x/y?q#h">l</a>
<script>
const out=[];const log=(...x)=>out.push(x.join(' '));
const d=document.getElementById('d'),a=document.getElementById('a');
const t=a.firstChild;
const r=document.createRange();r.setStart(t,2);r.setEnd(document.getElementById('c').firstChild,3);
log('range',r.toString(),r.commonAncestorContainer.id,r.comparePoint(a,0),r.intersectsNode(a.lastChild));
const f=r.cloneContents();const box=document.createElement('div');box.appendChild(f);log('clone',box.innerHTML);
t.insertData(0,'XX');log('live',r.startOffset,r.endOffset);
a.insertAdjacentHTML('beforeend','<i>!</i>');log('html',a.outerHTML);
const s=getSelection();s.selectAllChildren(a);log('sel',s.rangeCount,s.type,s.toString(),s.anchorNode.id,s.focusOffset);
s.collapse(t,1);s.extend(a,1);log('sel2',s.direction,s.isCollapsed);
const tw=document.createTreeWalker(d,NodeFilter.SHOW_ELEMENT,n=>n.localName==='b'?NodeFilter.FILTER_SKIP:NodeFilter.FILTER_ACCEPT);
const seen=[];for(let n=tw.nextNode();n;n=tw.nextNode())seen.push(n.localName);log('walk',seen.join(','));
const it=document.createNodeIterator(d,NodeFilter.SHOW_TEXT);let k=0;while(it.nextNode())k++;log('iter',k);
const o=document.getElementById('o'),i=document.getElementById('i'),l=document.getElementById('l');
log('reflect',o.start,i.maxLength,i.size,o.reversed,a.dir,l.pathname,l.hash);
a.dir='RTL';log('dir',a.getAttribute('dir'),a.dir);
try{i.size=0}catch(e){log('size',e.name)}
log('style',getComputedStyle(a).display,getComputedStyle(a).getPropertyValue('color'));
log('css',CSS.supports('display','block'),CSS.supports('(display: grid)'),CSS.supports('not (display: grid)'),CSS.escape('0a'),
  document.fonts.status,typeof document.fonts.ready.then,'color' in getComputedStyle(a),'backgroundColor' in getComputedStyle(a),getComputedStyle(a).length>10);
d.innerHTML='<p>new</p>';log('after',r.startContainer.nodeName,r.startOffset,d.textContent);
console.log('RESULT '+out.join(' | '));
</script>`;

function run(engine:HTMLEngine,lean:boolean){
  const turn=engine.scriptSession(page,{action:"start",url:"http://example.test/p.html",resources:[],instructionsPerMs:1e12,
    ...(lean?{engine:"bubblepop"}:{})}) as {logs:string[];errors:string[]};
  engine.scriptSession("",{action:"close"});
  return turn;
}

Deno.test({name:"DOM breadth: Range, Selection, traversal, markup, reflection, computed style (native library)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const info=engine.scriptInfo();
  if(!(info.engines??[]).includes("bubblepop")){console.log("NOT RUN: this engine has no BubblePopJS");return;}
  const lean=run(engine,true);
  assert.deepEqual(lean.errors,[]);
  const line=lean.logs.find(l=>l.startsWith("RESULT "))??"";
  for(const want of ["range llo big worldSec d -1 true","clone <p id=\"a\">llo <b>big</b> world</p><p id=\"c\">Sec</p>",
    "live 4 3","html <p id=\"a\">XXHello <b>big</b> world<i>!</i></p>","sel 1 Range XXHello big world! a 4",
    "sel2 forward false","walk p,i,p","iter 5","reflect -3 12 20 false  /x/y #h","dir RTL rtl","size IndexSizeError",
    "style block rgb(0, 0, 0)","css true false true \\30 a loaded function true true true","after DIV 0 new"])
    assert.ok(line.includes(want),`BubblePopJS: wanted "${want}" in ${line}`);
  if(guest){
    engine.scriptLoad(await Deno.readFile(guest));
    const qjs=run(engine,false);
    assert.deepEqual(qjs.logs,lean.logs,"QuickJS-NG and BubblePopJS differ");
  }
}});
