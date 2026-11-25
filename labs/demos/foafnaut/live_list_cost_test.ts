// The cost of reading a live collection in a loop, and that it stays live. A live list
// (children, childNodes, getElementsByTagName, getElementsByClassName, document.links and the
// like) read its nodes from the tree again at every read of an index or of its length: a loop
// `for (i = 0; i < list.length; i++) list[i]` over n nodes read the list 2n times, and for
// getElementsByTagName each reading is a walk of the document from script, with host calls
// for every node. With 1,600 children one step of such a loop took 8 ms (2026-11-17), and the
// page-side start's own loops over the script and img elements were a fifth of a news
// article's start. Now a list's nodes are kept while the arena's stamp stays (Lean's
// Dom.stamp, node_info 31; theorems addCommand_changes, commit_changes, nodeInfo_stamp).
// This page is an original construct: a list of `n` items in sections, and a script that
// loops over five kinds of live collection. The steps of the loops (the script clock's count,
// the same on every machine) at four times the nodes must be less than eight times the steps
// (linear is four; the old cost is sixteen). And the lists are live: an element appended,
// removed, or given a class or an id is in or out of each collection at the next read, also
// in the middle of a loop over it.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env live_list_cost_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Turn=ScriptTurn&{logs:string[];errors:string[]};

/** The page: `n` list items (some with a class, each with a link), and a script. */
export function page(n:number,script:string){
  const items=Array.from({length:n},(_,i)=>`<li class="item${i%3===0?" third":""}"><a href="#${i}">link ${i}</a> <span>s${i}</span></li>`).join("");
  return `<!doctype html><html><body><ul id="u">${items}</ul><form id="f"><input name="a"><input name="b"></form><script>
const u=document.getElementById('u');let out=0;
${script}
</script></body></html>`;
}
const loops=`
const kids=u.children;for(let i=0;i<kids.length;i++)out+=kids[i].nodeType;
const nodes=u.childNodes;for(let i=0;i<nodes.length;i++)out+=nodes[i].nodeType;
const spans=document.getElementsByTagName('span');for(let i=0;i<spans.length;i++)out+=spans[i].nodeType;
const thirds=document.getElementsByClassName('third');for(let i=0;i<thirds.length;i++)out+=thirds[i].nodeType;
const links=document.links;for(let i=0;i<links.length;i++)out+=links[i].nodeType;
for(const el of document.getElementsByTagName('li'))out+=el.nodeType;
console.log('OUT '+out);`;
const live=`
const kids=u.children,spans=document.getElementsByTagName('span'),thirds=document.getElementsByClassName('third'),nodes=u.childNodes,links=document.links;
const r=[kids.length,spans.length,thirds.length,nodes.length,links.length];
const li=document.createElement('li');li.innerHTML='<span>new</span><a href="#n">n</a>';
r.push(kids.length,spans.length);                       // made, not yet in the tree
u.appendChild(li);r.push(kids.length,spans.length,links.length,nodes.length,kids[kids.length-1]===li);
li.className='third';r.push(thirds.length,thirds[thirds.length-1]===li);
li.className='';r.push(thirds.length);
u.removeChild(u.firstElementChild);r.push(kids.length,spans.length,thirds.length,kids[0].textContent);
li.id='named';r.push(kids.namedItem('named')===li,kids.named===li);
li.removeAttribute('id');r.push(kids.named===undefined);
// a loop that removes as it goes sees the list shrink
let seen=0;while(kids.length>3){u.removeChild(kids[0]);seen++;}r.push(seen,kids.length,spans.length);
// a text node added is in childNodes and not in children
u.appendChild(document.createTextNode('t'));r.push(nodes.length,kids.length,nodes[nodes.length-1].nodeType);
// the same collection object of the same node; another node's is another
r.push(u.childNodes===nodes,document.forms[0].elements.length,document.forms.length);
console.log('OUT '+JSON.stringify(r));`;

function run(engine:HTMLEngine,n:number,script:string){
  const url="http://example.test/lists.html";
  const t0=performance.now();
  const turn=engine.scriptSession(page(n,script),{action:"start",url,resources:[],instructionsPerMs:1e12,engine:"bubblepop",layout:{url},width:800,height:600}) as Turn;
  const ms=performance.now()-t0;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(turn.errors,[],"page errors at start");
  const out=turn.logs.find(l=>l.includes("OUT "));
  return {ms,steps:turn.instructions,out:out?out.slice(out.indexOf("OUT ")+4):undefined};
}

Deno.test({name:"A loop over a live collection costs in proportion to its nodes (native library)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  if(!(engine.scriptInfo().engines??[]).includes("bubblepop")){console.log("NOT RUN: this engine has no BubblePopJS");return;}
  run(engine,10,loops); // warm the engine
  const base=run(engine,100,"console.log('OUT 0');"),small=run(engine,100,loops),large=run(engine,400,loops);
  const baseLarge=run(engine,400,"console.log('OUT 0');");
  const s=small.steps-base.steps,l=large.steps-baseLarge.steps;
  console.log(`native: 100 items ${small.ms.toFixed(0)} ms, ${s} steps in the loops; 400 items ${large.ms.toFixed(0)} ms, ${l} steps (x${(l/s).toFixed(1)})`);
  // nodeType 1 for each element, 1 for each child node of the list (all li): 100 + 100 + 100 + 34 + 100 + 100
  assert.equal(small.out,String(100+100+100+34+100+100));
  assert.equal(large.out,String(400+400+400+134+400+400));
  assert.ok(l<8*s,`the loops' steps grow faster than the nodes (x${(l/s).toFixed(1)} for 4 times the nodes)`);
}});

Deno.test({name:"A live collection follows the tree: nodes appended, removed, renamed and reclassed (native library)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  if(!(engine.scriptInfo().engines??[]).includes("bubblepop"))return;
  const r=JSON.parse(run(engine,9,live).out!);
  assert.deepEqual(r,[
    9,9,3,9,9,           // at first: 9 li, 9 span, 3 with the class, 9 child nodes, 9 links
    9,9,                 // an element made and not inserted is in no collection
    10,10,10,10,true,    // appended: in children, the spans, the links, childNodes; last of children
    4,true,3,            // the class given and taken away
    9,9,2,"link 1 s1",   // the first item removed (it had the class)
    true,true,true,      // named access by id, and none once the id is gone
    6,3,3,               // a loop that removes sees the list shrink
    4,3,3,               // a text node is a child node, not an element child
    true,2,1]);
}});
