// The engine's accessibility tree through its op (WebDocument accessibilityTree,
// HTML/AccessibleTree.lean), on the Wasm engine and, when it is built, the native library:
//
// * the tree of a laid-out page: roles, names and states; what the styles hide is not in it
//   (display: none prunes, visibility: hidden skips); boxes come from the layout;
// * the same layout again answers `unchanged` and makes no tree;
// * the forms for the hosts: `ax` for the macOS window, `web` for the Hub's mirror;
// * the chrome's controls come first, fixed in the window, with names in words;
// * the view page for a person;
// * cost: the tree of a page four times as large takes about four times as long, not sixteen.
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const pageURL=new URL("./pages/accessibility.html",import.meta.url).href;
type Node={id:number;depth:number;role:string;name?:string;description?:string;tag?:string;props?:Record<string,string>;
  focusable?:boolean;fixed?:boolean;box?:number[];ax?:Record<string,unknown>;web?:{role?:string;aria?:Record<string,string>;text?:string}};

const page=`<!doctype html><title>Shop</title><style>.gone{display:none}.dim{visibility:hidden}.dim b{visibility:visible}
h1,p{margin:0}</style><nav aria-label="Main"><a href="/a">Home</a></nav>
<main><h1>Deals</h1><p class="gone">never shown</p><div class="dim"><i>dimmed words</i> <b>bright</b></div>
<p><button aria-pressed="true">Mute</button> <input type="checkbox" checked aria-label="Agree"></p>
<div role="status">Saved</div><div aria-hidden="true">decoration</div></main><script>var secret=1</script>`;

function tree(engine:HTMLEngine,html:string,options:Record<string,unknown>={}) {
  return engine.accessibilityTree(html,800,600,{url:pageURL,...options});
}
const find=(nodes:Node[],role:string)=>{const node=nodes.find(n=>n.role===role);assert(node,`a ${role} node`);return node;};

function styledPage(engine:HTMLEngine) {
  const answer=tree(engine,page),nodes=answer.nodes as unknown as Node[];
  assert(Array.isArray(nodes)&&nodes.length>0,"the tree has nodes");
  const text=JSON.stringify(nodes);
  for(const gone of ["never shown","dimmed words","decoration","secret"])assert(!text.includes(gone),`"${gone}" is not in the tree`);
  assert(text.includes("bright"),"a visible child of a hidden element is in the tree");
  assert.deepEqual(nodes.filter(n=>n.role!=="text").map(n=>n.role),
    ["document","navigation","link","main","heading","paragraph","button","checkbox","status"],"the roles, in tree order");
  assert.equal(nodes[0].depth,0);assert.equal(nodes[0].name,"Shop","the document is named by its title");
  assert.equal(find(nodes,"navigation").name,"Main");
  assert(find(nodes,"link").depth>find(nodes,"navigation").depth,"the link is below the navigation");
  assert.equal(find(nodes,"link").name,"Home");assert.equal(find(nodes,"link").focusable,true);
  assert.equal(find(nodes,"heading").props?.level,"1");assert.equal(find(nodes,"heading").name,"Deals");
  assert.equal(find(nodes,"button").props?.pressed,"true");assert.equal(find(nodes,"button").name,"Mute");
  assert.equal(find(nodes,"checkbox").props?.checked,"true");assert.equal(find(nodes,"checkbox").name,"Agree");
  assert.equal(find(nodes,"status").props?.live,"polite");
  // Boxes from the layout: the heading has one, above the button's.
  const heading=find(nodes,"heading").box,button=find(nodes,"button").box;
  assert(heading&&heading[2]>0&&heading[3]>0,`the heading's box: ${JSON.stringify(heading)}`);
  assert(button&&button[2]>0&&button[3]>0&&button[1]>=heading[1]+heading[3],`the button's box is below the heading: ${JSON.stringify([heading,button])}`);
  // No node of the document twice.
  assert.equal(new Set(nodes.map(n=>n.id)).size,nodes.length,"node ids are distinct");
  // The same layout again: no tree.
  assert(answer.serial>0,"the layout is kept and numbered");
  const again=tree(engine,page,{since:answer.serial});
  assert.equal(again.unchanged,true,"the same layout answers unchanged");assert.equal(again.nodes,undefined);
  assert.equal(tree(engine,page.replace("Deals","Offers"),{since:answer.serial}).unchanged,undefined,"another page is not unchanged");
  return {nodes:nodes.length,serial:answer.serial};
}

function hostForms(engine:HTMLEngine) {
  const mac=tree(engine,page,{mac:true}).nodes as unknown as Node[];
  assert.equal(find(mac,"document").ax?.role,"AXWebArea");
  assert.deepEqual([find(mac,"heading").ax?.role,find(mac,"heading").ax?.value],["AXHeading",1]);
  assert.deepEqual([find(mac,"button").ax?.role,find(mac,"button").ax?.subrole,find(mac,"button").ax?.value,find(mac,"button").ax?.press],
    ["AXCheckBox","AXToggle",1,true]);
  assert.equal(find(mac,"navigation").ax?.subrole,"AXLandmarkNavigation");
  const web=tree(engine,page,{web:true}).nodes as unknown as Node[];
  assert.deepEqual(find(web,"heading").web,{role:"heading",aria:{label:"Deals",level:"1"}});
  assert.deepEqual(find(web,"button").web,{role:"button",aria:{label:"Mute",pressed:"true"}});
  assert.equal(web.find(n=>n.role==="text"&&n.web?.text==="Deals")?.web?.role,undefined,"text is text, with no role");
  const view=(tree(engine,page,{view:true}) as unknown as {source:string}).source;
  assert(view.includes("<h1>Accessibility tree</h1>")&&view.includes("<b>heading</b>")&&view.includes("Deals"),"the view page lists the tree");
}

function chrome(engine:HTMLEngine) {
  const shell={tabs:[{title:"Shop"}],active:0,address:"https://x.test/shop",focused:false,canBack:false,canForward:false,loading:false,
    scale:1,theme:"light",pages:1,scroll:0,pressed:""};
  const answer=tree(engine,page,{shell}),nodes=answer.nodes as unknown as Node[];
  const fixed=nodes.filter(n=>n.fixed);
  assert(fixed.length>3&&nodes.findIndex(n=>!n.fixed)===fixed.length,"the chrome's nodes come first");
  assert.deepEqual([fixed[0].role,fixed[0].depth],["toolbar",0]);
  assert(fixed.every(n=>n.id>=1073741824)&&nodes.filter(n=>!n.fixed).every(n=>n.id<1073741824),"chrome ids are above page ids");
  const named=(name:string)=>{const node=fixed.find(n=>n.name===name);assert(node,`the chrome has "${name}": ${fixed.map(n=>n.name).join(", ")}`);return node;};
  assert.deepEqual([named("Back").role,named("Back").props?.disabled],["button","true"],"Back is a button, disabled with no history");
  assert.equal(named("Reload").focusable,true);
  assert.deepEqual([named("Address").role,named("Address").props?.value],["textbox","https://x.test/shop"]);
  assert(fixed.every(n=>n.box&&n.box[2]>0&&n.box[3]>0),"every control has a box");
  assert(answer.top>0,"the page starts below the chrome");
  return {controls:fixed.length-1,top:answer.top};
}

// Median time of the tree alone (the layout is kept) for a page of `count` paragraphs.
function treeMs(engine:HTMLEngine,count:number) {
  const html=`<!doctype html><title>Long</title>${Array.from({length:count},(_,i)=>`<p>Paragraph ${i} with <a href="/l${i}">a link</a> and <b>bold</b> words.</p>`).join("")}`;
  const first=tree(engine,html);
  assert((first.nodes as unknown[]).length>count*3,"the long page has its nodes");
  const times=Array.from({length:5},()=>{const start=performance.now();tree(engine,html);return performance.now()-start;}).sort((a,b)=>a-b);
  return {nodes:(first.nodes as unknown[]).length,ms:Math.round(times[2]*10)/10};
}
function cost(engine:HTMLEngine) {
  const small=treeMs(engine,250),large=treeMs(engine,1000);
  // Four times the nodes: about four times the time; sixteen times would be quadratic.
  assert(large.ms<=Math.max(10,small.ms)*10,`the tree of ${large.nodes} nodes took ${large.ms} ms, of ${small.nodes} nodes ${small.ms} ms`);
  return {small,large};
}

for(const [name,path,ignore] of [["Wasm engine",undefined,false],["native library",library,noLibrary]] as const){
  Deno.test({name:`accessibility tree: a styled page, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(styledPage(await loadHTML(path))));}});
  Deno.test({name:`accessibility tree: the forms for the hosts and the view page, ${name}`,ignore,fn:async()=>{hostForms(await loadHTML(path));}});
  Deno.test({name:`accessibility tree: the chrome's controls, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(chrome(await loadHTML(path))));}});
  Deno.test({name:`accessibility tree: cost grows with the page, not its square, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(cost(await loadHTML(path))));}});
}
