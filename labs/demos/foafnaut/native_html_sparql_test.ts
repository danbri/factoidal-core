// The SPARQL planner page foafnaut:sparql (WebSparql.lean; owner, 2026-11-08): the ops
// sparqlInfo, sparqlExplain and sparqlPage, and the page laid out and drawn by Lean with no
// refusal, for each example query and for a step of the run. Run on the Wasm engine and, when
// it is built, the native library; the two must give the same plans and rows.
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile,prepareHTML} from "./native_html_document.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const encode=(q:string)=>encodeURIComponent(q).replace(/%20/g,"+");

async function runs(engine:HTMLEngine){
  await loadFontFile(engine,font,"Noto Sans");
  const info=engine.sparqlInfo();
  assert.deepEqual(info.ops,["sparqlInfo","sparqlExplain","sparqlPage"]);
  assert.equal(info.examples.length,6);
  const plans:unknown[]=[];
  for(const example of info.examples){
    const plan=engine.sparqlExplain({query:example.query});
    assert.equal(plan.ok,true);
    assert(plan.operators.length>1,example.name);
    // Children come before their parent: the operators are in execution order.
    plan.operators.forEach((op,i)=>op.children.forEach(c=>assert(c<i,`${example.name}: child ${c} of ${i}`)));
    assert.equal(plan.root,plan.operators.length-1);
    assert(plan.rowCount>0,`${example.name}: no rows`);
    for(const step of [undefined,1,Math.ceil(plan.operators.length/2)]){
      const argument="q="+encode(example.query)+(step?`&step=${step}`:"");
      const page=engine.sparqlPage(argument);
      assert.match(page.source,/<svg width=/);
      assert(!page.source.includes('class="bad"'),`${example.name}: the page has an error`);
      if(step)assert.match(page.next,new RegExp(`step=${step+1}$`));
      // Lean lays the page out and draws it: a refusal throws here.
      const doc=await prepareHTML(engine,"foafnaut:sparql/"+argument,undefined,page.source);
      const frame=doc.compile(900,2000);
      assert(frame.primitiveCount>100,`${example.name}: ${frame.primitiveCount} paint items`);
    }
    plans.push({name:example.name,operators:plan.operators.map(({ns:_,...op})=>op),capability:plan.capability,rows:plan.rows,answer:plan.answer});
  }
  // The default page, a query with a parse error, and a dataset given as Turtle.
  assert.match(engine.sparqlPage("").source,/SPARQL planner, live/);
  assert.match(engine.sparqlPage("q=SELECT+WHERE+%7B").source,/class="bad">parse error/);
  const own=engine.sparqlExplain({query:"SELECT ?o WHERE { <urn:a> <urn:p> ?o }",dataset:"turtle",data:"<urn:a> <urn:p> 1, 2 ."});
  assert.equal(own.rowCount,2);
  assert.throws(()=>engine.sparqlExplain({query:"ASK {}",dataset:"nope"}),/unknown dataset/);
  return plans;
}

Deno.test("Lean draws the SPARQL planner page (Wasm)",async()=>{await runs(await loadHTML());});
Deno.test({name:"Lean draws the SPARQL planner page (native library), with the plans of the Wasm engine",ignore:noLibrary,fn:async()=>{
  assert.equal(JSON.stringify(await runs(await loadHTML(library))),JSON.stringify(await runs(await loadHTML())));
}});
