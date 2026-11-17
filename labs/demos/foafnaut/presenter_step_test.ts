// The serial document op and the independent pure entry must give identical answers.
// FOAFNAUT_PRESENTER_ENGINE chooses the native library; absent, both use the Wasm build.
import {strict as assert} from "node:assert";
import {loadHTML,loadPresenter,type PresenterState,type PresenterInput} from "./native_html_engine.ts";

const library=Deno.env.get("FOAFNAUT_PRESENTER_ENGINE");
const pure=await loadPresenter(library);
const engine=await loadHTML(library);
const first={id:1,bandTop:100,bandHeight:300,keepFrom:100,keepTo:300};
const next={id:2,bandTop:300,bandHeight:300,keepFrom:300,keepTo:500};

Deno.test("presenter: pure export equals serial document op on input trace",()=>{
  let state:PresenterState={view:100,scroll:100,shown:null,asked:null};
  const inputs:PresenterInput[]=[{kind:"frame",frame:first},{kind:"scrollTo",y:200},{kind:"vsync"},
    {kind:"scrollTo",y:350},{kind:"scrollTo",y:350},{kind:"vsync"},
    {kind:"frame",frame:next},{kind:"frame",frame:first},{kind:"vsync"},{kind:"resize",h:120},{kind:"vsync"}];
  for(const input of inputs){
    const answer=pure(state,input);
    assert.deepEqual(answer,engine.presenterStep(state,input));
    state=answer.state;
  }
  assert.equal(state.shown?.id,2);
});

Deno.test("presenter: kept scroll asks nothing, requests coalesce and offsets stay in the band",()=>{
  const initial:PresenterState={view:100,scroll:100,shown:first,asked:null};
  const kept=pure(initial,{kind:"scrollTo",y:200});
  assert.deepEqual(kept.outputs,[]);
  assert.deepEqual(pure(kept.state,{kind:"vsync"}).outputs,[{kind:"present",frameId:1,offset:100}]);
  const past=pure(kept.state,{kind:"scrollTo",y:350});
  assert.deepEqual(past.outputs,[{kind:"needBand",scroll:350}]);
  assert.deepEqual(pure(past.state,{kind:"scrollTo",y:350}).outputs,[]);
  assert.deepEqual(past.placement,{frameId:1,offset:200,exact:false,kept:false});
  const before=pure(initial,{kind:"scrollTo",y:50});
  assert.deepEqual(before.placement,{frameId:1,offset:0,exact:false,kept:false});
});

Deno.test("presenter: malformed wire numbers are refused",()=>{
  const initial:PresenterState={view:100,scroll:100,shown:first,asked:null};
  for(const y of [-1,0.5,2147483648,NaN,Infinity]){
    assert.throws(()=>pure(initial,{kind:"scrollTo",y}));
    assert.throws(()=>engine.presenterStep(initial,{kind:"scrollTo",y}));
  }
});
