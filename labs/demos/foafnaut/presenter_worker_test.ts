// Runtime integration of the pure presenter, Deno worker and shared slots. Run against
// a rebuilt engine: FOAFNAUT_PRESENTER_ENGINE=/path/to/libweb-render.dylib deno test -A
// --unstable-ffi presenter_worker_test.ts. With no variable, use the rebuilt Wasm engine.
// This checks overlapping execution, not a latency target or a performance improvement.
import {strict as assert} from "node:assert";
import {loadHTML,loadPresenter,type HTMLArtifact,type HTMLLayers,type PresenterState,type ScriptTurn} from "./native_html_engine.ts";
import {startCompileWorker} from "./native_html_compile.ts";

const CHILD="--presenter-worker-child";
const epoch=()=>performance.timeOrigin+performance.now();
const width=320,height=240,url="file:///presenter-worker-test.html";
const page='<!doctype html><style>body{margin:0}.a{height:300px;background:#f00}.b{height:300px;background:#00f}</style>'+
  Array.from({length:8},()=>'<div class="a"></div><div class="b"></div>').join("");
const options=(scroll:number)=>({url,resources:[],commands:[],checks:false,cpu:true,
  shell:{scroll,scale:1,theme:"classic",tabs:[{title:"Presenter"}],active:0,address:url,focused:false}});

function equalScene(actual:HTMLArtifact,expected:HTMLArtifact,label:string){
  assert.equal(actual.width,expected.width,`${label} width`);
  assert.equal(actual.height,expected.height,`${label} height`);
  assert.equal(actual.wgsl,expected.wgsl,`${label} shader`);
  assert.deepEqual(new Float32Array(actual.data),new Float32Array(expected.data),`${label} scene words`);
  assert.deepEqual(new Uint32Array(actual.tiles),new Uint32Array(expected.tiles),`${label} tile words`);
  assert.ok(actual.pixels instanceof Uint8Array,`${label} worker supplied CPU pixels`);
  assert.ok(expected.pixels instanceof Uint8Array,`${label} oracle supplied CPU pixels`);
  assert.equal(actual.pixels.length,actual.width*actual.height*4,`${label} RGBA length`);
  assert.deepEqual(actual.pixels,expected.pixels,`${label} pixels`);
}

function equalFrame(actual:HTMLLayers,expected:HTMLLayers){
  for(const key of ["top","view","bandTop","bandHeight","keepFrom","keepTo","composite"] as const)
    assert.equal(actual.layers[key],expected.layers[key],key);
  equalScene(actual.chrome,expected.chrome,"chrome");
  equalScene(actual.page,expected.page,"page");
}

async function exercise(){
  const library=Deno.env.get("FOAFNAUT_PRESENTER_ENGINE");
  // Initialisation and all serial document calls finish before the worker starts. The
  // native document ABI has one mutable engine and must never run on both threads.
  const presenter=await loadPresenter(library);
  const serial=await loadHTML(library);
  const zero=serial.compileLayers(page,width,height,options(0));
  const middle=serial.compileLayers(page,width,height,options(1200));
  const worker=await startCompileWorker(undefined,library,false,true);
  try{
    const first=await worker.compileLayers(page,width,height,options(0));
    equalFrame(first.layers,zero);
    const prefetched=await worker.prefetchLayers(page,width,height,options(1200));
    assert.ok(prefetched,"the only prefetch must publish a frame");
    equalFrame(prefetched.layers,middle);
    const frameId=(layers:HTMLLayers)=>(layers as HTMLLayers&{presenterId:number}).presenterId;
    assert.ok(frameId(first.layers)>0);
    assert.ok(frameId(prefetched.layers)>frameId(first.layers),"publication ids increase");

    const place=first.layers.layers;
    let state:PresenterState={view:place.view,scroll:place.keepFrom,asked:null,
      shown:{id:frameId(first.layers),bandTop:place.bandTop,bandHeight:place.bandHeight,
        keepFrom:place.keepFrom,keepTo:place.keepTo}};
    // Finite original script, no page timers or host busy wait. Its completion log also
    // checks that the interpreter ran the loop, rather than refusing or slicing it.
    const busy='<!doctype html><script>var total=0;for(var i=0;i<300000;i++)total+=i;console.log("busy-done:"+total)</script>';
    const turn=worker.inputCall("scriptSession",busy,{action:"start",url,resources:[],engine:"bubblepop",
      instructionsPerMs:1e12,full:true});
    // This render waits behind the script. Its obsolete scroll is replaced from the slot
    // when the worker starts it, including requests sent while the script owns the worker.
    const band=worker.compileLayers(page,width,height,{...options(0),presenterFollowScroll:true});
    let ticks=0;
    const samples:{startEpochMs:number;endEpochMs:number;scroll:number}[]=[];
    const pulse=()=>{
      const startEpochMs=epoch();
      const y=ticks%2===0?place.keepFrom:place.keepTo;
      const shifted=presenter(state,{kind:"scrollTo",y});
      assert.deepEqual(shifted.outputs,[],"kept scroll has no engine request");
      const shown=presenter(shifted.state,{kind:"vsync"});
      assert.equal(shown.outputs.length,1);
      assert.equal(shown.outputs[0].kind,"present");
      assert.equal(shown.placement?.frameId,frameId(first.layers));
      assert.equal(shown.placement?.kept,true);
      state=shown.state;
      const scroll=ticks===0?600:ticks===1?900:1200;
      worker.requestBand(scroll);
      ticks++;
      if(samples.length<8192)samples.push({startEpochMs,endEpochMs:epoch(),scroll});
    };
    let pulseError:unknown;
    const interval=setInterval(()=>{try{pulse();}catch(error){pulseError=error;clearInterval(interval);}},1);
    let completed:Awaited<typeof turn>,latest:Awaited<typeof band>;
    try{[completed,latest]=await Promise.all([turn,band]);}
    finally{clearInterval(interval);}
    if(pulseError)throw pulseError;
    const script=completed.value as ScriptTurn;
    assert.deepEqual(script.errors,[]);
    assert.ok(script.logs.includes("busy-done:44999850000"),"busy script completed");
    equalFrame(latest.layers,middle);
    assert.ok(frameId(latest.layers)>frameId(prefetched.layers));
    await worker.inputCall("scriptSession","",{action:"close",session:script.session});
    console.log(JSON.stringify({type:"presenter-worker-pulses",samples}));
    console.log(JSON.stringify({type:"presenter-worker-result",ticks}));
  }finally{worker.terminate();}
}

if(Deno.args.includes(CHILD)){
  await exercise();
}else{
  Deno.test("presenter: worker pixels, publications and input during a script turn",async()=>{
    // Capture both threads' stamps so a delayed reply cannot be mistaken for execution
    // overlap. The deadline bounds this child process; it is not a performance budget.
    const result=await new Deno.Command(Deno.execPath(),{
      args:["run","--no-check","--no-config","--no-lock","-A","--unstable-ffi",new URL(import.meta.url).pathname,CHILD],
      stdout:"piped",stderr:"piped",env:{PRESENTER_TIMING_INPUT:"1"},signal:AbortSignal.timeout(120_000),
    }).output();
    const stdout=new TextDecoder().decode(result.stdout),stderr=new TextDecoder().decode(result.stderr);
    assert.equal(result.code,0,`worker integration child failed:\n${stdout}\n${stderr}`);
    const records:Record<string,unknown>[]=stdout.split("\n").flatMap(line=>{
      try{return [JSON.parse(line)];}catch{return [];}
    });
    const turn=records.find(r=>r.type==="presenter-engine-turn");
    assert.ok(turn,"worker emitted actual script execution stamps");
    const pulses=records.find(r=>r.type==="presenter-worker-pulses")?.samples as Record<string,unknown>[]|undefined;
    assert.ok(pulses,"child emitted presenter execution stamps");
    const during=pulses.filter(r=>
      Number(r.startEpochMs)>=Number(turn.startEpochMs)&&Number(r.endEpochMs)<=Number(turn.endEpochMs));
    assert.ok(during.length>0,"pure presenter completed input while the script was executing");
    assert.ok(during.some(r=>r.scroll===1200),"last band request was published during the script turn");
    assert.equal(records.filter(r=>r.type==="presenter-worker-result").length,1);
    console.log(`Presenter completed ${during.length} input/tick pairs during the script turn; CPU bytes matched the serial oracle.`);
  });
}
