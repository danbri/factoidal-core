// Back and forward swipes (WebGesture.lean) through the op `gesture` of the
// engine the hosts load. Lean is the only implementation; this checks its answers on
// generated touches and trackpad gestures against the conventions and the theorems, and
// that an engine answers the probe the hosts make. Wasm engine, and the native library when
// it is built. Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();

type Touch={width:number;startX:number;startY:number;x:number;y:number;vx:number;fingers:number;ended:boolean};

function checks(engine:HTMLEngine){
  const info=engine.gesture({action:"info"}) as unknown as Record<string,unknown>;
  assert.deepEqual(info,{actions:["touch","wheel","hold"],edgeZone:20,holdMs:500,tapSlop:10,commitPercent:30,flingSpeed:500,wheelCommit:140,dominance:2});
  const touch=(t:Touch)=>engine.gesture({action:"touch",...t});
  // Conventions.
  const at=(startX:number,x:number,more:Partial<Touch>={}):Touch=>({width:400,startX,startY:300,x,y:300,vx:0,fingers:1,ended:true,...more});
  assert.deepEqual(touch(at(5,140)),{phase:"swipe",direction:"back",progress:100,navigate:true,hint:-100});
  assert.equal(touch(at(395,260)).direction,"forward");assert.equal(touch(at(395,260)).navigate,true);
  assert.equal(touch(at(5,80)).navigate,false);
  assert.equal(touch(at(5,80,{vx:900})).navigate,true);
  assert.equal(touch(at(5,140,{vx:-900})).navigate,false);
  assert.equal(touch(at(5,12,{ended:false,y:305})).phase,"pending");
  assert.equal(touch(at(5,77,{ended:false})).hint,-60);
  // A host may send fractions: the whole part counts.
  assert.equal(engine.gesture({action:"touch",...at(5,140),x:140.7}).navigate,true);
  // Generated touches: every answer against the theorems.
  let n=0,navigations=0;
  const xs=[-5,0,3,10,19,20,21,100,180,200,350,379,380,381,390,399,400,405];
  const ds=[-300,-121,-120,-60,-11,-10,-9,0,9,10,11,60,119,120,121,300];
  for(const width of [30,40,400,1024])for(const startX of xs)for(const dx of ds)for(const dy of [-200,-30,-6,0,6,30,60,200])
    for(const vx of [-2000,-500,-499,0,499,500,2000])for(const fingers of [1,2])for(const ended of [true,false]){
      if(Math.abs(startX)>width+10)continue;
      const t={width,startX,startY:300,x:startX+dx,y:300+dy,vx,fingers,ended};
      const a=touch(t);n++;
      const left=startX<20,right=width-startX<20;
      if(a.navigate){
        navigations++;
        assert(ended&&fingers===1,`navigate before the end or with ${fingers} fingers: ${JSON.stringify(t)}`);
        assert(left!==right,`away from the edges: ${JSON.stringify(t)}`);
        assert(Math.abs(dx)>Math.abs(dy)*2,`not mostly across: ${JSON.stringify(t)}`);
        assert(Math.abs(dx)>=10,`a tap: ${JSON.stringify(t)}`);
        assert.equal(a.direction,left?"back":"forward");
        assert.equal(Math.sign(dx),left?1:-1);
      }
      if(a.phase!=="other")assert(left!==right&&fingers===1);
      assert(a.hint>=-100&&a.hint<=100&&a.hint%10===0);
      // The mirror image: back and forward swapped.
      const m=touch({...t,startX:width-startX,x:width-t.x,vx:-vx});
      assert.deepEqual(m,{...a,direction:a.direction===null?null:a.direction==="back"?"forward":"back",hint:a.hint===0?0:-a.hint},JSON.stringify(t));
    }
  assert(navigations>100,`only ${navigations} navigations`);
  // Trackpad.
  const wheel=(dx:number,dy:number,ended=true)=>engine.gesture({action:"wheel",dx,dy,ended});
  assert.deepEqual(wheel(-150,20),{phase:"swipe",direction:"back",progress:100,navigate:true,hint:-100});
  assert.equal(wheel(150,0).direction,"forward");
  assert.equal(wheel(-150,100).navigate,false);
  assert.equal(wheel(-150,20,false).navigate,false);
  let w=0;
  for(const dx of [-400,-141,-140,-139,-70,-11,-10,-9,0,9,10,70,139,140,141,400])for(const dy of [-300,-70,-5,0,5,70,300])for(const ended of [true,false]){
    const a=wheel(dx,dy,ended);w++;
    if(a.navigate)assert(ended&&Math.abs(dx)>=140&&Math.abs(dx)>2*Math.abs(dy)&&a.direction===(dx<0?"back":"forward"));
    const m=wheel(-dx,dy,ended);
    assert.deepEqual(m,{...a,direction:a.direction===null?null:a.direction==="back"?"forward":"back",hint:a.hint===0?0:-a.hint});
  }
  assert.throws(()=>engine.gesture({action:"pinch"}));
  console.log(JSON.stringify({touches:n,navigations,wheels:w}));
}

Deno.test("gestures: Lean's answers on generated touches and trackpad swipes (Wasm)",async()=>{checks(await loadHTML());});
Deno.test({name:"gestures: Lean's answers on generated touches and trackpad swipes (native)",ignore:noLibrary,async fn(){checks(await loadHTML(library));}});
