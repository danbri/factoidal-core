// Time of the large-buffer steps of Web Audio in the native engine, one step at a time, by buffer
// size (docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13.10; issue
// https://github.com/danbri/factoidal-core/issues/1169). Each step is one page turn (a `message`
// to the page), timed by the host with the monotonic clock; the page's clock is virtual.
// Run: deno run --no-check --unstable-ffi -A webaudio_bigbuffer_bench.ts [LOG2 ...]   (default 16 18 20 22)
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";
const lab=new URL("./",import.meta.url).pathname;
const library=Deno.env.get("WEB_RENDER_LIB")??lab+`.build/web-render/engines/libweb-render.${Deno.build.os==="darwin"?"dylib":"so"}`;
const page=`<!doctype html><meta charset=utf-8><body><script>
let buf,ch,ctx,src,N;
const steps={
  new:n=>{N=n;buf=new AudioBuffer({length:N,sampleRate:44100});},
  channel:()=>{ch=buf.getChannelData(0);},
  fill256:()=>{for(let k=0;k<256;k++)ch[N-1-k]=k%2;},
  fillAll:()=>{for(let i=0;i<N;i+=4096)ch.fill(0.25,i,Math.min(N,i+4096));},
  context:()=>{ctx=new OfflineAudioContext(1,256,44100);src=new AudioBufferSourceNode(ctx);},
  setBuffer:()=>{src.buffer=buf;},
  alloc:n=>{window.a1=new Float32Array(n);},
  copy:n=>{window.a2=new Float32Array(n);window.a2.set(window.a1);},
  bytesView:n=>{window.u=new Uint8Array(window.a1.buffer);},
  render:n=>{const o=new OfflineAudioContext(2,n,44100);o.startRendering().then(b=>{window.rendered=b;console.log('rendered',b.length);});},
};
window.addEventListener('message',e=>{const [name,arg]=e.data;steps[name](arg);console.log('did',name);});
</script>`;
const sizes=(Deno.args.length?Deno.args.map(Number):[16,18,20,22]);
const only=Deno.env.get("STEPS")?.split(",");
for(const k of sizes){
  const n=2**k;
  const engine=await loadHTML(library,"bytes",{session:true});
  const t0=engine.scriptSession(page,{action:"start",url:"file:///bench.html",resources:[],engine:"bubblepop",instructionsPerMs:1e12,full:true}) as ScriptTurn;
  const out:Record<string,number>={};
  for(const s of ["new","channel","fill256","fillAll","alloc","copy","bytesView","context","setBuffer","render"]){
    if(only&&!only.includes(s)&&!["new","channel","context"].includes(s))continue;
    const t=performance.now();
    let r=engine.scriptSession("",{action:"message",session:t0.session,data:JSON.stringify([s,n]),origin:"file://"}) as ScriptTurn;
    let logs:string[]=[...r.logs],errs:string[]=[...r.errors];let calls=1,turnNs=r.ns??0;
    for(let i=0;i<20000&&!logs.includes("did "+s)&&errs.length===0;i++){
      r=engine.scriptSession("",{action:"advance",session:t0.session,ms:1,full:true}) as ScriptTurn;logs.push(...r.logs);errs.push(...r.errors);calls++;turnNs+=r.ns??0;
    }
    out[s]=+(performance.now()-t).toFixed(1);out[s+"_turnMs"]=+(turnNs/1e6).toFixed(1);out[s+"_calls"]=calls;
    console.log(JSON.stringify({log2:k,step:s,ms:out[s],turnMs:out[s+"_turnMs"],calls}));
    if(errs.length)out[s+"_error"]=errs.join(";") as unknown as number;
  }
  // the render promise settles in a later turn
  const t=performance.now();
  for(let i=0;i<50;i++){const r=engine.scriptSession("",{action:"advance",session:t0.session,ms:10,full:true}) as ScriptTurn;if(r.logs.some(l=>l.startsWith("rendered")))break;}
  out.renderSettle=+(performance.now()-t).toFixed(1);
  console.log(JSON.stringify({log2:k,frames:n,ms:out}));
  engine.scriptSession("",{action:"close"});engine.endSession?.();
}
