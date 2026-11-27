// Real-time Web Audio in the engine: step D3 (first part) of
// docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13 (issue
// https://github.com/danbri/factoidal-core/issues/1169). Pages run on BubblePopJS in the native
// library (`build-web-render.sh --native`; `WEB_RENDER_LIB=` names another). Each check uses an
// engine session of its own, so the engine reads the environment's audio settings anew when the
// page starts: FOAFNAUT_AUDIO_SINK (`wav:FILE`: the frames the output took, silence included, as
// a 32-bit float WAV file; `null`). A start request with `dangerouslyPermitAudio: true` (what the
// window sends for --dangerously-permit-audio) lets a context start with no user activation; without
// it the page must be used first (CLAUDE.md, "Audio: AAC through AudioToolbox, HRTF data, autoplay
// rule"). The host gives turns as a window
// would: an `advance` by the real time since the last turn, every 10 ms (the engine asks for at most
// 25 ms while a context runs, `nextWake`). Checks:
//  1. `new AudioContext()` plays a 440 Hz OscillatorNode for one second through the wav sink: the
//     file holds, after its leading part (none when the output had no under-run at its start), the
//     frames of an OfflineAudioContext render of the same graph made in the same page (the second
//     and 2048 frames of silence after it), compared after binary32 rounding (bit for bit); no under-run
//     while it played; currentTime never decreases across turns; `ended` fires; close() resolves,
//     the sink closes (the WAV header has its sizes), the run's task ends (the registry holds no
//     run, its thread is gone). Prints the rendering thread's CPU time per second of audio and the
//     frames ahead of the output (least and most).
//  2. with no permission the context starts suspended, resume() waits; a press of the user's mouse
//     (pointer down and up, trusted input, which Lean's WebScripts.performInput turns into the page's
//     sticky activation) activates the page; resume() resolves, then statechange fires.
//  3. suspend() then resume(): no under-run and no silent frame is counted while suspended.
//  4. a run ends, and its thread is gone, on the document op audioEnd and when its engine session
//     ends with no close of the page (web_session_free).
// Run: deno test --no-check --unstable-ffi -A webaudio_realtime_test.ts (Deno reads /proc of its own process
// only with all permissions: the rendering thread's CPU time is /proc/<pid>/task/<tid>/schedstat).
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn,type AudioRun} from "./native_html_engine.ts";

const lab=new URL("./",import.meta.url).pathname;
const library=(()=>{try{const e=Deno.env.get("WEB_RENDER_LIB");if(e)return e;}catch{/* no env permission */}
  return lab+`.build/web-render/engines/libweb-render.${Deno.build.os==="darwin"?"dylib":"so"}`;})();
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));

type Turn=ScriptTurn&{engine?:string};
/** An engine session with the environment's audio settings, and a page started on BubblePopJS;
`permit`: the start request has `dangerouslyPermitAudio: true`. */
async function startPage(env:Record<string,string|undefined>,source:string,permit=false){
  for(const [k,v] of Object.entries(env)){if(v===undefined)Deno.env.delete(k);else Deno.env.set(k,v);}
  const engine=await loadHTML(library,"bytes",{session:true});
  const url="file:///webaudio.html";
  const turn=engine.scriptSession(source,{action:"start",url,resources:[],engine:"bubblepop",instructionsPerMs:1e12,full:true,
    ...(permit?{dangerouslyPermitAudio:true}:{})}) as Turn;
  assert.deepEqual(turn.errors,[],"page errors at start");
  return {engine,url,turn};
}
/** Turns every 10 ms, each an `advance` by the real time since the last, until `done` holds of the
logs so far or `limitMs` passes. `each` sees every turn. */
async function turnsUntil(engine:HTMLEngine,session:number,logs:string[],done:(logs:string[])=>boolean,limitMs:number,
    each?:(turn:Turn)=>void){
  const t0=performance.now();let last=t0;
  while(!done(logs)){
    if(performance.now()-t0>limitMs)throw new Error(`no end after ${limitMs} ms; logs: ${logs.slice(-12).join(" | ")}`);
    await sleep(10);
    const now=performance.now();
    const turn=engine.scriptSession("",{action:"advance",session,ms:Math.max(1,Math.round(now-last)),full:true}) as Turn;
    last=now;
    assert.deepEqual(turn.errors,[],"page errors");
    logs.push(...turn.logs);
    each?.(turn);
  }
}
const onlyRun=(engine:HTMLEngine)=>{const r=engine.audioRuns();assert.ok(r,"the engine has no audioRuns op");return r;};

const wavOf=(bytes:Uint8Array)=>{
  const dv=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  const tag=(o:number)=>String.fromCharCode(...bytes.subarray(o,o+4));
  assert.equal(tag(0),"RIFF");assert.equal(tag(8),"WAVE");assert.equal(tag(50),"data");
  assert.equal(dv.getUint16(20,true),3,"WAVE_FORMAT_IEEE_FLOAT");
  const channels=dv.getUint16(22,true),rate=dv.getUint32(24,true),dataBytes=dv.getUint32(54,true);
  const samples=new Float32Array(bytes.slice(58).buffer);
  return {channels,rate,dataBytes,samples,frames:samples.length/channels};
};
const fromBase64=(b:string)=>{const s=atob(b);const u=new Uint8Array(s.length);for(let i=0;i<s.length;i++)u[i]=s.charCodeAt(i);return new Float32Array(u.buffer);};
const schedNs=(tid:number)=>{try{return Number(Deno.readTextFileSync(`/proc/self/task/${tid}/schedstat`).split(" ")[0]);}catch{return NaN;}};
const threadAlive=(tid:number)=>{try{Deno.statSync(`/proc/self/task/${tid}`);return true;}catch{return false;}};

const playPage=`<!doctype html><meta charset=utf-8><body><p id=out>start</p><script>
const log=(...a)=>console.log(a.join(' '));
const ac=new AudioContext();
const osc=new OscillatorNode(ac,{frequency:440});
osc.connect(ac.destination);
osc.start();
const t0=ac.currentTime;
osc.stop(t0+1);
log('made',ac.state,ac.sampleRate,t0,ac.baseLatency,ac.destination.maxChannelCount);
setInterval(()=>log('time',ac.currentTime),20);
// The same graph rendered offline, in the same page; its channels go to the host as Base64 of their binary32 bytes.
const off=new OfflineAudioContext(2,Math.round(ac.sampleRate)+2048,ac.sampleRate);
const o2=new OscillatorNode(off,{frequency:440});
o2.connect(off.destination);o2.start();o2.stop(t0+1);
off.startRendering().then(buf=>{
  for(let c=0;c<2;c++){const d=buf.getChannelData(c);
    for(let i=0;i<d.length;i+=8192){const part=new Uint8Array(d.buffer,d.byteOffset+4*i,4*Math.min(8192,d.length-i));
      let b='';for(let j=0;j<part.length;j++)b+=String.fromCharCode(part[j]);log('offline',c,i,btoa(b));}}
  log('rendered',buf.length);
});
osc.onended=()=>{log('ended',ac.currentTime);document.getElementById('out').textContent='ended';};
window.addEventListener('message',e=>{if(e.data==='close')ac.close().then(()=>log('closed',ac.state));});
</script>`;

Deno.test({name:"real-time audio: an AudioContext plays what an OfflineAudioContext renders, with no under-run",ignore:noLibrary||Deno.build.os!=="linux",fn:async()=>{
  const wavPath=await Deno.makeTempFile({suffix:".wav"});
  const {engine,turn}=await startPage({FOAFNAUT_AUDIO_SINK:`wav:${wavPath}`},playPage,true);
  const session=turn.session,logs=[...turn.logs];
  try{
    const made=logs.find(l=>l.startsWith("made "))!.split(" ");
    // Web Audio API, the constructor: suspended at once; statechange to running follows.
    assert.equal(made[1],"suspended");
    const rate=Number(made[2]);
    // The offline render's length: one second of the oscillator, then 2048 frames of silence.
    const need=Math.round(rate)+2048;
    // Until `ended` and until the output has taken `need` frames (the rendering side is up to the
    // target ahead of it): currentTime from the interval's lines, the run's measures at each turn.
    let last:AudioRun|undefined,cpuNs=NaN,times:number[]=[];
    await turnsUntil(engine,session,logs,l=>l.some(x=>x.startsWith("ended "))&&last!==undefined&&last.read>=need,8000,()=>{
      const r=onlyRun(engine);
      if(r.items.length===1){last=r.items[0];const c=schedNs(last.tid);if(!Number.isNaN(c))cpuNs=c;}
    });
    times=logs.filter(l=>l.startsWith("time ")).map(l=>Number(l.split(" ")[1]));
    assert.ok(times.length>20,`only ${times.length} currentTime samples`);
    for(let i=1;i<times.length;i++)assert.ok(times[i]>=times[i-1],`currentTime went back: ${times[i-1]} then ${times[i]}`);
    assert.ok(last,"no run was seen");
    assert.equal(last!.underruns,0,`under-runs while it played: ${JSON.stringify(last)}`);
    assert.equal(last!.silent,0);assert.equal(last!.divergence,0);assert.equal(last!.sinkError,"");
    const tid=last!.tid;
    assert.ok(threadAlive(tid),"the rendering thread is not there while the context runs");
    // close(): the sink closes, the task ends, the run leaves the registry.
    let t=engine.scriptSession("",{action:"message",session,data:JSON.stringify("close"),origin:"file://"}) as Turn;logs.push(...t.logs);
    await turnsUntil(engine,session,logs,l=>l.some(x=>x.startsWith("closed ")),3000);
    assert.equal(logs.find(l=>l.startsWith("closed ")),"closed closed");
    // The run leaves the registry at the turn after its task has ended.
    await turnsUntil(engine,session,logs,()=>onlyRun(engine).runs===0,2000);
    for(let i=0;i<50&&threadAlive(tid);i++)await sleep(10);
    assert.ok(!threadAlive(tid),"the rendering thread is still there after close()");
    // The WAV file: the offline frames after the leading part.
    const wav=wavOf(await Deno.readFile(wavPath));
    assert.equal(wav.channels,2);assert.equal(wav.rate,rate);
    assert.equal(wav.dataBytes,wav.samples.length*4,"the header's data size (patched at close)");
    const offline=[0,1].map(c=>{
      const parts=logs.filter(l=>l.startsWith(`offline ${c} `)).map(l=>l.split(" ")).sort((a,b)=>Number(a[2])-Number(b[2]));
      const chunks=parts.map(p=>fromBase64(p[3]));
      const all=new Float32Array(chunks.reduce((n,x)=>n+x.length,0));let o=0;for(const x of chunks){all.set(x,o);o+=x.length;}
      return all;
    });
    assert.equal(offline[0].length,need);
    // The leading part: the frames before the first frame where the next 512 frames match.
    const match=(o:number,n:number)=>{for(let i=0;i<n;i++)for(let c=0;c<2;c++)if(wav.samples[2*(o+i)+c]!==offline[c][i])return false;return true;};
    let lead=-1;
    for(let o=0;o+512<=wav.frames;o++)if(match(o,512)){lead=o;break;}
    assert.ok(lead>=0,"the offline frames are not in the WAV file");
    const n=Math.min(offline[0].length,wav.frames-lead);
    let equal=0,maxDiff=0;
    for(let i=0;i<n;i++)for(let c=0;c<2;c++){const d=Math.abs(wav.samples[2*(lead+i)+c]-offline[c][i]);if(d===0)equal++;maxDiff=Math.max(maxDiff,d);}
    const seconds=last!.quanta*128/rate;
    console.log(JSON.stringify({leadingFrames:lead,comparedFrames:n,bitForBit:equal===2*n,equalValues:equal,maxDiff,
      wavFrames:wav.frames,underruns:last!.underruns,quanta:last!.quanta,audioSeconds:+seconds.toFixed(3),
      threadCpuMsPerAudioSecond:+(cpuNs/1e6/seconds).toFixed(3),renderMsPerAudioSecond:+(last!.renderNs/1e6/seconds).toFixed(3),
      aheadMin:last!.aheadMin,aheadMax:last!.aheadMax,looks:last!.looks,refused:last!.refused,currentTimeSamples:times.length}));
    assert.equal(lead,0,"the output did not start with the context's first frame");
    assert.equal(n,need,`only ${n} frames after the leading part`);
    assert.equal(equal,2*n,`not bit for bit: ${2*n-equal} values differ, the most by ${maxDiff}`);
  }finally{
    engine.scriptSession("",{action:"close"});
    engine.endSession?.();
    await Deno.remove(wavPath).catch(()=>{});
  }
}});

const activationPage=`<!doctype html><meta charset=utf-8><body style="margin:0">
<div id=pad style="position:absolute;left:0;top:0;width:300px;height:200px;background:#ccc">press</div><script>
const log=(...a)=>console.log(a.join(' '));
const ac=new AudioContext();
log('made',ac.state);
ac.onstatechange=()=>log('statechange',ac.state);
ac.resume().then(()=>log('resumed',ac.state));
</script>`;

Deno.test({name:"real-time audio: with no permission, resume() waits for the user's activation",ignore:noLibrary||Deno.build.os!=="linux",fn:async()=>{
  const {engine,url,turn}=await startPage({FOAFNAUT_AUDIO_SINK:"null"},activationPage);
  const session=turn.session,logs=[...turn.logs];
  try{
    assert.ok(logs.includes("made suspended"),logs.join("\n"));
    // A suspended context with a resume() that waits for activation asks for no turns.
    assert.equal(turn.nextWake,null,"a waiting resume() asked for turns");
    // 300 ms of turns: resume() still waits.
    const t0=performance.now();
    await turnsUntil(engine,session,logs,()=>performance.now()-t0>300,2000);
    assert.ok(!logs.some(l=>l.startsWith("resumed")||l.startsWith("statechange")),logs.join("\n"));
    assert.equal(onlyRun(engine).items.length,1,"the suspended context has no run");
    // The user's press: pointer down and up of a mouse, trusted.
    const commands=turn.commands??[];
    const at=engine.pointerAt(activationPage,800,600,{url,commands,x:50,y:50});
    assert.equal(typeof at.node,"number");
    for(const [kind,buttons] of [["down",1],["up",0]] as const){
      const t=engine.scriptSession("",{action:"pointer",session,kind,...at,button:0,buttons,pointerType:"mouse"}) as Turn;
      logs.push(...t.logs);
    }
    await turnsUntil(engine,session,logs,l=>l.some(x=>x.startsWith("statechange")),3000);
    const order=logs.filter(l=>l.startsWith("resumed")||l.startsWith("statechange"));
    assert.deepEqual(order,["resumed running","statechange running"],"resume() resolves, then statechange");
  }finally{
    engine.scriptSession("",{action:"close"});
    assert.equal(onlyRun(engine).runs,0,"a run is left after the page session closed");
    engine.endSession?.();
  }
}});

const suspendPage=`<!doctype html><meta charset=utf-8><body><script>
const log=(...a)=>console.log(a.join(' '));
const ac=new AudioContext();
const src=new ConstantSourceNode(ac,{offset:0.25});
src.connect(ac.destination);src.start();
ac.onstatechange=()=>log('statechange',ac.state);
window.addEventListener('message',e=>{
  if(e.data==='suspend')ac.suspend().then(()=>log('suspended',ac.state));
  if(e.data==='resume')ac.resume().then(()=>log('resumed',ac.state));
});
</script>`;

Deno.test({name:"real-time audio: no under-run is counted while a context is suspended",ignore:noLibrary||Deno.build.os!=="linux",fn:async()=>{
  const {engine,turn}=await startPage({FOAFNAUT_AUDIO_SINK:"null"},suspendPage,true);
  const session=turn.session,logs=[...turn.logs];
  const say=(data:string)=>{const t=engine.scriptSession("",{action:"message",session,data:JSON.stringify(data),origin:"file://"}) as Turn;logs.push(...t.logs);};
  try{
    let t0=performance.now();
    await turnsUntil(engine,session,logs,()=>performance.now()-t0>400,2000);
    say("suspend");
    await turnsUntil(engine,session,logs,l=>l.some(x=>x.startsWith("suspended")),2000);
    const atSuspend=onlyRun(engine).items[0];
    // 600 ms suspended, with turns.
    t0=performance.now();
    await turnsUntil(engine,session,logs,()=>performance.now()-t0>600,2000);
    const after=onlyRun(engine).items[0];
    assert.equal(after.underruns,atSuspend.underruns,"under-runs counted while suspended");
    assert.equal(after.silent,atSuspend.silent,"silent frames counted while suspended");
    assert.equal(after.read,atSuspend.read,"frames taken while suspended");
    say("resume");
    await turnsUntil(engine,session,logs,l=>l.some(x=>x.startsWith("resumed")),2000);
    t0=performance.now();
    await turnsUntil(engine,session,logs,()=>performance.now()-t0>300,2000);
    const resumed=onlyRun(engine).items[0];
    assert.ok(resumed.read>after.read,"nothing played after resume()");
    assert.equal(resumed.underruns,0,`under-runs: ${JSON.stringify(resumed)}`);
    // The first statechange is the start (Web Audio API, the constructor: suspended, then running).
    assert.deepEqual(logs.filter(l=>l.startsWith("statechange")),["statechange running","statechange suspended","statechange running"]);
    console.log(JSON.stringify({atSuspend:{read:atSuspend.read,underruns:atSuspend.underruns},suspended:{read:after.read,underruns:after.underruns},
      resumed:{read:resumed.read,underruns:resumed.underruns,aheadMin:resumed.aheadMin,aheadMax:resumed.aheadMax}}));
  }finally{
    engine.scriptSession("",{action:"close"});
    engine.endSession?.();
  }
}});

Deno.test({name:"real-time audio: a context's run ends on audioEnd, and with its engine session",ignore:noLibrary||Deno.build.os!=="linux",fn:async()=>{
  const env={FOAFNAUT_AUDIO_SINK:"null"};
  const runningTid=async(engine:HTMLEngine,session:number,logs:string[])=>{
    await turnsUntil(engine,session,logs,()=>onlyRun(engine).items.some(r=>r.tid>0&&r.quanta>0),2000);
    return onlyRun(engine).items[0].tid;
  };
  const gone=async(tid:number)=>{for(let i=0;i<50&&threadAlive(tid);i++)await sleep(10);return !threadAlive(tid);};
  // audioEnd (a host that drops an engine it does not free): the runs end, their threads are gone.
  {
    const {engine,turn}=await startPage(env,suspendPage,true);
    try{
      const tid=await runningTid(engine,turn.session,[...turn.logs]);
      assert.equal(engine.audioEnd()?.runs,0);
      assert.ok(await gone(tid),"the rendering thread is still there after audioEnd");
    }finally{
      engine.scriptSession("",{action:"close"});
      engine.endSession?.();
    }
  }
  // The engine session ends with no close of the page (a tab closed): web_session_free ends the runs.
  {
    const {engine,turn}=await startPage(env,suspendPage,true);
    const tid=await runningTid(engine,turn.session,[...turn.logs]);
    engine.endSession?.();
    assert.ok(await gone(tid),"the rendering thread is still there after its engine session ended");
  }
}});
