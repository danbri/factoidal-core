// The jukebox page (pages/jukebox.html) in the native engine with a `wav` audio sink: step D3 (second
// part) of docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13.10 (issue
// https://github.com/danbri/factoidal-core/issues/1169). The host clicks "Decode all" (the status
// reads "Decoded 6 of 6 tracks."), then "Play" (trusted pointer down and up); after about 4.5 s of
// turns the WAV file holds the first track's frames: the decoded buffer (`lake exe media-bench decode`
// of the same file at the context's rate) times the volume (0.8, as binary32), after the leading
// part the output took before the context's first frame (none when it had no under-run at its
// start). 0 under-runs. Records the page's "From the last click to the first frame played" line.
// Run: deno test --no-check --unstable-ffi -A webaudio_jukebox_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn,type AudioRun} from "./native_html_engine.ts";

const lab=new URL("./",import.meta.url).pathname;
const root=lab+"../../../";
const library=(()=>{try{const e=Deno.env.get("WEB_RENDER_LIB");if(e)return e;}catch{/* no env permission */}
  return lab+`.build/web-render/engines/libweb-render.${Deno.build.os==="darwin"?"dylib":"so"}`;})();
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const home=Deno.env.get("HOME")??"";
const decoders=Deno.env.get("FOAFNAUT_MEDIA_DECODERS")||`${home}/.cache/factoidal/media-decoders`;
const bench=Deno.env.get("MEDIA_BENCH")||`${root}formal/lean4/.lake/build/bin/media-bench`;
const have=(p:string)=>{try{Deno.statSync(p);return true;}catch{return false;}};
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));
type Turn=ScriptTurn;

const probe=`<script>
setTimeout(()=>{console.log('viewport '+innerWidth+' '+innerHeight);for(const id of ['decodeAll','play']){const r=document.getElementById(id).getBoundingClientRect();
  console.log('rect '+id+' '+[r.left,r.top,r.width,r.height].join(' '));}},0);
document.addEventListener('click',e=>console.log('click '+(e.target.id||e.target.tagName)+' trusted '+e.isTrusted),true);
window.addEventListener('message',e=>{document.getElementById(e.data).click();});
const st=document.getElementById('status');
new MutationObserver(()=>console.log('status '+st.textContent)).observe(st,{childList:true,characterData:true,subtree:true});
setInterval(()=>console.log('vol '+document.getElementById('vol').value+' '+JSON.stringify(window.jukebox.state())),1000);
setInterval(()=>console.log('latency '+document.getElementById('latency').textContent+' | time '+document.getElementById('time').textContent),500);
</script>`;

const wavOf=(bytes:Uint8Array)=>{
  const dv=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  assert.equal(String.fromCharCode(...bytes.subarray(0,4)),"RIFF");
  const channels=dv.getUint16(22,true),rate=dv.getUint32(24,true);
  const samples=new Float32Array(bytes.slice(58).buffer);
  return {channels,rate,samples,frames:samples.length/channels};
};

Deno.test({name:"jukebox: Decode all, then Play: the WAV file holds the first track's decoded frames",
    ignore:noLibrary||!have(bench)||!have(`${decoders}/mp3-wasmvm.wasm`)||Deno.build.os!=="linux",fn:async()=>{
  const wavPath=await Deno.makeTempFile({suffix:".wav"});
  Deno.env.set("FOAFNAUT_AUDIO_SINK",`wav:${wavPath}`);Deno.env.set("FOAFNAUT_AUTOPLAY","allow");Deno.env.set("FOAFNAUT_MEDIA_DECODERS",decoders);
  const page=Deno.readTextFileSync(lab+"pages/jukebox.html").replace("</body>",probe+"</body>");
  const engine=await loadHTML(library,"bytes",{session:true});
  const url="file:///jukebox.html";
  const turn=engine.scriptSession(page,{action:"start",url,resources:[],engine:"bubblepop",instructionsPerMs:1e12,full:true,dangerouslyPermitAudio:true}) as Turn;
  assert.deepEqual(turn.errors,[],"page errors at start");
  const session=turn.session,logs=[...turn.logs];
  let commands=turn.commands??[];
  let last=performance.now();
  const turns=async(ms:number,done?:()=>boolean)=>{
    const t0=performance.now();
    while(performance.now()-t0<ms&&!(done&&done())){
      await sleep(10);const now=performance.now();
      const t=engine.scriptSession("",{action:"advance",session,ms:Math.max(1,Math.round(now-last)),full:true}) as Turn;last=now;
      assert.deepEqual(t.errors,[],"page errors");logs.push(...t.logs);if(t.commands)commands=t.commands;
    }
  };
  const lastLog=(p:string)=>logs.filter(l=>l.startsWith(p)).pop();
  // The host's click: the page's script moves the buttons (it lists the tracks), and the engine's hit test
  // reads the page's static layout, so the host sends a message and the page calls the button's click().
  const click=(id:string)=>{
    const t=engine.scriptSession("",{action:"message",session,data:JSON.stringify(id),origin:"file://"}) as Turn;
    logs.push(...t.logs);
  };
  try{
    await turns(500,()=>lastLog("rect play ")!==undefined);
    assert.ok(lastLog("rect decodeAll "),logs.join("\n"));
    const t0=performance.now();
    click("decodeAll");
    await turns(60000,()=>lastLog("status Decoded ")!==undefined);
    const decodeMs=performance.now()-t0;
    assert.equal(lastLog("status Decoded "),"status Decoded 6 of 6 tracks.",lastLog("viewport ")+" "+logs.filter(l=>!l.startsWith("latency")).slice(-12).join(" | "));
    // Play: the first track.
    const readAtPlay=engine.audioRuns()?.items[0]?.read??0;
    click("play");
    let run:AudioRun|undefined;
    await turns(30000,()=>{const r=engine.audioRuns();run=r?.items[0];return run!==undefined&&run.read>=readAtPlay+48000*6;});
    const latency=lastLog("latency ")!;
    // The context's rate, from the output.
    assert.ok(run,"no run");
    assert.equal(run!.underruns,0,`under-runs: ${JSON.stringify(run)}`);
    assert.ok(run!.read>=0);
    engine.scriptSession("",{action:"close"});engine.endSession?.();
    const wav=wavOf(await Deno.readFile(wavPath));
    const rate=wav.rate;
    // The expected frames: the first track decoded at the context's rate, by the command line tool.
    const out=await Deno.makeTempFile({suffix:".f32"});
    const p=await new Deno.Command(bench,{args:["decode",decoders,`${root}third_party/media/arpeggio-cbr128.mp3`,String(rate),out],stdout:"piped",stderr:"piped"}).output();
    assert.equal(p.code,0,new TextDecoder().decode(p.stdout));
    const head=new TextDecoder().decode(p.stdout).match(/buffer (\d+) channels, ([\d.]+) Hz, (\d+) frames/)!;
    const nch=Number(head[1]),len=Number(head[3]);
    const dec=new Float32Array(Deno.readFileSync(out).slice().buffer);Deno.removeSync(out);
    assert.equal(wav.channels,2);assert.equal(nch,2);
    const gain=Math.fround(0.8);
    const want=(i:number,c:number)=>Math.fround(dec[i*nch+c]*gain);
    // The leading part: the first frame where the next 256 frames equal the decoded frames (the track
    // starts 0.05 s after the first click, so the file begins with silence).
    const near=(a:number,b:number)=>Math.abs(a-b)<=1e-6;
    const matchAt=(o:number,from:number,n:number)=>{for(let i=0;i<n;i++)for(let c=0;c<2;c++)if(!near(wav.samples[2*(o+i)+c],want(from+i,c)))return false;return true;};
    // find the first frame whose value is large enough to pin the alignment: the 3rd note's start at 1 s of the clip
    let lead=-1;const from=Math.round(rate*0.3);
    for(let o=from;o+256<=wav.frames&&lead<0;o++)if(matchAt(o,from,256))lead=o-from;
    if(lead<0){
      let nz=0;while(nz<wav.frames&&wav.samples[2*nz]===0&&wav.samples[2*nz+1]===0)nz++;
      const mx=(a:Float32Array)=>a.reduce((m,v)=>Math.max(m,Math.abs(v)),0);
      console.log(JSON.stringify(run));console.log(logs.filter(l=>!l.startsWith('latency')&&!l.startsWith('rect')).slice(-10).join(' | '));
      console.log(JSON.stringify({rate,frames:wav.frames,firstNonZero:nz,wavAtNz:Array.from(wav.samples.subarray(2*nz+2*from,2*nz+2*from+6)),
        decAtFrom:Array.from(dec.subarray(from*2,from*2+6)),wavMax:mx(wav.samples),decMax:mx(dec),len}));
    }
    assert.ok(lead>=0,"the decoded frames are not in the WAV file");
    const n=Math.min(len,wav.frames-lead);
    let equal=0,maxDiff=0;
    for(let i=0;i<n;i++)for(let c=0;c<2;c++){const d=Math.abs(wav.samples[2*(lead+i)+c]-want(i,c));if(d===0)equal++;maxDiff=Math.max(maxDiff,d);}
    console.log(JSON.stringify({decodeAllMs:+decodeMs.toFixed(0),contextRate:rate,trackFrames:len,leadingFrames:lead,comparedFrames:n,bitForBit:equal===2*n,
      equalValues:equal,values:2*n,maxDiff,underruns:run!.underruns,wavFrames:wav.frames,latencyLine:latency}));
    assert.equal(n,len,`only ${n} of ${len} frames compared`);
    assert.ok(maxDiff<=1e-6,`the WAV differs from the decoded buffer by up to ${maxDiff}`);
  }finally{await Deno.remove(wavPath).catch(()=>{});}
}});
