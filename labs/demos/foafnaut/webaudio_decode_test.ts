// decodeAudioData in pages: step D3 (second part) of
// docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13.10 (issue
// https://github.com/danbri/factoidal-core/issues/1169). Pages run on BubblePopJS in the native
// library (`build-web-render.sh --native`; `WEB_RENDER_LIB=` names another). The decoder modules are
// read from FOAFNAUT_MEDIA_DECODERS, else ~/.cache/factoidal/media-decoders (tools/fetch-media-decoders.sh).
// Checks:
//  1. each CC0 clip of third_party/media (MP3 CBR, MP3 VBR, MPEG-2 MP3, Ogg Vorbis, Opus), decoded by
//     an OfflineAudioContext at 44100 Hz: the buffer's channels, length and rate and every sample
//     (binary32, bit for bit) equal those of `lake exe media-bench decode` on the same file; the page's
//     ArrayBuffer is detached; the promise resolves, then the success callback is called. A WAV made in
//     the page decodes to its int16 / 32768 values.
//  2. a file that is not audio rejects with EncodingError (and calls the error callback); a second
//     decode of the same (detached) ArrayBuffer rejects with DataCloneError; a decode on an
//     AudioContext works too; bad arguments reject with TypeError.
//  3. with no decoder modules (FOAFNAUT_MEDIA_DECODERS names an empty directory) an MP3 rejects
//     with NotSupportedError naming tools/fetch-media-decoders.sh; a WAV (no module needed) decodes.
// Run: deno test --no-check --unstable-ffi -A webaudio_decode_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";

const lab=new URL("./",import.meta.url).pathname;
const root=lab+"../../../";
const library=(()=>{try{const e=Deno.env.get("WEB_RENDER_LIB");if(e)return e;}catch{/* no env permission */}
  return lab+`.build/web-render/engines/libweb-render.${Deno.build.os==="darwin"?"dylib":"so"}`;})();
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const home=Deno.env.get("HOME")??"";
const decoders=Deno.env.get("FOAFNAUT_MEDIA_DECODERS")||`${home}/.cache/factoidal/media-decoders`;
const bench=Deno.env.get("MEDIA_BENCH")||`${root}formal/lean4/.lake/build/bin/media-bench`;
const noBench=(()=>{try{Deno.statSync(bench);return false;}catch{return true;}})();
const sleep=(ms:number)=>new Promise(r=>setTimeout(r,ms));
const clips=["arpeggio-cbr128.mp3","arpeggio-vbr.mp3","arpeggio-mono22.mp3","arpeggio.ogg","arpeggio.opus"];

const b64=(b:Uint8Array)=>{let s="";for(let i=0;i<b.length;i+=8192)s+=String.fromCharCode(...b.subarray(i,i+8192));return btoa(s);};
/** FNV-1a over the 32-bit words of a Float32Array's bytes (the page computes the same). */
const fnv=(w:Uint32Array)=>{let h=0x811c9dc5;for(let i=0;i<w.length;i++){h^=w[i];h=Math.imul(h,0x01000193)>>>0;}return h>>>0;};

const decodePage=(clipsB64:Record<string,string>)=>`<!doctype html><meta charset=utf-8><body><script>
const log=(...a)=>console.log(a.join(' '));
const clips=${JSON.stringify(clipsB64)};
const bytesOf=s=>{const t=atob(s);const u=new Uint8Array(t.length);for(let i=0;i<t.length;i++)u[i]=t.charCodeAt(i);return u;};
const fnv=w=>{let h=0x811c9dc5;for(let i=0;i<w.length;i++){h^=w[i];h=Math.imul(h,0x01000193)>>>0;}return h>>>0;};
const describe=(name,b)=>{
  const hs=[];for(let c=0;c<b.numberOfChannels;c++){const d=b.getChannelData(c);hs.push(fnv(new Uint32Array(d.buffer,d.byteOffset,d.length)));}
  const d0=b.getChannelData(0);
  log('buffer',name,b.numberOfChannels,b.length,b.sampleRate,hs.join(','),Array.from(d0.subarray(0,4)).join(','));
};
// A 16-bit PCM mono WAV at 44100 Hz made here: 3000 frames of a 440 Hz sine; the decode needs no resampling.
const wav=(()=>{const n=3000,u=new Uint8Array(44+2*n),dv=new DataView(u.buffer);
  const tag=(o,s)=>{for(let i=0;i<4;i++)u[o+i]=s.charCodeAt(i);};
  tag(0,'RIFF');dv.setUint32(4,36+2*n,true);tag(8,'WAVE');tag(12,'fmt ');dv.setUint32(16,16,true);dv.setUint16(20,1,true);dv.setUint16(22,1,true);
  dv.setUint32(24,44100,true);dv.setUint32(28,88200,true);dv.setUint16(32,2,true);dv.setUint16(34,16,true);tag(36,'data');dv.setUint32(40,2*n,true);
  for(let i=0;i<n;i++)dv.setInt16(44+2*i,Math.round(Math.sin(2*Math.PI*440*i/44100)*20000),true);
  return u;})();
const ctx=new OfflineAudioContext(2,1,44100);
const order=[];
window.addEventListener('message',async e=>{
  const [cmd,name]=e.data;
  try{
    if(cmd==='clip'){
      const ab=bytesOf(clips[name]).buffer,before=ab.byteLength;
      const p=ctx.decodeAudioData(ab,b=>order.push('success'));
      log('detached',name,before,ab.byteLength);
      const b=await p;order.push('resolved');
      await new Promise(r=>setTimeout(r,0));
      describe(name,b);log('order',name,order.join(','));order.length=0;
    }else if(cmd==='wav'){
      const ab=wav.buffer.slice(0);const b=await ctx.decodeAudioData(ab);describe('wav',b);
    }else if(cmd==='bad'){
      const ab=new Uint8Array(2000).map((_,i)=>(i*7919)&255).buffer;
      let err2=null;
      await ctx.decodeAudioData(ab,()=>log('bad success'),e=>{err2=e;}).then(()=>log('bad resolved'),e=>log('bad',e.name,e instanceof DOMException,err2===e));
      // the buffer is detached now: a second decode of it
      await ctx.decodeAudioData(ab).then(()=>log('again resolved'),e=>log('again',e.name));
    }else if(cmd==='live'){
      const ac=new AudioContext();
      const ab=wav.buffer.slice(0);const b=await ac.decodeAudioData(ab);describe('live',b);await ac.close();
    }else if(cmd==='nomodule'){
      await ctx.decodeAudioData(bytesOf(clips[name]).buffer).then(()=>log('nomodule resolved',name),e=>log('nomodule',name,e.name,e.message));
    }else if(cmd==='args'){
      for(const a of [undefined,{},new Uint8Array(4)]){
        try{await ctx.decodeAudioData(a);log('args resolved');}catch(e){log('args',e.name);}
      }
      log('args done');
    }
  }catch(e){log('failed',cmd,name,e&&e.name,e&&e.message);}
});
</script>`;

type Turn=ScriptTurn;
async function startPage(env:Record<string,string|undefined>,source:string){
  for(const [k,v] of Object.entries(env)){if(v===undefined)Deno.env.delete(k);else Deno.env.set(k,v);}
  const engine=await loadHTML(library,"bytes",{session:true});
  const turn=engine.scriptSession(source,{action:"start",url:"file:///decode.html",resources:[],engine:"bubblepop",instructionsPerMs:1e12,full:true,dangerouslyPermitAudio:true}) as Turn;
  assert.deepEqual(turn.errors,[],"page errors at start");
  return {engine,turn};
}
/** Send a message to the page; give turns until a log line starting with `until` appears (or a `failed` line). */
async function say(engine:Awaited<ReturnType<typeof startPage>>["engine"],session:number,logs:string[],msg:unknown[],until:string,limitMs=20000){
  const from=logs.length;
  const t=engine.scriptSession("",{action:"message",session,data:JSON.stringify(msg),origin:"file://"}) as Turn;
  assert.deepEqual(t.errors,[],"page errors");logs.push(...t.logs);
  const t0=performance.now();let last=t0;
  const seen=()=>logs.slice(from).find(l=>l.startsWith(until)||l.startsWith("failed"));
  while(!seen()){
    if(performance.now()-t0>limitMs)throw new Error(`no '${until}' after ${limitMs} ms; logs: ${logs.slice(-8).join(" | ")}`);
    await sleep(10);const now=performance.now();
    const turn=engine.scriptSession("",{action:"advance",session,ms:Math.max(1,Math.round(now-last)),full:true}) as Turn;last=now;
    assert.deepEqual(turn.errors,[],"page errors");logs.push(...turn.logs);
  }
  const l=seen()!;assert.ok(!l.startsWith("failed")||until.startsWith("failed"),l);
  return l.split(" ");
}
const haveModules=(()=>{try{return Deno.statSync(`${decoders}/mp3-wasmvm.wasm`).isFile;}catch{return false;}})();

Deno.test({name:"decodeAudioData: the clips equal lake exe media-bench decode, bit for bit",ignore:noLibrary||noBench||!haveModules||Deno.build.os!=="linux",fn:async()=>{
  const files:Record<string,string>={};
  for(const c of clips)files[c]=b64(Deno.readFileSync(`${root}third_party/media/${c}`));
  const {engine,turn}=await startPage({FOAFNAUT_MEDIA_DECODERS:decoders,FOAFNAUT_AUDIO_SINK:"null"},decodePage(files));
  const session=turn.session,logs=[...turn.logs];
  try{
    const report:Record<string,unknown>={};
    for(const c of clips){
      const out=await Deno.makeTempFile({suffix:".f32"});
      const t0=performance.now();
      const p=await new Deno.Command(bench,{args:["decode",decoders,`${root}third_party/media/${c}`,"44100",out],stdout:"piped",stderr:"piped"}).output();
      assert.equal(p.code,0,new TextDecoder().decode(p.stdout)+new TextDecoder().decode(p.stderr));
      const head=new TextDecoder().decode(p.stdout).match(/buffer (\d+) channels, ([\d.]+) Hz, (\d+) frames/)!;
      const nch=Number(head[1]),rate=Number(head[2]),len=Number(head[3]);
      const inter=new Float32Array(Deno.readFileSync(out).slice().buffer);Deno.removeSync(out);
      assert.equal(inter.length,nch*len);
      const t1=performance.now();
      const l=await say(engine,session,logs,["clip",c],"buffer "+c);
      const ms=performance.now()-t1;
      assert.equal(Number(l[2]),nch,`${c}: channels`);assert.equal(Number(l[3]),len,`${c}: length`);assert.equal(Number(l[4]),rate,`${c}: rate`);
      const hashes=l[5].split(",").map(Number);
      for(let ch=0;ch<nch;ch++){
        const col=new Float32Array(len);for(let i=0;i<len;i++)col[i]=inter[i*nch+ch];
        assert.equal(hashes[ch],fnv(new Uint32Array(col.buffer)),`${c}: channel ${ch} differs from media-bench`);
      }
      const det=logs.filter(x=>x.startsWith(`detached ${c} `)).pop()!.split(" ");
      assert.equal(Number(det[3]),0,`${c}: the ArrayBuffer was not detached (length ${det[3]})`);
      assert.equal(logs.filter(x=>x.startsWith(`order ${c} `)).pop(),`order ${c} success,resolved`,`${c}: the success callback runs in the task that resolves the promise, before its reactions`);
      report[c]={channels:nch,frames:len,rate,decodeAndAnswerMs:+ms.toFixed(0),mediaBenchMs:+(t1-t0).toFixed(0)};
    }
    // The WAV made in the page: exact int16/32768 values.
    const w=await say(engine,session,logs,["wav"],"buffer wav");
    assert.equal(Number(w[2]),1);assert.equal(Number(w[3]),3000);assert.equal(Number(w[4]),44100);
    const exp=new Float32Array(3000);for(let i=0;i<3000;i++)exp[i]=Math.round(Math.sin(2*Math.PI*440*i/44100)*20000)/32768;
    assert.equal(Number(w[5]),fnv(new Uint32Array(exp.buffer)),"WAV samples");
    console.log(JSON.stringify(report));
  }finally{engine.scriptSession("",{action:"close"});engine.endSession?.();}
}});

Deno.test({name:"decodeAudioData: a bad file rejects with EncodingError, a detached buffer with DataCloneError, an AudioContext decodes",ignore:noLibrary||!haveModules||Deno.build.os!=="linux",fn:async()=>{
  const {engine,turn}=await startPage({FOAFNAUT_MEDIA_DECODERS:decoders,FOAFNAUT_AUDIO_SINK:"null"},decodePage({}));
  const session=turn.session,logs=[...turn.logs];
  try{
    await say(engine,session,logs,["bad"],"again");
    assert.ok(logs.includes("bad EncodingError true true"),logs.join("\n"));
    assert.ok(logs.includes("again DataCloneError"),"a second decode of the same ArrayBuffer: "+logs.slice(-3).join("|"));
    const l=await say(engine,session,logs,["live"],"buffer live");
    // the context plays at the output's rate, so the 44.1 kHz WAV is resampled to it
    const lr=Number(l[4]);assert.equal(l[2],"1");assert.ok(lr>=3000&&Math.abs(Number(l[3])-3000*lr/44100)<=1,l.join(" "));
    await say(engine,session,logs,["args"],"args done");
    assert.deepEqual(logs.filter(x=>x.startsWith("args ")&&x!=="args done"),["args TypeError","args TypeError","args TypeError"],logs.join("\n"));
  }finally{engine.scriptSession("",{action:"close"});engine.endSession?.();}
}});

Deno.test({name:"decodeAudioData: with no decoder modules an MP3 rejects with NotSupportedError, a WAV decodes",ignore:noLibrary||Deno.build.os!=="linux",fn:async()=>{
  const empty=await Deno.makeTempDir();
  const files:Record<string,string>={"arpeggio-cbr128.mp3":b64(Deno.readFileSync(`${root}third_party/media/arpeggio-cbr128.mp3`))};
  const {engine,turn}=await startPage({FOAFNAUT_MEDIA_DECODERS:empty,FOAFNAUT_AUDIO_SINK:"null"},decodePage(files));
  const session=turn.session,logs=[...turn.logs];
  try{
    const l=await say(engine,session,logs,["nomodule","arpeggio-cbr128.mp3"],"nomodule");
    assert.equal(l[1],"arpeggio-cbr128.mp3");assert.equal(l[2],"NotSupportedError",l.join(" "));
    assert.ok(l.join(" ").includes("fetch-media-decoders.sh"),l.join(" "));
    const w=await say(engine,session,logs,["wav"],"buffer wav");
    assert.equal(Number(w[3]),3000);
  }finally{engine.scriptSession("",{action:"close"});engine.endSession?.();await Deno.remove(empty).catch(()=>{});}
}});
