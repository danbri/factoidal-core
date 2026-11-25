// Particle Rex (pages/particle-rex.html, the owner's one-button canvas game, issue 1031):
// a cost ratchet for the canvas path it showed slow, and expected failures for the gaps it
// showed. When an engine change closes a gap, its test fails: change the assertion to the
// correct behaviour and close the issue in the same landing.
// - Canvas batches with fractional numbers: a frame of the game draws about 400 to 2,000
//   rects at fractional positions. The prelude sent every batch as text, and BubblePopJS
//   prints a fraction in about 20 microseconds; a fractional batch now goes as binary
//   numbers. The ratchet: 4,000 fillRect calls at fractional positions cost less than 3 times
//   the same calls at integer positions (release e4445d14 of main: 64.8 ms and 356.0 ms, ratio 5.49, Linux VM).
// - Expected failure: a key of the window reaches the page as keydown and keyup at once,
//   so a held key is a tap (the game's "hold = higher").
// - Expected failure: Canvas 2D text ignores the font family: "monospace" and "sans-serif"
//   measure the same.
// BubblePopJS sessions on the native library. Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const candidates=[Deno.env.get("FOAFNAUT_NATIVE_ENGINE")??"",
  new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname,
  new URL("./.build/web-render/engines/libweb-render.so",import.meta.url).pathname];
const library=candidates.find(p=>p&&exists(p))??"";
const ISSUE="https://github.com/danbri/factoidal-core/issues/";
const stillGap=(issue:string)=>`expected failure of ${ISSUE}${issue} no longer fails: make this test assert the correct result and close the issue`;
const url="file:///particle-rex-test.html";
const start=(engine:Awaited<ReturnType<typeof loadHTML>>,body:string)=>{
  const t=engine.scriptSession(`<!doctype html><html><body><canvas id=c width=800 height=500></canvas><script>${body}</script></body></html>`,
    {action:"start",url,resources:[],width:800,height:500,layout:{url},engine:"bubblepop",instructionsPerMs:1e12}) as ScriptTurn&{ns:number};
  assert.deepEqual(t.errors,[],body);
  return t;
};

Deno.test({name:"Canvas 2D: a batch of fractional numbers costs less than 3 times one of integers",ignore:!library,fn:async()=>{
  const engine=await loadHTML(library);
  const draw=(frac:boolean)=>`const x=document.getElementById('c').getContext('2d');let s=0.1;
    for(let i=0;i<4000;i++){s=s*1.0001+0.37;const v=${frac?"s%700+0.123456789":"(i*7)%700"};x.globalAlpha=${frac?"(i%7+1)/8.3":"1"};x.fillRect(v,(i*3)%480${frac?"+0.5":""},5,5);}`;
  const time=(frac:boolean)=>Math.min(...Array.from({length:3},()=>start(engine,draw(frac)).ns));
  const whole=time(false),frac=time(true),ratio=frac/whole;
  console.log(`4000 fillRect: integers ${(whole/1e6).toFixed(1)} ms, fractions ${(frac/1e6).toFixed(1)} ms, ratio ${ratio.toFixed(2)}`);
  assert.ok(ratio<3,`fractional batch ${ratio.toFixed(1)} times the integer batch`);
  engine.scriptSession("",{action:"close"});
}});

Deno.test({name:"expected failure, issue 1074: a key of the window is keydown and keyup in one turn",ignore:!library,fn:async()=>{
  const engine=await loadHTML(library);
  if(!engine.scriptInfo().ops.includes("key")){console.log("this engine has no key action");return;}
  const t=start(engine,"for(const k of ['keydown','keyup'])addEventListener(k,e=>console.log(k+' '+e.code));");
  const k=engine.scriptSession("",{action:"key",session:t.session,mac:49}) as ScriptTurn;
  // Today one host key is a press: down and up in the same turn, so the page can not see a hold.
  assert.deepEqual(k.logs.filter(l=>l.startsWith("key")),["keydown Space","keyup Space"],stillGap("1074"));
  engine.scriptSession("",{action:"close"});
}});

Deno.test({name:"expected failure, issue 1075: Canvas 2D text ignores the font family",ignore:!library,fn:async()=>{
  const engine=await loadHTML(library);
  // The window's faces: Noto Sans, and Liberation Mono as the monospace face (as run_html.ts holds them).
  const fonts=new URL("../../../third_party/fonts/",import.meta.url).pathname;
  await loadFontFile(engine,fonts+"noto-sans/NotoSans-Regular.ttf","Noto Sans");
  await loadFontFile(engine,fonts+"liberation-mono/LiberationMono-Regular.ttf","Liberation Mono","bytes","mono");
  const t=start(engine,`const x=document.getElementById('c').getContext('2d');const w=f=>{x.font='20px '+f;return x.measureText('iiiiWWWW').width;};
    console.log('w '+w('monospace')+' '+w('sans-serif')+' '+w('"Liberation Mono"'));`);
  const line=t.logs.find(l=>l.startsWith("w "))??"";
  const [mono,sans,named]=line.slice(2).split(" ").map(Number);
  assert.ok(mono>0,line);
  // A monospaced face gives i and W one advance; the engine measures both families with one face.
  assert.equal(mono,sans,stillGap("1075"));
  assert.equal(named,sans,stillGap("1075"));
  engine.scriptSession("",{action:"close"});
}});
