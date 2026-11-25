// Particle Rex (pages/particle-rex.html, the owner's one-button canvas game, issue 1031):
// a cost ratchet for the canvas path it showed slow, and expected failures for the gaps it
// showed. When an engine change closes a gap, its test fails: change the assertion to the
// correct behaviour and close the issue in the same landing.
// - Canvas batches with fractional numbers: a frame of the game draws about 400 to 2,000
//   rects at fractional positions. The prelude sent every batch as text, and BubblePopJS
//   prints a fraction in about 20 microseconds; a fractional batch now goes as binary
//   numbers. The ratchet: 4,000 fillRect calls at fractional positions cost less than 3 times
//   the same calls at integer positions (release e4445d14 of main: 64.8 ms and 356.0 ms, ratio 5.49, Linux VM).
// - Issue 1074 (closed): a key of the window reached the page as keydown and keyup at once,
//   so a held key was a tap (the game's "hold = higher"). Now: down, repeats, up.
// - Issue 1077 (closed): after a load the address bar kept the keyboard focus. Now the
//   committed page takes it (WebShell.focusOnCommit).
// - Issue 1075 (closed): Canvas 2D text ignored the font family. Now "monospace", the
//   monospace face's name and a list that ends in a monospace name draw with that face.
// BubblePopJS sessions on the native library. Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const candidates=[Deno.env.get("FOAFNAUT_NATIVE_ENGINE")??"",
  new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname,
  new URL("./.build/web-render/engines/libweb-render.so",import.meta.url).pathname];
const library=candidates.find(p=>p&&exists(p))??"";
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

Deno.test({name:"issue 1074: a held key is keydown, repeated keydowns, then one keyup",ignore:!library,fn:async()=>{
  const engine=await loadHTML(library);
  if(!engine.scriptInfo().ops.includes("key"))throw new Error("this engine has no key action");
  assert.equal((engine.scriptInfo() as {keyPhases?:boolean}).keyPhases,true,"the engine takes key phases (issue 1074)");
  const t=start(engine,"for(const k of ['keydown','keyup'])addEventListener(k,e=>console.log(k+' '+e.code+' '+e.repeat+' '+e.shiftKey));");
  const key=(request:Record<string,unknown>)=>(engine.scriptSession("",{action:"key",session:t.session,...request}) as ScriptTurn).logs.filter(l=>l.startsWith("key"));
  // Space held: a down, an auto-repeat, then the release, each in its own turn.
  assert.deepEqual(key({mac:49,phase:"down"}),["keydown Space false false"]);
  assert.deepEqual(key({mac:49,phase:"down"}),["keydown Space true false"]);
  assert.deepEqual(key({mac:49,phase:"up"}),["keyup Space false false"]);
  // A character key (its text, as the window gives it), held with Shift: Shift goes down first
  // and up after the key.
  assert.deepEqual(key({text:"W",modifiers:1,phase:"down"}),["keydown ShiftLeft false true","keydown KeyW false true"]);
  assert.deepEqual(key({text:"W",modifiers:1,phase:"down"}),["keydown KeyW true true"]);
  assert.deepEqual(key({text:"W",modifiers:1,phase:"up"}),["keyup KeyW false true","keyup ShiftLeft false false"]);
  // With no phase (an older window): a whole press, as before.
  assert.deepEqual(key({mac:126}),["keydown ArrowUp false false","keyup ArrowUp false false"]);
  // A held character key in a text field types at its down and at each repeat, not at its up.
  const f=engine.scriptSession(`<!doctype html><html><body><input id=i><script>const i=document.getElementById('i');i.focus();
    addEventListener('keyup',()=>console.log('value '+i.value));addEventListener('keydown',()=>console.log('down '+i.value));</script></body></html>`,
    {action:"start",url,resources:[],width:800,height:500,layout:{url},engine:"bubblepop",instructionsPerMs:1e12}) as ScriptTurn;
  const typed=(phase:string)=>(engine.scriptSession("",{action:"key",session:f.session,text:"w",phase}) as ScriptTurn).logs;
  typed("down");typed("down");
  assert.deepEqual(typed("up"),["value ww"]);
  engine.scriptSession("",{action:"close"});
}});

Deno.test({name:"issue 1075: Canvas 2D text takes its face from the family list",ignore:!library,fn:async()=>{
  const engine=await loadHTML(library);
  // The window's faces: Noto Sans, and Liberation Mono as the monospace face (as run_html.ts holds them).
  const fonts=new URL("../../../third_party/fonts/",import.meta.url).pathname;
  await loadFontFile(engine,fonts+"noto-sans/NotoSans-Regular.ttf","Noto Sans");
  await loadFontFile(engine,fonts+"liberation-mono/LiberationMono-Regular.ttf","Liberation Mono","bytes","mono");
  const t=start(engine,`const x=document.getElementById('c').getContext('2d');const w=(f,s)=>{x.font='20px '+f;return x.measureText(s).width;};
    for(const f of ['monospace','sans-serif','"Liberation Mono"','Silkscreen, "Courier New", monospace'])console.log('w '+w(f,'iiii')+' '+w(f,'WWWW'));`);
  const widths=t.logs.filter(l=>l.startsWith("w ")).map(l=>l.slice(2).split(" ").map(Number));
  assert.equal(widths.length,4,t.logs.join("\n"));
  const [mono,sans,named,list]=widths;
  // Liberation Mono gives i and W one advance (0.6 em: 12 px at 20 px, 48 px for four).
  for(const [i,w] of [mono,named,list])assert.ok(Math.abs(i-w)<0.01&&Math.abs(i-48)<0.5,`monospace face: ${i} ${w}`);
  // Noto Sans: i is narrower than W.
  assert.ok(sans[0]<sans[1]/2,`sans-serif: ${sans}`);
  engine.scriptSession("",{action:"close"});
}});

Deno.test({name:"issue 1077: a page that commits takes the keyboard focus from the address bar",ignore:!library,fn:async()=>{
  const engine=await loadHTML(library);
  const focus=(url:string,newTab:boolean,typed:boolean)=>engine.shellCommitFocus({url,newTab,focused:true,typed});
  // Before the change the engine had no such decision and the window kept the address bar focused.
  assert.equal(focus("file:///pages/particle-rex.html",false,false),"page");
  // The person typed in the address bar during the load: the bar keeps the focus.
  assert.equal(focus("https://example.org/",false,true),"address");
  // A new tab page and about:blank: the address bar takes the focus, to type an address.
  assert.equal(focus("file:///pages/newtab.html",true,false),"address");
  assert.equal(focus("about:blank",false,false),"address");
}});
