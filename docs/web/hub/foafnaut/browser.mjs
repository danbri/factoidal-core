// The page only forwards input and shows frames. The worker runs the browser loop;
// Lean decides what every click, key and address means.
const canvas=document.querySelector('#page'),keys=document.querySelector('#keys'),note=document.querySelector('#note'),statsLine=document.querySelector('#stats');
// ?check=1 keeps the readback path with Lean's pixel checks; ?check=surface draws to the
// canvas and reads each frame back to check it; ?stats=1 shows the frame timings;
// ?layers=0 asks Lean for a whole frame at each scroll, with no two-layer view.
// The host browser's history follows the pages shown: the Hub address gets the page address
// after #, with no https:// and no default port. A # in it is %23, and a % before 23 or 25 is
// %25, so the fragment reads back exactly (2026-11-08).
const hashOf=url=>{
  let text=url;
  try{if(!url.startsWith('foafnaut:')){const u=new URL(url);text=(u.protocol==='https:'?'':u.protocol+'//')+u.host+u.pathname+u.search+u.hash;}}catch{}
  return text.replace(/%(?=2[35])/gi,'%25').replace(/#/g,'%23');
};
const addressOf=hash=>{
  const text=hash.replace(/%23/gi,'#').replace(/%25(?=2[35])/gi,'%');
  return !text||/^(foafnaut:|https?:\/\/)/.test(text)?text:'https://'+text;
};
const hubAddress=()=>location.hash.length>1?addressOf(location.hash.slice(1)):'';
const query=new URLSearchParams(location.search),checkParam=query.get('check'),showStats=query.get('stats')==='1'||checkParam!==null;
// A sandboxed guest has an opaque origin and can not start a worker. The loop then
// runs here; it needs no extra capability.
let worker;
try{worker=new Worker(new URL('./browser-worker.mjs',import.meta.url),{type:'module'});}
catch{worker=await inPageLoop();}
async function inPageLoop(){
  const {onThisThread}=await import('./browser-worker.mjs');
  const loop={onmessage:null,onerror:null};
  const receive=onThisThread(message=>loop.onmessage?.(message));
  loop.postMessage=receive;
  return loop;
}
const scale=()=>Math.max(1,Math.round(window.devicePixelRatio||1));
const size=()=>({width:Math.min(4096,Math.round(innerWidth*scale())),height:Math.min(4096,Math.round(innerHeight*scale())),scale:scale()});
const point=event=>({x:Math.round(event.clientX*scale()),y:Math.round(event.clientY*scale())});
const edits={Backspace:51,Delete:117,ArrowLeft:123,ArrowRight:124,ArrowUp:126,ArrowDown:125,Home:115,End:119,Enter:36,Escape:53};
// Modifier bits as the window library sends them: 1 Shift, 2 Command, 4 Option.
const modifiers=event=>(event.shiftKey?1:0)|(event.metaKey?2:0)|(event.altKey?4:0);
// Input carries the time it happened, in epoch milliseconds, which both threads can read.
const now=()=>performance.timeOrigin+performance.now();
const send=message=>worker.postMessage(message.type==='start'||message.type==='hello'?message:{...message,t:now()});
window.foafnautThread=worker instanceof Worker?'worker':'page';
let focused=false,moved=undefined;
// Lean's key table for a host with no menu (WebHistory.keyTable): Command on a Mac, Control elsewhere.
const mac=/Mac|iPhone|iPad/.test(navigator.platform||navigator.userAgent);
let keyTable=[];
worker.onmessage=({data})=>{
  if(data.type==='caps')return begin(data.surface);
  if(data.type==='frame'){
    note.hidden=true;
    if(data.rgba){
      canvas.width=data.width;canvas.height=data.height;
      canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(data.rgba),data.width,data.height),0,0);
    }
    document.title=data.title?`foafnaut - ${data.title}`:'foafnaut';
    const latency=data.inputAt===undefined?undefined:Math.round(now()-data.inputAt);
    window.foafnautFrame={...data.stats,inputToFrameMs:latency};
    if(statsLine&&showStats){
      const s=window.foafnautFrame;
      statsLine.hidden=false;
      statsLine.textContent=`${s.path} layout ${s.layoutMs} ms, draw ${s.drawMs} ms, total ${s.totalMs} ms`+(s.leanRenders===undefined?'':`, Lean renders ${s.leanRenders}`)+
        (latency===undefined?'':`, input to frame ${latency} ms`)+(s.pixelHash?`, pixels ${s.pixelHash}`:'');
    }
  }
  if(data.type==='location'){
    const want=location.pathname+location.search+(data.home?'':'#'+hashOf(data.url));
    if(want!==location.pathname+location.search+location.hash){
      if(data.push&&!fromHost)history.pushState(null,'',want);else history.replaceState(null,'',want);
    }
    fromHost=false;
  }
  if(data.type==='keys')keyTable=data.table;
  // When each loading step ended (epoch ms): the engine compiled and started, the font, the page, the first frame.
  if(data.type==='phases')window.foafnautPhases=data.phases;
  // Copy and cut in the address bar: Lean chose the text; the key press still counts as a user action.
  if(data.type==='clipboard')navigator.clipboard?.writeText(data.text).catch(()=>{note.hidden=false;note.textContent='The browser did not allow writing to the clipboard.';});
  if(data.type==='focus'){focused=data.focused;if(focused)keys.focus({preventScroll:true});else keys.blur();}
  // A link to another site opens in a host tab. The worker answers after the tap has ended,
  // so a browser that only opens tabs during a tap (iPhone Safari) blocks window.open; the
  // note then offers the address as a link, and tapping that is a tap of its own.
  if(data.type==='open'){
    const opened=window.open(data.url,'_blank');
    if(opened)opened.opener=null;
    else{
      const link=document.createElement('a');link.href=data.url;link.target='_blank';link.rel='noopener';
      link.textContent=data.url;link.style.cssText='color:#00e;word-break:break-all';
      note.replaceChildren('Open in a new tab: ',link);note.hidden=false;
      const hide=()=>{note.hidden=true;};link.addEventListener('click',()=>setTimeout(hide,0));
      clearTimeout(note.hideTimer);note.hideTimer=setTimeout(hide,10000);
    }
  }
  // The page is at its top or bottom: a fling stops there (iOS stops a fling at the edge).
  if(data.type==='edge')fling.edge(data.direction);
  if(data.type==='error'){note.hidden=false;note.textContent=data.error;}
};
worker.onerror=event=>{note.hidden=false;note.textContent='The browser worker failed: '+event.message;};
// A canvas can be handed to the worker once, so the worker says first whether it can draw
// to an OffscreenCanvas with WebGPU. If not, or with ?check=1, the worker reads each frame
// back and the page paints it with putImageData.
function begin(surface){
  const options={...size(),page:query.get('page'),...(hubAddress()?{address:hubAddress()}:{}),check:checkParam==='1'||checkParam==='surface',stats:showStats,platform:mac?'mac':'other',...(query.get('layers')==='0'?{layers:false}:{})};
  if(surface&&checkParam!=='1'){
    const offscreen=canvas.transferControlToOffscreen();
    window.foafnautSurface=true;
    worker.postMessage({type:'start',...options,canvas:offscreen},[offscreen]);
  }else{window.foafnautSurface=false;send({type:'start',...options});}
}
const canTransfer=worker instanceof Worker&&typeof canvas.transferControlToOffscreen==='function'&&typeof OffscreenCanvas==='function';
if(canTransfer)send({type:'hello',page:query.get('page')});else begin(false);
addEventListener('resize',()=>{fling.stop();send({type:'resize',...size()});});
// Back and forward in the host browser: the engine shows that address, not as a new entry.
let fromHost=false;
addEventListener('popstate',()=>{fling.stop();fromHost=true;send({type:'visit',address:hubAddress()||new URL('pages/index.html',location.href).href});});
// Keep focus where the loop puts it: the press must not move it back to the page.
canvas.addEventListener('mousedown',event=>event.preventDefault());
// A long press or a right click is the inner browser's, not the outer page's menu; a touch
// drag never scrolls or bounces the outer page (iOS ignores overscroll-behavior on body).
canvas.addEventListener('contextmenu',event=>event.preventDefault());
for(const name of ['touchstart','touchmove'])canvas.addEventListener(name,event=>{if(event.cancelable)event.preventDefault();},{passive:false});
addEventListener('selectstart',event=>{if(event.target!==keys)event.preventDefault();});
// Two fingers on a touch screen are a pinch: Lean's text zoom, as Ctrl+wheel is on a
// trackpad. The page sends the ratio of finger distances since the pinch began, and the
// worker sets the zoom from it. A pinch ends any press, without a click.
const touches=new Map();let pinch;
const tapSlop=10;
const fingerGap=()=>{const [a,b]=[...touches.values()];return Math.hypot(a.x-b.x,a.y-b.y);};
// A finger whose lift never reached the canvas (the app left mid-touch, a system gesture)
// would stay in touches, and every later one-finger tap would start a pinch and click
// nothing. The primary pointer begins a new gesture, so it clears whatever is left.
// Momentum after a touch drag (owner, 2026-11-08), as iOS UIScrollView: the release velocity
// is taken from the moves of the last 100 ms, and the page keeps scrolling at a velocity that
// falls by the factor 0.998 each millisecond (UIScrollView.DecelerationRate.normal). Each step
// is an ordinary scroll message, so inside a band it moves only the composite: no Lean render.
// A new touch stops it, as does the page's top or bottom (the worker says `edge`), a wheel or
// key scroll and a pinch. A tap that stops a fling does nothing else, as on iOS. Wheel and
// trackpad scrolls have the system's own momentum and get none here.
const fling=(()=>{
  const rate=0.998,lnRate=Math.log(rate),windowMs=100,minStart=0.15,minSpeed=0.02,maxSpeed=8;
  let velocity=0,last=0,carry=0,frameId=0;
  const step=at=>{
    const dt=Math.min(64,Math.max(0,at-last));last=at;
    // The exact distance over dt at an exponentially falling velocity (frame rate independent).
    const decay=Math.pow(rate,dt),distance=velocity*(decay-1)/lnRate;
    velocity*=decay;carry+=distance*scale();
    const whole=Math.trunc(carry);
    if(whole){carry-=whole;send({type:'scroll',amount:whole,fling:true});}
    if(Math.abs(velocity)<minSpeed){stop();return;}
    frameId=requestAnimationFrame(step);
  };
  function stop(){if(frameId)cancelAnimationFrame(frameId);frameId=0;velocity=0;carry=0;}
  return {
    stop,
    /** The page reached its end in this direction: a fling that way stops (an older one may not). */
    edge(direction){if(frameId&&Math.sign(velocity)===direction)stop();},
    get active(){return frameId!==0;},
    /** Start from the moves of a drag ({t,y} in ms and CSS px), ending at the lift (t,y). */
    start(samples,t,y){
      stop();
      const recent=samples.filter(s=>t-s.t<=windowMs);
      if(!recent.length)return false;
      const first=recent[0],span=t-first.t;
      if(span<8)return false;
      // Scroll rows per ms: a finger moving up scrolls the page down.
      const v=(first.y-y)/span;
      if(Math.abs(v)<minStart)return false;
      velocity=Math.sign(v)*Math.min(maxSpeed,Math.abs(v));
      last=performance.now();frameId=requestAnimationFrame(step);
      return true;
    },
    constants:{rate,windowMs,minStart,minSpeed,maxSpeed},
  };
})();
window.foafnautFling=fling;
const forgetTouches=()=>{touches.clear();if(pinch){send({type:'pinch',phase:'end'});pinch=undefined;}};
addEventListener('visibilitychange',()=>{if(document.hidden){forgetTouches();moved=undefined;fling.stop();}});
canvas.addEventListener('pointerdown',event=>{
  // A touch during a fling stops it and is not a press: a tap then clicks nothing.
  const stopper=fling.active;fling.stop();
  if(event.isPrimary)forgetTouches();
  if(event.pointerType==='touch')touches.set(event.pointerId,{x:event.clientX,y:event.clientY});
  if(touches.size===2&&!pinch){
    if(moved&&!moved.stopper)send({type:'release',scrolled:true,...point(event)});
    moved=undefined;pinch={gap:Math.max(1,fingerGap())};send({type:'pinch',phase:'start'});return;
  }
  if(pinch)return;
  moved={y:event.clientY,startX:event.clientX,startY:event.clientY,scrolled:false,stopper,samples:[{t:event.timeStamp,y:event.clientY}]};
  if(!stopper)send({type:'press',...point(event)});
});
canvas.addEventListener('pointermove',event=>{
  if(touches.has(event.pointerId))touches.set(event.pointerId,{x:event.clientX,y:event.clientY});
  if(pinch){if(touches.size===2)send({type:'pinch',phase:'move',ratio:fingerGap()/pinch.gap});return;}
  // A finger drifts a few pixels during a tap. Until it has gone further than the
  // tap slop, the touch is still a tap: no scroll and no drag.
  const touch=event.pointerType==='touch';
  if(moved&&touch&&!moved.scrolled&&Math.hypot(event.clientX-moved.startX,event.clientY-moved.startY)<tapSlop)return;
  if(moved&&event.buttons&&!moved.stopper)send({type:'move',...point(event)});
  if(!moved||!touch)return;
  // Where the finger was and when, for the velocity at the lift (the last 100 ms are kept).
  moved.samples.push({t:event.timeStamp,y:event.clientY});
  while(moved.samples.length>2&&event.timeStamp-moved.samples[0].t>200)moved.samples.shift();
  const step=moved.y-event.clientY;if(Math.abs(step)<2)return;
  moved={...moved,y:event.clientY,scrolled:true};send({type:'scroll',amount:step*scale()});
});
const lift=event=>{
  touches.delete(event.pointerId);
  if(pinch){if(touches.size<2){send({type:'pinch',phase:'end'});pinch=undefined;}return;}
  if(moved&&event.type==='pointerup'){
    if(!moved.stopper)send({type:'release',scrolled:moved.scrolled,...point(event)});
    // A drag of a finger flings; a tap (no scroll) and a mouse drag do not.
    if(moved.scrolled&&event.pointerType==='touch'){
      const rest=moved.y-event.clientY;
      if(Math.abs(rest)>=1)send({type:'scroll',amount:rest*scale()});
      fling.start(moved.samples,event.timeStamp,event.clientY);
    }
  }
  moved=undefined;
};
canvas.addEventListener('pointerup',lift);
canvas.addEventListener('pointercancel',lift);
// Safari's own pinch would zoom the whole page, address bar included.
for(const name of ['gesturestart','gesturechange'])addEventListener(name,event=>event.preventDefault(),{passive:false});
// Ctrl+wheel is a trackpad pinch: Lean's text zoom, not the host browser's page zoom.
addEventListener('wheel',event=>{event.preventDefault();fling.stop();
  if(event.ctrlKey){if(event.deltaY)send({type:'command',command:event.deltaY<0?1:2});return;}
  send({type:'scroll',amount:event.deltaY*scale()});},{passive:false});
// Cmd/Ctrl with = + - _ 0 are the same zoom commands as the desktop View menu (1 in, 2 out,
// 3 actual size). Without this the host browser zooms the whole page, chrome included.
const zoomKeys={'=':1,'+':1,'-':2,'_':2,'0':3};
keys.addEventListener('input',()=>{for(const text of keys.value)send({type:'text',text});keys.value='';});
addEventListener('keydown',event=>{
  fling.stop();
  if((event.metaKey||event.ctrlKey)&&!event.altKey&&zoomKeys[event.key]){event.preventDefault();send({type:'command',command:zoomKeys[event.key]});return;}
  if(event.altKey&&event.key==='ArrowLeft'){event.preventDefault();send({type:'command',command:6});return;}
  if(event.altKey&&event.key==='ArrowRight'){event.preventDefault();send({type:'command',command:7});return;}
  // A key of Lean's table: the page keeps it from the host browser. Paste is left to the
  // paste event below, which carries the clipboard text.
  const modifier=(event.shiftKey?'shift+':'')+(mac?(event.metaKey?'command':''):(event.ctrlKey?'control':''));
  const entry=(mac?event.metaKey:event.ctrlKey)&&!event.altKey?keyTable.find(row=>row.modifier===modifier&&row.key.toLowerCase()===event.key.toLowerCase()):undefined;
  if(entry&&entry.command!==14){event.preventDefault();send({type:'command',command:entry.command});return;}
  if(focused&&edits[event.key]){event.preventDefault();send({type:'key',key:edits[event.key],modifiers:modifiers(event)});return;}
  if((event.metaKey||event.ctrlKey)&&event.key==='u'){event.preventDefault();send({type:'command',command:13});return;}
  if(!focused&&event.key==='/'){event.preventDefault();send({type:'command',command:9});return;}
  if(!focused&&event.key==='ArrowDown')send({type:'scroll',amount:80*scale()});
  if(!focused&&event.key==='ArrowUp')send({type:'scroll',amount:-80*scale()});
  if(!focused&&(event.key===' '||event.key==='PageDown'))send({type:'scroll',amount:innerHeight*0.8*scale()});
  if(!focused&&event.key==='PageUp')send({type:'scroll',amount:-innerHeight*0.8*scale()});
});
// Paste: the clipboard text goes to Lean, which puts it in the address bar (issue 1268).
addEventListener('paste',event=>{
  const text=event.clipboardData?.getData('text/plain');
  if(text===undefined)return;
  event.preventDefault();send({type:'paste',text});
});
