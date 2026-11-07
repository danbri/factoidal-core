// The page only forwards input and shows frames. The worker runs the browser loop;
// Lean decides what every click, key and address means.
const canvas=document.querySelector('#page'),keys=document.querySelector('#keys'),note=document.querySelector('#note'),statsLine=document.querySelector('#stats');
// ?check=1 keeps the readback path with Lean's pixel checks; ?check=surface draws to the
// canvas and reads each frame back to check it; ?stats=1 shows the frame timings.
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
      statsLine.textContent=`${s.path} layout ${s.layoutMs} ms, draw ${s.drawMs} ms, total ${s.totalMs} ms`+
        (latency===undefined?'':`, input to frame ${latency} ms`)+(s.pixelHash?`, pixels ${s.pixelHash}`:'');
    }
  }
  if(data.type==='keys')keyTable=data.table;
  // Copy and cut in the address bar: Lean chose the text; the key press still counts as a user action.
  if(data.type==='clipboard')navigator.clipboard?.writeText(data.text).catch(()=>{note.hidden=false;note.textContent='The browser did not allow writing to the clipboard.';});
  if(data.type==='focus'){focused=data.focused;if(focused)keys.focus({preventScroll:true});else keys.blur();}
  if(data.type==='open'&&!window.open(data.url,'_blank','noopener')){note.hidden=false;note.textContent=`Open this address in your browser: ${data.url}`;}
  if(data.type==='error'){note.hidden=false;note.textContent=data.error;}
  if(data.type==='note'){note.hidden=false;note.textContent=data.text;setTimeout(()=>{note.hidden=true;},6000);}
};
worker.onerror=event=>{note.hidden=false;note.textContent='The browser worker failed: '+event.message;};
// A canvas can be handed to the worker once, so the worker says first whether it can draw
// to an OffscreenCanvas with WebGPU. If not, or with ?check=1, the worker reads each frame
// back and the page paints it with putImageData.
function begin(surface){
  const options={...size(),page:query.get('page'),check:checkParam==='1'||checkParam==='surface',stats:showStats,platform:mac?'mac':'other'};
  if(surface&&checkParam!=='1'){
    const offscreen=canvas.transferControlToOffscreen();
    window.foafnautSurface=true;
    worker.postMessage({type:'start',...options,canvas:offscreen},[offscreen]);
  }else{window.foafnautSurface=false;send({type:'start',...options});}
}
const canTransfer=worker instanceof Worker&&typeof canvas.transferControlToOffscreen==='function'&&typeof OffscreenCanvas==='function';
if(canTransfer)send({type:'hello'});else begin(false);
addEventListener('resize',()=>send({type:'resize',...size()}));
// Keep focus where the loop puts it: the press must not move it back to the page.
canvas.addEventListener('mousedown',event=>event.preventDefault());
canvas.addEventListener('pointerdown',event=>{moved={y:event.clientY,scrolled:false};send({type:'press',...point(event)});});
canvas.addEventListener('pointermove',event=>{
  if(moved&&event.buttons)send({type:'move',...point(event)});
  if(!moved||event.pointerType!=='touch')return;
  const step=moved.y-event.clientY;if(Math.abs(step)<2)return;
  moved={y:event.clientY,scrolled:true};send({type:'scroll',amount:step*scale()});
});
canvas.addEventListener('pointerup',event=>{if(moved)send({type:'release',scrolled:moved.scrolled,...point(event)});moved=undefined;});
// Ctrl+wheel is a trackpad pinch: Lean's text zoom, not the host browser's page zoom.
addEventListener('wheel',event=>{event.preventDefault();
  if(event.ctrlKey){if(event.deltaY)send({type:'command',command:event.deltaY<0?1:2});return;}
  send({type:'scroll',amount:event.deltaY*scale()});},{passive:false});
// Cmd/Ctrl with = + - _ 0 are the same zoom commands as the desktop View menu (1 in, 2 out,
// 3 actual size). Without this the host browser zooms the whole page, chrome included.
const zoomKeys={'=':1,'+':1,'-':2,'_':2,'0':3};
keys.addEventListener('input',()=>{for(const text of keys.value)send({type:'text',text});keys.value='';});
addEventListener('keydown',event=>{
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
  // A key for the page's scripts (issue 1271): a character, or a key name of UI Events.
  if(!focused&&!event.metaKey&&!event.ctrlKey&&(event.key.length===1||/^(Enter|Escape|Backspace|Tab|Delete|Arrow(Up|Down|Left|Right)|Home|End|Page(Up|Down))$/.test(event.key)))send({type:'pagekey',key:event.key});
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
