// The page only forwards input and shows frames. The worker runs the browser loop;
// Lean decides what every click, key and address means.
const canvas=document.querySelector('#page'),keys=document.querySelector('#keys'),note=document.querySelector('#note');
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
const edits={Backspace:51,Delete:117,ArrowLeft:123,ArrowRight:124,Home:115,End:119,Enter:36,Escape:53};
const send=message=>worker.postMessage(message);
window.foafnautThread=worker instanceof Worker?'worker':'page';
let focused=false,moved=undefined;
worker.onmessage=({data})=>{
  if(data.type==='frame'){
    note.hidden=true;canvas.width=data.width;canvas.height=data.height;
    canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(data.rgba),data.width,data.height),0,0);
    document.title=data.title?`foafnaut - ${data.title}`:'foafnaut';window.foafnautFrame=data.stats;
  }
  if(data.type==='focus'){focused=data.focused;if(focused)keys.focus({preventScroll:true});else keys.blur();}
  if(data.type==='open'&&!window.open(data.url,'_blank','noopener')){note.hidden=false;note.textContent=`Open this address in your browser: ${data.url}`;}
  if(data.type==='error'){note.hidden=false;note.textContent=data.error;}
};
worker.onerror=event=>{note.hidden=false;note.textContent='The browser worker failed: '+event.message;};
send({type:'start',...size(),page:new URLSearchParams(location.search).get('page')});
addEventListener('resize',()=>send({type:'resize',...size()}));
// Keep focus where the loop puts it: the press must not move it back to the page.
canvas.addEventListener('mousedown',event=>event.preventDefault());
canvas.addEventListener('pointerdown',event=>{moved={y:event.clientY,scrolled:false};send({type:'press',...point(event)});});
canvas.addEventListener('pointermove',event=>{
  if(!moved||event.pointerType!=='touch')return;
  const step=moved.y-event.clientY;if(Math.abs(step)<2)return;
  moved={y:event.clientY,scrolled:true};send({type:'scroll',amount:step*scale()});
});
canvas.addEventListener('pointerup',event=>{if(moved&&!moved.scrolled)send({type:'release',...point(event)});moved=undefined;});
addEventListener('wheel',event=>{event.preventDefault();send({type:'scroll',amount:event.deltaY*scale()});},{passive:false});
keys.addEventListener('input',()=>{for(const text of keys.value)send({type:'text',text});keys.value='';});
addEventListener('keydown',event=>{
  if(event.altKey&&event.key==='ArrowLeft'){event.preventDefault();send({type:'command',command:6});return;}
  if(event.altKey&&event.key==='ArrowRight'){event.preventDefault();send({type:'command',command:7});return;}
  if(focused&&edits[event.key]){event.preventDefault();send({type:'key',key:edits[event.key]});return;}
  if((event.metaKey||event.ctrlKey)&&event.key==='u'){event.preventDefault();send({type:'command',command:13});return;}
  if(!focused&&event.key==='/'){event.preventDefault();send({type:'command',command:9});return;}
  if(!focused&&event.key==='ArrowDown')send({type:'scroll',amount:80*scale()});
  if(!focused&&event.key==='ArrowUp')send({type:'scroll',amount:-80*scale()});
  if(!focused&&(event.key===' '||event.key==='PageDown'))send({type:'scroll',amount:innerHeight*0.8*scale()});
  if(!focused&&event.key==='PageUp')send({type:'scroll',amount:-innerHeight*0.8*scale()});
});
