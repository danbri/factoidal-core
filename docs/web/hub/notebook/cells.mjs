// Cell outputs drawn by the built-in engine, for the Hub's notebook cells (hub.njk observable-js).
// One helper, three modes, one engine for the whole page (../textnaut/engine.mjs: a worker that
// starts at the first cell that asks, so a page that never asks loads nothing):
//
//   render(htmlOrSvg, options)     BubblePopKit only: the page drawn into a canvas, no chrome, no scripts
//   foafnaut(urlOrHtml, options)   a Foafnaut view: scripts run on BubblePopJS, clicks go to the
//                                  page, and links are followed inside the cell (pages of this site)
//   textnaut(urlOrHtml, options)   Textnaut's text grid, with numbered links followed in the cell
//   sideBySide(input, options)     the same input drawn and as text, next to each other
//
// Each returns an element at once; it fills in when the engine answers. Under each output, the
// engine's timings for that cell: engine start (first cell only), prepare, scripts, layout, draw,
// cells, primitives, glyph runs, links. Every finished cell is also in `window.hubNotebookCells`.
// options: width (CSS px, default the cell's width up to 720), height (default 400; the content
// height up to maxHeight unless autoHeight: false), cols (Textnaut), scripts (foafnaut: true).
import * as engine from '../textnaut/engine.mjs';
import {createGridView,gridStyle} from '../textnaut/grid-view.mjs';

let serial=0;
// Work starts after the cell's output is in the page, so that it can take the cell's width.
const later=f=>setTimeout(f,0);
const records=(globalThis.hubNotebookCells??=[]);

function style(){
  if(document.getElementById('hub-notebook-style'))return;
  gridStyle();
  const s=document.createElement('style');s.id='hub-notebook-style';
  s.textContent=`
.nb-out{margin:4px 0;max-width:100%}
.nb-out canvas{display:block;max-width:100%;height:auto;background:#fff;border:1px solid #c9ced3;border-radius:3px}
.nb-out.nb-foafnaut canvas{cursor:default}
.nb-bar{display:flex;gap:6px;align-items:center;font:12px ui-monospace,monospace;margin:0 0 4px;flex-wrap:wrap}
.nb-bar button{font:inherit;padding:2px 8px;min-height:28px;cursor:pointer}
.nb-bar .nb-url{overflow-wrap:anywhere;opacity:.85}
.nb-time{font:12px ui-monospace,monospace;opacity:.75;margin:4px 0 0;overflow-wrap:anywhere}
.nb-note{font:12px ui-monospace,monospace;margin:4px 0 0;color:#a33}
.nb-side{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,300px),1fr));gap:12px;align-items:start}
.nb-side h4{margin:0 0 4px;font:600 12px system-ui,sans-serif;opacity:.8}
.nb-out .textnaut-grid{max-height:420px}
.nb-timings{font:12px ui-monospace,monospace;border-collapse:collapse}.nb-timings th,.nb-timings td{padding:2px 8px;border-bottom:1px solid #8884;text-align:right}
.nb-timings th:first-child,.nb-timings td:first-child,.nb-timings td:nth-child(2){text-align:left}`;
  document.head.append(s);
}

const ms=x=>x===undefined?undefined:`${Math.round(x*10)/10} ms`;
/** The timing line of one answer, in the order the work happens. */
export function timingText(out){
  const t=out.timing??{},c=out.counters??{},parts=[];
  if(t.engineMs!==undefined)parts.push(`engine start ${ms(t.engineMs)} + font ${ms(t.fontMs)} (first cell)`);
  if(t.prepareMs!==undefined)parts.push(`prepare ${ms(t.prepareMs)}`);
  if(t.scriptMs!==undefined)parts.push(`scripts ${ms(t.scriptMs)}, ${out.scripts?.turns??0} turns`);
  parts.push(`layout ${ms(t.layoutMs)}${c.layouts>1?` (${c.layouts} layouts)`:''}`);
  if(t.drawMs!==undefined)parts.push(`draw ${ms(t.drawMs)} (${out.drawing})`);
  if(t.cellsMs!==undefined)parts.push(`cells ${ms(t.cellsMs)}`);
  parts.push(`${c.primitives} primitives`,`${c.glyphRuns} glyph runs`,`${c.links} links`);
  if(c.rows!==undefined)parts.push(`${c.rows}×${c.cols} cells`);
  if(t.totalMs!==undefined)parts.push(`total ${ms(t.totalMs)}`);
  return parts.join(' · ');
}

function frameOf(kind){
  style();
  const box=document.createElement('div');
  box.className=`nb-out nb-${kind}`;box.dataset.state='loading';
  const time=document.createElement('p');time.className='nb-time';
  time.textContent=engine.engineState().started?'Laying out…':'Starting the built-in engine…';
  return {box,time};
}
function finish(box,time,kind,out,cell){
  time.textContent=timingText(out);
  box.dataset.state='done';
  const record={cell,kind,url:out.url,title:out.title,timing:out.timing,counters:out.counters,drawing:out.drawing,at:performance.now()};
  records.push(record);
  box.dispatchEvent(new CustomEvent('nb-done',{detail:record}));
  globalThis.dispatchEvent?.(new CustomEvent('hub-notebook-cell',{detail:record}));
}
function fail(box,time,error){
  box.dataset.state='error';
  time.textContent='';
  const note=document.createElement('p');note.className='nb-note';note.textContent=String(error?.message??error);
  box.append(note);
  records.push({kind:box.className,error:note.textContent,at:performance.now()});
  box.dispatchEvent(new CustomEvent('nb-done',{detail:{error:note.textContent}}));
}
/** Pixels of an answer into a canvas: device pixels, shown at CSS size. */
function paint(canvas,out){
  canvas.width=out.width;canvas.height=out.height;
  canvas.style.width=`${out.width/out.scale}px`;
  if(out.rgba)canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(out.rgba.buffer??out.rgba),out.width,out.height),0,0);
}
const widthFor=(box,options)=>options.width??Math.max(200,Math.min(720,Math.floor((box.isConnected?box.clientWidth:0)||640)));
const scaleNow=()=>Math.max(1,Math.min(2,globalThis.devicePixelRatio||1));
const point=(canvas,event)=>{const r=canvas.getBoundingClientRect();return {x:(event.clientX-r.left)*(canvas.width/canvas.scale)/r.width||0,y:(event.clientY-r.top)*(canvas.height/canvas.scale)/r.height||0};};
const inputLabel=input=>typeof input==='string'&&!input.trim().startsWith('<')?input:input?.url??'(HTML of this cell)';

/** BubblePopKit only: `htmlOrSvg` laid out and drawn into a canvas, no chrome, no scripts. */
export function render(htmlOrSvg,options={}){
  const {box,time}=frameOf('render'),id=`nb${++serial}`,canvas=document.createElement('canvas');
  canvas.setAttribute('role','img');canvas.setAttribute('aria-label','A page drawn by the built-in engine');
  box.append(canvas,time);
  later(async()=>{
    try{
      const out=await engine.open(id,htmlOrSvg,{width:widthFor(box,options),height:options.height??400,autoHeight:options.autoHeight,maxHeight:options.maxHeight,
        scale:scaleNow(),base:location.href,scripts:false});
      canvas.scale=out.scale;paint(canvas,out);
      const text=out.title||'';if(text)canvas.setAttribute('aria-label',`${text}, drawn by the built-in engine`);
      finish(box,time,'render',out,id);
    }catch(error){fail(box,time,error);}
  });
  return box;
}

/** A Foafnaut view in the cell: scripts on BubblePopJS, links followed here (pages of this site). */
export function foafnaut(urlOrHtml,options={}){
  const {box,time}=frameOf('foafnaut'),id=`nb${++serial}`,canvas=document.createElement('canvas');
  const bar=document.createElement('div');bar.className='nb-bar';
  const back=document.createElement('button');back.type='button';back.textContent='Back';back.disabled=true;
  const where=document.createElement('span');where.className='nb-url';where.textContent=inputLabel(urlOrHtml);
  bar.append(back,where);
  canvas.setAttribute('role','img');canvas.setAttribute('aria-label','A Foafnaut view drawn by the built-in engine');canvas.tabIndex=0;
  box.append(bar,canvas,time);
  const history=[];let links=[],busy=false;
  const show=(out,cell=id)=>{canvas.scale=out.scale;paint(canvas,out);links=out.links??[];box.nbLinks=links;where.textContent=out.given==='html'&&history.length<2?'(HTML of this cell)':out.url;finish(box,time,'foafnaut',out,cell);};
  async function go(input,push){
    busy=true;box.dataset.state='loading';time.textContent='Laying out…';
    try{
      const out=await engine.open(id,input,{width:widthFor(box,options),height:options.height??400,autoHeight:options.autoHeight,maxHeight:options.maxHeight,
        scale:scaleNow(),base:location.href,scripts:options.scripts!==false});
      if(push)history.push(input);back.disabled=history.length<2;
      show(out);
    }catch(error){fail(box,time,error);}finally{busy=false;}
  }
  canvas.addEventListener('mousemove',event=>{const p=point(canvas,event);canvas.style.cursor=links.some(l=>p.x>=l.x&&p.x<=l.x+l.w&&p.y>=l.y&&p.y<=l.y+l.h)?'pointer':'default';});
  canvas.addEventListener('click',async event=>{
    if(busy)return;
    const p=point(canvas,event);
    try{
      const answer=await engine.click(id,p.x,p.y);
      if(answer.changed){show(answer.frame);return;}
      const link=answer.link;if(!link)return;
      const url=new URL(link.url);
      if(url.origin!==location.origin){time.textContent=`${link.url}: another site, not followed (the Hub has no proxy).`;return;}
      if(url.hash&&url.href.split('#')[0]===(history[history.length-1]?.url??'').split('#')[0])return;
      go({url:url.href},true);
    }catch(error){fail(box,time,error);}
  });
  back.addEventListener('click',()=>{if(history.length<2)return;history.pop();go(history[history.length-1],false);});
  later(()=>go(typeof urlOrHtml==='string'&&!urlOrHtml.trim().startsWith('<')?{url:new URL(urlOrHtml,location.href).href}:urlOrHtml,true));
  return box;
}

/** Textnaut's text grid of `urlOrHtml`, with numbered links followed in the cell. */
export function textnaut(urlOrHtml,options={}){
  const {box,time}=frameOf('textnaut'),id=`nb${++serial}`;
  const bar=document.createElement('div');bar.className='nb-bar';
  const back=document.createElement('button');back.type='button';back.textContent='Back';back.disabled=true;
  const where=document.createElement('span');where.className='nb-url';where.textContent=inputLabel(urlOrHtml);
  bar.append(back,where);
  const holder=document.createElement('div');
  box.append(bar,holder,time);
  const history=[];
  const view=createGridView(holder,{follow:url=>{
    if(new URL(url).origin!==location.origin){time.textContent=`${url}: another site, not followed (the Hub has no proxy).`;return;}
    go({url},true);},back:goBack});
  const cols=()=>options.cols??Math.max(30,Math.min(100,Math.floor(((box.isConnected?box.clientWidth:0)||640)/8.6)-2));
  async function go(input,push){
    box.dataset.state='loading';time.textContent=engine.engineState().started?'Laying out…':'Starting the built-in engine…';
    try{
      const out=await engine.textGrid(id,input,{cols:cols(),base:location.href,scripts:options.scripts!==false,height:options.height});
      if(push)history.push(input);back.disabled=history.length<2;
      view.show(out.grid);
      where.textContent=out.given==='html'&&history.length<2?'(HTML of this cell)':out.url;
      finish(box,time,'textnaut',out,id);
    }catch(error){fail(box,time,error);}
  }
  function goBack(){if(history.length<2)return;history.pop();go(history[history.length-1],false);}
  back.addEventListener('click',goBack);
  later(()=>go(urlOrHtml,true));
  return box;
}

/** The same input drawn by BubblePopKit and as Textnaut's grid, side by side. */
export function sideBySide(input,options={}){
  style();
  const box=document.createElement('div');box.className='nb-side';
  const left=document.createElement('div'),right=document.createElement('div');
  const h1=document.createElement('h4');h1.textContent='Drawn (render)';const h2=document.createElement('h4');h2.textContent='As text (textnaut)';
  left.append(h1,render(input,{width:options.width??360,...options}));
  right.append(h2,textnaut(input,{cols:options.cols??44,...options}));
  box.append(left,right);
  return box;
}

/** The finished cells' timings so far (also `window.hubNotebookCells`). */
export const timings=()=>records.slice();

/** A table of every finished cell's timings, which grows as cells finish. */
export function timingTable(){
  style();
  const table=document.createElement('table');table.className='nb-timings';
  const head=table.createTHead().insertRow();
  for(const h of ['cell','mode','engine start','prepare','scripts','layout','draw','cells','primitives','links','total'])
    head.append(Object.assign(document.createElement('th'),{textContent:h}));
  const body=table.createTBody();
  const add=r=>{
    if(r.error)return;
    const t=r.timing??{},c=r.counters??{},row=body.insertRow();
    for(const v of [r.cell,r.kind,ms(t.engineMs),ms(t.prepareMs),ms(t.scriptMs),ms(t.layoutMs),t.drawMs===undefined?undefined:`${ms(t.drawMs)} ${r.drawing}`,ms(t.cellsMs),c.primitives,c.links,ms(t.totalMs)])
      row.insertCell().textContent=v??'';
  };
  records.forEach(add);
  globalThis.addEventListener?.('hub-notebook-cell',event=>add(event.detail));
  return table;
}
