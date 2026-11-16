// The Hub's Textnaut page: an address (a page of this site) or typed HTML, laid out by the shared
// engine (engine.mjs) and shown as Textnaut's grid (grid-view.mjs). The page's history is a list
// of what was shown; Back returns to the one before. ?page=NAME.html opens a Foafnaut demo page,
// #ADDRESS opens an address of this site or of a Hub copy (copies.mjs); with neither, the start page.
import * as engine from './engine.mjs';
import {createGridView,gridStyle} from './grid-view.mjs';
import {copyOf} from '../foafnaut/copies.mjs';

gridStyle();
const $=id=>document.getElementById(id);
const address=$('address'),stats=$('stats'),note=$('note'),cols=$('cols'),engineChoice=$('engine'),source=$('source');
const settingsPanel=$('settings'),settingsButton=$('settings-button');
// Settings are kept in this browser only (localStorage); a private window starts with the defaults.
const saved=(()=>{try{return JSON.parse(localStorage.getItem('textnaut-settings')??'{}');}catch{return {};}})();
if(saved.engine==='off'||saved.engine==='bubblepop')engineChoice.value=saved.engine;
if([...cols.options].some(o=>o.value===saved.cols))cols.value=saved.cols;
function keep(){try{localStorage.setItem('textnaut-settings',JSON.stringify({engine:engineChoice.value,cols:cols.value}));}catch{/* not kept */}}
function toggleSettings(open=settingsPanel.hidden){
  settingsPanel.hidden=!open;settingsButton.setAttribute('aria-expanded',String(open));
  if(open)engineChoice.focus();
}
settingsButton.addEventListener('click',()=>toggleSettings());
document.addEventListener('keydown',event=>{
  if(event.key!=='s'||event.ctrlKey||event.metaKey||event.altKey)return;
  if(/^(INPUT|TEXTAREA|SELECT)$/.test(document.activeElement?.tagName??''))return;
  event.preventDefault();toggleSettings();
});
const pagesBase=new URL('../foafnaut/pages/',location.href).href;
const history=[];
let shown=0;

const view=createGridView($('view'),{
  follow:url=>hubPage(url)||visit({url},true),
  back,
  address:()=>{address.focus();address.select();},
});

// The Hub's own browser pages as link targets (the start page offers both for a reader in an
// ordinary browser): a link to this Textnaut page with an address after # opens that address
// here; a link to the Hub's Foafnaut page opens in a new tab.
function hubPage(url){
  let u;try{u=new URL(url);}catch{return false;}
  const page=u.origin+u.pathname.replace(/index\.html$/,'');
  if(page===new URL('./',location.href).href&&u.hash.length>1){visit({url:new URL(decodeURIComponent(u.hash.slice(1)),location.href).href},true);return true;}
  if(page===new URL('../foafnaut/',location.href).href){window.open(url,'_blank','noopener');return true;}
  return false;
}

/** Columns that fit the view: the grid's font is 14 px monospace, about 8.4 px a character. */
function columns(){
  if(cols.value!=='auto')return Number(cols.value);
  const probe=document.createElement('span');probe.className='textnaut-grid';probe.style.cssText='position:absolute;visibility:hidden;padding:0;border:0';
  probe.textContent='x'.repeat(100);document.body.append(probe);
  const each=probe.getBoundingClientRect().width/100;probe.remove();
  return Math.max(30,Math.min(140,Math.floor(($('view').clientWidth-24)/(each||8.4))));
}

const ms=x=>x===undefined?'':`${Math.round(x*10)/10} ms`;
function timingLine(out){
  const t=out.timing,c=out.counters,parts=[];
  if(t.engineMs!==undefined)parts.push(`engine start ${ms(t.engineMs)}, font ${ms(t.fontMs)}`);
  parts.push(`prepare ${ms(t.prepareMs)}`);
  if(t.scriptMs!==undefined)parts.push(`scripts ${ms(t.scriptMs)} (${out.scripts?.turns??0} turns)`);
  parts.push(`layout ${ms(t.layoutMs)} (${c.layouts} ${c.layouts===1?'layout':'layouts'})`,`cells ${ms(t.cellsMs)}`,
    `${c.primitives} primitives`,`${c.glyphRuns} glyph runs`,`${c.links} links`,`${c.rows}×${c.cols}`,`total ${ms(t.totalMs)}`);
  return parts.join(' · ');
}

async function visit(input,push){
  const shownNow=++shown;
  stats.textContent=engine.engineState().started?'Laying the page out…':'Starting the built-in engine…';
  note.textContent='';
  try{
    const out=await engine.textGrid('textnaut',input.url??{html:input.html,url:location.href},{cols:columns(),base:location.href,scripts:engineChoice.value!=='off'});
    if(shownNow!==shown)return;
    view.show(out.grid);
    stats.textContent=timingLine(out);
    address.value=input.url??'';
    document.title=out.title?`${out.title} — Textnaut`:'Textnaut';
    if(push)history.push(input);
    if(input.url)location.replace('#'+encodeURIComponent(new URL(input.url,location.href).href));
    window.textnautGridCheck=()=>engine.gridCheck('textnaut');
    window.textnautShown={url:out.url,title:out.title,timing:out.timing,counters:out.counters,text:out.text,targets:out.grid.targets};
    if(out.scripts?.errors?.length)note.textContent=`Page script errors: ${out.scripts.errors.slice(0,3).join(' | ')}`;
    // A page shown from the Hub's copy: who wrote it, its licence, when it was fetched.
    if(out.url&&new URL(out.url).origin!==location.origin){
      const found=await copyOf(out.url).catch(()=>undefined);
      if(shownNow===shown&&found?.copy){const c=found.copy;note.textContent=`Hub copy of ${c.url}, fetched ${String(c.fetched??'').slice(0,10)}. ${c.attribution}. Licence: ${c.licence}.`+(note.textContent?' '+note.textContent:'');}
    }
    view.element.focus({preventScroll:true});
  }catch(error){
    if(shownNow!==shown)return;
    stats.textContent='';
    note.textContent=String(error.message??error);
    window.textnautShown={error:note.textContent};
  }
}
function back(){
  if(history.length<2){note.textContent='Nothing to go back to.';return;}
  history.pop();
  visit(history[history.length-1],false);
}

$('go').addEventListener('submit',event=>{event.preventDefault();const a=address.value.trim();if(a)visit({url:new URL(a,location.href).href},true);});
$('back').addEventListener('click',back);
$('layout').addEventListener('click',()=>visit({html:source.value},true));
source.addEventListener('keydown',event=>{if((event.ctrlKey||event.metaKey)&&event.key==='Enter'){event.preventDefault();visit({html:source.value},true);}});
cols.addEventListener('change',()=>{keep();if(history.length)visit(history[history.length-1],false);});
engineChoice.addEventListener('change',()=>{keep();if(history.length)visit(history[history.length-1],false);});

const query=new URLSearchParams(location.search);
const page=query.get('page');
const fromHash=location.hash.length>1?decodeURIComponent(location.hash.slice(1)):'';
if(page&&/^[a-z0-9-]+\.html$/.test(page))visit({url:pagesBase+page},true);
else if(fromHash)visit({url:new URL(fromHash,location.href).href},true);
else visit({url:pagesBase+'start.html'},true);
