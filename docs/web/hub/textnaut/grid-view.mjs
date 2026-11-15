// A Textnaut grid (grid.mjs layoutGrid: cells, link numbers and targets) shown as monospace text
// in a page, with the terminal program's keys where a page can have them. The cells are page text:
// they go into the page as text nodes only, never as markup.
//
// Keys (when the grid has focus), as in textnaut.ts and help.ts:
//   Up Down j k         scroll a line; Page Up, Page Down, Space; Home, End
//   a number, Enter     follow link n (the number shown beside the link)
//   Tab, Shift-Tab      select the next or previous link (past the last, focus leaves the grid);
//                       Enter or Right follows it
//   b, Left, Backspace  back
//   g                   the address field (onAddress)
const rgb=c=>c?`rgb(${c[0]},${c[1]},${c[2]})`:'';

/** Style key of a cell: cells with the same key share one span. */
const keyOf=c=>`${c.link??0}|${c.mark?1:0}|${c.head?1:0}|${c.band??0}|${c.rule?1:0}|${rgb(c.fg)}|${rgb(c.bg)}`;

/**
 * Show grids in `root` (an element). `actions`: `follow(url, n)`, `back()`, `address()`.
 * Answer: `{show(grid), select(n), typed, element}`.
 */
export function createGridView(root,actions={}){
  const pre=document.createElement('pre');
  pre.className='textnaut-grid';
  pre.tabIndex=0;
  pre.setAttribute('role','document');
  pre.setAttribute('aria-roledescription','text grid');
  root.append(pre);
  const status=document.createElement('p');
  status.className='textnaut-typed';status.setAttribute('aria-live','polite');
  root.append(status);
  let grid,selected=0,typed='';
  const linkSpans=new Map();

  function show(next){
    grid=next;selected=0;typed='';status.textContent='';
    linkSpans.clear();
    const lines=document.createDocumentFragment();
    grid.rows.forEach((cells,r)=>{
      const line=document.createElement('span');line.className='row';
      if(grid.rules?.includes(r))line.classList.add('rule');
      let run=null,runKey='';
      for(const cell of cells){
        if(cell.w===0)continue;
        const key=keyOf(cell);
        if(!run||key!==runKey){
          run=document.createElement(cell.link?'a':'span');runKey=key;
          if(cell.link){
            const n=cell.link;
            run.href=grid.targets[n-1]??'#';
            run.dataset.link=String(n);
            run.addEventListener('click',event=>{event.preventDefault();follow(n);});
            if(!linkSpans.has(n))linkSpans.set(n,[]);
            linkSpans.get(n).push(run);
          }
          if(cell.mark)run.classList.add('mark');
          if(cell.head)run.classList.add('head');
          if(cell.band)run.classList.add(`band${cell.band}`);
          if(cell.fg)run.style.color=rgb(cell.fg);
          if(cell.bg)run.style.backgroundColor=rgb(cell.bg);
          line.append(run);
        }
        run.append(cell.c);
      }
      line.append('\n');
      lines.append(line);
    });
    pre.replaceChildren(lines);
    pre.scrollTop=0;
  }
  function select(n){
    for(const s of linkSpans.get(selected)??[])s.classList.remove('selected');
    selected=n;
    const spans=linkSpans.get(n)??[];
    for(const s of spans)s.classList.add('selected');
    spans[0]?.scrollIntoView({block:'nearest'});
    if(n)status.textContent=`[${n}] ${grid.targets[n-1]??''}`;
  }
  function follow(n){
    const target=grid?.targets[n-1];
    if(!target){status.textContent=`no link ${n}`;return;}
    actions.follow?.(target,n);
  }
  const lineHeight=()=>parseFloat(getComputedStyle(pre).lineHeight)||18;
  pre.addEventListener('keydown',event=>{
    if(!grid||event.metaKey||event.ctrlKey||event.altKey)return;
    const k=event.key,count=grid.targets.length;
    let handled=true;
    if(/^[0-9]$/.test(k)){typed+=k;status.textContent=`link ${typed}`;}
    else if(k==='Enter'||k==='ArrowRight'){const n=typed?Number(typed):selected;typed='';if(n)follow(n);}
    else if(k==='Tab'){
      const next=event.shiftKey?selected-1:selected+1;
      if(next<1||next>count){select(0);handled=false;}else select(next);
    }
    else if(k==='ArrowDown'||k==='j')pre.scrollTop+=lineHeight();
    else if(k==='ArrowUp'||k==='k')pre.scrollTop-=lineHeight();
    else if(k==='PageDown'||k===' ')pre.scrollTop+=pre.clientHeight-lineHeight();
    else if(k==='PageUp')pre.scrollTop-=pre.clientHeight-lineHeight();
    else if(k==='Home')pre.scrollTop=0;
    else if(k==='End')pre.scrollTop=pre.scrollHeight;
    else if(k==='b'||k==='ArrowLeft'||k==='Backspace'){typed='';actions.back?.();}
    else if(k==='g'&&actions.address)actions.address();
    else if(k==='Escape'){typed='';select(0);status.textContent='';}
    else handled=false;
    if(handled)event.preventDefault();
  });
  return {show,select,element:pre,get typed(){return typed;},get grid(){return grid;}};
}

/** The grid view's style, once per document. The grid keeps a light ground in either colour
scheme: the colours in it are the page's, chosen for a light page. */
export function gridStyle(){
  if(document.getElementById('textnaut-grid-style'))return;
  const style=document.createElement('style');style.id='textnaut-grid-style';
  style.textContent=`
.textnaut-grid{font:14px/1.35 ui-monospace,SFMono-Regular,Menlo,Consolas,"Liberation Mono",monospace;background:#fbfbf8;color:#1d2125;
  padding:8px 10px;margin:0;overflow:auto;white-space:pre;border:1px solid #c9ced3;border-radius:4px;max-height:70vh;outline-offset:2px}
.textnaut-grid .row>*{display:inline-block;vertical-align:top}
.textnaut-grid a{color:#0b5cad;text-decoration:underline;text-underline-offset:2px;cursor:pointer}
.textnaut-grid a.mark{text-decoration:none;color:#8a5a00}
.textnaut-grid a.selected{background:#0b5cad;color:#fff!important}
.textnaut-grid .head{font-weight:bold}
.textnaut-grid .band1{background:#e8eef3}.textnaut-grid .band2{background:#f0f3f6}
.textnaut-typed{font:12px ui-monospace,monospace;margin:4px 0 0;min-height:1.2em;opacity:.8}`;
  document.head.append(style);
}
