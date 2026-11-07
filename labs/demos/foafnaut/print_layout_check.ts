// Page breaks of the print showcase, from Lean (issue 1268): A4 inside 36-point margins
// at 2 device pixels a point. Each chapter heading must start a page (break-before:
// page), the screen-only note must not print, and every page must fit.
// deno run --allow-read --allow-ffi --allow-env print_layout_check.ts [ENGINE_DYLIB]
import {loadHTML} from "./native_html_engine.ts";
import {prepareHTML} from "./native_html_document.ts";

const engine=await loadHTML(Deno.args[0]);
const url=new URL("./pages/print-showcase.html",import.meta.url).href;
const page=await prepareHTML(engine,url);
const w=Math.round(523*2),h=Math.round(770*2);
const base=page.request(w,h,{textScalePercent:150});
const print={...base.options,media:"print"} as Record<string,unknown>;
const screen={...base.options} as Record<string,unknown>;
const layout=engine.printLayout(base.source,w,h,print);
const onScreen=engine.printLayout(base.source,w,h,screen);
const text=(options:Record<string,unknown>,top:number,rows:number)=>
  engine.selectedText(base.source,w,h,{...options,selection:[0,top,w,top+rows]});
console.log(JSON.stringify({type:"print-layout-check",pages:layout.pages,contentHeight:layout.contentHeight,screenPages:onScreen.pages.length}));
const failures:string[]=[];
if(layout.pages.length<4)failures.push(`expected at least 4 pages (title and 3 chapters), got ${layout.pages.length}`);
for(const [i,[,rows]] of layout.pages.entries())if(rows<1||rows>h)failures.push(`page ${i+1} has ${rows} rows`);
// The print rules: the note is not in the print layout; the screen layout has no forced breaks.
const all=text(print,0,layout.contentHeight);
if(all.includes("On screen you see this note"))failures.push("the screen-only note prints");
if(!text(screen,0,onScreen.contentHeight).includes("On screen you see this note"))failures.push("the note is missing on screen");
for(const [i,chapter] of ["Chapter 1","Chapter 2","Chapter 3"].entries()){
  const [top,rows]=layout.pages[i+1]??[0,0];
  const first=text(print,top,Math.min(rows,80)).trim();
  if(!first.startsWith(chapter))failures.push(`page ${i+2} starts with ${JSON.stringify(first.slice(0,30))}, not ${chapter}`);
}
for(const failure of failures)console.error("print layout check:",failure);
Deno.exit(failures.length?1:0);
