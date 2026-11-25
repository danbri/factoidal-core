// The handwritten pages (pages/manifest.json "handwritten") are whole documents: every element
// that holds raw text (style, script, title, textarea) ends, and the head ends before a body with
// content starts. No engine needed, so it runs in CI before any build.
// Cost of not having it: from 2026-11-16 (commit cdb310373) to 2026-11-25 pages/settings.html
// ended inside its <style> element, so the engine drew an empty Settings page; the gear, :settings
// and the menu all opened it, and check-demo-pages.py counted it as rendered (1 primitive).
import {strict as assert} from "node:assert";

const pagesDir=new URL("./pages/",import.meta.url);
const manifest=JSON.parse(await Deno.readTextFile(new URL("manifest.json",pagesDir))) as {pages:{page:string;handwritten?:boolean}[]};
const handwritten=manifest.pages.filter(p=>p.handwritten&&p.page.endsWith(".html")).map(p=>p.page);

/** Problems of one page's text, by the raw-text rule of the HTML parser: after <style>, the text up
to the first </style> is the element's content, whatever it holds. */
export function problems(source:string):string[]{
  const out:string[]=[],lower=source.toLowerCase();
  for(const tag of ["style","script","title","textarea"]){
    let at=0;
    for(;;){
      const open=lower.indexOf("<"+tag,at);if(open<0)break;
      const after=lower[open+tag.length+1];
      if(after!==">"&&after!==" "&&after!=="\n"&&after!=="\t"){at=open+1;continue;}
      const close=lower.indexOf("</"+tag,open);
      if(close<0){out.push(`<${tag}> at ${open} never ends: the rest of the page is its text`);break;}
      at=close+1;
    }
  }
  const head=lower.indexOf("</head>"),body=lower.indexOf("<body");
  if(head<0&&body<0)out.push("no </head> and no <body>");
  const text=source.slice(Math.max(head,body)).replace(/<[^>]*>/g,"").trim();
  if(text.length<20)out.push(`the body has ${text.length} characters of text`);
  return out;
}

Deno.test("the raw-text check finds the 2026-11-16 Settings page fault",()=>{
  assert(problems("<!doctype html><html><head><title>S</title><style>p{color:red}.engine{pad\n<h1>Settings</h1><p>text text text text</p></main></body></html>").length>0);
  assert(problems("<!doctype html><html><head><title>S</title><style>p{}</style></head><body><h1>Settings</h1><p>text text text text</p></body></html>").length===0);
});

Deno.test("handwritten pages are whole documents",async()=>{
  assert(handwritten.includes("settings.html")&&handwritten.includes("newtab.html")&&handwritten.includes("start.html"));
  for(const page of handwritten){
    const found=problems(await Deno.readTextFile(new URL(page,pagesDir)));
    assert(found.length===0,`${page}: ${found.join("; ")}`);
  }
});

// The new tab page: light (no script, no web font, no image), with the links and forms it promises.
Deno.test("the new tab page links Settings, the console, the game, and has its three forms",async()=>{
  const source=await Deno.readTextFile(new URL("newtab.html",pagesDir));
  for(const want of ['href="foafnaut:settings"','href="foafnaut:console"','href="particle-rex.html"','&#x1F996;',
    'action="foafnaut:search"','action="foafnaut:sparql"','action="https://en.wikipedia.org/wiki/Special:Search"'])
    assert(source.includes(want),`newtab.html lacks ${want}`);
  for(const banned of ["<script","@font-face","<img","<svg","url("])assert(!source.toLowerCase().includes(banned),`newtab.html has ${banned}`);
});
