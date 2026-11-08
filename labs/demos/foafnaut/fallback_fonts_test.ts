// The Hub's fallback fonts (docs/web/hub/foafnaut/fallback-fonts.mjs, font-coverage.mjs): every
// file is there with its size and SHA-256, and a page fetches only the fonts its characters need.
// deno test --no-check --no-config --allow-read labs/demos/foafnaut/fallback_fonts_test.ts
// @ts-ignore plain JavaScript module of the Hub
import {fallbackFonts,fontsFor,pageCharacters,ranges,inRanges} from "../../../docs/web/hub/foafnaut/font-coverage.mjs";
const root=new URL("../../../",import.meta.url);
const fontURL=(path:string)=>new URL("third_party/fonts/"+path.replace("./fonts/",""),root);
const coverage=async(path:string)=>JSON.parse(await Deno.readTextFile(fontURL(path)));
const pages=new URL("pages/",import.meta.url);
const families=async(page:string)=>(await fontsFor(await Deno.readTextFile(new URL(page,pages)),coverage)).map((f:{family:string})=>f.family);
function assert(ok:boolean,message:string){if(!ok)throw new Error(message);}

Deno.test("each fallback font file is there, with its size and SHA-256 and an OFL.txt", async()=>{
  for(const font of fallbackFonts){
    const bytes=await Deno.readFile(fontURL(font.path));
    assert(bytes.length===font.bytes,`${font.family}: ${bytes.length} bytes, table says ${font.bytes}`);
    const sha=[...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("");
    assert(sha===font.sha256,`${font.family}: SHA-256 ${sha}`);
    await Deno.stat(new URL("OFL.txt",fontURL(font.path)));
    const adds=font.adds!==undefined?ranges(font.adds):ranges((await coverage(font.coverage))[font.family]);
    assert(adds.length>0,`${font.family} adds no character`);
    if(font.coverage)for(const [lo,hi] of adds)assert(inRanges(ranges(font.blocks),lo)&&inRanges(ranges(font.blocks),hi),`${font.family}: U+${lo.toString(16)} outside its blocks`);
  }
});

Deno.test("character references count as characters", ()=>{
  const chars=pageCharacters("e&#x301; &#1488;x ב");
  assert(chars.has(0x301)&&chars.has(1488)&&chars.has(0x5d1)&&!chars.has(0x65),"characters "+[...chars]);
});

Deno.test("a page fetches only the fonts its characters need", async()=>{
  assert((await families("index.html")).length===0,"the demo index needs no fallback font");
  assert((await families("showcase.html")).length===0,"the showcase needs no fallback font: "+await families("showcase.html"));
  const textPath=await families("showcase-textpath.html");
  assert(JSON.stringify(textPath)===JSON.stringify(["Noto Sans JP Kana","Noto Sans JP Han"]),"textpath: "+textPath);
  const scripts=await families("showcase-scripts.html");
  for(const family of ["Noto Sans Armenian","Noto Sans Georgian","Noto Sans Ethiopic","Noto Sans Hebrew","Noto Sans Arabic",
    "Noto Sans Devanagari","Noto Sans Bengali","Noto Sans Tamil","Noto Sans Thai","Noto Sans Math","Noto Sans JP Kana",
    "Noto Sans JP Han","Noto Sans KR Hangul"])assert(scripts.includes(family),`scripts page lacks ${family}: ${scripts}`);
  for(const family of scripts)assert(!family.endsWith("More"),`scripts page fetches ${family}`);
  // A rare Han character goes to the larger slice; a page with no CJK never reads the coverage file.
  assert(JSON.stringify(await fontsFor("<p>\u{9F98}</p>",coverage))!=="[]","a rare Han character needs a font");
  assert((await fontsFor("<p>caf\u00e9 \u2122 \u20ac</p>",()=>{throw new Error("coverage read");})).length===0,"Latin page");
});
