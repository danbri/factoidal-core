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
    // A flag slice is asked for by the regional indicator pairs of a page, not by characters.
    const adds=font.adds!==undefined?ranges(font.adds):font.regional!==undefined?ranges(font.regional):ranges((await coverage(font.coverage))[font.family]);
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

// Emoji (issue 1276): Noto Color Emoji in slices, and Noto Emoji (monochrome outlines) last,
// for text presentation. A page with an emoji fetches the slices of its emoji; a page with
// none fetches no emoji font, and no other demo page has one.
const emojiFonts=fallbackFonts.filter((f:{family:string})=>/Emoji/.test(f.family));
const emojiFamilies=async(text:string)=>(await fontsFor(text,coverage)).map((f:{family:string})=>f.family).filter((f:string)=>/Emoji/.test(f));
Deno.test("only a page with emoji fetches an emoji font, and only the slices it needs", async()=>{
  const mono=fallbackFonts[fallbackFonts.length-1];
  assert(mono.family==="Noto Emoji","Noto Emoji is the last fallback font");
  assert(mono.bytes<1000000,`Noto Emoji is ${mono.bytes} bytes`);
  const slices=emojiFonts.filter((f:{family:string})=>f.family.startsWith("Noto Color Emoji"));
  assert(slices.length>=10,`${slices.length} colour slices`);
  for(const f of slices)assert(f.bytes<1000000,`${f.family} is ${f.bytes} bytes`);
  for(const name of ["index.html","showcase.html","showcase-scripts.html","showcase-textpath.html"])
    assert((await emojiFamilies(await Deno.readTextFile(new URL(name,pages)))).length===0,`${name} fetches an emoji font`);
  for await(const entry of Deno.readDir(pages)){
    if(!/\.(html|xml)$/.test(entry.name)||entry.name==="showcase-emoji.html")continue;
    const got=await emojiFamilies(await Deno.readTextFile(new URL(entry.name,pages)));
    assert(got.length===0,`${entry.name} fetches ${got}`);
  }
  const page=await families("showcase-emoji.html");
  assert(page.includes("Noto Color Emoji Smileys")&&page.includes("Noto Emoji"),"emoji page: "+page);
  // Symbols that Noto Sans or Noto Sans Math has, with text presentation, stay in those fonts.
  assert((await emojiFamilies("<p>\u00a9 \u00ae \u2122 \u2194 \u25b6 \u2665 # * 1</p>")).length===0,"text symbols fetch an emoji font");
  // One emoji fetches one slice; a sequence the slices of its characters.
  const one=async(text:string,want:string[])=>{
    const got=await emojiFamilies(`<p>${text}</p>`);
    assert(JSON.stringify(got)===JSON.stringify(want.map(w=>w==="Noto Emoji"?w:"Noto Color Emoji "+w)),`${JSON.stringify(text)}: ${got}`);
  };
  await one("\u{1F600}",["Smileys"]);
  await one("\u2b50",["Travel"]);                          // Emoji_Presentation=Yes, though a text font has it
  await one("\u2665\uFE0F",["Activities"]);                 // a text symbol asked for as emoji
  await one("\u2714",["Symbols"]);                         // only emoji fonts have it
  await one("1\uFE0F\u20E3",["Symbols"]);
  await one("&#x1F44D;&#x1F3FD;",["People"]);
  await one("\u{1F468}\u200D\u{1F469}\u200D\u{1F467}",["People","People ZWJ"]);
  await one("\u{1F1EC}\u{1F1E7} \u{1F1EF}\u{1F1F5}",["Flags F-K"]);
  await one("&#x1F1FA;&#x1F1E6;",["Flags T-Z"]);
  await one("\u{1F3F4}\u{E0067}\u{E0062}\u{E0073}\u{E0063}\u{E0074}\u{E007F}",["Flags"]);
  await one("\u2764\uFE0E",["Smileys","Noto Emoji"]);
  // SVG text draws outlines: with an SVG text element the outline emoji font comes too.
  assert(JSON.stringify(await emojiFamilies("<svg><text>\u{1F600}</text></svg>"))===JSON.stringify(["Noto Color Emoji Smileys","Noto Emoji"]),"SVG text emoji");
  // A page of one smiley fetches a small part of the colour font.
  const smileys=emojiFonts.find((f:{family:string})=>f.family==="Noto Color Emoji Smileys");
  assert(smileys.bytes<200000,`the smileys slice is ${smileys.bytes} bytes`);
});
