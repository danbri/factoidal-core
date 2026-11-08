// Fallback fonts in the native window (issue 1274): the Hub's table and its choice of fonts
// for a page (docs/web/hub/foafnaut/font-coverage.mjs, fallback-fonts.mjs), not a copy. The
// table names Hub paths ('./fonts/…'); here they are the same files in third_party/fonts/,
// which the Hub publishes at those paths (docs/.eleventy.js) and the compiled app holds
// (build-executables.sh). Lean picks the font for each character; this only moves bytes.
//
// For each page, after its source is known and before it is laid out, `page(source)` asks
// fontsFor which fonts its characters need that the engine does not hold, and loads only
// those, in table order, as fallback fonts after the first font. They stay held for later
// pages. A page with no character above ASCII and no numeric character reference reads no
// font file, no coverage file, and not even the table module.
import type {HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

/** A fallback font as a file path and the family Lean names it by. */
export type FallbackFont={path:string;family:string};
/** What loading one font answered: the fonts the engine holds, or why it did not load. */
export type FontAnswer={family:string;fonts?:number;error?:string};

const fontsDir=new URL("../../../third_party/fonts/",import.meta.url);
/** The file of a table path ('./fonts/noto-sans-thai/…' or a coverage file). */
export function fontFilePath(tablePath:string):string {
  if(!tablePath.startsWith("./fonts/"))throw new Error(`Not a fallback font table path: ${tablePath}`);
  return decodeURIComponent(new URL(tablePath.slice("./fonts/".length),fontsDir).pathname);
}

/** Fallback fonts into one engine, in order, each read as bytes (no Base64). Used by the
engine worker, and by the main-thread engine when it lays pages out. */
export async function loadFallbackFonts(engine:HTMLEngine,fonts:FallbackFont[]):Promise<FontAnswer[]> {
  const answers:FontAnswer[]=[];
  for(const font of fonts){
    try{answers.push({family:font.family,fonts:(await loadFontFile(engine,font.path,font.family,"bytes",true)).fonts});}
    catch(error){answers.push({family:font.family,error:String(error instanceof Error?error.message:error)});}
  }
  return answers;
}

/** Only a page with a character above ASCII, as text or as a numeric reference, can need a
fallback font: fontsFor wants none for any other (its pageCharacters is empty). The window
asks this on the main thread; the rest runs beside the engine that takes the fonts. */
export const mayNeedFallbackFonts=(source:string)=>/[^\x00-\x7f]|&#/.test(source);

/** What a page's fonts came to: the families loaded and failed, and every font now held. */
export type PageFonts={loaded:string[];failed:string[];held:FallbackFont[]};

/** The fallback fonts of one engine. `load` puts fonts into it, in order. `readText` reads a
coverage file (a test counts the reads). */
export function fallbackFontHost(load:(fonts:FallbackFont[])=>Promise<FontAnswer[]>,
  {readText=(path:string)=>Deno.readTextFile(path)}:{readText?:(path:string)=>Promise<string>}={}) {
  // Fonts held, or on their way, in the order they went in.
  const held:FallbackFont[]=[],families=new Set<string>();
  const coverageFiles=new Map<string,Promise<unknown>>();
  type Coverage={fontsFor(source:string,coverage:(path:string)=>Promise<unknown>,skip:Set<string>):Promise<{path:string;family:string}[]>};
  let table:Promise<Coverage>|undefined;
  const stats={pages:0,tableLoaded:false,coverageReads:0,fontsLoaded:0,fontFailures:0};
  const coverage=(path:string)=>{
    let file=coverageFiles.get(path);
    if(!file){stats.coverageReads++;file=readText(fontFilePath(path)).then(text=>JSON.parse(text));coverageFiles.set(path,file);}
    return file;
  };
  /** Load the fonts that are not held, in order. */
  const add=async(fonts:FallbackFont[]):Promise<PageFonts>=>{
    const wanted=fonts.filter(font=>!families.has(font.family));
    if(!wanted.length)return {loaded:[],failed:[],held:[...held]};
    for(const font of wanted){families.add(font.family);held.push(font);}
    const answers=await load(wanted);
    const failed=answers.filter(answer=>answer.error).map(answer=>answer.family);
    for(const family of failed){families.delete(family);held.splice(held.findIndex(font=>font.family===family),1);}
    stats.fontsLoaded+=wanted.length-failed.length;stats.fontFailures+=failed.length;
    return {loaded:wanted.map(font=>font.family).filter(family=>!failed.includes(family)),failed,held:[...held]};
  };
  return {
    stats,add,
    /** The fonts held, in the order they went in. */
    held:()=>[...held],
    /** Load the fonts the page needs that are not held. */
    async page(source:string):Promise<PageFonts> {
      stats.pages++;
      if(!mayNeedFallbackFonts(source))return {loaded:[],failed:[],held:[...held]};
      if(!table){
        stats.tableLoaded=true;
        // @ts-ignore plain JavaScript module of the Hub
        table=import("../../../docs/web/hub/foafnaut/font-coverage.mjs") as Promise<Coverage>;
      }
      const wanted=await (await table).fontsFor(source,coverage,families);
      return await add(wanted.map(font=>({path:fontFilePath(font.path),family:font.family})));
    },
  };
}
