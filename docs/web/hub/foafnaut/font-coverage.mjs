// Which fallback fonts a page needs (issue 1274): the characters of its source that a font in
// fallback-fonts.mjs adds. The Hub worker fetches only those fonts; Lean then picks the font
// for each character. fallback_fonts_test.ts checks the table and the pages with this module.
import {fallbackFonts} from './fallback-fonts.mjs';
export {fallbackFonts};
/** Hexadecimal code points and ranges ('5d0-5ea,fb1d') as sorted [low,high] pairs. */
export const ranges=text=>(text??'').split(',').filter(Boolean).map(part=>{const [a,b]=part.split('-');const lo=parseInt(a,16);return [lo,b===undefined?lo:parseInt(b,16)];});
export function inRanges(list,c){
  let lo=0,hi=list.length-1;
  while(lo<=hi){const m=(lo+hi)>>1;if(c<list[m][0])hi=m-1;else if(c>list[m][1])lo=m+1;else return true;}
  return false;
}
const reference=/&#(?:[xX]([0-9a-fA-F]{1,6})|([0-9]{1,7}));/g;
const referenced=(hex,dec)=>{const c=hex?parseInt(hex,16):Number(dec);return c>0&&c<=0x10ffff?c:undefined;};
/** The characters of a page above ASCII, from its text and its numeric character references. */
export function pageCharacters(source){
  const chars=new Set();
  for(const ch of source){const c=ch.codePointAt(0);if(c>0x7f)chars.add(c);}
  for(const [,hex,dec] of source.matchAll(reference)){const c=referenced(hex,dec);if(c>0x7f)chars.add(c);}
  return chars;
}
/** What a page with emoji asks of the colour slices (issue 1276): the characters followed by
U+FE0F, and the first letters of its regional indicator pairs (flags). Numeric references count
as their characters. Only a page with U+FE0F or a regional indicator does this pass. */
export function emojiRequests(source){
  const vs16=new Set(),regional=new Set();
  if(!/\uFE0F|[\u{1F1E6}-\u{1F1FF}]|&#/u.test(source))return {vs16,regional};
  const text=source.replace(reference,(m,hex,dec)=>{const c=referenced(hex,dec);return c===undefined?m:String.fromCodePoint(c);});
  let before,pending;
  for(const ch of text){
    const c=ch.codePointAt(0);
    if(c===0xfe0f&&before!==undefined)vs16.add(before);
    if(c>=0x1f1e6&&c<=0x1f1ff){if(pending===undefined)pending=c;else{regional.add(pending);pending=undefined;}}
    else pending=undefined;
    before=c;
  }
  return {vs16,regional};
}
const table=fallbackFonts.map(font=>({...font,adds:font.adds===undefined?undefined:ranges(font.adds),blocks:ranges(font.blocks),
  vs16:ranges(font.vs16),regional:ranges(font.regional),needs:font.needs?.map(ranges)}));
/** The fonts, in table order, that add a character of the source, less those in `skip` (families).
`coverage(path)` gives the JSON of a coverage file: it is read only for a page with a character
in a font's blocks, so a page with no CJK never fetches the CJK coverage. A colour emoji slice
is wanted for a character it adds, for a character in its `vs16` that U+FE0F follows, or for a
regional indicator pair whose first letter is in its `regional`; with `needs`, the page must
also have a character of each of those ranges (U+200D for the ZWJ sequences of people). */
export async function fontsFor(source,coverage,skip=new Set()){
  const chars=[...pageCharacters(source)];
  const wanted=[];
  if(!chars.length)return wanted;
  let asked;
  for(const font of table){
    if(skip.has(font.family))continue;
    if(font.regional.length||font.vs16.length){
      asked??=emojiRequests(source);
      if([...asked.regional].some(c=>inRanges(font.regional,c))||[...asked.vs16].some(c=>inRanges(font.vs16,c))){wanted.push(font);continue;}
      if(font.adds===undefined)continue;
    }
    let adds=font.adds;
    if(adds===undefined){
      if(!chars.some(c=>inRanges(font.blocks,c)))continue;
      adds=font.adds=ranges((await coverage(font.coverage))[font.family]);
    }
    if(chars.some(c=>inRanges(adds,c))&&(font.needs??[]).every(need=>chars.some(c=>inRanges(need,c))))wanted.push(font);
  }
  return wanted;
}
