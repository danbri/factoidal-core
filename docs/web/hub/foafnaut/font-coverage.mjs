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
/** The characters of a page above ASCII, from its text and its numeric character references. */
export function pageCharacters(source){
  const chars=new Set();
  for(const ch of source){const c=ch.codePointAt(0);if(c>0x7f)chars.add(c);}
  for(const [,hex,dec] of source.matchAll(/&#(?:[xX]([0-9a-fA-F]{1,6})|([0-9]{1,7}));/g)){const c=hex?parseInt(hex,16):Number(dec);if(c>0x7f&&c<=0x10ffff)chars.add(c);}
  return chars;
}
const table=fallbackFonts.map(font=>({...font,adds:font.adds===undefined?undefined:ranges(font.adds),blocks:ranges(font.blocks)}));
/** The fonts, in table order, that add a character of the source, less those in `skip` (families).
`coverage(path)` gives the JSON of a coverage file: it is read only for a page with a character
in a font's blocks, so a page with no CJK never fetches the CJK coverage. */
export async function fontsFor(source,coverage,skip=new Set()){
  const chars=[...pageCharacters(source)];
  const wanted=[];
  if(!chars.length)return wanted;
  for(const font of table){
    if(skip.has(font.family))continue;
    let adds=font.adds;
    if(adds===undefined){
      if(!chars.some(c=>inRanges(font.blocks,c)))continue;
      adds=font.adds=ranges((await coverage(font.coverage))[font.family]);
    }
    if(chars.some(c=>inRanges(adds,c)))wanted.push(font);
  }
  return wanted;
}
