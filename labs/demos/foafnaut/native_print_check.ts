// The window library's print path with no panel (issue 1268): three page images go to
// NSPrintOperation, which saves a PDF; the PDF must have three pages of the paper size.
// Run on the main thread: deno run --allow-ffi --allow-read --allow-write native_print_check.ts [LIBRARY] [PDF]
import {libraryPath} from "./native_window.ts";

const library=Deno.args[0]??libraryPath();
const pdfPath=Deno.args[1]??await Deno.makeTempFile({suffix:".pdf"});
const lib=Deno.dlopen(library,{
  ng_app_start:{parameters:[],result:"void"},
  ng_print_paper:{parameters:["buffer"],result:"void"},
  ng_print:{parameters:["buffer","u32","u32","u32","f64","f64","buffer","buffer"],result:"i32"},
});
lib.symbols.ng_app_start();
const paper=new Float64Array(6);lib.symbols.ng_print_paper(paper);
const [paperWidth,paperHeight,left,right,top,bottom]=paper;
const pointWidth=paperWidth-left-right,pointHeight=paperHeight-top-bottom;
const w=Math.round(pointWidth*2),h=Math.round(pointHeight*2),count=3;
// Each page is white with a band of grey whose height says the page number.
const images=new Uint8Array(w*h*4*count).fill(255);
for(let page=0;page<count;page++)for(let y=0;y<40*(page+1);y++)for(let x=0;x<w;x++){
  const i=((page*h+y)*w+x)*4;images[i]=images[i+1]=images[i+2]=96;
}
const encoder=new TextEncoder();
const sent=lib.symbols.ng_print(images,count,w,h,pointWidth,pointHeight,encoder.encode("print check\0"),encoder.encode(pdfPath+"\0"));
const pdf=new TextDecoder("latin1").decode(await Deno.readFile(pdfPath));
const pages=(pdf.match(/\/Type\s*\/Page(?![s\w])/g)??[]).length;
const box=pdf.match(/\/MediaBox\s*\[\s*([-\d. ]+)\]/)?.[1]?.trim().split(/\s+/).map(Number);
console.log(JSON.stringify({type:"native-print-check",paper:{width:paperWidth,height:paperHeight,left,right,top,bottom},pixels:[w,h],sent,pages,mediaBox:box,pdf:pdfPath}));
if(sent!==count||pages!==count){console.error(`print check: ${count} pages sent, ${pages} in the PDF`);Deno.exit(1);}
if(!box||Math.abs(box[2]-paperWidth)>1||Math.abs(box[3]-paperHeight)>1){console.error("print check: the PDF page is not the paper size");Deno.exit(1);}
Deno.exit(0);
