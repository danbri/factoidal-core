// The whole print path with no window and no panel (issue 1268): Lean lays out and draws
// the pages of a demo page for the paper of the page setup, the GPU renders them, and
// NSPrintOperation saves a PDF. The PDF must have the pages Lean laid out.
// deno run --unstable-webgpu --allow-read --allow-ffi --allow-env print_document_check.ts PAGE PDF [ENGINE_DYLIB]
import {loadHTML} from "./native_html_engine.ts";
import {prepareHTML} from "./native_html_document.ts";
import {loadNativeWindow} from "./native_window.ts";
import {printImages,pdfPageCount,DEFAULT_PAPER} from "./native_print.ts";

const [name="print-showcase.html",pdfPath,dylib]=Deno.args;
if(!pdfPath)throw new Error("usage: print_document_check.ts PAGE PDF [ENGINE_DYLIB]");
if(!navigator.gpu||!await navigator.gpu.requestAdapter()){console.log("NOT RUN: print_document_check.ts needs a GPU adapter");Deno.exit(0);}
const engine=await loadHTML(dylib);
const native=loadNativeWindow();native.appStart();
const page=await prepareHTML(engine,new URL(`./pages/${name}`,import.meta.url).href);
const paper=native.printPaper()??DEFAULT_PAPER;
const job=await printImages(engine,page,paper);
const sent=native.print(job.images,job.count,job.width,job.height,job.pointWidth,job.pointHeight,page.title||name,pdfPath);
const pdfPages=sent>0?pdfPageCount(await Deno.readFile(pdfPath)):0;
console.log(JSON.stringify({type:"print-document-check",page:name,paper,pages:job.count,breaks:job.breaks,sent,pdfPages,pdf:pdfPath}));
if(sent!==job.count||pdfPages!==job.count){console.error(`print document check: ${job.count} pages laid out, ${sent} sent, ${pdfPages} in the PDF`);Deno.exit(1);}
Deno.exit(0);
