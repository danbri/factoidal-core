// Printing (issue 1268). Lean lays the page out for the paper with the print media type
// and says where the pages break (`printLayout`); it draws each page (`printPage`); the
// GPU renders it offscreen. The window library gives the images to the system print
// operation. Device pixels are 2 for each point (144 dpi), so CSS text is 150%: 16 CSS
// pixels print as 12 points.
import {render} from "./gpu_transport.ts";
import type {HTMLArtifact,PrintLayout} from "./native_html_engine.ts";

export const PIXELS_PER_POINT=2,PRINT_TEXT_PERCENT=150;
export type Paper={width:number;height:number;left:number;right:number;top:number;bottom:number};
/** The paper when the window library can not say: A4 with half-inch margins. */
export const DEFAULT_PAPER:Paper={width:595,height:842,left:36,right:36,top:36,bottom:36};
type PrintEngine={
  printLayout(source:string,width:number,height:number,options:Record<string,unknown>):PrintLayout|Promise<PrintLayout>;
  compile(source:string,width:number,height:number,options:Record<string,unknown>):HTMLArtifact|Promise<HTMLArtifact>;
};
type Printable={request(width:number,height:number,view?:Record<string,unknown>):{source:string;options:Record<string,unknown>}};

/** The page images of `page` for `paper`, one after another, RGBA. */
export async function printImages(lean:PrintEngine,page:Printable,paper:Paper) {
  const pointWidth=paper.width-paper.left-paper.right,pointHeight=paper.height-paper.top-paper.bottom;
  const width=Math.min(4096,Math.round(pointWidth*PIXELS_PER_POINT)),height=Math.min(4096,Math.round(pointHeight*PIXELS_PER_POINT));
  const base=page.request(width,height,{textScalePercent:PRINT_TEXT_PERCENT});
  // No chrome, selection or scroll on paper.
  const options={...base.options,media:"print"} as Record<string,unknown>;
  for(const key of ["shell","selection","live","checks","layers"])delete options[key];
  const layout=await lean.printLayout(base.source,width,height,options);
  const images=new Uint8Array(width*height*4*layout.pages.length);
  for(const [index,[top,rows]] of layout.pages.entries()){
    const artifact=await lean.compile(base.source,width,height,{...options,printPage:[top,rows]});
    const rgba=await render(artifact as unknown as Parameters<typeof render>[0],"svg-offscreen");
    if(!rgba)throw new Error("no GPU adapter to draw the printed page");
    images.set(rgba,index*width*height*4);
  }
  return {images,count:layout.pages.length,breaks:layout.pages,width,height,pointWidth,pointHeight};
}

/** The pages of a PDF that Quartz wrote: each page object has /Type /Page. */
export function pdfPageCount(pdf:Uint8Array) {
  return (new TextDecoder("latin1").decode(pdf).match(/\/Type\s*\/Page(?![s\w])/g)??[]).length;
}
