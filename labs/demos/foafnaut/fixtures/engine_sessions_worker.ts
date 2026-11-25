// One thread of engine_sessions_test.ts: an engine session of its own in the shared library,
// the font, then the answers of fixtures/engine_sessions_answers.ts.
import {loadHTML} from "../native_html_engine.ts";
import {loadFontFile} from "../native_html_document.ts";
import {answersOf} from "./engine_sessions_answers.ts";
const scope=globalThis as unknown as {onmessage:(e:MessageEvent)=>void;postMessage(m:unknown):void};
scope.onmessage=async e=>{
  const {library,font,pagesDir,rounds}=e.data as {library:string;font:string;pagesDir:string;rounds:number};
  try{
    const engine=await loadHTML(library,"bytes",{session:true});
    if(!engine.sessionOwn)throw new Error("the library has no engine sessions");
    await loadFontFile(engine,font,"Noto Sans");
    const answers=await answersOf(engine,pagesDir,rounds);
    engine.endSession();
    scope.postMessage({answers});
  }catch(error){scope.postMessage({error:String(error instanceof Error?error.message:error)});}
};
