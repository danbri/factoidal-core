// The answers that engine_sessions_test.ts compares: the SHA-256 of the storage bytes and tile
// words of each page's frame, `rounds` times over, on one engine. Shared by the test and its
// worker (fixtures/engine_sessions_worker.ts). A refusal is an answer too (its message).
import type {HTMLArtifact} from "../native_html_engine.ts";
/** An engine on this thread or a task session: `compile` answers now or as a promise. */
type Compiles={compile(source:string,width:number,height:number,options:Record<string,unknown>):HTMLArtifact|Promise<HTMLArtifact>};
export const SESSION_PAGES=["status.html","index.html","particle-rex.html"];
const W=800,H=600;
const hex=async(bytes:Uint8Array<ArrayBuffer>)=>[...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("");
export async function answersOf(engine:Compiles,pagesDir:string,rounds:number):Promise<string[]>{
  const out:string[]=[];
  for(let r=0;r<rounds;r++)for(const name of SESSION_PAGES){
    const source=await Deno.readTextFile(pagesDir+name);
    try{
      const scene=await engine.compile(source,W,H,{checks:false,url:"https://example.invalid/"+name,images:[]});
      const data=scene.data as Float32Array,tiles=scene.tiles as Uint32Array;
      const all=new Uint8Array(data.byteLength+tiles.byteLength);
      all.set(new Uint8Array(data.buffer,data.byteOffset,data.byteLength));
      all.set(new Uint8Array(tiles.buffer,tiles.byteOffset,tiles.byteLength),data.byteLength);
      out.push(name+" "+await hex(all));
    }catch(error){out.push(name+" refused "+String(error instanceof Error?error.message:error));}
  }
  return out;
}
