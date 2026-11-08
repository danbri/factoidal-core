// WebAssembly run by WasmVM, Lean's WebAssembly engine, inside the Foafnaut engine
// (WebWasm.lean, issue 1244): the ops wasmInfo, wasmRun, wasmSpecSample and wasmPage.
// The host's WebAssembly only runs the Foafnaut engine itself; the modules below are run
// by Lean. Run on the Wasm engine and, when it is built, the native library, and the two
// must give the same values. Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type WasmRun,type WasmValue} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();

const base64=(bytes:Uint8Array)=>{let text="";for(const b of bytes)text+=String.fromCharCode(b);return btoa(text);};
const wasm=(...bytes:number[])=>base64(new Uint8Array(bytes));
// (module (func (export "add") (param i32 i32) (result i32) local.get 0 local.get 1 i32.add))
const add=wasm(0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00,0x01,0x07,0x01,0x60,0x02,0x7f,0x7f,0x01,0x7f,0x03,0x02,0x01,0x00,
  0x07,0x07,0x01,0x03,0x61,0x64,0x64,0x00,0x00,0x0a,0x09,0x01,0x07,0x00,0x20,0x00,0x20,0x01,0x6a,0x0b);
// (module (func (export "div") (param i32 i32) (result i32) local.get 0 local.get 1 i32.div_s))
const div=wasm(0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00,0x01,0x07,0x01,0x60,0x02,0x7f,0x7f,0x01,0x7f,0x03,0x02,0x01,0x00,
  0x07,0x07,0x01,0x03,0x64,0x69,0x76,0x00,0x00,0x0a,0x09,0x01,0x07,0x00,0x20,0x00,0x20,0x01,0x6d,0x0b);
// (module (import "env" "f" (func)))
const envImport=wasm(0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00,0x01,0x04,0x01,0x60,0x00,0x00,0x02,0x09,0x01,0x03,0x65,0x6e,0x76,0x01,0x66,0x00,0x00);
// (module (memory 1000)): over the page limit.
const bigMemory=wasm(0x00,0x61,0x73,0x6d,0x01,0x00,0x00,0x00,0x05,0x04,0x01,0x00,0xe8,0x07);
const hello=base64(await Deno.readFile(new URL("./pages/hello-wasm.wasm",import.meta.url)));
const i32=(n:number):WasmValue=>({type:"i32",value:String(n)});
const shown=(run:WasmRun)=>(run.values??[]).map(v=>v.shown);

function runs(engine:HTMLEngine){
  const info=engine.wasmInfo();
  assert.equal(info.engine,"WasmVM");
  assert(info.ops.includes("wasmRun")&&info.ops.includes("wasmPage"));
  const added=engine.wasmRun({wasmBase64:add,export:"add",args:[i32(40),i32(2)]});
  assert.equal(added.outcome,"values");
  assert.deepEqual(added.values,[{type:"i32",value:"42",shown:"42"}]);
  assert.deepEqual(added.exports,[{name:"add",kind:"func",params:["i32","i32"],results:["i32"]}]);
  assert(typeof added.instructions==="number"&&added.instructions>0);
  // Signed arguments wrap to i32; the answer gives the bits and the signed value.
  const negative=engine.wasmRun({wasmBase64:add,export:"add",args:[i32(-5),i32(2)]});
  assert.deepEqual(negative.values,[{type:"i32",value:"4294967293",shown:"-3"}]);
  const trap=engine.wasmRun({wasmBase64:div,export:"div",args:[i32(1),i32(0)]});
  assert.equal(trap.outcome,"trap");
  assert.equal(trap.message,"integer divide by zero");
  const refused=engine.wasmRun({wasmBase64:envImport});
  assert.equal(refused.outcome,"error");assert.equal(refused.stage,"link");
  assert.match(refused.message??"",/env\.f refused/);
  const big=engine.wasmRun({wasmBase64:bigMemory});
  assert.equal(big.stage,"limits");
  const malformed=engine.wasmRun({wasmBase64:wasm(0x00,0x61,0x73,0x6d,0x02,0x00,0x00,0x00)});
  assert.equal(malformed.stage,"decode");
  const main=engine.wasmRun({wasmBase64:hello,export:"main"});
  assert.deepEqual(shown(main),["10945"]);
  assert.deepEqual(main.prints,["print_i32(1)","print_i32(2)","print_i32(3)"]);
  // WASI, deny by default: fd_write to stdout reaches the output, proc_exit ends the run.
  const wasi=engine.wasmRun({wasmBase64:base64(Deno.readFileSync(new URL("./pages/hello-wasi.wasm",import.meta.url))),export:"_start"});
  assert.equal(wasi.outcome,"exit");assert.equal(wasi.message,"exit 0");
  assert.deepEqual(wasi.prints,["Hello from WASI, run by Lean\n"]);
  const fuel=engine.wasmRun({wasmBase64:hello,export:"fib",args:[i32(25)],fuel:1000});
  assert.equal(fuel.outcome,"outOfFuel");
  assert.equal(fuel.instructions,1000);
  assert.throws(()=>engine.wasmRun({wasmBase64:"not base64!"}),/invalid base64/);
  assert.throws(()=>engine.wasmRun({wasmBase64:add,fuel:1e12}),/fuel is over the limit/);
  const sample=engine.wasmSpecSample();
  assert.equal(sample.fail,0,JSON.stringify(sample.files.flatMap(f=>f.fails)));
  assert(sample.pass>1500,`spec sample passed ${sample.pass}`);
  const page=engine.wasmPage({wasmBase64:hello,export:"main",url:"hello-wasm.wasm"});
  assert.match(page.source,/WebAssembly, run by Lean/);
  assert.match(page.source,/Module hello-wasm\.wasm/);
  assert(!page.source.includes("class=\"bad\""),"a demo or a spec case failed on the page");
  return {added,negative,trap,main,wasi,fuel,sample:{pass:sample.pass,fail:sample.fail,notRun:sample.notRun}};
}
// Times differ from run to run; values and counts do not.
const stable=(r:ReturnType<typeof runs>)=>JSON.stringify(r,(k,v)=>["ns","perSecond","stages"].includes(k)?undefined:v);

Deno.test("Lean runs WebAssembly in the Foafnaut engine (Wasm)",async()=>{runs(await loadHTML());});
Deno.test({name:"Lean runs WebAssembly in the Foafnaut engine (native library), as the Wasm engine does",ignore:noLibrary,fn:async()=>{
  assert.equal(stable(runs(await loadHTML(library))),stable(runs(await loadHTML())));
}});
