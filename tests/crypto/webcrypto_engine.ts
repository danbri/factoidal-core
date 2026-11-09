// webcrypto_engine.ts: crypto.subtle end to end in the Foafnaut engine (page script ->
// prelude.js -> Lean WebApi/WebCryptoKeys -> ffi/hacl_webcrypto.c -> HACL*), on standard
// vectors and hostile inputs, and its timings. Record:
// docs/designissues/2026-11-09-hacl-web-crypto.md, "Vectors" and "Performance".
//
//   deno run -A tests/crypto/webcrypto_engine.ts [--native-engine DYLIB | --wasm]
//     [--quickjs-wasm FILE] [--script-engine quickjs|bubblepop] [--bench] [--vectors] [--crypto-host]
//
// --crypto-host: the Hub's arrangement, the primitives done by the host's crypto.subtle
// (here Deno's) through docs/web/hub/foafnaut/crypto-host.mjs, Lean deciding the rest.
//
// Each page runs in its own script session; its console lines carry the results. A timing
// is the wall time of one session (start and settle) less that of a page that does the same
// with no crypto work, so it includes the boundary crossings but not page start.
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";

const args=Deno.args,opt=(n:string,d="")=>{const i=args.indexOf(n);return i>=0?args[i+1]:d;};
const here=dirname(fileURLToPath(import.meta.url)),root=resolve(here,"../..");
const {loadHTML}=await import("../../labs/demos/foafnaut/native_html_engine.ts");
const wasm=args.includes("--wasm");
const engine=await loadHTML(wasm?undefined:opt("--native-engine",join(root,"labs/demos/foafnaut/.build/web-render/engines/libweb-render.dylib")));
const bubblepop=opt("--script-engine","quickjs")==="bubblepop";
const {cryptoHost,settleCrypto}=await import("../../docs/web/hub/foafnaut/crypto-host.mjs");
const host=args.includes("--crypto-host")?cryptoHost(crypto.subtle):undefined;
if(!bubblepop)engine.scriptLoad(await Deno.readFile(opt("--quickjs-wasm",join(Deno.env.get("HOME")??"","working/qjs-wasm/qjs-wasmvm.wasm"))));

async function run(script:string):Promise<{logs:string[];ms:number}> {
  const html=`<!doctype html><meta charset=utf-8><body><script>${script}</script>`;
  const t0=performance.now();
  // deno-lint-ignore no-explicit-any
  let turn:any=engine.scriptSession(html,{action:"start",url:"https://web-platform.test/crypto.html",commandLimit:200000,logLimit:100000,
    instructionsPerMs:1e12,...(bubblepop?{engine:"bubblepop"}:{}),...(host?{cryptoHost:true}:{})});
  const session=turn.session,logs=[...turn.logs];
  // deno-lint-ignore no-explicit-any
  const act=(r:any)=>engine.scriptSession("",{...r,session});
  for(;;){
    // deno-lint-ignore no-explicit-any
    if(host&&turn.crypto?.length)turn=await settleCrypto(host,turn,act,(t:any)=>logs.push(...t.logs));
    turn=engine.scriptSession("",{action:"settle",session,budgetMs:600000});
    logs.push(...turn.logs);
    if(!host||!turn.crypto?.length)break;
  }
  engine.scriptSession("",{action:"close"});
  host?.clear();
  return {logs,ms:performance.now()-t0};
}

const vectorsSource=await Deno.readTextFile(join(here,"webcrypto_vectors.js"));
const vectors=()=>`const HOST = ${!!host};\n`+vectorsSource;

const benches:[string,string,string][]=[
  ["digest SHA-256, 1 MiB","await crypto.subtle.digest('SHA-256', new Uint8Array(1 << 20));","await crypto.subtle.digest('SHA-256', new Uint8Array(1));"],
  ["PBKDF2-SHA-256, 100,000 iterations","const k = await crypto.subtle.importKey('raw', new Uint8Array(16), 'PBKDF2', false, ['deriveBits']); await crypto.subtle.deriveBits({name: 'PBKDF2', hash: 'SHA-256', salt: new Uint8Array(16), iterations: 100000}, k, 256);",
    "const k = await crypto.subtle.importKey('raw', new Uint8Array(16), 'PBKDF2', false, ['deriveBits']); await crypto.subtle.deriveBits({name: 'PBKDF2', hash: 'SHA-256', salt: new Uint8Array(16), iterations: 1}, k, 256);"],
  ["ChaCha20-Poly1305 encrypt, 1 MiB","const k = await crypto.subtle.importKey('raw', new Uint8Array(32), 'ChaCha20-Poly1305', false, ['encrypt']); await crypto.subtle.encrypt({name: 'ChaCha20-Poly1305', iv: new Uint8Array(12)}, k, new Uint8Array(1 << 20));",
    "const k = await crypto.subtle.importKey('raw', new Uint8Array(32), 'ChaCha20-Poly1305', false, ['encrypt']); await crypto.subtle.encrypt({name: 'ChaCha20-Poly1305', iv: new Uint8Array(12)}, k, new Uint8Array(1));"],
  ["Ed25519 sign + verify (x100)","const p = await crypto.subtle.generateKey('Ed25519', false, ['sign', 'verify']); const m = new Uint8Array(32); for (let i = 0; i < 100; i++) { const s = await crypto.subtle.sign('Ed25519', p.privateKey, m); await crypto.subtle.verify('Ed25519', p.publicKey, s, m); }",
    "const p = await crypto.subtle.generateKey('Ed25519', false, ['sign', 'verify']); const m = new Uint8Array(32); for (let i = 0; i < 100; i++) { await crypto.subtle.digest('SHA-256', m); await crypto.subtle.digest('SHA-256', m); }"],
  ["ECDSA P-256 sign + verify (x100)","const p = await crypto.subtle.generateKey({name: 'ECDSA', namedCurve: 'P-256'}, false, ['sign', 'verify']); const m = new Uint8Array(32); const a = {name: 'ECDSA', hash: 'SHA-256'}; for (let i = 0; i < 100; i++) { const s = await crypto.subtle.sign(a, p.privateKey, m); await crypto.subtle.verify(a, p.publicKey, s, m); }",
    "const p = await crypto.subtle.generateKey({name: 'ECDSA', namedCurve: 'P-256'}, false, ['sign', 'verify']); const m = new Uint8Array(32); for (let i = 0; i < 100; i++) { await crypto.subtle.digest('SHA-256', m); await crypto.subtle.digest('SHA-256', m); }"],
];

if(args.includes("--vectors")||!args.includes("--bench")) {
  const r=await run(vectors());
  const lines=r.logs.flatMap(l=>l.split("\n")).filter(l=>/^(PASS|FAIL) /.test(l));
  for(const l of lines)console.log(l);
  const fails=lines.filter(l=>l.startsWith("FAIL")).length;
  console.log(`vectors: ${lines.length-fails} passed, ${fails} failed`);
  if(fails||lines.length===0){if(lines.length===0)console.log(r.logs.slice(0,20).join("\n"));Deno.exitCode=1;}
}
if(args.includes("--bench")) {
  const reps=Number(opt("--reps","3"));
  for(const [name,work,base] of benches) {
    const wrap=(s:string)=>`(async () => { ${s} console.log('bench done'); })().catch(e => console.log('bench error ' + e));`;
    const times:number[]=[];let note="";
    for(let i=0;i<reps;i++){
      const w=await run(wrap(work)),b=await run(wrap(base));
      if(!w.logs.some(l=>l.includes("bench done")))note=" "+(w.logs.find(l=>l.includes("bench error"))??"no result");
      times.push(w.ms-b.ms);
    }
    times.sort((a,b)=>a-b);
    console.log(`${name}: ${times[Math.floor(times.length/2)].toFixed(1)} ms (median of ${reps}, page start subtracted)${note}`);
  }
}
