// boundary_attack_engine.ts: hostile page scripts against crypto.subtle's boundary, in the
// engine (page JS -> prelude -> Lean -> HACL*), each with the answer the boundary must give.
// Record: docs/designissues/2026-11-09-crypto-boundary-security.md (findings F2, F3, and
// "Attacks tried that the boundary held").
//
//   deno run -A tests/crypto/boundary_attack_engine.ts [--native-engine DYLIB]
//     [--quickjs-wasm FILE] [--script-engine quickjs|bubblepop]
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";

const args=Deno.args,opt=(n:string,d="")=>{const i=args.indexOf(n);return i>=0?args[i+1]:d;};
const here=dirname(fileURLToPath(import.meta.url)),root=resolve(here,"../..");
const {loadHTML}=await import("../../labs/demos/foafnaut/native_html_engine.ts");
const engine=await loadHTML(opt("--native-engine",join(root,"labs/demos/foafnaut/.build/web-render/engines/libweb-render.dylib")));
const bubblepop=opt("--script-engine","quickjs")==="bubblepop";
if(!bubblepop)engine.scriptLoad(await Deno.readFile(opt("--quickjs-wasm",join(Deno.env.get("HOME")??"","working/qjs-wasm/qjs-wasmvm.wasm"))));

function run(script:string):{logs:string[];ms:number} {
  const html=`<!doctype html><meta charset=utf-8><body><script>(async () => { const S = crypto.subtle;
    const say = (...x) => console.log(x.join(' '));
    const hex = b => Array.from(new Uint8Array(b), x => x.toString(16).padStart(2, '0')).join('');
    const err = async f => { try { await f(); return 'OK'; } catch (e) { return e && e.name; } };
    ${script} })().catch(e => console.log('script error ' + e));</script>`;
  const t0=performance.now();
  // deno-lint-ignore no-explicit-any
  let turn:any=engine.scriptSession(html,{action:"start",url:"https://a.test/x.html",commandLimit:200000,logLimit:100000,
    instructionsPerMs:1e12,...(bubblepop?{engine:"bubblepop"}:{})});
  const session=turn.session,logs=[...turn.logs];
  turn=engine.scriptSession("",{action:"settle",session,budgetMs:600000});
  logs.push(...turn.logs);
  engine.scriptSession("",{action:"close"});
  return {logs,ms:performance.now()-t0};
}
let fails=0;
const check=(name:string,ok:boolean,detail:string)=>{console.log(`${ok?"PASS":"FAIL"} ${name}${ok?"":" ("+detail+")"}`);if(!ok)fails++;};
const line=(r:{logs:string[]},key:string)=>(r.logs.find(l=>l.startsWith(key+" "))??"").slice(key.length+1);

// F2: Math.random is a session's own.
const m1=run(`say('MR', Math.random(), Math.random());`),m2=run(`say('MR', Math.random(), Math.random());`);
check("Math.random differs between sessions",line(m1,"MR")!==""&&line(m1,"MR")!==line(m2,"MR"),`${line(m1,"MR")} / ${line(m2,"MR")}`);

// Non-extractable keys: nothing of them leaves.
const leak=run(`
  const k = await S.generateKey({name: 'HMAC', hash: 'SHA-256'}, false, ['sign']);
  say('json', JSON.stringify(k)); say('own', Object.getOwnPropertyNames(k).length);
  say('raw', await err(() => S.exportKey('raw', k))); say('jwk', await err(() => S.exportKey('jwk', k)));
  const c = structuredClone(k); say('clone', c.extractable, c.usages.join(','), await err(() => S.exportKey('raw', c)));
  k.usages.push('verify'); say('mutated', await err(() => S.verify('HMAC', k, new Uint8Array(32), new Uint8Array(1))));
  const w = await S.generateKey('ChaCha20-Poly1305', false, ['wrapKey']);
  say('wrap', await err(() => S.wrapKey('raw', k, w, {name: 'ChaCha20-Poly1305', iv: new Uint8Array(12)})));
  say('forged', await err(() => S.exportKey('raw', Object.create(CryptoKey.prototype))));`);
check("JSON of a CryptoKey is {}",line(leak,"json")==="{}",line(leak,"json"));
check("a CryptoKey has no own properties",line(leak,"own")==="0",line(leak,"own"));
check("export raw of a non-extractable key",line(leak,"raw")==="InvalidAccessError",line(leak,"raw"));
check("export jwk of a non-extractable key",line(leak,"jwk")==="InvalidAccessError",line(leak,"jwk"));
check("a clone keeps extractable false and its usages, and is not exported",line(leak,"clone")==="false sign InvalidAccessError",line(leak,"clone"));
check("a usage pushed into key.usages is not a usage",line(leak,"mutated")==="InvalidAccessError",line(leak,"mutated"));
check("wrapKey of a non-extractable key",line(leak,"wrap")==="InvalidAccessError",line(leak,"wrap"));
check("a forged CryptoKey",line(leak,"forged")==="TypeError",line(leak,"forged"));

// Algorithms and curves.
const conf=run(`
  const e = await S.generateKey({name: 'ECDSA', namedCurve: 'P-256'}, true, ['sign', 'verify']);
  say('asEcdh', await err(() => S.deriveBits({name: 'ECDH', public: e.publicKey}, e.privateKey, 256)));
  const h = await S.generateKey({name: 'HMAC', hash: 'SHA-256'}, false, ['sign']);
  say('asEcdsa', await err(() => S.sign({name: 'ECDSA', hash: 'SHA-256'}, h, new Uint8Array(1))));
  const spki = Array.from(new Uint8Array(await S.exportKey('spki', e.publicKey)));
  const p384 = [0x06,0x05,0x2b,0x81,0x04,0x00,0x22], algid = [0x30, 9 + p384.length, 0x06,0x07,0x2a,0x86,0x48,0xce,0x3d,0x02,0x01, ...p384];
  const bits = [0x03, 66, 0x00, ...spki.slice(spki.length - 65)];
  say('oid', await err(() => S.importKey('spki', new Uint8Array([0x30, algid.length + bits.length, ...algid, ...bits]), {name: 'ECDSA', namedCurve: 'P-256'}, true, ['verify'])));
  const s1 = hex(await S.sign({name: 'ECDSA', hash: 'SHA-256'}, e.privateKey, new Uint8Array(1)));
  const s2 = hex(await S.sign({name: 'ECDSA', hash: 'SHA-256'}, e.privateKey, new Uint8Array(1)));
  say('hedged', s1.slice(0, 64) !== s2.slice(0, 64), await S.verify({name: 'ECDSA', hash: 'SHA-256'}, e.publicKey, new Uint8Array(s1.match(/../g).map(x => parseInt(x, 16))), new Uint8Array(1)));
  const jwk = await S.exportKey('jwk', e.privateKey);
  say('pad', await err(() => S.importKey('jwk', {...jwk, d: jwk.d + '='}, {name: 'ECDSA', namedCurve: 'P-256'}, true, ['sign'])));`);
check("an ECDSA key used for ECDH",line(conf,"asEcdh")==="InvalidAccessError",line(conf,"asEcdh"));
check("an HMAC key used for ECDSA",line(conf,"asEcdsa")==="InvalidAccessError",line(conf,"asEcdsa"));
check("a P-384 OID in a P-256 import",line(conf,"oid")==="DataError",line(conf,"oid"));
check("hedged ECDSA: two signatures of one message differ and verify",line(conf,"hedged")==="true true",line(conf,"hedged"));
check("a padded base64url d",line(conf,"pad")==="DataError",line(conf,"pad"));

// F3: work is bounded before it runs, and charged to script time.
const dos=run(`
  let t = Date.now(); say('hmac', await err(() => S.generateKey({name: 'HMAC', hash: 'SHA-256', length: 4294967295}, false, ['sign'])));
  const k = await S.importKey('raw', new Uint8Array(16), 'PBKDF2', false, ['deriveBits']);
  say('pbkdf2', await err(() => S.deriveBits({name: 'PBKDF2', hash: 'SHA-256', salt: new Uint8Array(16), iterations: 4294967295}, k, 256)));
  t = Date.now(); await S.deriveBits({name: 'PBKDF2', hash: 'SHA-256', salt: new Uint8Array(16), iterations: 200000}, k, 256);
  say('charged', Date.now() - t > 0);
  const ops = []; for (let i = 0; i < 4000; i++) ops.push('x' + i); ops.push('sign');
  t = Date.now(); say('keyops', await err(() => S.importKey('jwk', {kty: 'oct', k: 'AAAA', key_ops: ops}, {name: 'HMAC', hash: 'SHA-256'}, false, ['sign'])));`);
check("an HMAC key of 2^32 - 1 bits is refused before it runs",line(dos,"hmac")==="OperationError"&&dos.ms<30000,`${line(dos,"hmac")}, ${Math.round(dos.ms)} ms`);
check("PBKDF2 at 2^32 - 1 iterations is refused before it runs",line(dos,"pbkdf2")==="OperationError",line(dos,"pbkdf2"));
check("PBKDF2's work moves the script clock",line(dos,"charged")==="true",line(dos,"charged"));
check("key_ops of 4,001 entries",["OK","OperationError"].includes(line(dos,"keyops")),line(dos,"keyops"));

console.log(`boundary attacks: ${fails?fails+" FAILED":"all held"} (${bubblepop?"BubblePopJS":"QuickJS-NG"})`);
if(fails)Deno.exitCode=1;
