// wycheproof_engine.ts: the Wycheproof corpora (third_party/testing/wycheproof, a git
// submodule of C2SP/wycheproof, Apache-2.0; test input only, not vendored) through
// crypto.subtle in the Foafnaut engine: page JS -> prelude.js -> Lean (WebCryptoKeys) ->
// ffi/hacl_webcrypto.c -> HACL*. Record docs/designissues/2026-11-09-hacl-web-crypto.md,
// "Vectors".
//
//   git submodule update --init --depth 1 third_party/testing/wycheproof
//   deno run -A tests/crypto/wycheproof_engine.ts [--native-engine DYLIB | --wasm]
//     [--quickjs-wasm FILE] [--script-engine quickjs|bubblepop] [--only NAME]
//
// Each file runs in one page. A test passes when the outcome matches its `result`:
// "valid" must succeed with the expected bytes (or verify true), "invalid" must fail
// (an error, a false verify, or other bytes), "acceptable" may do either but must not
// give wrong bytes on success. Exit 1 on any failure.
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";

const args=Deno.args,opt=(n:string,d="")=>{const i=args.indexOf(n);return i>=0?args[i+1]:d;};
const root=resolve(dirname(fileURLToPath(import.meta.url)),"../..");
const dir=join(root,"third_party/testing/wycheproof/testvectors_v1");
const {loadHTML}=await import("../../labs/demos/foafnaut/native_html_engine.ts");
const engine=await loadHTML(args.includes("--wasm")?undefined:opt("--native-engine",join(root,"labs/demos/foafnaut/.build/web-render/engines/libweb-render.dylib")));
const bubblepop=opt("--script-engine","quickjs")==="bubblepop";
if(!bubblepop)engine.scriptLoad(await Deno.readFile(opt("--quickjs-wasm",join(Deno.env.get("HOME")??"","working/qjs-wasm/qjs-wasmvm.wasm"))));

// Per kind: how one test runs in the page. `t` is the test, `g` its group; each returns
// {ok: boolean, bytes?: hex} or throws.
const kinds:Record<string,string>=String.raw`
ed25519|async (g, t) => { const k = await S.importKey('raw', hex(g.publicKey.pk), 'Ed25519', false, ['verify']); return {ok: await S.verify('Ed25519', k, hex(t.sig), hex(t.msg))}; }
ecdsa|async (g, t) => { const k = await S.importKey('raw', hex(g.publicKey.uncompressed), {name: 'ECDSA', namedCurve: 'P-256'}, false, ['verify']); return {ok: await S.verify({name: 'ECDSA', hash: g.sha}, k, hex(t.sig), hex(t.msg))}; }
x25519|async (g, t) => { const sk = await S.importKey('pkcs8', cat(hex('302e020100300506032b656e04220420'), hex(t.private)), 'X25519', false, ['deriveBits']); const pk = await S.importKey('raw', hex(t.public), 'X25519', true, []); return {ok: true, bytes: toHex(await S.deriveBits({name: 'X25519', public: pk}, sk, 256)), want: t.shared}; }
ecdh|async (g, t) => { const sk = await S.importKey('jwk', t.private, {name: 'ECDH', namedCurve: 'P-256'}, false, ['deriveBits']); const pk = await S.importKey('jwk', t.public, {name: 'ECDH', namedCurve: 'P-256'}, true, []); return {ok: true, bytes: toHex(await S.deriveBits({name: 'ECDH', public: pk}, sk, 256)), want: t.shared}; }
hkdf|async (g, t) => { const k = await S.importKey('raw', hex(t.ikm), 'HKDF', false, ['deriveBits']); return {ok: true, bytes: toHex(await S.deriveBits({name: 'HKDF', hash: HASH, salt: hex(t.salt), info: hex(t.info)}, k, t.size * 8)), want: t.okm}; }
hmac|async (g, t) => { const k = await S.importKey('raw', hex(t.key), {name: 'HMAC', hash: HASH}, false, ['sign', 'verify']); const m = toHex(await S.sign('HMAC', k, hex(t.msg))); const full = await S.verify('HMAC', k, hex(m), hex(t.msg)); return {ok: full, bytes: m.slice(0, g.tagSize / 4), want: t.tag}; }
pbkdf2|async (g, t) => { const k = await S.importKey('raw', hex(t.password), 'PBKDF2', false, ['deriveBits']); return {ok: true, bytes: toHex(await S.deriveBits({name: 'PBKDF2', hash: HASH, salt: hex(t.salt), iterations: t.iterationCount}, k, t.dkLen * 8)), want: t.dk}; }
chacha|async (g, t) => { const k = await S.importKey('raw', hex(t.key), 'ChaCha20-Poly1305', false, ['encrypt', 'decrypt']); const p = {name: 'ChaCha20-Poly1305', iv: hex(t.iv), additionalData: hex(t.aad)}; const m = toHex(await S.decrypt(p, k, cat(hex(t.ct), hex(t.tag)))); if (t.result === 'valid') { const c = toHex(await S.encrypt(p, k, hex(t.msg))); if (c !== t.ct + t.tag) return {ok: false}; } return {ok: true, bytes: m, want: t.msg}; }
`.trim().split("\n").reduce((o,l)=>{const i=l.indexOf("|");o[l.slice(0,i)]=l.slice(i+1);return o;},{} as Record<string,string>);

const files:[string,string,string][]=[
  ["ed25519_test.json","ed25519",""],
  ["ecdsa_secp256r1_sha256_p1363_test.json","ecdsa",""],
  ["ecdsa_secp256r1_sha512_p1363_test.json","ecdsa",""],
  ["x25519_test.json","x25519",""],
  ["ecdh_secp256r1_webcrypto_test.json","ecdh",""],
  ["hkdf_sha1_test.json","hkdf","SHA-1"],["hkdf_sha256_test.json","hkdf","SHA-256"],
  ["hkdf_sha384_test.json","hkdf","SHA-384"],["hkdf_sha512_test.json","hkdf","SHA-512"],
  ["hmac_sha1_test.json","hmac","SHA-1"],["hmac_sha256_test.json","hmac","SHA-256"],
  ["hmac_sha384_test.json","hmac","SHA-384"],["hmac_sha512_test.json","hmac","SHA-512"],
  ["pbkdf2_hmacsha1_test.json","pbkdf2","SHA-1"],["pbkdf2_hmacsha256_test.json","pbkdf2","SHA-256"],
  ["pbkdf2_hmacsha384_test.json","pbkdf2","SHA-384"],["pbkdf2_hmacsha512_test.json","pbkdf2","SHA-512"],
  ["chacha20_poly1305_test.json","chacha",""],
];
const only=opt("--only");
let allPass=0,allFail=0;
for(const [file,kind,hash] of files) {
  if(only&&!file.includes(only))continue;
  const data=JSON.parse(await Deno.readTextFile(join(dir,file)));
  const script=`
const hex = s => { const u = new Uint8Array(s.length / 2); for (let i = 0; i < u.length; i++) u[i] = parseInt(s.substr(2 * i, 2), 16); return u; };
const toHex = b => { const u = new Uint8Array(b); let s = ''; for (let i = 0; i < u.length; i++) s += (u[i] < 16 ? '0' : '') + u[i].toString(16); return s; };
const cat = (a, b) => { const u = new Uint8Array(a.length + b.length); u.set(a); u.set(b, a.length); return u; };
const S = crypto.subtle, HASH = ${JSON.stringify(hash)}, run = ${kinds[kind]};
const data = ${JSON.stringify(data.testGroups)};
(async () => {
  let pass = 0; const bad = [];
  for (const g of data) for (const t of g.tests) {
    let r;
    try { r = await run(g, t); } catch (e) { r = {error: e.name}; }
    const good = r.error ? t.result !== 'valid'
      : t.result === 'valid' ? r.ok && (r.want === undefined || r.bytes === r.want)
      : t.result === 'invalid' ? !r.ok || (r.want !== undefined && r.bytes !== r.want)
      : (r.want === undefined || r.bytes === r.want || !r.ok);
    if (good) pass++; else bad.push(t.tcId + ':' + t.result + ':' + (r.error || (r.ok ? 'ok' : 'false')));
  }
  console.log('WYCHEPROOF ' + pass + ' ' + bad.length + ' ' + bad.slice(0, 12).join(','));
})().catch(e => console.log('WYCHEPROOF 0 1 threw ' + e));`;
  const html=`<!doctype html><meta charset=utf-8><script>${script}</script>`;
  let turn=engine.scriptSession(html,{action:"start",url:"https://web-platform.test/w.html",commandLimit:200000,logLimit:100000,instructionsPerMs:1e12,...(bubblepop?{engine:"bubblepop"}:{})});
  const logs=[...turn.logs];
  turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:3600000});
  logs.push(...turn.logs);
  engine.scriptSession("",{action:"close"});
  const line=logs.find(l=>l.startsWith("WYCHEPROOF "))??"WYCHEPROOF 0 1 no result";
  const [,p,f,...rest]=line.split(" ");
  allPass+=+p;allFail+=+f;
  console.log(`${file}: ${p} passed, ${f} failed${+f?" "+rest.join(" "):""}`);
}
console.log(`wycheproof: ${allPass} passed, ${allFail} failed`);
if(allFail)Deno.exitCode=1;
