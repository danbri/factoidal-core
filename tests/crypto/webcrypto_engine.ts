// webcrypto_engine.ts: crypto.subtle end to end in the Foafnaut engine (page script ->
// prelude.js -> Lean WebApi/WebCryptoKeys -> ffi/hacl_webcrypto.c -> HACL*), on standard
// vectors and hostile inputs, and its timings. Record:
// docs/designissues/2026-11-09-hacl-web-crypto.md, "Vectors" and "Performance".
//
//   deno run -A tests/crypto/webcrypto_engine.ts [--native-engine DYLIB | --wasm]
//     [--quickjs-wasm FILE] [--script-engine quickjs|bubblepop] [--bench] [--vectors]
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
if(!bubblepop)engine.scriptLoad(await Deno.readFile(opt("--quickjs-wasm",join(Deno.env.get("HOME")??"","working/qjs-wasm/qjs-wasmvm.wasm"))));

function run(script:string):{logs:string[];ms:number} {
  const html=`<!doctype html><meta charset=utf-8><body><script>${script}</script>`;
  const t0=performance.now();
  let turn=engine.scriptSession(html,{action:"start",url:"https://web-platform.test/crypto.html",commandLimit:200000,logLimit:100000,
    instructionsPerMs:1e12,engine:bubblepop?"bubblepop":"quickjs"});
  const logs=[...turn.logs];
  turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:600000});
  logs.push(...turn.logs);
  engine.scriptSession("",{action:"close"});
  return {logs,ms:performance.now()-t0};
}

const vectors=String.raw`
const hex = s => { const u = new Uint8Array(s.length / 2); for (let i = 0; i < u.length; i++) u[i] = parseInt(s.substr(2 * i, 2), 16); return u; };
const toHex = b => Array.from(new Uint8Array(b), x => x.toString(16).padStart(2, '0')).join('');
const S = crypto.subtle, out = [];
const ok = (n, c) => out.push((c ? 'PASS ' : 'FAIL ') + n);
const rejects = async (n, p, name) => { try { await p; ok(n + ' (no error)', false); } catch (e) { ok(n + ' -> ' + e.name, e.name === name); } };
(async () => {
  const abc = new TextEncoder().encode('abc');
  ok('SHA-1 abc', toHex(await S.digest('SHA-1', abc)) === 'a9993e364706816aba3e25717850c26c9cd0d89d');
  ok('SHA-256 abc', toHex(await S.digest('SHA-256', abc)) === 'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');
  ok('SHA-384 abc', toHex(await S.digest('SHA-384', abc)) === 'cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7');
  ok('SHA-512 abc', toHex(await S.digest('SHA-512', abc)).startsWith('ddaf35a193617aba'));
  // RFC 4231 case 2.
  const hk = await S.importKey('raw', new TextEncoder().encode('Jefe'), {name: 'HMAC', hash: 'SHA-256'}, false, ['sign', 'verify']);
  const what = new TextEncoder().encode('what do ya want for nothing?');
  const mac = await S.sign('HMAC', hk, what);
  ok('HMAC-SHA-256 RFC 4231 case 2', toHex(mac) === '5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843');
  ok('HMAC verify', await S.verify('HMAC', hk, mac, what));
  const bad = new Uint8Array(mac); bad[31] ^= 1;
  ok('HMAC verify forged', !(await S.verify('HMAC', hk, bad, what)));
  // RFC 5869 A.1.
  const ikm = await S.importKey('raw', new Uint8Array(22).fill(11), 'HKDF', false, ['deriveBits']);
  ok('HKDF RFC 5869 A.1', toHex(await S.deriveBits({name: 'HKDF', hash: 'SHA-256', salt: hex('000102030405060708090a0b0c'), info: hex('f0f1f2f3f4f5f6f7f8f9')}, ikm, 336))
    === '3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865');
  // RFC 6070 case 2, RFC 7914 §11.
  const pw = await S.importKey('raw', new TextEncoder().encode('password'), 'PBKDF2', false, ['deriveBits']);
  ok('PBKDF2-SHA-1 RFC 6070 case 2', toHex(await S.deriveBits({name: 'PBKDF2', hash: 'SHA-1', salt: new TextEncoder().encode('salt'), iterations: 2}, pw, 160))
    === 'ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957');
  const pw2 = await S.importKey('raw', new TextEncoder().encode('passwd'), 'PBKDF2', false, ['deriveBits']);
  ok('PBKDF2-SHA-256 RFC 7914 §11', toHex(await S.deriveBits({name: 'PBKDF2', hash: 'SHA-256', salt: new TextEncoder().encode('salt'), iterations: 1}, pw2, 512))
    === '55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783');
  // RFC 8032 §7.1 test 1.
  const edSk = await S.importKey('pkcs8', hex('302e020100300506032b657004220420' + '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60'), 'Ed25519', true, ['sign']);
  const edSig = await S.sign('Ed25519', edSk, new Uint8Array(0));
  ok('Ed25519 RFC 8032 test 1 sign', toHex(edSig) === 'e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b');
  const edJwk = await S.exportKey('jwk', edSk);
  ok('Ed25519 RFC 8032 test 1 public (jwk x)', edJwk.x === '11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo');
  const edPk = await S.importKey('raw', hex('d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a'), 'Ed25519', true, ['verify']);
  ok('Ed25519 verify', await S.verify('Ed25519', edPk, edSig, new Uint8Array(0)));
  ok('Ed25519 verify wrong message', !(await S.verify('Ed25519', edPk, edSig, new Uint8Array(1))));
  // RFC 7748 §6.1.
  const xa = await S.importKey('pkcs8', hex('302e020100300506032b656e04220420' + '77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a'), 'X25519', false, ['deriveBits']);
  const xb = await S.importKey('raw', hex('de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f'), 'X25519', true, []);
  ok('X25519 RFC 7748 §6.1', toHex(await S.deriveBits({name: 'X25519', public: xb}, xa, 256)) === '4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742');
  const zero = await S.importKey('raw', new Uint8Array(32), 'X25519', true, []);
  await rejects('X25519 small-order point', S.deriveBits({name: 'X25519', public: zero}, xa, 256), 'OperationError');
  // RFC 6979 A.2.5 (P-256, SHA-256, "sample").
  const q = hex('0460fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb67903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299');
  const ecPk = await S.importKey('raw', q, {name: 'ECDSA', namedCurve: 'P-256'}, true, ['verify']);
  const sample = new TextEncoder().encode('sample');
  const rs = hex('efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8');
  ok('ECDSA P-256 RFC 6979 verify', await S.verify({name: 'ECDSA', hash: 'SHA-256'}, ecPk, rs, sample));
  const rs2 = new Uint8Array(rs); rs2[0] ^= 1;
  ok('ECDSA verify forged', !(await S.verify({name: 'ECDSA', hash: 'SHA-256'}, ecPk, rs2, sample)));
  const ecSk = await S.importKey('jwk', {kty: 'EC', crv: 'P-256', d: 'ya-p2EW6dRZrXCFXZ7HWk05Qw9s26JsSe4piKxIPZyE',
    x: 'YP7UuiVanTHJYet0xjVtaMBJuJI7Yfps5mliLmDyn7Y', y: 'eQP-EAi4vJmkGunpVii8ZPLxsgwtfp9Rd6PClNRGIpk'}, {name: 'ECDSA', namedCurve: 'P-256'}, false, ['sign']);
  const fresh = await S.sign({name: 'ECDSA', hash: 'SHA-384'}, ecSk, sample);
  ok('ECDSA sign then verify (SHA-384)', await S.verify({name: 'ECDSA', hash: 'SHA-384'}, ecPk, fresh, sample));
  ok('ECDSA spki round trip', toHex(await S.exportKey('spki', ecPk)).endsWith(toHex(q)));
  // ECDH both ways; hostile points.
  const e1 = await S.generateKey({name: 'ECDH', namedCurve: 'P-256'}, false, ['deriveBits']);
  const e2 = await S.generateKey({name: 'ECDH', namedCurve: 'P-256'}, false, ['deriveBits']);
  ok('ECDH agrees', toHex(await S.deriveBits({name: 'ECDH', public: e2.publicKey}, e1.privateKey, 256)) === toHex(await S.deriveBits({name: 'ECDH', public: e1.publicKey}, e2.privateKey, 256)));
  const off = new Uint8Array(q); off[64] ^= 1;
  await rejects('P-256 off-curve point', S.importKey('raw', off, {name: 'ECDH', namedCurve: 'P-256'}, true, []), 'DataError');
  const inf = new Uint8Array(65); inf[0] = 4;
  await rejects('P-256 point at infinity', S.importKey('raw', inf, {name: 'ECDH', namedCurve: 'P-256'}, true, []), 'DataError');
  await rejects('P-256 x >= p', S.importKey('raw', (() => { const u = new Uint8Array(q); u.fill(255, 1, 33); return u; })(), {name: 'ECDSA', namedCurve: 'P-256'}, true, ['verify']), 'DataError');
  await rejects('P-256 zero private (jwk d)', S.importKey('jwk', {kty: 'EC', crv: 'P-256', d: 'AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
    x: 'YP7UuiVanTHJYet0xjVtaMBJuJI7Yfps5mliLmDyn7Y', y: 'eQP-EAi4vJmkGunpVii8ZPLxsgwtfp9Rd6PClNRGIpk'}, {name: 'ECDSA', namedCurve: 'P-256'}, false, ['sign']), 'DataError');
  await rejects('P-384 not in HACL*', S.generateKey({name: 'ECDSA', namedCurve: 'P-384'}, false, ['sign']), 'NotSupportedError');
  // RFC 8439 §2.8.2.
  const ck = await S.importKey('raw', hex('808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f'), 'ChaCha20-Poly1305', false, ['encrypt', 'decrypt']);
  const pt = new TextEncoder().encode("Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.");
  const prm = {name: 'ChaCha20-Poly1305', iv: hex('070000004041424344454647'), additionalData: hex('50515253c0c1c2c3c4c5c6c7')};
  const ct = await S.encrypt(prm, ck, pt);
  ok('ChaCha20-Poly1305 RFC 8439 §2.8.2', toHex(ct).endsWith('1ae10b594f09e26a7e902ecbd0600691') && toHex(ct).startsWith('d31a8d34648e60db7b86afbc53ef7ec2'));
  ok('ChaCha20-Poly1305 decrypt', new TextDecoder().decode(await S.decrypt(prm, ck, ct)) === new TextDecoder().decode(pt));
  const ct2 = new Uint8Array(ct); ct2[0] ^= 1;
  await rejects('ChaCha20-Poly1305 forged', S.decrypt(prm, ck, ct2), 'OperationError');
  // Hostile arguments.
  await rejects('Ed25519 31-byte key', S.importKey('raw', new Uint8Array(31), 'Ed25519', true, ['verify']), 'DataError');
  await rejects('JWK x not base64url', S.importKey('jwk', {kty: 'OKP', crv: 'Ed25519', x: '+/+/'}, 'Ed25519', true, ['verify']), 'DataError');
  await rejects('JWK with no kty', S.importKey('jwk', {crv: 'Ed25519', x: 'AAAA'}, 'Ed25519', true, ['verify']), 'DataError');
  await rejects('deriveBits length NaN', S.deriveBits({name: 'X25519', public: xb}, xa, NaN), 'TypeError');
  await rejects('deriveBits length -8', S.deriveBits({name: 'X25519', public: xb}, xa, -8), 'TypeError');
  await rejects('export non-extractable', S.exportKey('raw', hk), 'InvalidAccessError');
  await rejects('export private as spki', S.exportKey('spki', edSk), 'InvalidAccessError');
  await rejects('sign with a verify key', S.sign('Ed25519', edPk, new Uint8Array(1)), 'InvalidAccessError');
  await rejects('truncated pkcs8', S.importKey('pkcs8', hex('302e020100300506032b65700422042001'), 'Ed25519', true, ['sign']), 'DataError');
  await rejects('pkcs8 long-form length (non-DER)', S.importKey('pkcs8', hex('30812e020100300506032b657004220420' + '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60'), 'Ed25519', true, ['sign']), 'DataError');
  const buf = new Uint8Array(16).buffer;
  if (typeof buf.transfer === 'function') { buf.transfer(); ok('digest of a detached buffer is of empty bytes', toHex(await S.digest('SHA-256', buf)) === 'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855'); }
  ok('a CryptoKey has no key bytes in JavaScript', Object.getOwnPropertyNames(ecSk).length === 0 && JSON.stringify(ecSk) === '{}');
})().catch(e => out.push('FAIL threw ' + e)).then(() => console.log(out.join('\n')));
`;

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
  const r=run(vectors);
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
      const w=run(wrap(work)),b=run(wrap(base));
      if(!w.logs.some(l=>l.includes("bench done")))note=" "+(w.logs.find(l=>l.includes("bench error"))??"no result");
      times.push(w.ms-b.ms);
    }
    times.sort((a,b)=>a-b);
    console.log(`${name}: ${times[Math.floor(times.length/2)].toFixed(1)} ms (median of ${reps}, page start subtracted)${note}`);
  }
}
