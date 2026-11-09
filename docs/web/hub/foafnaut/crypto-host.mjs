// crypto-host.mjs — the primitives of crypto.subtle for a page on the Hub, done by the
// browser's own crypto.subtle. Lean (WebApi host mode) has already made every WebCrypto
// decision for the operation (the registry, usages, extractability, key types, the JWK
// members, the error of each refusal); a request here is only the primitive. Keys are the
// browser's CryptoKey objects in this table: the page and Lean see a number, and the bytes
// of a non-extractable key never enter WebAssembly memory.
// Record: docs/designissues/2026-11-09-hacl-web-crypto.md, "The Hub".
//
// A request: {id, op, ...}; bytes are {"$b": base64url}, a key in an algorithm member is
// {"$key": n}. The answer: {bytes}, {bool}, {jwk}, {key}, {pair: [public, private]}, or
// {error: DOMException name}. `drop` answers nothing.

const b64 = {
  dec(s) {
    const t = s.replace(/-/g, '+').replace(/_/g, '/');
    const bin = atob(t + '='.repeat((4 - t.length % 4) % 4));
    const u = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i);
    return u;
  },
  enc(buf) {
    const u = new Uint8Array(buf);
    let s = '';
    for (let i = 0; i < u.length; i += 0x8000) s += String.fromCharCode(...u.subarray(i, i + 0x8000));
    return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  },
};

export function cryptoHost(subtle = globalThis.crypto?.subtle) {
  const keys = new Map();
  let next = 1;
  const conv = v => {
    if (v === null || typeof v !== 'object' || Array.isArray(v)) return v;
    if ('$b' in v) return b64.dec(v.$b);
    if ('$key' in v) { const k = keys.get(v.$key); if (!k) throw new DOMException('no such key', 'InvalidAccessError'); return k; }
    const o = {};
    for (const [k, x] of Object.entries(v)) o[k] = conv(x);
    return o;
  };
  const key = h => { const k = keys.get(h); if (!k) throw new DOMException('no such key', 'InvalidAccessError'); return k; };
  const keyJson = k => {
    const h = next++;
    keys.set(h, k);
    const a = { ...k.algorithm };
    if (a.hash) a.hash = { name: a.hash.name };
    if (a.publicExponent) a.publicExponent = b64.enc(a.publicExponent);
    return { h, type: k.type, extractable: k.extractable, algorithm: a, usages: [...k.usages] };
  };
  async function run(r) {
    try {
      switch (r.op) {
        case 'drop': keys.delete(r.key); return null;
        case 'digest': return { bytes: b64.enc(await subtle.digest(conv(r.algorithm), conv(r.data))) };
        case 'generateKey': {
          const k = await subtle.generateKey(conv(r.algorithm), r.extractable, r.usages);
          return k.publicKey ? { pair: [keyJson(k.publicKey), keyJson(k.privateKey)] } : { key: keyJson(k) };
        }
        case 'importKey':
          return { key: keyJson(await subtle.importKey(r.format, r.format === 'jwk' ? r.keyData : conv(r.keyData),
            conv(r.algorithm), r.extractable, r.usages)) };
        case 'exportKey': {
          const x = await subtle.exportKey(r.format, key(r.key));
          return r.format === 'jwk' ? { jwk: x } : { bytes: b64.enc(x) };
        }
        case 'sign': return { bytes: b64.enc(await subtle.sign(conv(r.algorithm), key(r.key), conv(r.data))) };
        case 'verify': return { bool: await subtle.verify(conv(r.algorithm), key(r.key), conv(r.signature), conv(r.data)) };
        case 'encrypt': return { bytes: b64.enc(await subtle.encrypt(conv(r.algorithm), key(r.key), conv(r.data))) };
        case 'decrypt': return { bytes: b64.enc(await subtle.decrypt(conv(r.algorithm), key(r.key), conv(r.data))) };
        case 'deriveBits': return { bytes: b64.enc(await subtle.deriveBits(conv(r.algorithm), key(r.baseKey), r.length)) };
        case 'deriveKey':
          return { key: keyJson(await subtle.deriveKey(conv(r.algorithm), key(r.baseKey), conv(r.derivedKeyType),
            r.extractable, r.usages)) };
        case 'wrapKey':
          return { bytes: b64.enc(await subtle.wrapKey(r.format, key(r.key), key(r.wrappingKey), conv(r.algorithm))) };
        case 'unwrapKey':
          return { key: keyJson(await subtle.unwrapKey(r.format, conv(r.wrappedKey), key(r.unwrappingKey),
            conv(r.algorithm), conv(r.unwrappedKeyAlgorithm), r.extractable, r.usages)) };
        default: return { error: 'NotSupportedError' };
      }
    } catch (e) {
      return { error: e?.name ?? 'OperationError' };
    }
  }
  return { run, clear: () => keys.clear(), get size() { return keys.size; } };
}

/** Answer the crypto requests of a turn, then the next turn's, until none is left.
 * `act(request)` runs one scriptSession action and returns the turn; `onTurn(turn)` sees
 * each turn. For hosts that wait for each answer (tests, the WPT runner).
 * @param {{run: (r: any) => Promise<any>}} host
 * @param {any} turn
 * @param {(r: any) => any} act
 * @param {(t: any) => unknown} [onTurn] */
export async function settleCrypto(host, turn, act, onTurn = (_t) => {}) {
  const queue = [...(turn?.crypto ?? [])];
  let last = turn;
  while (queue.length) {
    const r = queue.shift();
    const answer = await host.run(r);
    if (r.op === 'drop') continue;
    last = act({ action: 'crypto', id: r.id, answer });
    onTurn(last);
    queue.push(...(last?.crypto ?? []));
  }
  return last;
}
