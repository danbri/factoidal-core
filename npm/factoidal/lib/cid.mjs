// Controlled Identifiers v1.0 (https://www.w3.org/TR/cid-1.0/):
// cidValidate and cidRetrieveVerificationMethod
// (https://github.com/danbri/factoidal/issues/1100, items 7 and 9).
//
// The engine decides everything (formal/lean4/L4Factoidal/CID/Validate.lean,
// CID/Fetch.lean, over the ops cidValidate and cidRetrieve of
// formal/lean4/Wasm/Ops/Cid.lean): the §2 checks; which URL to fetch; whether
// its scheme and addresses may be fetched (the private-address guard of the
// authorization server); whether the status and the Content-Type of the
// answer are accepted; §3.3; expiry and revocation with `now`. This file
// moves bytes: it resolves the host name the engine names, GETs the URL the
// engine names from the address the engine names, and passes the status,
// the Content-Type and the body back.
//
// ES module, no Node built-ins: the browser loads this file as it is. The
// Node and Deno host functions (name resolution, a GET pinned to one
// address) are lib/cid-node.mjs, which index.mjs passes in.

import { FactoidalError } from './errors.mjs';

// The engine names at most one resolution and one fetch; a longer loop is
// a defect, not a document.
const MAX_STEPS = 4;

/**
 * The browser host: no name resolution (a page cannot resolve names; the
 * engine then checks only IP literals and localhost names), and the page's
 * fetch, which does not follow redirects and sends no credentials.
 */
export const browserCidHost = Object.freeze({
  resolve: null,
  fetch: (url, init) => globalThis.fetch(url, {
    method: 'GET',
    headers: init.headers,
    redirect: 'manual',
    credentials: 'omit',
  }),
});

// The status, Content-Type and body of a fetch answer: a WHATWG Response,
// or an object of the same shape.
async function answerOf(url, response) {
  const status = Number(response && response.status) || 0;
  const headers = response && response.headers;
  const contentType = headers && typeof headers.get === 'function'
    ? (headers.get('content-type') || '') : '';
  const body = response && typeof response.text === 'function' ? String(await response.text()) : '';
  return { url, status, contentType, body };
}

function nowSeconds(now) {
  if (now === undefined || now === null) return undefined;
  if (now instanceof Date) return Math.floor(now.getTime() / 1000);
  if (typeof now === 'number' && Number.isFinite(now)) return Math.floor(now);
  throw new TypeError('cidRetrieveVerificationMethod: options.now must be a Date or a number of seconds');
}

/**
 * The two functions over an entry (lib/lean-entry.mjs) and a host.
 * @param {object} deps
 * @param {() => Promise<object>} deps.entry
 * @param {(jsonText: string, what: string) => object} deps.entryResult
 * @param {(e: object, fn: string, what: string) => void} deps.requireEntryFn
 * @param {{resolve: ((host: string) => Promise<string[]>)|null, fetch: Function}} [deps.host]
 */
export function cidFunctions({ entry, entryResult, requireEntryFn, host }) {
  const defaults = host || browserCidHost;

  /**
   * CID 1.0 §2: check a controlled identifier document.
   * @param {string|object} doc JSON text, or a value JSON.stringify writes
   * @returns {Promise<{valid: boolean, errors: Array<{code: string, message: string, path: string}>}>}
   */
  async function cidValidate(doc) {
    const text = typeof doc === 'string' ? doc : JSON.stringify(doc);
    if (typeof text !== 'string') throw new TypeError('cidValidate: doc must be JSON text or a JSON value');
    const e = await entry();
    requireEntryFn(e, 'cidValidate', 'CID 1.0 document check');
    const r = entryResult(e.cidValidate(text), 'cidValidate');
    return { valid: r.valid === true, errors: Array.isArray(r.errors) ? r.errors : [] };
  }

  /**
   * CID 1.0 §3.3 Retrieve Verification Method, with the fetch done here.
   * @param {string} url the verification method URL
   * @param {string} relationship a verification relationship of §2.3
   * @param {object} [options]
   * @returns {Promise<{ok: true, verificationMethod: object, controllerDocument: string}
   *                  | {ok: false, code: string, problem: {type: string, title: string, detail: string}}>}
   */
  async function cidRetrieveVerificationMethod(url, relationship, options) {
    if (typeof url !== 'string' || typeof relationship !== 'string') {
      throw new TypeError('cidRetrieveVerificationMethod: url and relationship must be strings');
    }
    const o = options || {};
    const fetchFn = typeof o.fetch === 'function' ? o.fetch : defaults.fetch;
    // `resolve: null` says the caller cannot resolve names.
    const resolveFn = 'resolve' in o ? o.resolve : defaults.resolve;
    const request = {
      vm: url,
      relationship,
      allowHttp: o.allowHttp === true,
      allowPrivateFetch: o.allowPrivateFetch === true,
      resolver: typeof resolveFn === 'function',
      resolved: [],
      fetched: [],
    };
    const now = nowSeconds(o.now);
    if (now !== undefined) request.now = now;
    const e = await entry();
    requireEntryFn(e, 'cidRetrieve', 'CID 1.0 Retrieve Verification Method');
    for (let i = 0; i < MAX_STEPS; i += 1) {
      const r = entryResult(e.cidRetrieve(JSON.stringify(request)), 'cidRetrieve');
      if (r.step === 'method') {
        return { ok: true, verificationMethod: r.verificationMethod, controllerDocument: r.controllerDocument };
      }
      if (r.step === 'error') return { ok: false, code: r.code, problem: r.problem };
      if (r.step === 'resolve') {
        let addresses = [];
        try {
          const got = await resolveFn(r.host);
          addresses = Array.isArray(got) ? got.map(String) : [];
        } catch (_error) {
          addresses = [];
        }
        request.resolved.push({ host: r.host, addresses });
      } else if (r.step === 'fetch') {
        let answer;
        try {
          const init = { method: 'GET', headers: { accept: r.accept }, redirect: 'manual' };
          if (r.address !== null && r.address !== undefined) init.address = r.address;
          answer = await answerOf(r.url, await fetchFn(r.url, init));
        } catch (_error) {
          answer = { url: r.url, status: 0, contentType: '', body: '' };
        }
        request.fetched.push(answer);
      } else {
        break;
      }
    }
    throw new FactoidalError('cidRetrieveVerificationMethod: the engine asked for more steps than one retrieval needs',
      { code: 'op.failed' });
  }

  return { cidValidate, cidRetrieveVerificationMethod };
}
