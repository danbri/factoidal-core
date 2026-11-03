// The Node and Deno host of cidRetrieveVerificationMethod (lib/cid.mjs,
// https://github.com/danbri/factoidal/issues/1100 item 9): name resolution,
// and a GET that connects to the one address the engine chose, so a second
// answer of a name server cannot move the request (the authorization
// server's fetch, authz/server.mjs). Pure I/O: the engine decides which
// URL, which address, and what the answer means
// (formal/lean4/L4Factoidal/CID/Fetch.lean). No redirect is followed.

const FETCH_TIMEOUT_MS = 10000;
const MAX_DOCUMENT_BYTES = 1048576;

/** Every address of a name, as the system resolver gives them. */
async function resolve(host) {
  try {
    const dns = await import('node:dns');
    const found = await dns.promises.lookup(host, { all: true, verbatim: true });
    return found.map((a) => a.address);
  } catch (_error) {
    return [];
  }
}

// A Response-like answer: status, headers.get, text().
function answer(status, contentType, body) {
  return {
    status,
    headers: { get: (name) => (String(name).toLowerCase() === 'content-type' ? contentType : null) },
    text: async () => body,
  };
}

/**
 * GET `url` from `init.address`, sending `init.headers`. With no address
 * (the engine named none), the system resolver connects.
 */
async function fetch(url, init) {
  let target;
  try {
    target = new URL(url);
  } catch (_error) {
    return answer(0, '', '');
  }
  const mod = target.protocol === 'https:' ? await import('node:https') : await import('node:http');
  const address = init && typeof init.address === 'string' ? init.address : null;
  const family = address && address.indexOf(':') >= 0 ? 6 : 4;
  const options = { method: 'GET', headers: (init && init.headers) || {}, timeout: FETCH_TIMEOUT_MS };
  if (address) {
    options.lookup = (_host, opts, callback) => {
      if (opts && opts.all) callback(null, [{ address, family }]);
      else callback(null, address, family);
    };
  }
  return new Promise((done) => {
    const request = mod.request(target, options, (response) => {
      const chunks = [];
      let size = 0;
      response.on('data', (chunk) => {
        size += chunk.length;
        if (size > MAX_DOCUMENT_BYTES) {
          response.destroy();
          done(answer(0, '', ''));
          return;
        }
        chunks.push(chunk);
      });
      response.on('end', () => done(answer(response.statusCode || 0,
        String(response.headers['content-type'] || ''), Buffer.concat(chunks).toString('utf8'))));
      response.on('error', () => done(answer(0, '', '')));
    });
    request.on('timeout', () => request.destroy(new Error('timeout')));
    request.on('error', () => done(answer(0, '', '')));
    request.end();
  });
}

/** The host index.mjs passes to the API. */
export const nodeCidHost = Object.freeze({ resolve, fetch });
