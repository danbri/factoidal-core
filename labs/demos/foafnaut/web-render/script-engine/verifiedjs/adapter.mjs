// @ts-self-types="./adapter.d.ts"
// VerifiedJS as a page script engine, behind the same session interface as QuickJS-NG
// (session.mjs): start, dispatch, timers, frame, reset. Issue 1252 and issue 1271.
//
// LICENCE: VerifiedJS has no licence file. Nothing from it is in this repository:
// fetch-verifiedjs.mjs fetches the pinned commit into the ignored .build/verifiedjs/,
// and its compiler is built there. This adapter only runs that local build.
//
// At the pin (b6eabd76) a compiled module imports only wasi_snapshot_preview1.fd_write
// and exports main, _start and memory (docs/designissues/2026-11-07-verifiedjs-page-scripts.md
// section 4). It has no host import that could reach the document, and no export that
// could deliver an event. So a page script compiles, and is then refused with that
// reason. The refusal is shown on the page and in the chrome; the setting stays.
import { VERIFIEDJS_COMMIT } from './pin.mjs';

export const VERIFIEDJS_ISSUE = 'https://github.com/danbri/factoidal/issues/1252';
const binaryURL = new URL('../../../.build/verifiedjs/.lake/build/bin/verifiedjs', import.meta.url);
const deno = globalThis.Deno;
const pin = VERIFIEDJS_COMMIT.slice(0, 8);

/** The local compiler, or undefined when it is not built. */
export function verifiedJSBinary(path = binaryURL) {
  if (!deno) return undefined;
  try { return deno.statSync(path).isFile ? (path instanceof URL ? decodeURIComponent(path.pathname) : String(path)) : undefined; }
  catch { return undefined; }
}

/** Why VerifiedJS can not run in this host, or "" when its compiler is present. */
export function verifiedJSAvailable(path = binaryURL) {
  if (!deno) return `VerifiedJS compiles page scripts with a native Lean program and has no WebAssembly build, so it can not run in a web page (${VERIFIEDJS_ISSUE})`;
  if (verifiedJSBinary(path)) return '';
  return `VerifiedJS is not built here. Its source has no licence, so it is not in this repository: run node labs/demos/foafnaut/web-render/script-engine/verifiedjs/fetch-verifiedjs.mjs, then lake build verifiedjs in labs/demos/foafnaut/.build/verifiedjs (Lean 4.29.0-rc6, about 3.6 GB with its toolchain) (${VERIFIEDJS_ISSUE})`;
}

/** The host interface of a compiled module, as text. */
export function moduleInterface(bytes) {
  const module = new WebAssembly.Module(bytes);
  return {
    imports: WebAssembly.Module.imports(module).map(i => `${i.module}.${i.name}`),
    exports: WebAssembly.Module.exports(module).map(e => e.name)
  };
}

// A module can reach the document only through a host import that answers a value;
// fd_write writes bytes and answers a count, so it is not one.
const DOM_IMPORT = /document|dom|factoidal/i;

export function createVerifiedJSSession({ binary = verifiedJSBinary() } = {}) {
  let started = false;
  const refuse = reason => { throw Error(reason); };
  return {
    get listeners() { return []; },
    get documentListeners() { return []; },
    get running() { return started; },
    async start({ sources = [] } = {}) {
      started = false;
      if (!binary) refuse(verifiedJSAvailable());
      const work = await deno.makeTempDir({ prefix: 'verifiedjs-' });
      try {
        for (const [index, source] of sources.entries()) {
          const input = `${work}/script-${index}.js`, output = `${work}/script-${index}.wasm`;
          await deno.writeTextFile(input, source);
          const run = await new deno.Command(binary, { args: [input, '-o', output], stdout: 'piped', stderr: 'piped' }).output();
          if (!run.success) {
            const message = new TextDecoder().decode(run.stderr).trim().split('\n').slice(0, 3).join(' ').slice(0, 300);
            refuse(`VerifiedJS (pin ${pin}) did not compile script ${index + 1}: ${message || 'exit ' + run.code} (${VERIFIEDJS_ISSUE})`);
          }
          const shape = moduleInterface(await deno.readFile(output));
          if (!shape.imports.some(name => DOM_IMPORT.test(name)))
            refuse(`VerifiedJS (pin ${pin}) compiled script ${index + 1}, but the module has no DOM host interface (imports: ${shape.imports.join(', ') || 'none'}; exports: ${shape.exports.join(', ')}), so the script can not reach the page (${VERIFIEDJS_ISSUE})`);
          refuse(`VerifiedJS (pin ${pin}): a module with a DOM host interface is not wired yet (${VERIFIEDJS_ISSUE})`);
        }
      } finally { await deno.remove(work, { recursive: true }).catch(() => {}); }
      refuse('VerifiedJS: the page has no classic script');
    },
    dispatch() { return Promise.reject(Error('VerifiedJS session is not running')); },
    timers() { return Promise.reject(Error('VerifiedJS session is not running')); },
    frame() { return Promise.reject(Error('VerifiedJS session is not running')); },
    reset() { started = false; }
  };
}
