// Loading the Lean engine (L4Factoidal compiled to WebAssembly) for the
// `factoidal` command, under Node and under Deno.
// https://github.com/danbri/factoidal/issues/641
//
// This file resolves three files that must stay together and keep their
// names -- l4factoidal.js, l4factoidal.mjs and l4factoidal.wasm -- and
// imports the loader. The core engine (`@factoidal/core/core`, issue 713
// stage 4) is the same three files under the name l4factoidal-core; every
// function here takes the name, 'l4factoidal' (the full engine) by default. The Emscripten glue resolves the .wasm sidecar from
// its own basename, so a rename breaks the load on every runtime
// (skills/lean4-wasm-export, "the naming trap").
//
// The library entries (`index.mjs`, `browser.js`) load the engine their
// own way; this file stays free of require() so the command loads under
// Deno without the CommonJS compatibility path.
//
// WHAT THIS FILE IS ALLOWED TO DO
// Find the engine, load it, and turn bytes into the hexadecimal string
// two of the three store operations take as their small argument. It
// makes no format decision: it never parses a manifest, verifies a
// digest, decodes a block, or chooses an artifact.

import { readWhole } from '../store-host/index.mjs'
import { fileUrlToPath, joinPath } from '../store-host/paths.mjs'

/** Read one environment variable, or null where reading it is refused. */
function environment (name) {
  try {
    if (typeof globalThis.Deno !== 'undefined' && globalThis.Deno.env) {
      const value = globalThis.Deno.env.get(name)
      return typeof value === 'string' && value.length > 0 ? value : null
    }
  } catch (_error) {
    // Deno without --allow-env. An absent override is the normal case.
    return null
  }
  const value = globalThis.process && globalThis.process.env
    ? globalThis.process.env[name]
    : undefined
  return typeof value === 'string' && value.length > 0 ? value : null
}

function readable (path) {
  try {
    readWhole(path)
    return true
  } catch (_error) {
    return false
  }
}

/** The package directory that holds this command. */
export function packageDirectory () {
  return fileUrlToPath(new URL('..', import.meta.url).href).replace(/\/$/, '')
}

/** The two engines: the full module and the core module (issue 713 stage 4). */
export const ENGINE_NAMES = Object.freeze(['l4factoidal', 'l4factoidal-core'])

function checkName (name) {
  if (!ENGINE_NAMES.includes(name)) {
    throw new TypeError(`unknown engine '${name}' (expected one of ${ENGINE_NAMES.join(', ')})`)
  }
  return name
}

/**
 * The loader file of the first engine source that exists, or null.
 *
 * Order, first hit wins:
 *   1. this package's own l4-assets/ (what `npm install` gives);
 *   2. $FACTOIDAL_L4_ASSETS (a custom deployment);
 *   3. the repository checkout layout, docs/web/hub/assets/l4/.
 *
 * @param {string} [name] 'l4factoidal' (the full engine) or 'l4factoidal-core'
 */
export function resolveEngine (name = 'l4factoidal') {
  checkName(name)
  const inPackage = joinPath(packageDirectory(), `l4-assets/${name}.js`)
  if (readable(inPackage)) return inPackage
  const override = environment('FACTOIDAL_L4_ASSETS')
  if (override !== null) {
    const path = joinPath(override, `${name}.js`)
    if (readable(path)) return path
    throw new Error(`FACTOIDAL_L4_ASSETS=${override} holds no ${name}.js`)
  }
  const inCheckout = joinPath(packageDirectory(),
    `../../docs/web/hub/assets/l4/${name}.js`)
  if (readable(inCheckout)) return inCheckout
  return null
}

const enginePromises = new Map()

/**
 * Load an engine once per process and return its handle: `call(op, args)`,
 * `callBlob(op, args, bytes)`, `callBlobIO(op, args, bytes)`.
 *
 * @param {string} [name] 'l4factoidal' (the full engine) or 'l4factoidal-core'
 */
export function loadEngine (name = 'l4factoidal') {
  checkName(name)
  if (enginePromises.has(name)) return enginePromises.get(name)
  const promise = (async () => {
    const loaderPath = resolveEngine(name)
    if (loaderPath === null) {
      throw new Error(
        `the Lean engine assets are missing (${name}). They normally ship in this ` +
        "package's own l4-assets/ directory; if it is absent this install " +
        'is incomplete. Otherwise set FACTOIDAL_L4_ASSETS to a directory ' +
        `holding ${name}.js, ${name}.mjs and ${name}.wasm.`)
    }
    const url = loaderPath.startsWith('file://')
      ? loaderPath
      : 'file://' + encodeURI(loaderPath).replace(/#/g, '%23')
    const module = await import(url)
    return module.loadL4()
  })()
  enginePromises.set(name, promise)
  return promise
}

const HEX = (() => {
  const table = new Array(256)
  for (let byte = 0; byte < 256; byte += 1) {
    table[byte] = byte.toString(16).padStart(2, '0')
  }
  return table
})()

/**
 * Lowercase hexadecimal of a byte array. This is a transport encoding for
 * the manifest argument of `storeManifestInspect` and `storeQueryPlan`,
 * not an interpretation of the bytes. Artifact bytes never take this
 * path: they cross raw through `callBlob`.
 * @param {Uint8Array} bytes
 * @returns {string}
 */
export function hexOfBytes (bytes) {
  const parts = new Array(bytes.length)
  for (let index = 0; index < bytes.length; index += 1) parts[index] = HEX[bytes[index]]
  return parts.join('')
}
