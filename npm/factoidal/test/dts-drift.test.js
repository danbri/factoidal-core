// Cheap drift gate: every function/const a .d.ts DECLARES must actually
// exist on the module it types, and (the direction that bit us) every
// runtime export of the .js should be typed in its .d.ts. This is a
// regex-level structural check — not a real tsc typecheck — but it is
// enough to have caught an fn.d.ts/fn.js divergence (names exported from
// fn.js but undeclared in fn.d.ts) in 0.8.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

// Names that are declared in a .d.ts but are NOT runtime value exports
// (types/interfaces/classes-as-types), so they legitimately have no
// module.exports entry. Kept explicit so a genuinely-missing function
// can't hide behind a blanket allowlist.
const TYPE_ONLY = new Set([
  // index.d.ts type-level declarations
  'NamedNode', 'BlankNode', 'Literal', 'Variable', 'DefaultGraph', 'Quad',
  'Quad_Subject', 'Quad_Predicate', 'Quad_Object', 'Quad_Graph', 'Term',
  'DataFactory', 'DataFormat', 'EntailRegime', 'Bindings', 'DataInput',
  'ParseOptions', 'QueryOptions', 'SerializeOptions', 'ShaclValidateResult',
  'CsvwOptions', 'JsonLdOptions', 'JsonLdFromRdfOptions', 'XPathResult',
  'MathValue', 'XFormsBind', 'XFormsNodeValidity', 'SchematronFinding',
  'ToanExpr', 'MatrixCell', 'MatrixResult', 'SrjTerm', 'SparqlResultsJson',
  'OutputFormat', 'QueryInput', 'StoreReader', 'OpenStoreOptions',
  // fn.d.ts type-level declarations
  'FnDataset', 'Builder', 'ValidateResult', 'Cell', 'Derived',
  // api.d.ts type-level declarations
  'EngineSource', 'CreateApiOptions',
]);

// Parse `export function NAME` / `export const NAME` / `export class NAME`
// / `export interface NAME` / `export type NAME` from a .d.ts.
function declaredValueNames(dtsPath) {
  const src = fs.readFileSync(dtsPath, 'utf8');
  const names = new Set();
  const re = /^export\s+(?:declare\s+)?(?:async\s+)?(function|const|class)\s+([A-Za-z_$][\w$]*)/gm;
  let m;
  while ((m = re.exec(src)) !== null) {
    if (!TYPE_ONLY.has(m[2])) names.add(m[2]);
  }
  return names;
}

// `__esModule` is the interop marker require() adds when it loads an ES
// module (index.js, api.js hand index.mjs, api.mjs to require()).
function runtimeNames(mod) {
  return new Set(Object.keys(mod).filter((k) => k !== 'default' && k !== '__esModule'));
}

test('fn.d.ts declares nothing fn.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'fn.d.ts'));
  const runtime = runtimeNames(require('../fn.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `fn.d.ts declares names absent from fn.js: ${missing.join(', ')}`);
});

test('fn.js implements nothing that fn.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'fn.d.ts'));
  const runtime = runtimeNames(require('../fn.js'));
  // FnDataset is exported as a value (class) but declared as a type in
  // fn.d.ts; treat it as typed.
  const untyped = [...runtime].filter((n) => !declared.has(n) && !TYPE_ONLY.has(n));
  assert.deepEqual(untyped, [],
    `fn.js exports names undeclared in fn.d.ts: ${untyped.join(', ')}`);
});

test('index.d.ts declares nothing index.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'index.d.ts'));
  const runtime = runtimeNames(require('../index.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `index.d.ts declares names absent from index.js: ${missing.join(', ')}`);
});

test('index.js implements nothing that index.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'index.d.ts'));
  const runtime = runtimeNames(require('../index.js'));
  const untyped = [...runtime].filter((n) => !declared.has(n) && !TYPE_ONLY.has(n));
  assert.deepEqual(untyped, [],
    `index.js exports names undeclared in index.d.ts: ${untyped.join(', ')}`);
});

test('api.d.ts declares nothing api.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'api.d.ts'));
  const runtime = runtimeNames(require('../api.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `api.d.ts declares names absent from api.js: ${missing.join(', ')}`);
});

test('api.js implements nothing that api.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'api.d.ts'));
  const runtime = runtimeNames(require('../api.js'));
  const untyped = [...runtime].filter((n) => !declared.has(n) && !TYPE_ONLY.has(n));
  assert.deepEqual(untyped, [],
    `api.js exports names undeclared in api.d.ts: ${untyped.join(', ')}`);
});

test('the VC crypto surface is typed on both index.d.ts and fn.d.ts', () => {
  const vc = [
    'vcSha256Hex', 'vcEd25519SecretToPublic', 'vcEd25519Sign',
    'vcEd25519Verify', 'vcEddsaCreateFromCanonical', 'vcEddsaVerifyFromCanonical',
  ];
  const indexDecl = declaredValueNames(path.join(__dirname, '..', 'index.d.ts'));
  const fnDecl = declaredValueNames(path.join(__dirname, '..', 'fn.d.ts'));
  for (const name of vc) {
    assert.ok(indexDecl.has(name), `index.d.ts declares ${name}`);
    assert.ok(fnDecl.has(name), `fn.d.ts declares ${name}`);
  }
});

// browser.d.ts re-exports the main entry's declarations by name
// (`export { ... } from './index'`) and declares its own two functions.
function browserDeclaredNames() {
  const src = fs.readFileSync(path.join(__dirname, '..', 'browser.d.ts'), 'utf8');
  const names = declaredValueNames(path.join(__dirname, '..', 'browser.d.ts'));
  const m = /export \{([^}]*)\} from '\.\/index';/m.exec(src.replace(/export type \{[^}]*\} from '\.\/index';/m, ''));
  for (const n of m[1].split(',').map((x) => x.trim()).filter(Boolean)) names.add(n);
  return names;
}

test('browser.d.ts and browser.js declare and export the same names', async () => {
  const declared = browserDeclaredNames();
  const runtime = runtimeNames(await import('../browser.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  const untyped = [...runtime].filter((n) => !declared.has(n));
  assert.deepEqual(missing, [], `browser.d.ts declares names absent from browser.js: ${missing.join(', ')}`);
  assert.deepEqual(untyped, [], `browser.js exports names undeclared in browser.d.ts: ${untyped.join(', ')}`);
});

test('browser.js exports the main entry minus the Node-only names, plus setAssetsUrl/getAssetsUrl', async () => {
  const browser = runtimeNames(await import('../browser.js'));
  const main = runtimeNames(require('../index.js'));
  const nodeOnly = new Set(['sampleStorePath', 'sampleStoreFacts']);
  const browserOnly = new Set(['setAssetsUrl', 'getAssetsUrl']);
  assert.deepEqual([...main].filter((n) => !nodeOnly.has(n) && !browser.has(n)), []);
  assert.deepEqual([...browser].filter((n) => !browserOnly.has(n) && !main.has(n)), []);
});

test('l4.d.ts and l4-core.d.ts re-export index.d.ts, and the modules are the main entry', () => {
  for (const f of ['l4.d.ts', 'l4-core.d.ts']) {
    const src = fs.readFileSync(path.join(__dirname, '..', f), 'utf8');
    assert.match(src, /^export \* from '\.\/index';$/m, f);
  }
  assert.equal(require('../l4.js'), require('../index.js'));
  assert.equal(require('../l4-core.js'), require('../index.js'));
});

test('lib/version.mjs carries package.json version', async () => {
  const { version } = await import('../lib/version.mjs');
  assert.equal(version, require('../package.json').version);
});
