// Reference run of the same module in Node: node labs/demos/foafnaut/tor-wasm/node-ref.cjs [timeoutMs]
const fs = require('fs'), path = require('path'), dir = path.join(__dirname, '.build');
global.self = global;
require('vm').runInThisContext(fs.readFileSync(path.join(dir, 'foafnaut_tor_wasm.js'), 'utf8') + ';globalThis.wasm_bindgen=wasm_bindgen;');
(async () => {
  await wasm_bindgen({ module_or_path: fs.readFileSync(path.join(dir, 'foafnaut_tor_wasm_bg.wasm')) });
  const t = Date.now();
  await wasm_bindgen.bootstrap(Number(process.argv[2] || 15000));
  console.log('wall ms ' + (Date.now() - t));
  process.exit(0);
})().catch(e => { console.log('error ' + e); process.exit(1); });
