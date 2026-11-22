// An application recipe built entirely through the public GDSL API.
// This module has no DOM dependency and no arithmetic evaluator.
export async function buildSignalMixer({createPVGraphWasm, loadEngine, gain = 3}) {
  const builder = await createPVGraphWasm(loadEngine);
  const a = builder.input('a', 'buffer<u32>', {id: 'input_a'});
  const b = builder.input('b', 'buffer<u32>', {id: 'input_b'});
  const amplified = builder.op('u32.map.mul', {x: a}, {value: gain},
    {resultType: 'buffer<u32>', id: 'amplify'});
  const mixed = builder.op('u32.zip.add', {a: amplified, b}, {},
    {resultType: 'buffer<u32>', id: 'mix'});
  const cumulative = builder.op('u32.scan.sum', {x: mixed}, {},
    {resultType: 'buffer<u32>', id: 'accumulate'});
  builder.output('mixed', mixed, {id: 'mixed_output'});
  builder.output('cumulative', cumulative, {id: 'cumulative_output'});
  return {builder, pvgraph: await builder.build()};
}

// The displayed and downloadable program embeds the actual recipe above.
// Its relative imports work in an independent app with the package at vendor/.
export function integrationSource({gain = 3, bindings, mode = 'auto',
  minWords = 0, dynamicImports = false} = {}) {
  const imports = dynamicImports
    ? "const {createPVGraphWasm, runPVGraph} = await import('./vendor/factoidal/gdsl.mjs');\n" +
      "const {loadEngine} = await import('./vendor/factoidal/browser.js');"
    : "import {createPVGraphWasm, runPVGraph} from './vendor/factoidal/gdsl.mjs';\n" +
      "import {loadEngine} from './vendor/factoidal/browser.js';";
  const execution = mode === 'cpu'
    ? "const result = {\n  status: 'lean-reference', dispatches: 0,\n  outputs: await builder.evaluate(pvgraph, bindings)\n};"
    : `const result = await runPVGraph({\n  pvgraph, bindings, loadEngine,\n  requireGPU: ${mode === 'gpu'},\n  // Diagnostic threshold: try even small inputs; the API default is 1024.\n  minWords: ${JSON.stringify(minWords)},\n  verifyWithLean: true\n});`;
  return `${imports}\n\n${buildSignalMixer.toString()}\n\n` +
    `const {builder, pvgraph} = await buildSignalMixer({\n  createPVGraphWasm, loadEngine, gain: ${JSON.stringify(gain)}\n});\n` +
    `const bindings = ${JSON.stringify(bindings, null, 2)};\n\n${execution}\n\n` +
    "console.log(result.status, result.outputs);\n";
}

export function standaloneHtml(settings) {
  const source = integrationSource({...settings, dynamicImports: true})
    .replace(/<\/script/gi, '<\\/script');
  return `<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>GDSL in my app</title>
<style>body{font:16px/1.5 system-ui;max-width:70ch;margin:2rem auto;padding:0 1rem}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:#f1f4f7;padding:1rem}a{color:#145aa3}</style>
<h1>GDSL in my app</h1>
<p>This page loads <code>./vendor/factoidal/</code>. Serve it from localhost or HTTPS.</p>
<pre id="result" role="status">Loading the local engine…</pre>
<script type="module">
try {
${source}
document.getElementById('result').textContent = JSON.stringify(result, null, 2);
} catch (error) {
  document.getElementById('result').textContent = 'Run failed: ' + (error.message || error) + '\\nCheck the console and the local vendor/factoidal/ files.';
}
</script>
</html>\n`;
}
