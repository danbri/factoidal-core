import {buildSignalMixer, integrationSource, standaloneHtml} from './example.mjs';

const MAX_EDITOR_WORDS = 4096;
const PREVIEW_WORDS = 128;
const CHART_WORDS = 64;
const pretty = value => JSON.stringify(value, null, 2);
const ms = value => Number.isFinite(value) ? `${value.toFixed(1)} ms` : '—';

// Page controls and display only. The public API constructs and executes the PVGraph.
export function mountGdslApp({document: doc = globalThis.document,
  loadModule = url => import(url)} = {}) {
  const $ = id => doc.getElementById(id);
  const win = doc.defaultView ?? globalThis;
  const now = () => globalThis.performance.now();
  let api, core, runtime, busy = false, validSource = true, lastReport;

  function element(tag, text) {
    const node = doc.createElement(tag);
    if (text !== undefined) node.textContent = String(text);
    return node;
  }
  function status(id, text, kind = '') {
    $(id).textContent = text;
    $(id).dataset.kind = kind;
  }
  function controls() {
    for (const node of doc.querySelectorAll('input, select, textarea, button')) node.disabled = busy;
    for (const id of ['package-url', 'assets-url']) $(id).disabled = busy || !!core;
    $('save-report').disabled = busy || !lastReport;
    $('copy-code').disabled = busy || !validSource;
    $('download-app').disabled = busy || !validSource;
    $('run-status').setAttribute('aria-busy', String(busy));
  }
  function words(id, label) {
    const text = $(id).value;
    if (text.length > 65536) throw new Error(`${label} exceeds this editor's text limit.`);
    let value;
    try { value = JSON.parse(text); }
    catch { throw new Error(`${label} must be a JSON array.`); }
    if (!Array.isArray(value) || value.length > MAX_EDITOR_WORDS)
      throw new Error(`${label} must contain 0–${MAX_EDITOR_WORDS.toLocaleString()} words in this editor.`);
    if (!value.every(n => Number.isInteger(n) && n >= 0 && n <= 0xffffffff))
      throw new Error(`${label} needs unsigned integers from 0 to 4294967295.`);
    return value;
  }
  function integer(id, label, maximum) {
    const text = $(id).value.trim(), value = Number(text);
    if (!text || !Number.isSafeInteger(value) || value < 0 || value > maximum)
      throw new Error(`${label} must be an integer from 0 to ${maximum}.`);
    return value;
  }
  function settings() {
    return {gain: integer('gain', 'Gain', 0xffffffff),
      bindings: {a: words('input-a', 'Input A'), b: words('input-b', 'Input B')},
      mode: $('execution-mode').value,
      minWords: integer('minimum-words', 'Minimum words', 4194240)};
  }
  function updateSource() {
    try {
      $('integration-code').textContent = integrationSource(settings());
      validSource = true;
      status('code-status', 'Complete module for the current inputs. Imports use your local vendor/factoidal directory.');
    } catch (error) {
      validSource = false;
      $('integration-code').textContent = 'Correct the inputs to generate the integration example.';
      status('code-status', error.message, 'error');
    }
    controls();
  }
  function emptyResults(message) {
    lastReport = undefined;
    for (const id of ['backend', 'dispatches', 'wall-ms', 'mixed-range', 'cumulative-range']) $(id).textContent = '—';
    $('mixed-chart').replaceChildren();
    $('cumulative-chart').replaceChildren();
    const row = element('tr'), cell = element('td', message);
    cell.colSpan = 5;
    row.append(cell);
    $('result-rows').replaceChildren(row);
    $('pvgraph-json').textContent = 'No PVGraph for these settings.';
    $('execution-json').textContent = 'No completed execution for these settings.';
    $('preview-note').textContent = 'The charts display returned words; no JavaScript evaluator computes them.';
    status('agreement', message);
    $('placement').textContent = 'Each GPU run compares its complete output with the built-in CPU evaluator.';
  }
  function changed() {
    emptyResults('Inputs changed. Run again to see their result.');
    status('run-status', 'Ready to run the current inputs.');
    updateSource();
  }
  function localDirectory(value, label) {
    const url = new URL(value.endsWith('/') ? value : `${value}/`, win.location.href);
    if (!['http:', 'https:'].includes(url.protocol) || url.origin !== win.location.origin)
      throw new Error(`${label} must be served from this page's HTTP origin.`);
    return url.href;
  }
  async function loadRuntime() {
    if (core) return {api, core};
    status('runtime-status', 'Loading the local modules and matching Wasm…');
    try {
      const base = localDirectory($('package-url').value.trim(), 'The package directory');
      const assetInput = $('assets-url').value.trim();
      const assets = assetInput ? localDirectory(assetInput, 'The assets directory') : null;
      const started = now();
      const [nextApi, nextCore] = await Promise.all([
        loadModule(new URL('gdsl.mjs', base).href),
        loadModule(new URL('browser.js', base).href)
      ]);
      for (const name of ['createPVGraphWasm', 'runPVGraph'])
        if (typeof nextApi[name] !== 'function') throw new Error(`The local GDSL module is missing ${name}().`);
      if (typeof nextCore.loadEngine !== 'function') throw new Error('The local browser module is missing loadEngine().');
      if (assets) {
        if (typeof nextCore.setAssetsUrl !== 'function') throw new Error('The local browser module cannot select an assets directory.');
        nextCore.setAssetsUrl(assets);
      }
      const engine = await nextCore.loadEngine();
      const operations = engine.call('ops', []);
      for (const name of ['pvgraphBuild', 'pvgraphAdmit', 'pvgraphEvaluate', 'pvgraphGpuPlan'])
        if (!operations?.ops?.includes(name)) throw new Error(`The Wasm build is missing ${name}. Use a matching current runtime.`);
      runtime = {packageUrl: base, assetsUrl: nextCore.getAssetsUrl?.() ?? assets,
        loadMs: now() - started, engineVersion: engine.version?.()};
      api = nextApi;
      core = nextCore;
      status('runtime-status', `Local runtime ready · ${ms(runtime.loadMs)} to load.`, 'success');
      return {api, core};
    } catch (error) {
      status('runtime-status', error.message || String(error), 'error');
      throw error;
    }
  }
  function chart(id, rangeId, values) {
    const shown = values.slice(0, CHART_WORDS), maximum = Math.max(0, ...shown);
    $(id).replaceChildren();
    for (const [i, value] of shown.entries()) {
      const bar = element('span');
      bar.style.height = `${maximum ? Math.max(1, value / maximum * 100) : 1}%`;
      bar.title = `${i}: ${value}`;
      $(id).append(bar);
    }
    $(rangeId).textContent = shown.length ? `0–${maximum.toLocaleString()}` : 'Empty buffer';
  }
  function showResult(report) {
    const {request, execution} = report;
    const {mixed, cumulative} = execution.outputs;
    if (!Array.isArray(mixed) || !Array.isArray(cumulative))
      throw new Error('The runtime returned an unexpected output shape.');
    const gpu = execution.status === 'gpu-observed';
    $('backend').textContent = gpu ? 'WebGPU' : 'CPU';
    $('dispatches').textContent = String(execution.dispatches);
    $('wall-ms').textContent = ms(execution.wallMs);
    status('agreement', gpu
      ? execution.verifiedAgainstLeanWasm ? 'All GPU output words matched the CPU reference.' : 'GPU output returned without a reference comparison.'
      : 'Completed with the built-in CPU reference evaluator.', 'success');
    $('placement').textContent = execution.reason ?? 'The engine emitted a GPU plan. Dispatch count includes scan passes.';
    chart('mixed-chart', 'mixed-range', mixed);
    chart('cumulative-chart', 'cumulative-range', cumulative);
    $('preview-note').textContent = `${mixed.length.toLocaleString()} words per output. Charts show the first ${Math.min(CHART_WORDS, mixed.length)}; table shows the first ${Math.min(PREVIEW_WORDS, mixed.length)}. The saved report contains both complete outputs.`;
    $('result-rows').replaceChildren();
    for (let i = 0; i < Math.min(mixed.length, PREVIEW_WORDS); i++) {
      const row = element('tr');
      for (const value of [i, request.bindings.a[i], request.bindings.b[i], mixed[i], cumulative[i]])
        row.append(element('td', value));
      $('result-rows').append(row);
    }
    if (!mixed.length) {
      const row = element('tr'), cell = element('td', 'Both output buffers are empty.');
      cell.colSpan = 5;
      row.append(cell);
      $('result-rows').append(row);
    }
    $('pvgraph-json').textContent = pretty(report.pvgraph);
    const {outputs, ...metadata} = execution;
    $('execution-json').textContent = pretty({runtime: report.runtime, ...metadata});
  }
  async function run() {
    if (busy) return;
    emptyResults('Running the current inputs…');
    busy = true;
    controls();
    status('run-status', 'Building and running the PVGraph…');
    try {
      const request = settings();
      await new Promise(resolve => setTimeout(resolve, 0));
      const {api: gdsl, core: browser} = await loadRuntime();
      const started = now();
      const {builder, pvgraph} = await buildSignalMixer({
        createPVGraphWasm: gdsl.createPVGraphWasm,
        loadEngine: browser.loadEngine, gain: request.gain
      });
      const answer = request.mode === 'cpu'
        ? {status: 'lean-reference', dispatches: 0, reason: 'CPU mode selected.',
          outputs: await builder.evaluate(pvgraph, request.bindings)}
        : await gdsl.runPVGraph({pvgraph, bindings: request.bindings,
          loadEngine: browser.loadEngine, requireGPU: request.mode === 'gpu',
          minWords: request.minWords, verifyWithLean: true});
      const report = {format: 'factoidal-gdsl-app/1', capturedAt: new Date().toISOString(),
        runtime, request, pvgraph, execution: {...answer, wallMs: now() - started}};
      showResult(report);
      lastReport = report;
      status('run-status', 'Computation complete.', 'success');
      return report;
    } catch (error) {
      emptyResults('No result returned. Correct the input or choose another execution mode.');
      status('run-status', error.message || String(error), 'error');
    } finally {
      busy = false;
      controls();
    }
  }
  function download(filename, content, type) {
    const url = win.URL.createObjectURL(new Blob([content], {type}));
    const link = element('a');
    link.href = url;
    link.download = filename;
    doc.body.append(link);
    link.click();
    link.remove();
    setTimeout(() => win.URL.revokeObjectURL(url), 1000);
  }

  $('run-example').addEventListener('click', run);
  $('load-sample').addEventListener('click', () => {
    const count = Number($('sample-size').value);
    $('input-a').value = pretty(count === 8 ? [2, 3, 5, 7, 11, 13, 17, 19]
      : Array.from({length: count}, (_, i) => i % 31 + 1));
    $('input-b').value = pretty(count === 8 ? [1, 4, 1, 5, 9, 2, 6, 5]
      : Array.from({length: count}, (_, i) => i % 7));
    changed();
  });
  for (const id of ['input-a', 'input-b', 'gain', 'execution-mode', 'minimum-words'])
    $(id).addEventListener('input', changed);
  for (const id of ['input-a', 'input-b']) $(id).addEventListener('keydown', event => {
    if (event.key === 'Enter' && (event.ctrlKey || event.metaKey)) {
      event.preventDefault();
      run();
    }
  });
  $('copy-code').addEventListener('click', async () => {
    try {
      await win.navigator.clipboard.writeText(integrationSource(settings()));
      status('code-status', 'JavaScript module copied.', 'success');
    } catch {
      status('code-status', 'Clipboard unavailable. Select and copy the complete module below.');
      $('integration-code').focus();
    }
  });
  $('download-app').addEventListener('click', () => {
    download('gdsl-example.html', standaloneHtml(settings()), 'text/html');
    status('code-status', 'Standalone HTML downloaded. Put vendor/factoidal beside it and serve the directory.', 'success');
  });
  $('save-report').addEventListener('click', () => {
    if (lastReport) download('gdsl-run-report.json', pretty(lastReport), 'application/json');
  });
  updateSource();
  return {run, loadRuntime, get report() { return lastReport; }};
}

if (globalThis.document?.getElementById('run-example')) mountGdslApp();
