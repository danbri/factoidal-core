import { queries, sampleDataset } from './fixtures.mjs';

const displayRows = 200;
const graphPreviewChars = 65536;
const ms = value => Number.isFinite(value) ? `${value.toFixed(1)} ms` : '—';
const count = value => Number.isFinite(value) ? value.toLocaleString() : '—';
const json = value => JSON.stringify(value, null, 2);

// Display and host interaction only. Every parse, query, placement decision,
// readback check and graph-isomorphism comparison is the shipping API's.
// The injectable module loader lets the UI smoke test use that same API.
export function mountGpuSparql({ document: doc = globalThis.document,
  loadModule = url => import(url) } = {}) {
  const $ = id => doc.getElementById(id);
  const location = doc.defaultView?.location ?? globalThis.location;
  const now = () => globalThis.performance.now();
  let core, runtimeInfo, dataset, parsedText, parsedFormat, busy = false;
  let sourceName = 'Bundled people and projects', lastReport = null;

  function element(tag, text) {
    const node = doc.createElement(tag);
    if (text !== undefined) node.textContent = String(text);
    return node;
  }
  function status(id, message, kind = '') {
    $(id).textContent = message;
    $(id).dataset.kind = kind;
  }
  function controls() {
    for (const node of doc.querySelectorAll('input, select, textarea, button')) node.disabled = busy;
    for (const id of ['runtime-module', 'runtime-assets', 'load-runtime']) $(id).disabled = busy || !!core;
    $('download-report').disabled = busy || !lastReport;
    $('status').setAttribute('aria-busy', String(busy));
  }
  async function action(work) {
    if (busy) return;
    busy = true;
    controls();
    try {
      // Let the browser paint the pending state before synchronous Wasm work.
      await new Promise(resolve => setTimeout(resolve, 0));
      return await work();
    } catch (error) {
      status('status', String(error?.message || error), 'error');
      if ($('result-view').dataset.state === 'pending') {
        $('result-view').dataset.state = 'refused';
        $('result-view').replaceChildren(element('p', 'No answer returned. See the refusal above.'));
        $('result-json').textContent = 'No answer returned.';
        $('backend-status').textContent = 'Query did not complete.';
      }
    } finally {
      busy = false;
      controls();
    }
  }
  function localUrl(value, label) {
    const url = new URL(value, location.href);
    if (!['http:', 'https:'].includes(url.protocol) || url.origin !== location.origin)
      throw new Error(`${label} must be served from this page's HTTP origin. Serve the Hub and your local build together.`);
    return url.href;
  }
  async function loadRuntime() {
    if (core) return core;
    status('runtime-status', 'Loading the local module and Wasm engine…');
    try {
      const moduleUrl = localUrl($('runtime-module').value.trim(), 'The module');
      const assetInput = $('runtime-assets').value.trim();
      const assetsUrl = assetInput ? localUrl(assetInput, 'The assets directory') : null;
      const started = now();
      const api = await loadModule(moduleUrl);
      for (const name of ['ready', 'parse', 'query', 'stages', 'loadEngine', 'isomorphic']) {
        if (typeof api[name] !== 'function') throw new Error(`The local module is missing ${name}(). Use the matching browser.js and full Wasm build.`);
      }
      if (assetsUrl) {
        if (typeof api.setAssetsUrl !== 'function') throw new Error('This module does not support a separate assets directory.');
        api.setAssetsUrl(assetsUrl);
      }
      await api.ready();
      const engine = await api.loadEngine();
      const operations = engine.call('ops', []);
      for (const name of ['datasetQueryGpuBegin', 'datasetQueryGpuStep', 'datasetQueryGpuRestart', 'datasetQueryGpuClose']) {
        if (!operations?.ops?.includes(name)) throw new Error(`The loaded Wasm build is missing ${name}. Rebuild the engine from the mixed-SPARQL source; updating JavaScript alone is insufficient.`);
      }
      const stage = (await api.stages()).find(item => item.name === 'gpuSparqlStage');
      if (!stage?.runnable || !stage?.bound) throw new Error('The loaded runtime has no runnable, bound gpuSparqlStage in its registry.');
      runtimeInfo = {
        module: moduleUrl, assets: api.getAssetsUrl?.() ?? assetsUrl,
        packageVersion: api.version, engineVersion: engine.version?.(),
        loadMs: now() - started, registry: stage
      };
      core = api;
      $('runtime-info').textContent = json(runtimeInfo);
      $('registry-json').textContent = json(stage);
      status('runtime-status', `Local runtime ready · package ${api.version ?? 'version not reported'} · ${ms(runtimeInfo.loadMs)} to load · GPU stage registered.`, 'success');
      return core;
    } catch (error) {
      status('runtime-status', String(error?.message || error), 'error');
      throw error;
    }
  }
  function dirtyDataset(message = 'Source changed. The next run will parse it in the engine.') {
    status('dataset-status', message);
  }
  async function loadDataset() {
    const api = await loadRuntime();
    const text = $('dataset-text').value, format = $('dataset-format').value;
    if (dataset && text === parsedText && format === parsedFormat) return dataset;
    status('dataset-status', 'Parsing the RDF source…');
    const started = now();
    try {
      const next = await api.parse(text, format ? { format } : {});
      dataset?.dispose();
      dataset = next;
      parsedText = text;
      parsedFormat = format;
      status('dataset-status', `${count(dataset.size)} quads loaded · ${ms(now() - started)} to parse · ${sourceName}.`, 'success');
      return dataset;
    } catch (error) {
      status('dataset-status', String(error?.message || error), 'error');
      throw error;
    }
  }
  function useSample() {
    $('dataset-text').value = sampleDataset(Number($('sample-size').value));
    $('dataset-format').value = 'turtle';
    sourceName = `Bundled sample with ${count(Number($('sample-size').value))} people`;
    dirtyDataset(`${sourceName}. Parse the dataset or run a query.`);
  }
  function options() {
    const result = { execution: $('execution-mode').value };
    for (const [id, key] of [['gpu-min-rows', 'gpuMinRows'], ['gpu-max-pairs', 'gpuMaxPairs']]) {
      const text = $(id).value.trim();
      if (text !== '') result[key] = Number(text);
    }
    return result; // The engine validates option domains and chooses placement.
  }
  function rowData(rows) {
    // Transport snapshots for an exact ordered comparison, including duplicate
    // rows. This is not RDF value equality or blank-node isomorphism.
    return rows.map(row => Array.from(row.entries()));
  }
  async function describe(answer) {
    if (Array.isArray(answer)) {
      const rows = rowData(answer);
      return { kind: 'select', count: answer.length, rows,
        preview: json(rows.slice(0, displayRows)), exact: JSON.stringify(rows) };
    }
    if (typeof answer === 'boolean') return { kind: 'ask', value: answer, preview: String(answer), exact: String(answer) };
    if (answer && typeof answer.serialize === 'function') {
      const text = await answer.serialize({ format: 'nquads' });
      return { kind: 'graph', count: answer.size,
        preview: text.slice(0, graphPreviewChars), truncated: text.length > graphPreviewChars };
    }
    throw new Error('The runtime returned an unsupported result shape.');
  }
  function tableRows(id, rows, empty, columns) {
    const target = $(id);
    target.replaceChildren();
    if (!rows.length) {
      const tr = element('tr'), td = element('td', empty);
      td.colSpan = columns;
      tr.append(td);
      target.append(tr);
    } else for (const row of rows) {
      const tr = element('tr');
      for (const value of row) tr.append(element('td', value));
      target.append(tr);
    }
  }
  function renderAnswer(result) {
    const view = $('result-view');
    view.replaceChildren();
    view.dataset.state = 'complete';
    $('result-json').textContent = result.preview + (result.truncated ? '\n[Display preview ends here; the query result was complete.]' : '');
    if (result.kind === 'ask') {
      const value = element('p', String(result.value));
      value.className = 'boolean';
      view.append(value);
      return;
    }
    if (result.kind === 'graph') {
      view.append(element('pre', result.preview));
      if (result.truncated) view.append(element('p', 'The graph preview is shortened. The quad count and CPU comparison cover the complete result.'));
      return;
    }
    const variables = [...new Set(result.rows.flatMap(row => row.map(([name]) => name)))];
    if (!result.rows.length) { view.append(element('p', 'No solution bindings.')); return; }
    const table = element('table'), thead = element('thead'), header = element('tr'), body = element('tbody');
    for (const name of variables) header.append(element('th', `?${name}`));
    thead.append(header);
    table.append(thead, body);
    for (const row of result.rows.slice(0, displayRows)) {
      const bindings = new Map(row), tr = element('tr');
      for (const name of variables) {
        const term = bindings.get(name), td = element('td');
        if (!term) td.textContent = '—';
        else {
          td.append(element('span', term.termType === 'Quad' ? JSON.stringify(term) : term.value));
          const detail = element('span', [term.termType, term.language, term.direction, term.datatype?.value].filter(Boolean).join(' · '));
          detail.className = 'term-type';
          td.append(detail);
        }
        tr.append(td);
      }
      body.append(tr);
    }
    view.append(table);
    if (result.count > displayRows) view.append(element('p', `Showing ${displayRows} of ${count(result.count)} complete result rows. Comparison includes every row.`));
  }
  function renderExecution(execution, requestedMode, kind) {
    $('gpu-joins').textContent = execution ? count(execution.gpuJoins) : requestedMode === 'cpu' ? '0' : '—';
    $('cpu-fallbacks').textContent = execution ? count(execution.cpuFallbacks) : '—';
    $('backend-status').textContent = execution
      ? `Reported backend: ${execution.backend}. Selection: ${execution.selection}.`
      : kind === 'ask'
        ? 'ASK keeps its boolean result shape and does not expose execution metadata. Required GPU mode still requires an observed GPU join.'
        : requestedMode === 'cpu'
          ? 'CPU execution was requested. The ordinary CPU result has no mixed-plan trace.'
          : 'This result has no mixed-plan metadata. The ordinary CPU path can return without a device trace.';
    tableRows('join-rows', (execution?.joins ?? []).map(join =>
      [join.label, join.backend, count(join.leftRows), count(join.rightRows), count(join.pairs), join.reason]),
      'No candidate-join trace was returned.', 6);
    tableRows('phase-rows', (execution?.observed ?? []).map(phase =>
      [`${phase.round + 1} / ${phase.phase}`, count(phase.dispatches), ms(phase.timing?.compileMs),
        ms(phase.timing?.uploadMs), ms(phase.timing?.dispatchMs), ms(phase.timing?.readbackMs)]),
      'No GPU dispatch was reported for this result.', 6);
    $('execution-json').textContent = execution ? json(execution) : 'No execution metadata on this result shape.';
  }
  function clearRun() {
    lastReport = null;
    for (const id of ['query-ms', 'result-count', 'gpu-joins', 'cpu-fallbacks']) $(id).textContent = '—';
    $('result-view').replaceChildren(element('p', 'Query pending…'));
    $('result-view').dataset.state = 'pending';
    $('result-json').textContent = 'Query pending…';
    $('execution-json').textContent = 'No completed execution.';
    $('backend-status').textContent = 'Waiting for the query result.';
    tableRows('join-rows', [], 'No completed join trace.', 6);
    tableRows('phase-rows', [], 'No completed device trace.', 6);
    status('comparison', 'CPU comparison has not been run.');
  }
  async function run(compare = false) {
    clearRun();
    status('status', 'Preparing the query…');
    const ds = await loadDataset();
    const query = $('query-text').value, opts = options();
    status('status', `Running ${opts.execution} query…`);
    let answer, reference;
    try {
      const started = now();
      answer = await core.query(ds, query, opts);
      const wallMs = now() - started;
      const result = await describe(answer), execution = answer?.execution;
      renderAnswer(result);
      renderExecution(execution, opts.execution, result.kind);
      $('query-ms').textContent = ms(wallMs);
      $('result-count').textContent = result.kind === 'ask' ? String(result.value) : `${count(result.count)} ${result.kind === 'graph' ? 'quads' : 'rows'}`;
      lastReport = {
        measuredAt: new Date().toISOString(), runtime: runtimeInfo,
        source: { name: sourceName, quads: ds.size, characters: parsedText.length, format: parsedFormat || 'engine-detected' },
        query, options: opts, wallMs, result: { kind: result.kind, count: result.count, value: result.value, preview: result.preview },
        execution: execution ?? null
      };
      if (compare) {
        status('status', 'Query completed. Running the separate CPU comparison…');
        try {
          const cpuStarted = now();
          reference = await core.query(ds, query, { ...opts, execution: 'cpu' });
          const cpuWallMs = now() - cpuStarted, cpuResult = await describe(reference);
          const same = result.kind === cpuResult.kind && (result.kind === 'graph'
            ? await core.isomorphic(answer, reference) : result.exact === cpuResult.exact);
          const basis = result.kind === 'graph' ? 'Graph isomorphism checked by the engine'
            : result.kind === 'ask' ? 'Boolean comparison' : 'Exact ordered bindings, including duplicate rows';
          lastReport.comparison = { equal: same, basis, cpuWallMs };
          status('comparison', `${same ? 'Results agree.' : 'Results differ between the two runs.'} ${basis}. Selected mode: ${ms(wallMs)}; CPU: ${ms(cpuWallMs)}.${same ? '' : ' Nondeterministic expressions or fresh blank nodes can differ across separate queries; inspect the result data.'}`, same ? 'success' : 'error');
        } catch (error) {
          lastReport.comparison = { error: String(error?.message || error) };
          status('comparison', `Query result is available; CPU comparison failed: ${lastReport.comparison.error}`, 'error');
        }
      }
      status('status', `Completed ${opts.execution} query. ${result.kind === 'ask' ? 'Boolean answer shown.' : `${count(result.count)} ${result.kind === 'graph' ? 'quads' : 'rows'} returned.`}`, 'success');
      return lastReport;
    } finally {
      if (answer && !Array.isArray(answer) && typeof answer.dispose === 'function') answer.dispose();
      if (reference && !Array.isArray(reference) && typeof reference.dispose === 'function') reference.dispose();
    }
  }

  for (const [id, fixture] of Object.entries(queries)) {
    const option = element('option', fixture.label);
    option.value = id;
    $('query-preset').append(option);
  }
  const custom = element('option', 'Custom query'); custom.value = ''; $('query-preset').append(custom);
  $('query-preset').value = 'people';
  $('query-text').value = queries.people.text;
  useSample();
  $('webgpu-status').textContent = globalThis.navigator?.gpu ? 'WebGPU API exposed · device checked on demand' : 'WebGPU API unavailable · CPU mode works';

  $('load-runtime').addEventListener('click', () => action(loadRuntime));
  $('load-dataset').addEventListener('click', () => action(loadDataset));
  $('load-sample').addEventListener('click', useSample);
  $('dataset-text').addEventListener('input', () => { sourceName = 'Edited RDF source'; dirtyDataset(); });
  $('dataset-format').addEventListener('change', () => dirtyDataset());
  $('dataset-file').addEventListener('change', () => action(async () => {
    const file = $('dataset-file').files?.[0];
    if (!file) return;
    $('dataset-text').value = await file.text();
    $('dataset-format').value = '';
    sourceName = file.name;
    dirtyDataset(`Local file ${file.name} read. The engine will detect its RDF format.`);
  }));
  $('query-preset').addEventListener('change', () => {
    const fixture = queries[$('query-preset').value];
    if (fixture) $('query-text').value = fixture.text;
  });
  $('query-text').addEventListener('input', () => { $('query-preset').value = ''; });
  $('query-text').addEventListener('keydown', event => {
    if (event.key === 'Enter' && (event.ctrlKey || event.metaKey)) { event.preventDefault(); action(() => run()); }
  });
  $('run-query').addEventListener('click', () => action(() => run()));
  $('compare-cpu').addEventListener('click', () => action(() => run(true)));
  $('download-report').addEventListener('click', () => {
    if (!lastReport) return;
    const url = URL.createObjectURL(new Blob([json(lastReport) + '\n'], { type: 'application/json' }));
    const link = element('a'); link.href = url; link.download = 'factoidal-gpu-sparql-run.json';
    doc.body.append(link); link.click(); link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  });
  controls();
  return { run: compare => action(() => run(compare)), loadRuntime: () => action(loadRuntime),
    loadDataset: () => action(loadDataset), dispose: () => dataset?.dispose() };
}

if (typeof document !== 'undefined') mountGpuSparql();
