import '../assets/sparql-result-elements.mjs';
import { exampleQuery, exampleResults } from './example.mjs';
import { highlightTokens, viewDirectives, viewNames } from './view-data.mjs';
import { createResultViews } from './views.mjs';

const $ = id => document.getElementById(id);
const editor = $('query');
const highlight = $('highlight');
const language = $('language');
const endpoint = $('endpoint');
const runButton = $('run');
const inspectButton = $('inspect');
const visualTab = $('visual-tab');
const rawTab = $('raw-tab');
const visualPanel = $('visual-panel');
const rawPanel = $('raw-panel');
const view = $('view');
const views = createResultViews();
const endpoints = {
  classic: ['Blazegraph', 'https://query.wikidata.org/sparql'],
  qlever: ['QLever', 'https://query-next.wikidata.org/sparql'],
};

let runtime;
let parseJob = 0;
let controller;
let result;
let directives;
let viewCleanup;
let drawId = 0;
let visualSelected = true;

function element(name, content) {
  const node = document.createElement(name);
  if (content !== undefined) node.textContent = content;
  return node;
}

function fetchRuntime() {
  if (!runtime) {
    runtime = import('../../../npm/factoidal/browser.js').then(api => {
      api.setAssetsUrl(new URL('../assets/l4/', import.meta.url));
      return api;
    });
    runtime.catch(() => { runtime = undefined; });
  }
  return runtime;
}

function chosenLanguage() {
  const tag = language.value.trim().toLowerCase() || 'en';
  if (!/^[a-z]{2,8}(?:-[a-z0-9]{1,8})*$/.test(tag)) {
    throw new Error('Enter a language tag such as en or pt-br.');
  }
  return tag;
}

function controls() {
  const empty = !editor.value.trim();
  inspectButton.disabled = empty;
  runButton.disabled = Boolean(controller) || empty;
}

function paintEditor() {
  const fragments = [];
  let previous = 0;
  for (const { at, text, kind } of highlightTokens(editor.value)) {
    fragments.push(document.createTextNode(editor.value.slice(previous, at)));
    const span = element('span', text);
    span.className = 'syntax-' + kind;
    fragments.push(span);
    previous = at + text.length;
  }
  fragments.push(document.createTextNode(editor.value.slice(previous) + '\n'));
  highlight.replaceChildren(...fragments);
  highlight.scrollLeft = editor.scrollLeft;
  highlight.scrollTop = editor.scrollTop;
}

function clearStructure() {
  parseJob += 1;
  $('parse-state').textContent = '';
  $('parsed').hidden = true;
}

async function inspectQuery() {
  const id = ++parseJob;
  $('parsed').hidden = true;
  $('parse-state').textContent = 'Parsing with Factoidal Wasm…';
  try {
    const api = await fetchRuntime();
    const structure = await api.parseSparqlStructure(editor.value, { wdqs: true });
    if (id !== parseJob) return;
    $('parsed').textContent = structure.sse;
    $('parsed').hidden = false;
    $('parse-state').textContent = structure.form.toUpperCase() + ' query' +
      (structure.variables.length ? ' · ' + structure.variables.map(variable => '?' + variable).join(', ') : '');
  } catch (error) {
    if (id === parseJob) $('parse-state').textContent = error.message;
  }
}

function resetDraw() {
  drawId += 1;
  viewCleanup?.();
  viewCleanup = undefined;
  visualPanel.replaceChildren();
}

async function draw() {
  resetDraw();
  if (!visualSelected || result?.kind !== 'select') return;
  const id = drawId;
  const name = view.value;
  visualTab.textContent = viewNames[name];
  const panel = element('div');
  visualPanel.append(panel);
  if (directives.title) panel.append(element('h3', directives.title));
  if (directives.unknownView) panel.append(element('p', 'Unrecognised view ' + directives.unknownView +
    '. Use the view menu to select a supported format.'));
  if (directives.invalidOptions) panel.append(element('p', 'A view option could not be read as JSON.'));
  const { vars } = result.data.head;
  const rows = result.data.results.bindings;
  const preview = name === 'Table' ? rows : rows.slice(0, 400);
  if (preview.length < rows.length) {
    panel.append(element('p', `Visualising the first ${preview.length} of ${rows.length} rows.`));
  }
  try {
    const cleanup = await views.get(name)(panel, { vars, rows: preview, options: directives.options.get(name) ?? {} }, name);
    if (id === drawId) viewCleanup = cleanup;
    else cleanup?.();
  } catch (error) {
    if (id === drawId) panel.append(element('p', 'View unavailable. ' + error.message));
  }
}

function selectTab(showVisual, focus = false) {
  visualSelected = showVisual;
  const active = showVisual ? visualTab : rawTab;
  for (const tab of [visualTab, rawTab]) {
    tab.setAttribute('aria-selected', String(tab === active));
    tab.tabIndex = tab === active ? 0 : -1;
  }
  visualPanel.hidden = !showVisual;
  rawPanel.hidden = showVisual;
  $('view-choice').hidden = !showVisual;
  if (focus) active.focus();
  draw();
}

function downloadResult() {
  const rdf = result.kind === 'rdf';
  const blob = new Blob([rdf ? result.data : JSON.stringify(result.data, null, 2)],
    { type: rdf ? result.contentType : 'application/sparql-results+json' });
  const url = URL.createObjectURL(blob);
  const link = element('a');
  link.download = rdf ? 'wikidata-results.rdf.txt' : 'wikidata-results.srj';
  link.href = url;
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function renderRaw() {
  rawPanel.replaceChildren();
  const actions = element('p');
  const download = element('button', 'Download complete results');
  download.type = 'button';
  download.onclick = downloadResult;
  actions.append(download);
  rawPanel.append(actions);
  if (result.kind === 'rdf') {
    const text = element('pre', result.data);
    text.className = 'rdf';
    rawPanel.append(element('p', result.contentType), text);
  } else {
    const component = element(result.kind === 'ask' ? 'factoidal-sparql-boolean' : 'factoidal-sparql-results');
    component.setAttribute('max-rows', '200');
    component.results = result.data;
    rawPanel.append(component);
  }
}

function showResult(value, query, source) {
  result = value;
  directives = viewDirectives(query);
  visualTab.hidden = value.kind !== 'select';
  view.value = directives.defaultView;
  const rows = value.kind === 'select' ? ` · ${value.data.results.bindings.length.toLocaleString()} rows` : '';
  $('result-state').textContent = source + rows;
  renderRaw();
  selectTab(value.kind === 'select');
}

async function run() {
  const which = endpoint.value;
  const [name, url] = endpoints[which];
  const body = editor.value;
  let query;
  try {
    query = body.replaceAll('[AUTO_LANGUAGE]', chosenLanguage());
  } catch (error) {
    $('result-state').textContent = error.message;
    return;
  }
  const active = new AbortController();
  controller = active;
  const timeout = setTimeout(() => active.abort(), 45000);
  controls();
  $('result-state').textContent = 'Waiting for ' + name + '…';
  try {
    const encoded = new URLSearchParams({ query });
    const get = encoded.toString().length < 7000;
    const response = await fetch(get ? url + '?' + encoded : url, {
      method: get ? 'GET' : 'POST', body: get ? undefined : encoded,
      headers: { Accept: 'application/sparql-results+json, application/n-triples;q=0.9, text/turtle;q=0.8, application/rdf+xml;q=0.5' },
      signal: active.signal,
    });
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}. ${(await response.text()).trim().slice(0, 320)}`);
    }
    const contentType = response.headers.get('content-type')?.split(';')[0] ?? 'Unknown media type';
    let value;
    if (contentType.endsWith('json')) {
      const data = await response.json();
      if (typeof data.boolean === 'boolean') value = { kind: 'ask', data };
      else if (Array.isArray(data.head?.vars) && Array.isArray(data.results?.bindings)) value = { kind: 'select', data };
      else throw new Error('The response is missing SPARQL result bindings.');
    } else {
      if (!['application/n-triples', 'text/turtle', 'application/rdf+xml', 'application/n-quads',
        'application/trig', 'text/plain'].includes(contentType)) throw new Error('Unexpected media type ' + contentType + '.');
      value = { kind: 'rdf', data: await response.text(), contentType };
    }
    if (controller !== active) return;
    showResult(value, body, name);
  } catch (error) {
    if (controller === active) {
      $('result-state').textContent = name + (error.name === 'AbortError' ? ' timed out.' : '. ' + error.message);
    }
  } finally {
    clearTimeout(timeout);
    if (controller === active) {
      controller = undefined;
      controls();
    }
  }
}

function stopRunning() {
  if (controller) {
    controller.abort();
    controller = undefined;
    $('result-state').textContent = 'Query cancelled.';
  }
}

function loadExample() {
  stopRunning();
  editor.value = exampleQuery;
  paintEditor();
  clearStructure();
  endpoint.value = 'classic';
  showResult({ kind: 'select', data: exampleResults }, exampleQuery, 'Graph example · saved results');
  controls();
}

for (const [id, label] of Object.entries(viewNames)) {
  if (!views.has(id)) continue;
  const option = element('option', label);
  option.value = id;
  view.add(option);
}
$('example').onclick = loadExample;
inspectButton.onclick = inspectQuery;
runButton.onclick = run;
editor.oninput = () => { stopRunning(); clearStructure(); paintEditor(); controls(); };
editor.onscroll = () => {
  highlight.scrollTop = editor.scrollTop;
  highlight.scrollLeft = editor.scrollLeft;
};
editor.onkeydown = event => {
  if (event.key === 'Enter' && (event.ctrlKey || event.metaKey) && !runButton.disabled) {
    event.preventDefault();
    run();
  }
};
language.oninput = () => { stopRunning(); controls(); };
visualTab.onclick = () => selectTab(true);
rawTab.onclick = () => selectTab(false);
visualTab.parentElement.onkeydown = event => {
  if (visualTab.hidden || !['ArrowLeft', 'ArrowRight', 'Home', 'End'].includes(event.key)) return;
  event.preventDefault();
  selectTab(event.key === 'Home' || (event.key !== 'End' && !visualSelected), true);
};
view.onchange = draw;
loadExample();
