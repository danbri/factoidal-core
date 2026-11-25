import '../assets/sparql-result-elements.mjs';
import { groups } from './example.mjs?v=gallery-preview';
import { drawRaw, element, mountGallery } from './gallery.mjs?v=gallery-preview';
import { queryQlever } from './qlever.mjs';
import { highlightTokens, viewDirectives, viewNames } from './view-data.mjs?v=gallery-preview';
import { createResultViews } from './views.mjs?v=gallery-preview';

const $ = id => document.getElementById(id);
const editor = $('query');
const highlight = $('highlight');
const language = $('language');
const runButton = $('run');
const inspectButton = $('inspect');
const visualTab = $('visual-tab');
const rawTab = $('raw-tab');
const visualPanel = $('visual-panel');
const rawPanel = $('raw-panel');
const view = $('view');
const views = createResultViews();

let runtime;
let parseJob = 0;
let controller;
let result;
let directives;
let viewCleanup;
let drawId = 0;
let visualSelected = true;
let gallery;

function fetchRuntime() {
  if (!runtime) {
    runtime = import('./inspect.mjs').then(async ({ inspectSparql }) => {
      const { browserEngine } = await import('../../../npm/factoidal/lib/browser-engine.mjs');
      const assetsUrl = new URL('../assets/l4/', import.meta.url);
      const engine = await browserEngine('l4factoidal-core', assetsUrl).loadEngine();
      return query => inspectSparql(engine, query);
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
  runButton.disabled = Boolean(controller || gallery?.busy) || empty;
  gallery?.controls();
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
    const inspect = await fetchRuntime();
    if (id !== parseJob) return;
    const { form, sse, variables } = inspect(editor.value);
    if (sse === undefined) {
      $('parse-state').textContent = 'Valid ' + form.toUpperCase() + ' query. This engine can check syntax.';
      return;
    }
    $('parsed').textContent = sse;
    $('parsed').hidden = false;
    $('parse-state').textContent = form.toUpperCase() + ' query' +
      (variables.length ? ' · ' + variables.map(variable => '?' + variable).join(', ') : '');
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

function showResult(value, query, source) {
  result = value;
  directives = viewDirectives(query);
  visualTab.hidden = value.kind !== 'select';
  view.value = directives.defaultView;
  const rows = value.kind === 'select' ? ` · ${value.data.results.bindings.length.toLocaleString()} rows` : '';
  $('result-state').textContent = source + rows;
  $('result-panels').hidden = false;
  drawRaw(rawPanel, result);
  selectTab(value.kind === 'select');
}

async function run() {
  if (controller || gallery?.busy) return;
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
  $('result-state').textContent = 'Waiting for QLever…';
  try {
    const value = await queryQlever(query, { signal: active.signal });
    if (controller !== active) return;
    showResult(value, body, 'QLever');
  } catch (error) {
    if (controller === active) {
      $('result-state').textContent = 'QLever' + (error.name === 'AbortError' ? ' timed out.' : '. ' + error.message);
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

function loadQuery(query) {
  stopRunning();
  editor.value = query;
  paintEditor();
  clearStructure();
  result = undefined;
  resetDraw();
  $('result-panels').hidden = true;
  $('result-state').textContent = '';
  controls();
}

function openEditor(query) {
  if (query !== undefined) loadQuery(query);
  $('query-editor').open = true;
  $('query-editor').scrollIntoView();
  editor.focus({ preventScroll: true });
}

for (const [id, label] of Object.entries(viewNames)) {
  if (!views.has(id)) continue;
  const option = element('option', label);
  option.value = id;
  view.add(option);
}
$('editor-link').onclick = event => { event.preventDefault(); openEditor(); };
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
$('query-editor').addEventListener('toggle', event => {
  if (event.currentTarget.open) paintEditor();
});
gallery = mountGallery({ groups, views, onEdit: openEditor, canRun: () => !controller, onChange: controls });
editor.value = groups[0].query;
controls();
