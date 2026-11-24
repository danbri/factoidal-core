import { groups } from './example.mjs';
import { batchSize, queryQlever, runBatch } from './qlever.mjs';
import { viewDirectives, viewNames } from './view-data.mjs';

const labels = { ...viewNames, Ask: 'Boolean result', Rdf: 'RDF triples' };

export function element(name, content, className) {
  const node = document.createElement(name);
  if (content !== undefined) node.textContent = content;
  if (className) node.className = className;
  return node;
}

function button(text, action, className) {
  const node = element('button', text, className);
  node.type = 'button';
  node.onclick = action;
  return node;
}

function link(text, href) {
  const node = element('a', text);
  node.href = href;
  return node;
}

function download(result) {
  const rdf = result.kind === 'rdf';
  const blob = new Blob([rdf ? result.data : JSON.stringify(result.data, null, 2)],
    { type: rdf ? result.contentType : 'application/sparql-results+json' });
  const url = URL.createObjectURL(blob);
  const file = link('', url);
  file.download = rdf ? 'wikidata-results.rdf.txt' : 'wikidata-results.srj';
  file.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function rdfResult(result) {
  const panel = element('div', undefined, 'rdf-result');
  panel.append(element('span', result.contentType, 'rdf-type'), element('pre', result.data, 'rdf'));
  return panel;
}

export function drawRaw(root, result) {
  const output = result.kind === 'rdf' ? rdfResult(result) :
    element(result.kind === 'ask' ? 'factoidal-sparql-boolean' : 'factoidal-sparql-results');
  if (result.kind !== 'rdf') {
    output.setAttribute('max-rows', '200');
    output.results = result.data;
  }
  root.replaceChildren(button('Download complete results', () => download(result), 'download-btn'), output);
}

function drawBoolean(root, result) {
  const answer = element('div', undefined, 'ask-answer');
  answer.dataset.value = String(result.data.boolean);
  answer.append(element('span', result.data.boolean ? '✓' : '×', 'ask-mark'),
    element('strong', result.data.boolean ? 'True' : 'False'),
    element('span', result.data.boolean ? 'The pattern matched.' : 'No matching pattern.'));
  answer.firstElementChild.setAttribute('aria-hidden', 'true');
  root.append(answer);
}

function countText(result) {
  if (result.kind !== 'select') return '';
  const n = result.data.results.bindings.length;
  return ' · ' + n.toLocaleString() + (n === 1 ? ' row' : ' rows');
}

export function mountGallery({ views, onEdit, canRun, onChange }) {
  const root = document.getElementById('gallery');
  const nav = document.getElementById('gallery-nav');
  const batchButton = document.getElementById('batch-run');
  const batchStatus = document.getElementById('batch-state');
  const entries = [];
  let busy = false;

  function controls() {
    const pending = entries.filter(entry => !entry.loaded).length;
    const blocked = busy || !canRun();
    batchButton.disabled = blocked || !pending;
    batchButton.textContent = busy ? 'Loading live examples…' :
      pending ? 'Load ' + Math.min(pending, batchSize) + ' live ' + (pending === 1 ? 'example' : 'examples') :
        'All examples loaded';
    for (const { run } of entries) run.disabled = blocked;
  }

  async function renderCard(entry, card, result) {
    const revision = ++card.revision;
    card.cleanup?.();
    card.cleanup = undefined;
    const target = element('div', undefined, 'view-output');
    card.panel.replaceChildren(target);
    try {
      if (result.kind === 'ask') drawBoolean(target, result);
      else if (result.kind === 'rdf') target.append(rdfResult(result));
      else {
        const { head: { vars }, results: { bindings: rows } } = result.data;
        const cleanup = await views.get(card.id)(target,
          { vars, rows, options: entry.directives.options.get(card.id) ?? {} }, card.id);
        if (revision === card.revision) card.cleanup = cleanup;
        else cleanup?.();
      }
    } catch (error) {
      if (revision === card.revision) target.append(element('p', 'View unavailable. ' + error.message, 'view-note'));
    }
  }

  function render(entry, result, caption) {
    entry.result = result;
    entry.status.textContent = caption + countText(result);
    entry.status.dataset.live = String(entry.loaded);
    for (const card of entry.cards) void renderCard(entry, card, result);
    if (entry.raw.open) drawRaw(entry.rawOutput, result);
  }

  async function load(items) {
    if (busy || !canRun()) return;
    busy = true;
    controls();
    onChange();
    let successes = 0;
    let failures = 0;
    let paused = false;
    try {
      await runBatch(items, async entry => {
        entry.status.textContent = 'Waiting for QLever…';
        batchStatus.textContent = 'Loading ' + entry.group.title + '…';
        const active = new AbortController();
        const timeout = setTimeout(() => active.abort(), 45000);
        try {
          const result = await queryQlever(entry.group.query, { signal: active.signal });
          if (result.kind !== entry.group.preview.kind) throw new Error('Unexpected result format.');
          entry.loaded = true;
          successes += 1;
          render(entry, result, 'Live QLever result');
        } catch (error) {
          failures += 1;
          const timeoutError = error.name === 'AbortError';
          const retained = entry.loaded ? 'The previous response is still shown.' : 'The saved preview is still shown.';
          entry.status.textContent = (timeoutError ? 'QLever timed out.' : 'QLever. ' + error.message) + ' ' + retained;
          paused = timeoutError || error.status === 429 || error.status === 503;
          if (paused) return false;
        } finally {
          clearTimeout(timeout);
        }
        return true;
      });
    } finally {
      busy = false;
      controls();
      onChange();
      const fresh = successes + (successes === 1 ? ' example updated.' : ' examples updated.');
      const skipped = failures ? ' ' + failures + (failures === 1 ? ' request failed.' : ' requests failed.') : '';
      batchStatus.textContent = fresh + skipped + (paused ? ' QLever is busy. The batch has paused.' : '');
    }
  }

  for (const group of groups) {
    const section = element('section', undefined, 'gallery-group');
    section.id = group.id;
    section.setAttribute('aria-labelledby', group.id + '-title');
    nav.append(link(group.title, '#' + group.id));

    const heading = element('header', undefined, 'group-heading');
    const summary = element('div', undefined, 'group-summary');
    const title = element('h2', group.title);
    title.id = group.id + '-title';
    const status = element('p', '', 'group-status');
    status.setAttribute('role', 'status');
    summary.append(title);
    if (group.description) summary.append(element('p', group.description, 'group-description'));
    for (const [label, href] of group.sources ?? []) summary.append(link(label, href));
    summary.append(status);
    heading.append(summary);

    const actions = element('div', undefined, 'group-actions');
    const run = button('Run on QLever', () => void load([entry]));
    actions.append(run, button('Edit query', () => onEdit(group.query)));
    heading.append(actions);
    section.append(heading);

    const grid = element('div', undefined, 'view-grid');
    const cards = group.views.map(({ id, description }) => {
      const card = element('article', undefined, 'view-card');
      card.dataset.view = id;
      const label = element('h3', labels[id]);
      label.id = group.id + '-' + id;
      card.setAttribute('aria-labelledby', label.id);
      const panel = element('div', undefined, 'view-panel');
      card.append(label, element('p', description, 'view-description'), panel);
      grid.append(card);
      return { id, panel, revision: 0 };
    });

    const raw = element('details', undefined, 'group-raw');
    const rawOutput = element('div', undefined, 'raw-output');
    raw.append(element('summary', 'Raw results'), rawOutput);
    section.append(grid, raw);
    root.append(section);

    const entry = { group, cards, directives: viewDirectives(group.query), status, run, raw, rawOutput, loaded: false };
    raw.addEventListener('toggle', () => {
      if (raw.open && entry.result) drawRaw(rawOutput, entry.result);
    });
    entries.push(entry);
    render(entry, group.preview, 'Saved preview');
  }

  batchButton.onclick = () => void load(entries.filter(entry => !entry.loaded));
  controls();
  return { get busy() { return busy; }, controls };
}
