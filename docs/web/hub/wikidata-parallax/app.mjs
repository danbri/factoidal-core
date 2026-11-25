// Stepper for a query page: walk the blocks one step at a time, with the
// draft query for each step in a drawer below, and run any step (or every
// step's count) against a Wikidata SPARQL endpoint.
//
// The page works without this script: blocks, highlighting and folding are
// plain HTML and CSS. The script reads the grammar's steps from the inert
// <script type="application/json" id="grammar"> block; draft.mjs turns them
// into SPARQL.
import { draftQuery, fragmentsUpTo } from './draft.mjs';

const $ = (sel, root = document) => root.querySelector(sel);
const $$ = (sel, root = document) => [...root.querySelectorAll(sel)];
const data = $('#grammar');
const blocks = $('.blocks');
const drawer = $('.drawer');
if (data && blocks && drawer) start(JSON.parse(data.textContent));

function start(g) {
  const n = g.steps.length;          // steps 0..n-1, then n: the whole query
  const last = n;
  const stepEl = (k) => $(`[data-step="${k}"]`, blocks);
  const tools = $('.step-tools', blocks);
  const ui = {
    title: $('.dr-title', drawer), text: $('.dr-sparql', drawer), status: $('.dr-status', drawer),
    result: $('.dr-result', drawer), endpoint: $('.dr-endpoint', drawer), open: $('.dr-open', drawer),
    toggle: $('.dr-toggle', drawer), prev: $('.dr-prev', drawer), next: $('.dr-next', drawer),
  };
  const fmt = new Intl.NumberFormat('en');
  const counts = new Map();          // `${endpoint}\n${query}` -> {items, rows}
  let cur = -1, running = null, countingAll = false;

  tools.hidden = false;
  if (!n) $('.st-counts', tools).hidden = true;
  try { const ep = localStorage.getItem('wdp-endpoint'); if (ep && [...ui.endpoint.options].some(o => o.value === ep)) ui.endpoint.value = ep; } catch {}

  const queryFor = (k, opts) => (k >= last ? g.full : draftQuery(g, k, opts));
  const labelOf = (k) => {
    if (k >= last) return 'the whole query';
    const el = stepEl(k);
    if (!el) return g.steps[k].kind;
    const c = (el.matches('details') ? $('summary', el) : el).cloneNode(true);
    c.querySelectorAll('.pz-count, .cb-why, .pz-desc').forEach(x => x.remove());
    return c.textContent.replace(/\s+/g, ' ').trim().slice(0, 90);
  };

  function show(k) {
    cur = Math.max(0, Math.min(last, k));
    blocks.classList.add('stepping');
    drawer.hidden = false;
    document.body.classList.add('has-drawer');
    for (const el of $$('[data-step]', blocks)) {
      const s = +el.dataset.step;
      el.classList.toggle('st-current', s === cur);
      el.classList.toggle('st-later', s > cur && cur < last);
    }
    const el = stepEl(cur);
    if (el) {
      for (let p = el.parentElement; p && p !== blocks; p = p.parentElement) if (p.matches('details')) p.open = true;
      el.scrollIntoView({ block: 'nearest', behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth' });
    }
    ui.title.textContent = `Step ${cur + 1} of ${last + 1}: ${labelOf(cur)}`;
    ui.text.value = queryFor(cur);
    ui.prev.disabled = cur === 0;
    ui.next.disabled = cur === last;
    ui.result.replaceChildren();
    ui.status.textContent = '';
    updateOpen();
  }

  function stop() {
    cur = -1;
    blocks.classList.remove('stepping');
    for (const el of $$('.st-current, .st-later', blocks)) el.classList.remove('st-current', 'st-later');
    drawer.hidden = true;
    document.body.classList.remove('has-drawer');
    running?.abort();
  }

  function updateOpen() {
    const ep = ui.endpoint.value, q = ui.text.value;
    ui.open.href = ep.includes('query.wikidata.org') ? `https://query.wikidata.org/#${encodeURIComponent(q)}`
      : ep.includes('qlever.dev') ? `https://qlever.dev/wikidata/?query=${encodeURIComponent(q)}`
        : `https://query-next.wikidata.org/?query=${encodeURIComponent(q)}`;
  }

  async function sparql(query, signal) {
    const ep = ui.endpoint.value;
    const body = new URLSearchParams({ query });
    const get = body.toString().length < 6000;
    // A busy endpoint answers 429 (or 503): wait as it asks, a few times, then give up.
    for (let attempt = 0; ; attempt++) {
      const r = await fetch(get ? `${ep}?${body}` : ep, {
        method: get ? 'GET' : 'POST', body: get ? undefined : body, signal,
        headers: { Accept: 'application/sparql-results+json' },
      });
      if (r.ok) return r.json();
      if ((r.status === 429 || r.status === 503) && attempt < 3) {
        const wait = Math.min(20, +r.headers.get('retry-after') || 2 * 3 ** attempt);
        ui.status.textContent = `The endpoint is busy; trying again in ${wait} s…`;
        await new Promise((ok, no) => { const t = setTimeout(ok, wait * 1000); signal?.addEventListener('abort', () => { clearTimeout(t); no(signal.reason); }, { once: true }); });
        continue;
      }
      if (r.status === 429) throw new Error('the endpoint is busy (too many requests); try again in a minute, or pick another endpoint');
      throw new Error(`HTTP ${r.status}: ${(await r.text()).replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 200)}`);
    }
  }
  const withTimeout = (ms) => { running?.abort(); const c = new AbortController(); running = c; const t = setTimeout(() => c.abort(new Error(`no answer after ${ms / 1000} s`)), ms); return { signal: c.signal, done: () => clearTimeout(t) }; };

  function badge(k, c) {
    const el = stepEl(k);
    const b = el && $(':scope > .pz-count, :scope > summary > .pz-count, :scope > .cb-bar > .pz-count', el);
    if (!b) return;
    const v = g.steps[k]?.v;
    b.textContent = c.items != null ? `${fmt.format(c.items)}` : `${fmt.format(c.rows)} rows`;
    b.title = c.items != null ? `${fmt.format(c.items)} distinct ?${v}, in ${fmt.format(c.rows)} rows (draft up to this step)` : `${fmt.format(c.rows)} rows (draft up to this step)`;
    b.classList.toggle('zero', !(c.items ?? c.rows));
  }

  async function count(k, signal) {
    const q = k >= last ? `SELECT (COUNT(*) AS ?rows) WHERE { ${stripPrefixes(g.full)} }` : queryFor(k, { count: true });
    const query = k >= last ? `${g.prefixes}\n${q}` : q;
    const key = `${ui.endpoint.value}\n${query}`;
    if (!counts.has(key)) {
      const j = await sparql(query, signal);
      const b = j.results.bindings[0] || {};
      counts.set(key, { items: b.items ? +b.items.value : null, rows: b.rows ? +b.rows.value : 0 });
    }
    const c = counts.get(key);
    if (k < last) badge(k, c);
    return c;
  }
  // "Run" fetches a sample: a query without a LIMIT of its own gets one (the whole query can have 100,000s of rows).
  const limited = (q) => (/\bLIMIT\s+\d+\s*(OFFSET\s+\d+\s*)?$/i.test(q.replace(/#[^\n]*$/gm, '').trim()) ? q : `${q.trim()}\nLIMIT 50`);
  // The whole query counted as a subquery; its own PREFIX lines move outside.
  const stripPrefixes = (q) => q.replace(/^\s*PREFIX[^\n]*\n/gim, '');

  async function act(kind) {
    const t = withTimeout(90000);
    ui.status.textContent = kind === 'count' ? 'Counting…' : 'Running…';
    ui.result.replaceChildren();
    try {
      if (kind === 'count' && cur < last && !fragmentsUpTo(g.steps, cur).length) {
        ui.status.textContent = 'Nothing to count yet: this set is defined by the steps that follow.';
      } else if (kind === 'count') {
        const c = await count(cur, t.signal);
        ui.status.textContent = c.items != null ? `${fmt.format(c.items)} distinct ?${g.steps[cur].v} in ${fmt.format(c.rows)} rows` : `${fmt.format(c.rows)} rows`;
      } else {
        const t0 = performance.now();
        const j = await sparql(limited(ui.text.value), t.signal);
        ui.status.textContent = `${fmt.format(j.results.bindings.length)} rows in ${((performance.now() - t0) / 1000).toFixed(1)} s`;
        ui.result.append(table(j));
      }
    } catch (e) {
      ui.status.textContent = `Failed: ${e.name === 'AbortError' && t.signal.reason ? t.signal.reason.message : e.message}`;
    } finally { t.done(); }
  }

  async function countAll(button) {
    if (countingAll) { countingAll = false; running?.abort(); return; }
    countingAll = true;
    button.textContent = 'Stop counting';
    for (let k = 0; k < n && countingAll; k++) {
      // A step that adds no SPARQL of its own (a set named only for what follows) has nothing to count yet.
      if (!g.steps[k].sparql.length) continue;
      const el = stepEl(k);
      const b = el && $('.pz-count', el);
      if (b) { b.textContent = '…'; b.classList.add('busy'); }
      const t = withTimeout(90000);
      try { await count(k, t.signal); } catch (e) { if (b) { b.textContent = '?'; b.title = e.message; } }
      finally { t.done(); b?.classList.remove('busy'); }
      await new Promise(r => setTimeout(r, 600));
    }
    countingAll = false;
    button.textContent = 'Count every step on Wikidata';
  }

  function table(j) {
    const vars = j.head.vars;
    const t = document.createElement('table');
    const tr = t.createTHead().insertRow();
    for (const v of vars) { const th = document.createElement('th'); th.textContent = `?${v}`; tr.append(th); }
    const body = t.createTBody();
    for (const row of j.results.bindings.slice(0, 200)) {
      const r = body.insertRow();
      for (const v of vars) {
        const c = r.insertCell(), x = row[v];
        if (!x) continue;
        const m = x.type === 'uri' && /^http:\/\/www\.wikidata\.org\/entity\/([PQL]\d+)$/.exec(x.value);
        if (m) { const a = document.createElement('a'); a.href = `https://www.wikidata.org/wiki/${m[1]}`; a.textContent = m[1]; c.append(a); }
        else c.textContent = x.value.length > 120 ? x.value.slice(0, 117) + '…' : x.value;
      }
    }
    if (!j.results.bindings.length) { const p = document.createElement('p'); p.textContent = 'No rows.'; return p; }
    const wrap = document.createElement('div'); wrap.className = 'dr-table'; wrap.append(t); return wrap;
  }

  $('.st-start', tools).addEventListener('click', () => show(cur < 0 ? 0 : cur));
  $('.st-counts', tools).addEventListener('click', (e) => countAll(e.currentTarget));
  $('.st-fold', tools).addEventListener('click', (e) => {
    const all = $$('details.cb', blocks), fold = all.some(d => d.open);
    all.forEach(d => { d.open = !fold; });
    e.currentTarget.textContent = fold ? 'Unfold all blocks' : 'Fold all blocks';
  });
  ui.prev.addEventListener('click', () => show(cur - 1));
  ui.next.addEventListener('click', () => show(cur + 1));
  $('.dr-close', drawer).addEventListener('click', stop);
  ui.toggle.addEventListener('click', () => {
    const open = drawer.classList.toggle('dr-min');
    ui.toggle.setAttribute('aria-expanded', String(!open));
    ui.toggle.textContent = open ? 'Show query' : 'Hide query';
  });
  $('.dr-count', drawer).addEventListener('click', () => act('count'));
  $('.dr-run', drawer).addEventListener('click', () => act('run'));
  ui.text.addEventListener('input', updateOpen);
  ui.endpoint.addEventListener('change', () => { try { localStorage.setItem('wdp-endpoint', ui.endpoint.value); } catch {} updateOpen(); });
  // Selecting a step's block while stepping jumps there.
  blocks.addEventListener('click', (e) => {
    if (cur < 0 || e.target.closest('a, summary')) return;
    const el = e.target.closest('[data-step]');
    if (el) show(+el.dataset.step);
  });
  document.addEventListener('keydown', (e) => {
    if (cur < 0 || e.target.closest('textarea, input, select') || e.altKey || e.metaKey || e.ctrlKey) return;
    if (e.key === 'ArrowRight' || e.key === 'j') { show(cur + 1); e.preventDefault(); }
    else if (e.key === 'ArrowLeft' || e.key === 'k') { show(cur - 1); e.preventDefault(); }
    else if (e.key === 'Escape') stop();
  });
}
