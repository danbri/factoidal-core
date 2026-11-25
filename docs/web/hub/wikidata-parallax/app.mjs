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
if (blocks) linkWraps(blocks);

// Where a chain's row wraps onto a new line, draw a dotted line from the end of
// one line to the start of the next, so the flow still reads as one pipeline.
// Redrawn whenever a row changes size (window width, folding, counts).
function linkWraps(root) {
  const NS = 'http://www.w3.org/2000/svg';
  const draw = (row) => {
    row.querySelector(':scope > .wrap-path')?.remove();
    const items = [...row.children].filter(x => x.matches('li.pz'));
    if (!row.offsetParent || items.length < 2) { items.forEach(x => x.classList.remove('wrap-in')); return; }
    // Marking a piece moves it a little, which can change the wrapping: settle first.
    for (let pass = 0; pass < 3; pass++) {
      let changed = false;
      items.forEach((x, i) => {
        const w = i > 0 && x.offsetTop >= items[i - 1].offsetTop + items[i - 1].offsetHeight / 2;
        if (w !== x.classList.contains('wrap-in')) { x.classList.toggle('wrap-in', w); changed = true; }
      });
      if (!changed) break;
    }
    const breaks = items.filter(x => x.classList.contains('wrap-in'));
    if (!breaks.length) return;
    const R = row.getBoundingClientRect();
    const box = (el) => { const b = el.getBoundingClientRect(); return { l: b.left - R.left, r: b.right - R.left, t: b.top - R.top, b: b.bottom - R.top, m: b.top - R.top + b.height / 2 }; };
    let d = '';
    for (const el of breaks) {
      const i = items.indexOf(el), a = box(items[i - 1]), b = box(el);
      // The gap between the two lines: below everything on the line before, above everything on this one.
      const lineAbove = items.slice(0, i).filter(x => !x.classList.contains('wrap-in') || items.indexOf(x) >= i - 1).map(box).filter(x => x.b > a.t).reduce((m, x) => Math.max(m, x.b), a.b);
      const lineBelow = items.slice(i).map(box).filter(x => x.t < b.b).reduce((m, x) => Math.min(m, x.t), b.t);
      const gap = (lineAbove + lineBelow) / 2, x1 = a.r + 9, x2 = Math.max(3, b.l - 11);
      d += `M${x1} ${a.m}h7V${gap}H${x2}V${b.m}h${b.l - x2 - 3}`;
    }
    const svg = document.createElementNS(NS, 'svg');
    svg.setAttribute('class', 'wrap-path');
    svg.setAttribute('aria-hidden', 'true');
    const path = document.createElementNS(NS, 'path');
    path.setAttribute('d', d);
    svg.append(path);
    row.append(svg);
  };
  let queued = false;
  const all = () => { queued = false; root.querySelectorAll('.pz-row').forEach(draw); };
  const soon = () => { if (!queued) { queued = true; requestAnimationFrame(all); } };
  const ro = new ResizeObserver(soon);
  root.querySelectorAll('.pz-row').forEach(r => ro.observe(r));
  root.addEventListener('toggle', soon, true);
  addEventListener('load', soon);
  soon();
}

function start(g) {
  const n = g.steps.length;          // steps 0..n-1, then n: the whole query
  const last = n;
  const stepEl = (k) => $(`[data-step="${k}"]`, blocks);
  const tools = $('.step-tools', blocks);
  const ui = {
    title: $('.dr-title', drawer), text: $('.dr-sparql', drawer), status: $('.dr-status', drawer),
    result: $('.dr-result', drawer), endpoint: $('.dr-endpoint', drawer), open: $('.dr-open', drawer),
    toggle: $('.dr-toggle', drawer), prev: $('.dr-prev', drawer), next: $('.dr-next', drawer),
    diff: $('.dr-diff', drawer), edit: $('.dr-edit', drawer), legend: $('.dr-legend', drawer),
  };
  const fmt = new Intl.NumberFormat('en');
  // Counts are kept for the browser session, so revisiting a page asks the endpoint nothing.
  const counts = {
    get(q) { try { const v = sessionStorage.getItem(`wdp-count\n${q}`); return v ? JSON.parse(v) : null; } catch { return null; } },
    set(q, v) { try { sessionStorage.setItem(`wdp-count\n${q}`, JSON.stringify(v)); } catch {} },
  };
  const ENDPOINTS = [...ui.endpoint.options].map(o => ({ url: o.value, name: o.textContent }));
  const busyUntil = new Map();       // endpoint -> time before which we leave it alone
  let cur = -1, running = null, countingAll = false, editing = false;

  const stStatus = $('.st-status', tools);
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
    c.querySelectorAll('span, a, b').forEach(x => x.append(' '));
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
    renderDiff();
    const st = g.steps[cur];
    $('.dr-top', drawer).hidden = !(cur < last && st?.v && (st.carries || []).some(v => v !== st.v));
    ui.prev.disabled = cur === 0;
    ui.next.disabled = cur === last;
    ui.result.replaceChildren();
    ui.status.textContent = '';
    updateOpen();
  }

  // The draft for this step against the draft for the step before, line by line:
  // lines this step's own SPARQL adds are "new", other added lines (the SELECT
  // list, labels) "changed", lines that went "gone"; the rest unchanged.
  function renderDiff() {
    const now = ui.text.value.split('\n');
    const whole = cur >= last;
    ui.legend.hidden = whole || editing;
    const before = whole || cur === 0 ? (whole ? now : []) : queryFor(cur - 1).split('\n');
    const own = new Set(whole ? [] : g.steps[cur].sparql.flatMap(f => f.s.split('\n').map(l => l.trim())));
    const ops = diffLines(before, now).map(([t, line]) => [t === 'add' ? (own.has(line.trim()) ? 'new' : 'chg') : t, line]);
    ui.diff.replaceChildren(...ops.map(([t, line]) => {
      const span = document.createElement('span');
      span.className = `dl dl-${t}`;
      span.textContent = line + '\n';
      return span;
    }));
    const first = ui.diff.querySelector('.dl-new, .dl-chg');
    if (first) ui.diff.scrollTop = Math.max(0, first.offsetTop - ui.diff.offsetTop - 24);
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
    const ep = ui.endpoint.value, q = encodeURIComponent(ui.text.value);
    ui.open.href = ep.includes('qlever.dev') ? `https://qlever.dev/wikidata/?query=${q}` : `https://query-next.wikidata.org/?query=${q}`;
  }

  // Ask the chosen QLever endpoint; if it is busy (429) or failing (5xx, network),
  // ask the other one once. A busy endpoint is left alone for as long as it asks
  // (Retry-After), or a minute. No retry loops: that is how rate limits get worse.
  async function sparql(query, signal) {
    const body = new URLSearchParams({ query });
    const get = body.toString().length < 6000;
    const chosen = ui.endpoint.value;
    const order = [chosen, ...ENDPOINTS.map(e => e.url).filter(u => u !== chosen)];
    const nameOf = (u) => ENDPOINTS.find(e => e.url === u)?.name || u;
    let problem = null;
    for (const ep of order) {
      if ((busyUntil.get(ep) || 0) > Date.now()) { problem ||= `${nameOf(ep)} asked us to wait`; continue; }
      let r;
      try {
        r = await fetch(get ? `${ep}?${body}` : ep, { method: get ? 'GET' : 'POST', body: get ? undefined : body, signal, headers: { Accept: 'application/sparql-results+json' } });
      } catch (e) {
        if (signal?.aborted) throw e;
        problem = `${nameOf(ep)} could not be reached`; continue;
      }
      if (r.ok) { const j = await r.json(); j.endpoint = ep === chosen ? null : nameOf(ep); return j; }
      if (r.status === 429) {
        busyUntil.set(ep, Date.now() + 1000 * Math.min(300, +r.headers.get('retry-after') || 60));
        problem = `${nameOf(ep)} is busy (too many requests)`; continue;
      }
      if (r.status >= 500) { problem = `${nameOf(ep)} failed (HTTP ${r.status})`; continue; }
      // A 4xx other than 429 is about the query itself: another endpoint would say the same.
      throw new Error(`HTTP ${r.status}: ${(await r.text()).replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 300)}`);
    }
    const wait = Math.max(0, ...[...busyUntil.values()].map(t => Math.ceil((t - Date.now()) / 1000)));
    const e = new Error(`${problem}; no QLever endpoint answered.${wait ? ` Try again in about ${wait} s.` : ''}`);
    e.busy = true;
    throw e;
  }
  const withTimeout = (ms) => { running?.abort(); const c = new AbortController(); running = c; const t = setTimeout(() => c.abort(new Error(`no answer after ${ms / 1000} s`)), ms); return { signal: c.signal, done: () => clearTimeout(t) }; };

  function badge(k, c) {
    const el = stepEl(k);
    const b = el && $(':scope > .pz-count, :scope > summary > .pz-count, :scope > .cb-bar > .pz-count', el);
    if (!b) return;
    const from = Object.entries(c.per || {});
    const near = from[from.length - 1];
    // "96 · from 285 ?alum · 317 rows": the landing set, the set it was reached from, the rows (pairs).
    // A pivot shows just how many it reaches; the set it lands on tells the rest.
    b.textContent = c.items == null ? `${fmt.format(c.rows)} rows` : g.steps[k].kind === 'pivot' ? fmt.format(c.items)
      : [fmt.format(c.items), near ? `from ${fmt.format(near[1])} ?${near[0]}` : null, c.rows !== c.items ? `${fmt.format(c.rows)} rows` : null].filter(Boolean).join(' · ');
    b.title = describe(k, c) + ' (the draft up to this step)';
    b.classList.toggle('zero', !(c.items ?? c.rows));
  }

  // A count in words: the set, what it was reached from, and whether rows repeat it.
  function describe(k, c) {
    const v = g.steps[k]?.v;
    if (c.items == null) return `${fmt.format(c.rows)} rows`;
    const from = Object.entries(c.per || {}).map(([x, n]) => `${fmt.format(n)} ?${x}`);
    let t = `${fmt.format(c.items)} distinct ?${v}`;
    if (from.length) t += `, reached from ${from.join(' and ')}`;
    if (c.rows !== c.items) t += `, in ${fmt.format(c.rows)} rows${from.length ? ` (one per ?${Object.keys(c.per).pop()}–?${v} pair, so some ?${v} repeat)` : ''}`;
    return t;
  }

  async function count(k, signal) {
    const q = k >= last ? `SELECT (COUNT(*) AS ?rows) WHERE { ${stripPrefixes(g.full)} }` : queryFor(k, { count: true });
    const query = k >= last ? `${g.prefixes}\n${q}` : q;
    let c = counts.get(query);
    if (!c) {
      const j = await sparql(query, signal);
      const b = j.results.bindings[0] || {};
      const per = Object.fromEntries(Object.entries(b).filter(([x]) => x.startsWith('n_')).map(([x, y]) => [x.slice(2), +y.value]));
      c = { items: b.items ? +b.items.value : null, rows: b.rows ? +b.rows.value : 0, per, endpoint: j.endpoint };
      counts.set(query, c);
    }
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
        ui.status.textContent = describe(cur, c) + (c.endpoint ? ` (answered by ${c.endpoint})` : '');
      } else if (kind === 'top') {
        const j = await sparql(queryFor(cur, { top: true }), t.signal);
        ui.status.textContent = `The ${fmt.format(j.results.bindings.length)} ?${g.steps[cur].v} reached most often${j.endpoint ? ` (answered by ${j.endpoint})` : ''}`;
        ui.result.append(table(j));
      } else {
        const t0 = performance.now();
        const j = await sparql(limited(ui.text.value), t.signal);
        ui.status.textContent = `${fmt.format(j.results.bindings.length)} rows in ${((performance.now() - t0) / 1000).toFixed(1)} s${j.endpoint ? ` (answered by ${j.endpoint})` : ''}`;
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
      const cached = !!counts.get(queryFor(k, { count: true }));
      const t = withTimeout(90000);
      try { await count(k, t.signal); } catch (e) {
        if (b) { b.textContent = '?'; b.title = e.message; }
        // Both endpoints busy: stop here rather than keep asking.
        if (e.busy) { stStatus.textContent = e.message; countingAll = false; }
      } finally { t.done(); b?.classList.remove('busy'); }
      // One request at a time, with a pause, so a page never floods the endpoint.
      if (!cached && countingAll) await new Promise(r => setTimeout(r, 1500));
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
  $('.dr-top', drawer).addEventListener('click', () => act('top'));
  ui.text.addEventListener('input', () => { updateOpen(); });
  ui.edit.addEventListener('click', () => {
    editing = !editing;
    ui.edit.setAttribute('aria-pressed', String(editing));
    ui.edit.textContent = editing ? 'Show changes' : 'Edit';
    ui.text.hidden = !editing;
    ui.diff.hidden = editing;
    ui.legend.hidden = editing || cur >= last;
    if (editing) ui.text.focus(); else renderDiff();
  });
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

/** Line diff (longest common subsequence): [['same'|'add'|'del', line], …]. */
export function diffLines(a, b) {
  const n = a.length, m = b.length;
  const L = Array.from({ length: n + 1 }, () => new Uint16Array(m + 1));
  for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) L[i][j] = a[i] === b[j] ? L[i + 1][j + 1] + 1 : Math.max(L[i + 1][j], L[i][j + 1]);
  const out = [];
  let i = 0, j = 0;
  while (i < n && j < m) {
    if (a[i] === b[j]) { out.push(['same', b[j]]); i++; j++; }
    else if (L[i + 1][j] >= L[i][j + 1]) out.push(['del', a[i++]]);
    else out.push(['add', b[j++]]);
  }
  while (i < n) out.push(['del', a[i++]]);
  while (j < m) out.push(['add', b[j++]]);
  return out;
}
