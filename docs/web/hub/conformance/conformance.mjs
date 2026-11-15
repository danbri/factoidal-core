// The Hub Conformance page: Test262 first, then WPT, from data.json and history.json
// (written by tests/browser-wpt/passmap-data.py --hub; schema data.schema.json).
//
// The page is built as HTML strings by pure functions (no DOM at import), so Node tests can
// render it with sample data (tests/hub/conformance_test.mjs). mount() is the browser part:
// it fetches the two files, writes the HTML, loads d3 (vendored, /vendor/observable/d3.esm.js)
// only for the treemap, and wires the controls.

export const NAMES = {us: 'Foafnaut', chrome: 'Chrome', firefox: 'Firefox', safari: 'Safari', edge: 'Edge', servo: 'Servo', wpewebkit: 'WPE WebKit', ladybird: 'Ladybird'};
export const STALE_HOURS = 12;
const T262_EXPLAIN = {'EU bar': '80% EU bar', Goal: '90% goal'};

const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
const fmt = n => n == null ? 'n/a' : Number(n).toLocaleString('en-GB');
const p1 = x => x == null ? 'n/a' : (x * 100).toFixed(1) + '%';          // share 0..1
const p2 = x => x == null ? 'n/a' : (x * 100).toFixed(2) + '%';
const when = iso => iso ? iso.replace('T', ' ').slice(0, 16) + ' UTC' : 'n/a';
const ageH = (iso, now) => (now - Date.parse(iso)) / 36e5;
const ageText = h => h < 48 ? Math.round(h) + ' hours' : Math.round(h / 24) + ' days';
const commitLink = c => `<a href="https://github.com/danbri/factoidal-core/commit/${esc(c)}">${esc(String(c).slice(0, 9))}</a>`;

/** Which engines have a column in each stratum row: [name, chrome subtests, Foafnaut, ...browsers, run, names]. */
export function engines(D) {
  const list = [{k: 'us', i: 2, name: 'Foafnaut', sub: 'BubblePopJS, full run, measured'}];
  D.engines.forEach((k, j) => {
    const b = D.browsers[k] || {};
    list.push({k, i: 3 + j, name: NAMES[k] || k,
      sub: [String(b.browser_version || '').split(' ')[0], b.os_name, b.channel === 'experimental' ? 'experimental' : ''].filter(Boolean).join(', ')});
  });
  return list;
}

function missingRows(D) {
  return Object.entries(D.missing || {}).map(([b, why]) =>
    `<div class="row miss"><span>${esc(NAMES[b] || b)}</span><span class="why">${esc(NAMES[b] || b)}: ${esc(why)}</span></div>`).join('');
}

function bar(share, marks, label) {
  const w = Math.max(0, Math.min(100, share * 100));
  return `<div class="hbar" role="img" aria-label="${esc(label)}"><div class="fill" style="width:${w.toFixed(2)}%"></div>` +
    marks.map(([l, v], j) => `<i class="mk${(marks.length - 1 - j) % 2 ? ' up' : ' down'}" style="left:${v}%"><span>${esc(l)} ${v}%</span></i>`).join('') + '</div>';
}

function compareRows(rows, marks) {
  return '<div class="cmp">' + rows.map(r => {
    const w = Math.max(0, Math.min(100, r.share * 100));
    return `<div class="row${r.us ? ' us' : ''}"><span>${r.us ? '<b>' + esc(r.name) + '</b>' : esc(r.name)}${r.sub ? `<small>${esc(r.sub)}</small>` : ''}</span>` +
      `<span class="track"><span class="fill" style="width:${w.toFixed(2)}%"></span>${marks.map(m => `<i class="tick" style="left:${m[1]}%"></i>`).join('')}</span>` +
      `<span class="v">${p1(r.share)}</span></div>`;
  }).join('') + '</div>';
}

/** A line chart of shares over time as an SVG string. series: [{label, cls, pts: [{t, v, tip}]}]. */
export function lineChart({width, height = 220, series, targets = [], title}) {
  const W = Math.max(280, Math.round(width)), H = height, m = {l: 40, r: 12, t: 14, b: 26};
  const pts = series.flatMap(s => s.pts);
  if (!pts.length) return `<p class="muted">No runs to chart yet.</p>`;
  const vals = pts.map(p => p.v).concat(targets.map(t => t[1] / 100));
  let lo = Math.floor(Math.min(...vals) * 10) / 10, hi = Math.min(1, Math.ceil(Math.max(...vals) * 10 + 0.0001) / 10);
  if (hi - lo < 0.1) lo = Math.max(0, hi - 0.1);
  const t0 = Math.min(...pts.map(p => p.t)), t1 = Math.max(...pts.map(p => p.t));
  const x = t => t1 === t0 ? (m.l + W - m.r) / 2 : m.l + (t - t0) / (t1 - t0) * (W - m.l - m.r);
  const y = v => m.t + (hi - v) / (hi - lo) * (H - m.t - m.b);
  let g = '';
  for (let v = lo; v <= hi + 1e-9; v += 0.1) {
    g += `<line class="grid" x1="${m.l}" x2="${W - m.r}" y1="${y(v).toFixed(1)}" y2="${y(v).toFixed(1)}"/><text class="ax" x="${m.l - 6}" y="${(y(v) + 4).toFixed(1)}" text-anchor="end">${Math.round(v * 100)}%</text>`;
  }
  for (const [l, v] of targets) {
    const yy = y(v / 100).toFixed(1);
    g += `<line class="target" x1="${m.l}" x2="${W - m.r}" y1="${yy}" y2="${yy}"/><text class="tl" x="${m.l + 4}" y="${(+yy - 4).toFixed(1)}">${esc(l)} ${v}%</text>`;
  }
  const nt = W < 520 ? 1 : 3, ticks = t1 === t0 ? [t0] : Array.from({length: nt + 1}, (_, i) => t0 + (t1 - t0) * i / nt);
  const dfmt = t => new Date(t).toLocaleDateString('en-GB', {day: 'numeric', month: 'short', timeZone: 'UTC'}) + (t1 - t0 < 4 * 864e5 ? ' ' + new Date(t).toISOString().slice(11, 16) : '');
  ticks.forEach((t, i) => { g += `<text class="ax" x="${x(t).toFixed(1)}" y="${H - 6}" text-anchor="${i === 0 && ticks.length > 1 ? 'start' : i === ticks.length - 1 && ticks.length > 1 ? 'end' : 'middle'}">${esc(dfmt(t))}</text>`; });
  for (const s of series) {
    const ps = s.pts.slice().sort((a, b) => a.t - b.t);
    if (ps.length > 1) g += `<path class="ln ${s.cls}" d="${ps.map((p, i) => (i ? 'L' : 'M') + x(p.t).toFixed(1) + ' ' + y(p.v).toFixed(1)).join('')}"/>`;
    g += ps.map(p => `<g class="pt"><circle class="dot ${s.cls}" cx="${x(p.t).toFixed(1)}" cy="${y(p.v).toFixed(1)}" r="4"/><circle class="hit" cx="${x(p.t).toFixed(1)}" cy="${y(p.v).toFixed(1)}" r="10"><title>${esc(s.label + ': ' + p.tip)}</title></circle></g>`).join('');
    const last = ps[ps.length - 1];
    if (series.length > 1) g += `<text class="dl ${s.cls}" x="${Math.min(x(last.t) - 6, W - m.r - 4).toFixed(1)}" y="${(y(last.v) + (s.cls === 's2' ? 16 : -8)).toFixed(1)}" text-anchor="end">${esc(s.label)}</text>`;
  }
  const legend = series.length > 1 ? `<div class="legend">${series.map(s => `<span><i class="sw ${s.cls}"></i>${esc(s.label)}</span>`).join('')}</div>` : '';
  return legend + `<svg class="chart" viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="${esc(title)}">${g}</svg>`;
}

const tPoint = (iso, v, tip) => ({t: Date.parse(iso), v, tip});

function staleNote(iso, now, what) {
  const h = ageH(iso, now);
  return h > STALE_HOURS ? `<p class="stale">${esc(what)} is ${ageText(h)} old (finished ${when(iso)}). Newer runs may be recorded; this page is refreshed every 3 hours.</p>` : '';
}

/** The Test262 section: full Test262 first and largest, then Test262 through WPT. */
export function test262HTML(D, H, {now, width}) {
  const T = D.test262, F = T.full, w = T.wpt, marks = T.targets;
  let h = '<section class="suite t262" id="test262" aria-labelledby="t262h"><h2 id="t262h">Test262</h2>' +
    '<p class="muted">The ECMAScript conformance suite, run on BubblePopJS, the built-in JavaScript engine. The EU browser-engine bar for Test262 is 80%; the project goal is 90%.</p>';
  if (F && F.latest) {
    const x = F.latest, nx = marks.find(t => t[1] / 100 > x.share);
    h += '<div class="card hero"><h3>Full Test262</h3>' +
      `<div class="big"><b>${p1(x.share)}</b><span>${fmt(x.passed)} of ${fmt(x.total)} tests passed</span></div>` +
      (x.shareEx != null ? `<div class="big second"><b>${p1(x.shareEx)}</b><span>without the excluded features${x.excludedFeatures && x.excludedFeatures.length ? ' (' + x.excludedFeatures.map(esc).join(', ') + ')' : ''}</span></div>` : '') +
      bar(x.share, marks, `Full Test262 ${p1(x.share)}; EU bar 80%, goal 90%`) +
      `<p class="muted">${nx ? fmt(Math.ceil(nx[1] / 100 * x.total - x.passed)) + ' more passing tests reach the ' + T262_EXPLAIN[nx[0]] + '.' : 'Above the 90% goal.'} ` +
      `Run finished ${when(x.finished)}, engine ${commitLink(x.engine)}, ${esc(x.where)}${x.workflow ? `, <a href="${esc(x.workflow)}">workflow run</a>` : ''}.</p>` +
      staleNote(x.finished, now, 'The newest full Test262 run') +
      '<p class="muted">Other engines: no full Test262 runs of other engines are recorded here; Test262 through WPT, below, compares them on the same tests.</p>';
    const dirs = (x.directories || []).map(([name, total, passed]) => ({name, total, passed, fail: total - passed})).filter(d => d.fail > 0).sort((a, b) => b.fail - a.fail);
    if (dirs.length) {
      h += '<h4>Directories with the most failing tests</h4><div class="tw"><table class="num-table"><thead><tr><th>Directory</th><th>Tests</th><th>Failing</th><th>Passed</th></tr></thead><tbody>' +
        dirs.slice(0, 12).map(d => `<tr><td>${esc(d.name)}</td><td>${fmt(d.total)}</td><td><b>${fmt(d.fail)}</b></td><td>${p1(d.passed / d.total)}</td></tr>`).join('') + '</tbody></table></div>';
    }
    h += '<h4>Full Test262 over time</h4>' + lineChart({width, series: [
      {label: 'Full Test262', cls: 's1', pts: H.test262.map(r => tPoint(r.finished, r.share, `${p1(r.share)}, ${r.engine}, ${when(r.finished)}`))},
      ...(H.test262.some(r => r.shareEx != null) ? [{label: 'Without excluded features', cls: 's2', pts: H.test262.filter(r => r.shareEx != null).map(r => tPoint(r.finished, r.shareEx, `${p1(r.shareEx)}, ${r.engine}`))}] : [])],
      targets: marks, title: 'Full Test262 share over time, with the 80% EU bar and the 90% goal'}) + '</div>';
  } else {
    h += '<div class="card hero empty"><h3>Full Test262</h3><p><b>No full Test262 run recorded yet.</b> When the Test262 workflow records its first valid run, its share, its share without the excluded features, the directories with the most failures and its history appear here. Until then, Test262 through WPT, below, is the Test262 number.</p></div>';
  }
  if (w) {
    const share = w.us / w.u, nx = marks.find(t => t[1] / 100 > share);
    const rows = [{name: 'Foafnaut', us: true, share}].concat(D.engines.filter(b => w.browsers[b] != null).map(b => ({name: NAMES[b] || b, share: w.browsers[b] / w.u})));
    h += `<div class="card${F ? '' : ' hero'}"><h3>Test262 through WPT</h3>` +
      `<div class="big${F ? ' second' : ''}"><b>${p1(share)}</b><span>${fmt(w.us)} of ${fmt(w.u)} tests in WPT's third_party/test262, in the full WPT run below</span></div>` +
      bar(share, marks, `Test262 through WPT ${p1(share)}; EU bar 80%, goal 90%`) +
      `<p class="muted">${nx ? fmt(Math.ceil(nx[1] / 100 * w.u - w.us)) + ' more passing tests reach the ' + T262_EXPLAIN[nx[0]] + '.' : 'Above the 90% goal.'} Other engines from wpt.fyi at the same WPT commit.</p>` +
      compareRows(rows, marks) + `<div class="cmp">${missingRows(D)}</div>` +
      '<h4>Test262 through WPT over time</h4>' + lineChart({width, series: [{label: 'Test262 through WPT', cls: 's1',
        pts: H.test262wpt.map(r => tPoint(r.finished, r.share, `${p1(r.share)}, ${r.engine}, WPT ${r.wpt}`))}], targets: marks,
        title: 'Test262 through WPT share over time, with the 80% EU bar and the 90% goal'}) + '</div>';
  }
  return h + '</section>';
}

/** The WPT section: headline, engines, history chart, then the treemap slot and the tables. */
export function wptHTML(D, H, {now, width}) {
  const L = D.latest, ENG = engines(D), nx = D.milestones.find(m => m[1] > L.share);
  let h = '<section class="suite wpt" id="wpt" aria-labelledby="wpth"><h2 id="wpth">Web Platform Tests</h2><div class="card">' +
    `<div class="big"><b>${(L.share).toFixed(2)}%</b><span>${fmt(L.passed)} of the ${fmt(L.denominator)} WPT subtests that Chrome runs</span></div>` +
    `<div class="big second"><b>${(L.shareEx).toFixed(2)}%</b><span>without the encoding directory</span></div>` +
    bar(L.share / 100, D.milestones, `WPT ${L.share.toFixed(2)}%; milestones ${D.milestones.map(m => m[0] + ' ' + m[1] + '%').join(', ')}`) +
    `<p class="muted">${nx ? 'The next milestone, ' + esc(nx[0]) + ' at ' + nx[1] + '%, is ' + fmt(Math.ceil(nx[1] / 100 * L.denominator - L.passed)) + ' subtests away. ' : ''}` +
    `Full run of all ${fmt(L.tests)} tests, finished ${when(L.finished)}, engine ${commitLink(L.engine)}, ${esc(L.where)}, WPT ${esc(L.wpt)}${L.workflow ? `, <a href="${esc(L.workflow)}">workflow run</a>` : ''}.</p>` +
    staleNote(L.finished, now, 'The newest full WPT run') +
    '<h4>WPT by engine</h4>' +
    `<p class="muted">Every engine at the run's WPT commit (${esc(D.wptCommit.slice(0, 10))}), on Chrome's subtests there. Tap an engine to colour the map by it.</p>` +
    '<div class="cmp engines">' + ENG.map((e, j) => {
      const s = Math.min(1, D.tot[e.k] / D.tot.u);
      return `<button class="row eng${j === 0 ? ' us' : ''}" data-eng="${j}" aria-pressed="${j === 0}"><span>${j === 0 ? '<b>' + esc(e.name) + '</b>' : esc(e.name)}<small>${esc(e.sub)}</small></span>` +
        `<span class="track"><span class="fill" style="width:${(s * 100).toFixed(2)}%"></span>${D.milestones.map(m => `<i class="tick" style="left:${m[1]}%"></i>`).join('')}</span><span class="v">${p1(s)}</span></button>`;
    }).join('') + missingRows(D) + '</div>' +
    '<h4>WPT over time</h4>' + lineChart({width, series: [
      {label: 'All subtests', cls: 's1', pts: H.wpt.map(r => tPoint(r.finished, r.share, `${p2(r.share)}, ${r.engine}, WPT ${r.wpt}`))},
      {label: 'Without encoding', cls: 's2', pts: H.wpt.map(r => tPoint(r.finished, r.shareEx, `${p2(r.shareEx)}, ${r.engine}`))}],
      targets: [D.milestones[D.milestones.length - 1]].map(m => ['EU bar', m[1]]), title: 'WPT share over time, all subtests and without encoding'}) + '</div>' +
    '<div class="card"><h4>Map of WPT directories</h4>' +
    '<p class="muted">Each rectangle is a WPT directory; its area is the number of Chrome\'s subtests in it, its colour the share the selected engine passes. Tap a rectangle for its numbers.</p>' +
    '<div class="controls"><span class="crumb" id="crumb">All directories</span><button class="btn" id="up" hidden>Back to all directories</button>' +
    '<button class="btn" id="areaSqrt" aria-pressed="false">Area: square root</button>' +
    '<span class="ramp"><span>0%</span><span class="rbar"></span><span>100%</span></span></div>' +
    '<div id="map" role="group" aria-label="Treemap of WPT directories"></div><div class="detail" id="detail" aria-live="polite"></div></div>' +
    '<div class="card"><h4>Top-level directories</h4><p class="muted">Tap a column heading to sort by it.</p><div class="tw"><table id="tbl" class="num-table"></table></div><button class="btn" id="more" hidden></button></div>' +
    '<div class="card"><h4>Full measured runs</h4><p class="muted">Complete, valid runs only, one row per engine commit (its newest run), each on its own WPT commit.</p><div class="tw"><table class="num-table"><thead><tr><th>Finished (UTC)</th><th>Engine</th><th>WPT</th><th>Where</th><th>Share</th><th>Without encoding</th></tr></thead><tbody>' +
    H.wpt.map(r => `<tr><td>${esc(r.finished.replace('T', ' ').slice(0, 16))}</td><td>${esc(r.engine)}</td><td>${esc(r.wpt)}</td><td>${esc(r.where)}</td><td><b>${p2(r.share)}</b></td><td>${p2(r.shareEx)}</td></tr>`).join('') +
    '</tbody></table></div></div></section>';
  return h;
}

/** The whole page body below the title, except the parts mount() fills (treemap, directory table). */
export function pageHTML(D, H, {now = Date.now(), width = 760} = {}) {
  const newest = [D.latest.finished, D.test262.full?.latest?.finished].filter(Boolean).sort().pop();
  const hh = ageH(newest, now);
  const head = `<p class="asof">Data as of <b>${when(newest)}</b> (newest run). Page data built ${when(D.generatedAt)}.</p>` +
    (hh > STALE_HOURS ? `<p class="stale">The newest run here is ${ageText(hh)} old. Runs are recorded by the release-tests and Test262 workflows; this page's data is regenerated every 3 hours and when a run is recorded.</p>` : '');
  const notes = '<section class="notes"><h2>About these numbers</h2>' +
    '<p><b>Test262.</b> Full Test262 runs are the suite=test262 rows of runs.csv. Test262 through WPT is WPT\'s third_party/test262 directory, scored like the rest of WPT in the full WPT run: one subtest per test.</p>' +
    '<p><b>WPT.</b> Every share is of Chrome\'s subtests at the run\'s WPT commit, with each engine\'s passes in a test capped at Chrome\'s count for it. About half of all WPT subtests are in the encoding directory, one per character of the legacy encodings. Milestones: ' + D.milestones.map(m => esc(m[0]) + ' ' + m[1] + '%').join(', ') + '.</p>' +
    '<p><b>Other browsers.</b> wpt.fyi runs at the same WPT commit only; runs of other commits are never used in their place, and a run that reports fewer than 95% of Chrome\'s tests is not shown.' + (Object.keys(D.missing || {}).length ? ' Not shown: ' + Object.entries(D.missing).map(([b, w]) => esc(NAMES[b] || b) + ' (' + esc(w) + ')').join(', ') + '.' : '') + '</p>' +
    '<p><b>Source.</b> The data files <a href="data.json">data.json</a> and <a href="history.json">history.json</a> are written by tests/browser-wpt/passmap-data.py from the wpt-scores branch of danbri/factoidal-builds, and kept with their history on its <a href="https://github.com/danbri/factoidal-builds/commits/hub-data">hub-data</a> branch.</p></section>';
  return head + test262HTML(D, H, {now, width}) + wptHTML(D, H, {now, width}) + notes;
}

/** Strata rows as objects. */
export function strata(D) {
  return D.strata.map(r => ({name: r[0], top: r[0].split('/')[0], u: r[1], v: r, run: r[r.length - 2], n: r[r.length - 1]}));
}

const RAMP = ['--r0', '--r1', '--r2', '--r3', '--r4', '--r5'];

/** The treemap as positioned buttons. colours: 6 ramp colours light to dark. */
export function treemapHTML(D, {d3, width, height, eng = 0, zoom = null, sqrt = false, sel = null, colours}) {
  const S = strata(D), E = engines(D)[eng];
  const val = s => sqrt ? Math.sqrt(s.u) : s.u;
  let root;
  if (zoom) root = {children: S.filter(s => s.top === zoom)};
  else root = {children: [...d3.group(S, s => s.top)].map(([k, a]) => a.length > 1 ? {name: k, children: a} : a[0])};
  const h = d3.hierarchy(root).sum(d => d.children ? 0 : val(d)).sort((a, b) => b.value - a.value);
  d3.treemap().size([width, height]).paddingInner(2)
    .paddingTop(n => n.depth === 1 && n.children && (n.x1 - n.x0 > 60) && (n.y1 - n.y0 > 40) ? 14 : 0).round(true)(h);
  const interp = d3.interpolateRgbBasis(colours);
  const ink = c => { const {r, g, b} = d3.rgb(c); return (0.2126 * r + 0.7152 * g + 0.0722 * b) / 255 > 0.55 ? '#0e131a' : '#ffffff'; };
  let out = '';
  if (!zoom) h.children.filter(n => n.children).forEach(n => {
    const w = n.x1 - n.x0, hh = n.y1 - n.y0;
    if (w > 60 && hh > 40) out += `<div class="grp" style="left:${n.x0}px;top:${n.y0}px;width:${w}px">${esc(n.data.name)}</div>`;
  });
  h.leaves().forEach(n => {
    const s = n.data, w = n.x1 - n.x0, hh = n.y1 - n.y0;
    if (w < 1 || hh < 1) return;
    const share = Math.min(1, s.v[E.i] / s.u), c = interp(share), idx = S.findIndex(x => x.name === s.name);
    const label = s.name.includes('/') && (zoom || (n.parent && n.parent.data.name)) ? s.name.slice(s.top.length + 1) : s.name;
    out += `<button class="cell${sel === s.name ? ' on' : ''}" data-i="${idx}" style="left:${n.x0}px;top:${n.y0}px;width:${w}px;height:${hh}px;background:${c};color:${ink(c)}" ` +
      `aria-label="${esc(s.name)}: ${esc(E.name)} passes ${p1(share)} of ${fmt(s.u)} subtests" title="${esc(s.name)}: ${p1(share)}">` +
      (w > 44 && hh > 16 ? `<b>${esc(label)}</b>` + (hh > 30 ? `<span>${p1(share)}</span>` : '') : '') + '</button>';
  });
  return out;
}

export function detailHTML(D, name, eng, zoom) {
  const S = strata(D), s = S.find(x => x.name === name);
  if (!s) return '<span class="muted">Tap a rectangle to see the numbers for that directory.</span>';
  const kids = S.filter(x => x.top === s.top).length;
  return `<div class="head"><b>${esc(s.name)}</b><span class="muted">${fmt(s.u)} of Chrome's subtests, in ${fmt(s.n)} tests</span></div>` +
    compareRows(engines(D).map((e, j) => ({name: e.name, us: j === eng, share: Math.min(1, s.v[e.i] / s.u)})), []) +
    (kids > 1 && zoom !== s.top ? `<button class="btn" id="zin" data-top="${esc(s.top)}">Show only ${esc(s.top)} (${kids} parts)</button>` : '');
}

export function tableHTML(D, {eng = 0, sortCol = 'u', sortDir = -1, showAll = false} = {}) {
  const S = strata(D), ENG = engines(D), byTop = new Map();
  for (const s of S) {
    const r = byTop.get(s.top) || {k: s.top, u: 0, p: ENG.map(() => 0)};
    r.u += s.u; ENG.forEach((e, i) => { r.p[i] += s.v[e.i]; });
    byTop.set(s.top, r);
  }
  const rows = [...byTop.values()].map(r => ({...r, gap: Math.max(0, (r.p[1] ?? 0) - r.p[0])}));
  const share = (r, i) => r.u ? Math.min(1, r.p[i] / r.u) : 0;
  const key = sortCol === 'k' ? r => r.k : sortCol === 'u' ? r => r.u : sortCol === 'gap' ? r => r.gap : r => share(r, +sortCol);
  rows.sort((a, b) => { const x = key(a), y = key(b); const c = typeof x === 'string' ? x.localeCompare(y) : x - y; return c * sortDir || b.u - a.u; });
  const cols = [['k', 'Directory'], ['u', 'Subtests']].concat(ENG.map((e, i) => [String(i), e.name]), [['gap', (ENG[1]?.name || 'Chrome') + ' passes, Foafnaut not']]);
  return {rows: rows.length, html: '<thead><tr>' + cols.map(([c, label]) => {
    const on = c === sortCol;
    return `<th aria-sort="${on ? (sortDir < 0 ? 'descending' : 'ascending') : 'none'}"><button class="sortb" data-c="${c}">${esc(label)}${on ? (sortDir < 0 ? ' ↓' : ' ↑') : ''}</button></th>`;
  }).join('') + '</tr></thead><tbody>' + (showAll ? rows : rows.slice(0, 30)).map(r =>
    `<tr><td>${esc(r.k)}</td><td>${fmt(r.u)}</td>${ENG.map((e, i) => `<td>${i === eng ? '<b>' : ''}${p1(share(r, i))}${i === eng ? '</b>' : ''}</td>`).join('')}<td>${fmt(r.gap)}</td></tr>`).join('') + '</tbody>'};
}

/** Browser: fetch the data, render, wire the controls. */
export async function mount(root, {d3url, base = './'} = {}) {
  let D, H;
  try {
    const get = async n => { const r = await fetch(base + n, {cache: 'no-cache'}); if (!r.ok) throw Error(`${n}: HTTP ${r.status}`); return r.json(); };
    [D, H] = await Promise.all([get('data.json'), get('history.json')]);
  } catch (e) {
    root.innerHTML = `<p class="stale">No conformance data in this build of the site (${esc(e.message)}). The Pages build copies data.json and history.json from the hub-data branch of danbri/factoidal-builds.</p>`;
    return;
  }
  const st = {eng: 0, zoom: null, sqrt: false, sel: null, sortCol: 'u', sortDir: -1, showAll: false};
  const width = () => Math.min(root.clientWidth || 760, 1100) - 30;
  const draw = () => { root.innerHTML = pageHTML(D, H, {now: Date.now(), width: width()}); wire(); };
  let d3 = null;
  const $ = id => root.querySelector('#' + id);
  const colours = () => { const cs = getComputedStyle(root); return RAMP.map(v => cs.getPropertyValue(v).trim() || '#888'); };
  const drawMap = async () => {
    const map = $('map'); if (!map) return;
    if (!d3) { map.innerHTML = '<p class="muted" style="padding:8px">Loading the map…</p>'; d3 = await import(d3url); }
    map.innerHTML = treemapHTML(D, {d3, width: map.clientWidth, height: map.clientHeight, ...st, colours: colours()});
    $('crumb').textContent = st.zoom ? 'Directory: ' + st.zoom : 'All directories';
    $('up').hidden = !st.zoom;
  };
  const drawDetail = () => { $('detail').innerHTML = detailHTML(D, st.sel, st.eng, st.zoom); };
  const drawTable = () => {
    const t = tableHTML(D, st); $('tbl').innerHTML = t.html;
    const more = $('more'); more.hidden = t.rows <= 30; more.textContent = st.showAll ? 'Show the first 30' : `Show all ${t.rows} directories`;
  };
  function wire() {
    root.querySelectorAll('button.eng').forEach(b => b.onclick = () => {
      st.eng = +b.dataset.eng;
      root.querySelectorAll('button.eng').forEach(x => x.setAttribute('aria-pressed', x === b));
      drawMap(); drawDetail(); drawTable();
    });
    $('map').onclick = e => { const c = e.target.closest('.cell'); if (!c) return; st.sel = strata(D)[+c.dataset.i].name; drawMap(); drawDetail(); };
    $('detail').onclick = e => { const z = e.target.closest('#zin'); if (z) { st.zoom = z.dataset.top; drawMap(); drawDetail(); } };
    $('up').onclick = () => { st.zoom = null; drawMap(); drawDetail(); };
    $('areaSqrt').onclick = () => { st.sqrt = !st.sqrt; $('areaSqrt').setAttribute('aria-pressed', st.sqrt); drawMap(); };
    $('tbl').onclick = e => { const b = e.target.closest('.sortb'); if (!b) return; const c = b.dataset.c;
      if (c === st.sortCol) st.sortDir = -st.sortDir; else { st.sortCol = c; st.sortDir = c === 'k' ? 1 : -1; } drawTable(); };
    $('more').onclick = () => { st.showAll = !st.showAll; drawTable(); };
    drawMap(); drawDetail(); drawTable();
  }
  draw();
  if (location.hash) document.getElementById(location.hash.slice(1))?.scrollIntoView();
  let rt, lastW = width();
  addEventListener('resize', () => { clearTimeout(rt); rt = setTimeout(() => { if (width() !== lastW) { lastW = width(); draw(); } }, 150); });
  matchMedia('(prefers-color-scheme: dark)').addEventListener('change', drawMap);
  return {D, H};
}
