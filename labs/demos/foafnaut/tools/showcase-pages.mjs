// Write the generated showcase pages of foafnaut (issues 1268 and 1270).
//
//     node labs/demos/foafnaut/tools/showcase-pages.mjs
//
// Writes pages/showcase-dataviz.html, showcase-lettering.html and showcase-tables-svg.html.
// The other showcase pages are written by hand.
//
// Plain ECMAScript with no packages. Every layout function (bars, lines, tidy tree,
// circle packing, force layout, lettering, tables) is a pure function from data to an
// SVG string, so a page script can call the same functions in a browser later. Only
// `main` reads files and writes the pages. Every label is SVG `text`, `tspan` or
// `textPath`; the Lean engine shapes and draws it with the held font.

export const PALETTE = ["#3b6fb6", "#e07b39", "#3f9d6b", "#c4455a", "#7a5cb8", "#8a6d3b", "#cc6aa8", "#6b7480"];
export const INK = "#22303c", MUTED = "#5b6876", GRID = "#d8dee6";
export const FONT = "Noto Sans";

/** A number with at most two decimals, as the SVG is written. */
export function fmt(v) {
  const s = (Math.round(v * 100) / 100).toFixed(2).replace(/0+$/, "").replace(/\.$/, "");
  return s === "-0" || s === "" ? "0" : s;
}

const escapeText = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
const thousands = (n) => n.toLocaleString("en-US");

/** A line of SVG text with its baseline at (x, y), turned by angle degrees about (x, y). */
export function label(text, x, y, size, fill = INK, anchor = "start", angle = 0) {
  const turn = angle ? ` transform="rotate(${fmt(angle)} ${fmt(x)} ${fmt(y)})"` : "";
  const a = anchor === "start" ? "" : ` text-anchor="${anchor}"`;
  return `<text x="${fmt(x)}" y="${fmt(y)}" font-size="${fmt(size)}" fill="${fill}"${a}${turn}>${escapeText(text)}</text>`;
}

/** Text along a path: centred on the path, as `startOffset="50%"` and `text-anchor="middle"` place it. */
export function onPath(text, href, size, fill = INK, spacing = 0) {
  const ls = spacing ? ` letter-spacing="${fmt(spacing)}"` : "";
  return `<text font-size="${fmt(size)}" fill="${fill}"${ls}><textPath href="#${href}" startOffset="50%" text-anchor="middle">${escapeText(text)}</textPath></text>`;
}

/** Points of a curve fn(t), t in [0, 1], as path data: n steps, every eighth point kept. */
export function sampledPath(fn, n = 800) {
  const pts = [];
  for (let i = 0; i <= n; i++) pts.push(fn(i / n));
  const kept = pts.filter((_, i) => i % 8 === 0);
  if ((n % 8) !== 0) kept.push(pts[n]);
  return "M" + kept.map(([x, y]) => `${fmt(x)} ${fmt(y)}`).join(" L");
}

const svgOpen = (w, h, viewBox = `0 0 ${w} ${h}`) => `<svg width="${w}" height="${h}" viewBox="${viewBox}" font-family="${FONT}">`;

// ---------------------------------------------------------------- data

export function groupOf(module) {
  for (const [prefix, group] of [["SVG", "SVG"], ["Web", "HTML and CSS"], ["Font", "Fonts"], ["Foaf", "FOAF"],
    ["Solving", "Solving"], ["Image", "Images"], ["Render", "GPU plan"], ["Scene", "GPU plan"]])
    if (module.startsWith(prefix)) return group;
  return "Other";
}
export const GROUPS = ["SVG", "HTML and CSS", "Fonts", "FOAF", "Solving", "Images", "GPU plan", "Other"];
export const COLOUR = Object.fromEntries(GROUPS.map((g, i) => [g, PALETTE[i]]));

const lineCount = (text) => (text.match(/\n/g) ?? []).length;

/** Hours of daylight at a latitude on a day of the year, from the solar declination. */
export function dayLength(lat, day) {
  const decl = -23.44 * Math.cos(2 * Math.PI * (day + 10) / 365);
  const x = -Math.tan(lat * Math.PI / 180) * Math.tan(decl * Math.PI / 180);
  return x < -1 ? 24 : x > 1 ? 0 : 24 * Math.acos(x) / Math.PI;
}

/** A small seeded generator (mulberry32), so the force layout is the same each run. */
export function random(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// ---------------------------------------------------------------- charts

/** files: {module name: source text}. */
export function barChart(files) {
  const lines = Object.fromEntries(GROUPS.map((g) => [g, 0]));
  for (const [m, text] of Object.entries(files)) lines[groupOf(m)] += lineCount(text);
  const data = Object.entries(lines).filter(([, n]) => n).sort((a, b) => b[1] - a[1]);
  const W = 760, H = 340, L = 64, B = 300, T = 20;
  const top = Math.ceil(Math.max(...data.map(([, n]) => n)) / 2000) * 2000;
  const step = (W - L - 16) / data.length;
  const out = [svgOpen(W, H)];
  for (let v = 0; v <= top; v += 2000) {
    const y = B - (B - T) * v / top;
    out.push(`<line x1="${L}" y1="${fmt(y)}" x2="${W - 8}" y2="${fmt(y)}" stroke="${GRID}" stroke-width="1"/>`);
    out.push(label(thousands(v), L - 8, y + 4, 11, MUTED, "end"));
  }
  data.forEach(([g, n], i) => {
    const x = L + i * step + step * 0.15, h = (B - T) * n / top;
    out.push(`<rect x="${fmt(x)}" y="${fmt(B - h)}" width="${fmt(step * 0.7)}" height="${fmt(h)}" rx="3" fill="${COLOUR[g]}"/>`);
    out.push(label(thousands(n), x + step * 0.35, B - h - 6, 11, INK, "middle"));
    out.push(label(g, x + step * 0.35, B + 18, 12, INK, "middle"));
  });
  out.push(`<line x1="${L}" y1="${B}" x2="${W - 8}" y2="${B}" stroke="${INK}" stroke-width="1.5"/>`, "</svg>");
  return {svg: out.join("\n"), total: data.reduce((s, [, n]) => s + n, 0), count: Object.keys(files).length};
}

export function lineChart() {
  const W = 760, H = 330, L = 52, B = 290, T = 16, R = 120;
  const series = [["Equator", 0, PALETTE[2], 0], ["Lisbon 38.7° N", 38.7, PALETTE[1], -4],
    ["London 51.5° N", 51.5, PALETTE[0], 4], ["Tromsø 69.6° N", 69.6, PALETTE[3], 0]];
  const sx = (d) => L + (W - L - R) * d / 364, sy = (h) => B - (B - T) * h / 24;
  const out = [svgOpen(W, H)];
  for (let h = 0; h < 25; h += 6) {
    out.push(`<line x1="${L}" y1="${fmt(sy(h))}" x2="${W - R}" y2="${fmt(sy(h))}" stroke="${GRID}" stroke-width="1" stroke-dasharray="3 3"/>`);
    out.push(label(`${h} h`, L - 8, sy(h) + 4, 11, MUTED, "end"));
  }
  ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"].forEach((m, i) => {
    const d = i * 365 / 12;
    out.push(`<line x1="${fmt(sx(d))}" y1="${B}" x2="${fmt(sx(d))}" y2="${B + 5}" stroke="${INK}" stroke-width="1"/>`);
    out.push(label(m, sx(d + 15), B + 20, 11, MUTED, "middle"));
  });
  const curve = (lat) => {
    const pts = [];
    for (let d = 0; d < 365; d += 4) pts.push([sx(d), sy(dayLength(lat, d))]);
    pts.push([sx(364), sy(dayLength(lat, 364))]);
    return pts;
  };
  // London as an area under its curve, as a D3 area generator would make it.
  const london = curve(51.5);
  const area = `M${fmt(london[0][0])} ${B} ` + london.map(([x, y]) => `L${fmt(x)} ${fmt(y)}`).join(" ") + ` L${fmt(london.at(-1)[0])} ${B} Z`;
  out.push(`<path d="${area}" fill="${PALETTE[0]}" fill-opacity="0.12"/>`);
  for (const [name, lat, colour, nudge] of series) {
    const pts = curve(lat);
    out.push(`<path d="M${pts.map(([x, y]) => `${fmt(x)} ${fmt(y)}`).join(" L")}" fill="none" stroke="${colour}" stroke-width="2.5" stroke-linejoin="round"/>`);
    for (const d of [172, 355])
      out.push(`<circle cx="${fmt(sx(d))}" cy="${fmt(sy(dayLength(lat, d)))}" r="3.5" fill="white" stroke="${colour}" stroke-width="2"/>`);
    out.push(label(name, W - R + 8, pts.at(-1)[1] + 4 + nudge, 11, colour));
  }
  out.push(`<line x1="${L}" y1="${B}" x2="${W - R}" y2="${B}" stroke="${INK}" stroke-width="1.5"/>`, "</svg>");
  return out.join("\n");
}

export const TREE = ["foafnaut", [
  ["HTML", [["tokenizer", []], ["tree builder", []], ["DOM arena", []]]],
  ["CSS", [["selectors", []], ["cascade", []], ["block layout", []], ["inline layout", []]]],
  ["SVG", [["paths", []], ["strokes", []], ["dashes", []], ["gradients", []], ["clips", []]]],
  ["text", [["sfnt tables", []], ["shaper", []], ["outlines", []]]],
  ["GPU", [["render plan", []], ["WGSL", []], ["tiles", []]]],
]];

/** A tidy tree: leaves at equal spacing, each parent over the mean of its children. */
export function treeChart(tree = TREE) {
  const W = 760, H = 330, leaves = [];
  const walk = ([name, kids], depth) => {
    const rec = {name, depth, kids: kids.map((k) => walk(k, depth + 1))};
    if (!kids.length) { rec.x = leaves.length; leaves.push(rec); }
    else rec.x = rec.kids.reduce((s, k) => s + k.x, 0) / rec.kids.length;
    return rec;
  };
  const root = walk(tree, 0), n = leaves.length;
  const sx = (i) => 24 + (W - 48) * i / (n - 1), sy = (d) => 30 + d * 110;
  const links = [], nodes = [];
  const draw = (rec, colour) => {
    const x = sx(rec.x), y = sy(rec.depth);
    rec.kids.forEach((k, i) => {
      const c = rec.depth === 0 ? PALETTE[i] : colour, kx = sx(k.x), ky = sy(k.depth), my = (y + ky) / 2;
      links.push(`<path d="M${fmt(x)} ${fmt(y)} C${fmt(x)} ${fmt(my)} ${fmt(kx)} ${fmt(my)} ${fmt(kx)} ${fmt(ky)}" fill="none" stroke="${c}" stroke-opacity="0.55" stroke-width="1.5"/>`);
      draw(k, c);
    });
    const r = rec.depth < 2 ? 7 : 4.5;
    nodes.push(`<circle cx="${fmt(x)}" cy="${fmt(y)}" r="${r}" fill="${rec.kids.length ? colour : "white"}" stroke="${colour}" stroke-width="2"/>`);
    if (rec.depth === 2) nodes.push(label(rec.name, x + 3, y + 12, 11, INK, "start", 55));
    else nodes.push(label(rec.name, x + 11, y - 9, rec.depth === 0 ? 13 : 12, INK));
  };
  draw(root, INK);
  return [svgOpen(W, H), ...links, ...nodes, "</svg>"].join("\n");
}

/** Greedy circle packing: each circle goes to the free tangent place nearest the centre. */
export function pack(radii) {
  let placed = [];
  for (const r of radii) {
    if (!placed.length) { placed.push([0, 0, r]); continue; }
    if (placed.length === 1) { const [x0, y0, r0] = placed[0]; placed.push([x0 + r0 + r, y0, r]); continue; }
    let best;
    placed.forEach(([xa, ya, ra], i) => {
      for (const [xb, yb, rb] of placed.slice(i + 1)) {
        const d = Math.hypot(xb - xa, yb - ya), p = ra + r, q = rb + r;
        if (d === 0 || d > p + q || d < Math.abs(p - q)) continue;
        const a = (p * p - q * q + d * d) / (2 * d), h = Math.sqrt(Math.max(0, p * p - a * a));
        const mx = xa + a * (xb - xa) / d, my = ya + a * (yb - ya) / d;
        for (const sgn of [1, -1]) {
          const cx = mx + sgn * h * (yb - ya) / d, cy = my - sgn * h * (xb - xa) / d;
          if (placed.every(([x, y, rr]) => Math.hypot(cx - x, cy - y) >= rr + r - 1e-6)) {
            const dist = Math.hypot(cx, cy);
            if (!best || dist < best[0]) best = [dist, cx, cy];
          }
        }
      }
    });
    placed.push([best[1], best[2], r]);
  }
  const cx = placed.reduce((s, [x]) => s + x, 0) / placed.length, cy = placed.reduce((s, [, y]) => s + y, 0) / placed.length;
  placed = placed.map(([x, y, r]) => [x - cx, y - cy, r]);
  return {placed, radius: Math.max(...placed.map(([x, y, r]) => Math.hypot(x, y) + r))};
}

export function packChart(files) {
  const W = 760, H = 420, groups = {};
  for (const [m, text] of Object.entries(files)) (groups[groupOf(m)] ??= []).push([m, lineCount(text)]);
  const inner = GROUPS.filter((g) => groups[g]).map((g) => {
    const items = groups[g].slice().sort((a, b) => b[1] - a[1]);
    const {placed, radius} = pack(items.map(([, n]) => Math.sqrt(n) * 0.9));
    return [g, items, placed, radius + 4];
  });
  const outer = pack(inner.map(([, , , R]) => R));
  const scale = (H / 2 - 12) / outer.radius, ox0 = W / 2 - 120;
  const out = [svgOpen(W, H), `<circle cx="${fmt(ox0)}" cy="${H / 2}" r="${fmt(outer.radius * scale)}" fill="#f3f5f8" stroke="${GRID}"/>`];
  let legendY = 40;
  inner.forEach(([g, items, circles, R], i) => {
    const colour = COLOUR[g], [gx, gy] = outer.placed[i], cx = ox0 + gx * scale, cy = H / 2 + gy * scale;
    out.push(`<circle cx="${fmt(cx)}" cy="${fmt(cy)}" r="${fmt(R * scale)}" fill="${colour}" fill-opacity="0.10" stroke="${colour}" stroke-opacity="0.5"/>`);
    items.forEach((_, j) => {
      const [x, y, r] = circles[j];
      out.push(`<circle cx="${fmt(cx + x * scale)}" cy="${fmt(cy + y * scale)}" r="${fmt(r * scale)}" fill="${colour}" fill-opacity="0.75"/>`);
    });
    out.push(`<circle cx="${W - 250}" cy="${legendY - 4}" r="6" fill="${colour}" fill-opacity="0.75"/>`);
    out.push(label(`${g}: ${items.length} files, ${thousands(items.reduce((s, [, n]) => s + n, 0))} lines`, W - 238, legendY, 12, INK));
    legendY += 22;
  });
  out.push("</svg>");
  return out.join("\n");
}

/** The import graph of the Lean files: its largest connected part, laid out by a
spring-electric simulation with cooling, in the manner of d3-force. */
export function forceChart(files) {
  const W = 760, H = 460, names = Object.keys(files).sort();
  const index = new Map(names.map((m, i) => [m, i]));
  const edgeKeys = new Set();
  for (const [m, text] of Object.entries(files))
    for (const [, imp] of text.matchAll(/^import\s+(\S+)/gm))
      if (index.has(imp) && imp !== m) { const a = index.get(m), b = index.get(imp); edgeKeys.add(a < b ? `${a},${b}` : `${b},${a}`); }
  let edges = [...edgeKeys].map((k) => k.split(",").map(Number));
  const adj = new Map();
  for (const [a, b] of edges) { if (!adj.has(a)) adj.set(a, new Set()); if (!adj.has(b)) adj.set(b, new Set()); adj.get(a).add(b); adj.get(b).add(a); }
  const seen = new Set(); let best = [];
  for (const start of [...adj.keys()].sort((a, b) => a - b)) {
    if (seen.has(start)) continue;
    const comp = [], todo = [start]; seen.add(start);
    while (todo.length) { const v = todo.pop(); comp.push(v); for (const w of adj.get(v)) if (!seen.has(w)) { seen.add(w); todo.push(w); } }
    if (comp.length > best.length) best = comp;
  }
  const inBest = new Set(best), linked = [...best].sort((a, b) => a - b);
  edges = edges.filter(([a]) => inBest.has(a)).sort((p, q) => p[0] - q[0] || p[1] - q[1]);
  const rng = random(1268), pos = new Map(), vel = new Map(), degree = new Map();
  for (const i of linked) { pos.set(i, [(rng() * 2 - 1) * 200, (rng() * 2 - 1) * 150]); vel.set(i, [0, 0]); degree.set(i, 0); }
  for (const [a, b] of edges) { degree.set(a, degree.get(a) + 1); degree.set(b, degree.get(b) + 1); }
  let alpha = 1;
  for (let step = 0; step < 400; step++) {
    const f = new Map(linked.map((i) => [i, [0, 0]]));
    linked.forEach((i, ii) => {
      for (const j of linked.slice(ii + 1)) {
        const dx = pos.get(j)[0] - pos.get(i)[0], dy = pos.get(j)[1] - pos.get(i)[1], k = 900 / (dx * dx + dy * dy + 0.01);
        f.get(i)[0] -= dx * k; f.get(i)[1] -= dy * k; f.get(j)[0] += dx * k; f.get(j)[1] += dy * k;
      }
    });
    for (const [a, b] of edges) {
      const dx = pos.get(b)[0] - pos.get(a)[0], dy = pos.get(b)[1] - pos.get(a)[1], d = Math.hypot(dx, dy) + 1e-9, k = (d - 46) * 0.08 / d;
      f.get(a)[0] += dx * k; f.get(a)[1] += dy * k; f.get(b)[0] -= dx * k; f.get(b)[1] -= dy * k;
    }
    for (const i of linked) {
      const p = pos.get(i), v = vel.get(i), fi = f.get(i);
      fi[0] -= p[0] * 0.03; fi[1] -= p[1] * 0.05;
      v[0] = (v[0] + fi[0] * alpha) * 0.6; v[1] = (v[1] + fi[1] * alpha) * 0.6;
      p[0] += v[0]; p[1] += v[1];
    }
    alpha *= 0.99;
  }
  const xs = linked.map((i) => pos.get(i)[0]), ys = linked.map((i) => pos.get(i)[1]);
  const minX = Math.min(...xs), minY = Math.min(...ys);
  const sc = Math.min((W - 80) / (Math.max(...xs) - minX), (H - 60) / (Math.max(...ys) - minY));
  const px = (i) => 40 + (pos.get(i)[0] - minX) * sc, py = (i) => 30 + (pos.get(i)[1] - minY) * sc;
  const out = [svgOpen(W, H)];
  for (const [a, b] of edges)
    out.push(`<line x1="${fmt(px(a))}" y1="${fmt(py(a))}" x2="${fmt(px(b))}" y2="${fmt(py(b))}" stroke="#9aa5b1" stroke-opacity="0.6" stroke-width="1"/>`);
  for (const i of linked)
    out.push(`<circle cx="${fmt(px(i))}" cy="${fmt(py(i))}" r="${fmt(3 + 1.6 * Math.sqrt(degree.get(i)))}" fill="${COLOUR[groupOf(names[i])]}" stroke="white" stroke-width="1.5"/>`);
  for (const i of linked) if (degree.get(i) >= 5) out.push(label(names[i], px(i) + 8, py(i) - 6, 11, INK));
  out.push("</svg>");
  return {svg: out.join("\n"), nodes: linked.length, links: edges.length};
}

// ---------------------------------------------------------------- pages

export const STYLE = "body{margin:16px;font-size:14px;line-height:20px;color:#22303c;background:white}" +
  "h1{margin:0;font-size:24px;line-height:32px;color:#184078}" +
  "h2{margin:0;padding-top:18px;font-size:18px;line-height:26px;color:#184078}" +
  "p{margin:0;padding-top:6px}svg{display:block}" +
  ".note{color:#5b6876;font-size:13px}.figure{padding-top:8px}";

export function page(title, body) {
  return `<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>${title}</title>` +
    `<style>${STYLE}</style></head><body><main>\n` +
    `<p><a href="showcase.html">Showcase</a> · <a href="index.html">Demo index</a></p>\n` +
    `<h1>${title}</h1>\n${body}\n</main></body></html>\n`;
}

export function dataviz(files) {
  const bars = barChart(files), force = forceChart(files);
  const body = `<p>Five chart layouts in the manner of D3, made with no library. A Node program
(<code>tools/showcase-pages.mjs</code>, plain ECMAScript) computes each layout and writes plain SVG; the Lean engine
draws it. Every label is SVG <code>text</code>, which Lean shapes and draws with the held font
(<a href="https://github.com/danbri/factoidal/issues/1270">issue 1270</a>).</p>
<p class="note">The page does not use script. The desktop window refuses a page with a script,
and the script binding has no timers, so the charts can not animate yet; see
<a href="showcase-dataviz-script.html">the scripted version</a> and
<a href="https://github.com/danbri/factoidal/issues/1271">issue 1271</a>.</p>
<h2>Bar chart: lines of Lean in this browser, by part</h2>
<p class="note">${bars.count} Lean files in labs/demos/foafnaut, ${thousands(bars.total)} lines in all.</p>
<div class="figure">${bars.svg}</div>
<h2>Line chart: hours of daylight through the year</h2>
<p class="note">From the solar declination, no refraction. The shaded area is London.</p>
<div class="figure">${lineChart()}</div>
<h2>Tidy tree: the parts of the engine</h2>
<p class="note">Leaves at equal spacing, each parent over the mean of its children, links as cubic Bézier curves.</p>
<div class="figure">${treeChart()}</div>
<h2>Circle packing: each Lean file, sized by its lines</h2>
<p class="note">Circle area is proportional to the line count. Files are packed in their group, and the groups are packed together.</p>
<div class="figure">${packChart(files)}</div>
<h2>Force-directed graph: which Lean file imports which</h2>
<p class="note">The largest connected part: ${force.nodes} files, ${force.links} import links. 400 steps of a spring-electric simulation with cooling; files with five or more links are named.</p>
<div class="figure">${force.svg}</div>`;
  return page("Data visualisation", body);
}

export function lettering() {
  // 1. A badge: text round a circle, outside and inside, as textPath on two arcs.
  const cx = 190, cy = 190, R = 150;
  const badge = [svgOpen(380, 380), "<defs>",
    `<path id="badge-top" d="M${cx - R} ${cy} A${R} ${R} 0 0 1 ${cx + R} ${cy}"/>`,
    `<path id="badge-bottom" d="M${cx - R + 28} ${cy} A${R - 28} ${R - 28} 0 0 0 ${cx + R - 28} ${cy}"/>`, "</defs>",
    `<circle cx="${cx}" cy="${cy}" r="${R + 22}" fill="#184078"/>`,
    `<circle cx="${cx}" cy="${cy}" r="${R - 50}" fill="#f7f3e8"/>`,
    `<circle cx="${cx}" cy="${cy}" r="${R + 14}" fill="none" stroke="#f0c75e" stroke-width="2"/>`,
    `<circle cx="${cx}" cy="${cy}" r="${R - 42}" fill="none" stroke="#f0c75e" stroke-width="2"/>`,
    onPath("FOAFNAUT · A BROWSER IN LEAN", "badge-top", 26, "#f7f3e8", 1.5),
    onPath("HTML · CSS · SVG · WEBGPU", "badge-bottom", 17, "#f0c75e", 2),
    label("2525", cx, cy + 22, 64, "#184078", "middle"), "</svg>"];
  // 2. A wave.
  const wave = sampledPath((t) => [20 + 700 * t, 110 + 55 * Math.sin(t * 2 * Math.PI * 1.5)]);
  const waveSvg = [svgOpen(740, 220),
    `<path id="wave" d="${wave}" fill="none" stroke="#c9d6e8" stroke-width="22" stroke-linecap="round"/>`,
    `<path d="${wave}" fill="none" stroke="#3b6fb6" stroke-width="1" stroke-dasharray="4 4"/>`,
    onPath("Each glyph sits on the curve and turns with its tangent, as SVG textPath places it.", "wave", 17), "</svg>"];
  // 3. A spiral.
  const spiral = sampledPath((t) => {
    const r = 16 + 150 * (1 - t), a = 6 * Math.PI * t - Math.PI / 2;
    return [190 + r * Math.cos(a), 190 + r * Math.sin(a)];
  }, 2000);
  const words = "The Resource Description Framework is a framework for representing information in the Web. " +
    "An RDF graph is a set of RDF triples. An RDF triple has a subject, a predicate and an object. " +
    "The set of nodes of an RDF graph is the set of subjects and objects of the triples in the graph.";
  const spiralSvg = [svgOpen(380, 380), `<path id="spiral" d="${spiral}" fill="none" stroke="#efe3cc" stroke-width="1"/>`,
    onPath(words, "spiral", 13, "#8a3b2b"), "</svg>"];
  // 4. A sunburst of rotated words. On the left half the words turn half round and end
  // at the inner radius (text-anchor end), so they stay upright.
  const rays = ["subject", "predicate", "object", "graph", "triple", "literal", "IRI", "blank node", "dataset", "datatype", "language", "quad"];
  const burst = [svgOpen(380, 380), '<circle cx="190" cy="190" r="34" fill="#e07b39"/>'];
  rays.forEach((w, i) => {
    const a = i * 360 / rays.length, rad = a * Math.PI / 180, u = [Math.cos(rad), Math.sin(rad)], n = [-Math.sin(rad), Math.cos(rad)];
    const r0 = 48, size = 15;
    if (a > 90 && a <= 270)
      burst.push(label(w, 190 + r0 * u[0] - 5 * n[0], 190 + r0 * u[1] - 5 * n[1], size, PALETTE[i % 8], "end", a + 180));
    else burst.push(label(w, 190 + r0 * u[0] + 5 * n[0], 190 + r0 * u[1] + 5 * n[1], size, PALETTE[i % 8], "start", a));
  });
  burst.push("</svg>");
  // 5. Vertical, rotated and scaled lettering.
  const stack = [svgOpen(740, 150)];
  [..."VERTICAL"].forEach((ch, i) => stack.push(label(ch, 30, 22 + i * 16, 16, "#3f9d6b", "middle")));
  stack.push(label("rotated 90°", 70, 20, 16, "#7a5cb8", "start", 90));
  stack.push(label("rotated −90°", 110, 128, 16, "#7a5cb8", "start", -90));
  // One text: each tspan larger than the one before, 14 units after it.
  const sizes = [12, 16, 21, 28, 36, 46];
  stack.push(`<text x="150" y="120">` + sizes.map((s, i) => `<tspan${i ? ' dx="14"' : ""} font-size="${s}" fill="${PALETTE[i % 8]}">Aa</tspan>`).join("") + "</text>");
  stack.push(label("rotated −12°", 540, 80, 22, "#c4455a", "start", -12));
  stack.push("</svg>");
  const body = `<p>Lettering on circles, waves and spirals, and rotated words. Every word is SVG
<code>text</code>, <code>tspan</code> or <code>textPath</code>, written by <code>tools/showcase-pages.mjs</code>;
the Lean engine shapes it with the held font and draws the glyph outlines
(<a href="https://github.com/danbri/factoidal/issues/1270">issue 1270</a>).</p>
<p class="note">On a path, the middle of each glyph's advance sits on the path and the glyph turns
with the tangent there (SVG 1.1 §10.13). The page <a href="showcase-textpath.html">showcase-textpath.html</a>
is written by hand with the same features.</p>
<h2>A badge: text round a circle</h2>
<div class="figure">${badge.join("")}</div>
<h2>A wave</h2>
<div class="figure">${waveSvg.join("")}</div>
<h2>A spiral</h2>
<div class="figure">${spiralSvg.join("")}</div>
<h2>Rotated words</h2>
<div class="figure">${burst.join("")}</div>
<h2>Vertical, rotated and scaled</h2>
<div class="figure">${stack.join("")}</div>`;
  return page("Lettering on curves", body);
}

/** A table drawn in SVG: columns are [heading, width, "left" or "right"]; rows are lists
of cells; spans maps "row,column" to a column count, as colspan would. */
export function svgTable(caption, columns, rows, foot = null, spans = {}) {
  const W = columns.reduce((s, [, w]) => s + w, 0), pad = 10, rowH = 30, headH = 34, capH = 38;
  const H = capH + headH + rowH * (rows.length + (foot ? 1 : 0)) + 2;
  const out = [`<svg width="${W + 2}" height="${H}" viewBox="-1 0 ${W + 2} ${H}" font-family="${FONT}">`,
    `<rect x="0" y="0" width="${W}" height="${capH}" rx="6" fill="#184078"/>`,
    `<rect x="0" y="${capH - 8}" width="${W}" height="8" fill="#184078"/>`,
    label(caption, pad + 2, 25, 15, "white"),
    `<rect x="0" y="${capH}" width="${W}" height="${headH}" fill="#dfe7f1"/>`];
  let x = 0;
  for (const [heading, w, align] of columns) {
    out.push(label(heading, x + (align === "right" ? w - pad : pad), capH + 22, 13, "#184078", align === "right" ? "end" : "start"));
    x += w;
  }
  let y = capH + headH;
  out.push(`<line x1="0" y1="${y}" x2="${W}" y2="${y}" stroke="#184078" stroke-width="2"/>`);
  const body = rows.map((r) => [r, false]).concat(foot ? [[foot, true]] : []);
  body.forEach(([row, isFoot], i) => {
    out.push(`<rect x="0" y="${y}" width="${W}" height="${rowH}" fill="${isFoot ? "#fff4d6" : i % 2 === 0 ? "#f6f8fb" : "white"}"/>`);
    if (isFoot) out.push(`<line x1="0" y1="${y}" x2="${W}" y2="${y}" stroke="#184078" stroke-width="2"/>`);
    let cx = 0, c = 0;
    while (c < columns.length) {
      const span = spans[`${i},${c}`] ?? 1;
      const w = columns.slice(c, c + span).reduce((s, [, cw]) => s + cw, 0), align = columns[c][2], cell = row[c] ?? "";
      if (span > 1) {
        out.push(`<rect x="${cx + 1}" y="${y + 1}" width="${w - 2}" height="${rowH - 2}" fill="#eef3e9"/>`);
        out.push(label(cell, cx + w / 2, y + 20, 13, "#2d6a3e", "middle"));
      } else out.push(label(cell, cx + (align === "right" ? w - pad : pad), y + 20, 13, INK, align === "right" ? "end" : "start"));
      if (c > 0) out.push(`<line x1="${cx}" y1="${y + 6}" x2="${cx}" y2="${y + rowH - 6}" stroke="#d8dee6" stroke-width="1"/>`);
      cx += w; c += span;
    }
    y += rowH;
    out.push(`<line x1="0" y1="${y}" x2="${W}" y2="${y}" stroke="#e3e8ee" stroke-width="1"/>`);
  });
  out.push(`<rect x="0" y="${capH}" width="${W}" height="${H - capH - 2}" fill="none" stroke="#c9d2dc" stroke-width="1"/>`, "</svg>");
  return out.join("");
}

export function tables(files) {
  const counts = Object.fromEntries(GROUPS.map((g) => [g, [0, 0]]));
  for (const [m, text] of Object.entries(files)) { counts[groupOf(m)][0]++; counts[groupOf(m)][1] += lineCount(text); }
  const total = Object.values(counts).reduce((s, [, n]) => s + n, 0);
  const rows = Object.entries(counts).filter(([, [f]]) => f).sort((a, b) => b[1][1] - a[1][1])
    .map(([g, [f, n]]) => [g, String(f), thousands(n), `${(100 * n / total).toFixed(1)}%`]);
  const first = svgTable("Lean files in the foafnaut lab, by part",
    [["Part", 220, "left"], ["Files", 110, "right"], ["Lines", 130, "right"], ["Share", 110, "right"]],
    rows, ["Total", String(Object.keys(files).length), thousands(total), "100.0%"]);
  const second = svgTable("What the engine draws, by layer",
    [["Layer", 110, "left"], ["HTML page, in Lean", 250, "left"], ["SVG document, in Lean", 250, "left"]],
    [["Parse", "HTML5 tokenizer, tree builder", "XML namespace view"],
      ["Style", "CSS cascade, small profile", "attributes and CSS"],
      ["Layout", "block and inline boxes", "paths, strokes, dashes"],
      ["Paint", "one WGSL program from Lean draws every primitive, in tiles", ""]],
    null, {"3,1": 2});
  const body = `<p>The tables of <a href="showcase-tables.html">showcase-tables.html</a>, drawn as SVG:
a caption bar, a header row with a rule, zebra rows, numbers aligned right on their last digit, a cell
that spans two columns, and a totals row. <code>tools/showcase-pages.mjs</code> computes the column
positions; the labels are SVG <code>text</code> with <code>text-anchor</code>.</p>
<p class="note">HTML table layout is in Lean now, with some gaps
(<a href="https://github.com/danbri/factoidal/issues/1272">issue 1272</a>); this page shows the same tables drawn by hand in SVG.</p>
<h2>Numbers aligned right, with a total</h2>
<div class="figure">${first}</div>
<h2>A cell that spans two columns</h2>
<div class="figure">${second}</div>`;
  return page("Tables drawn as SVG", body);
}

// ---------------------------------------------------------------- main: the only file I/O

async function main() {
  const fs = await import("node:fs");
  const path = await import("node:path");
  const {fileURLToPath} = await import("node:url");
  const lab = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
  const files = {};
  for (const name of fs.readdirSync(lab).sort())
    if (name.endsWith(".lean")) files[name.slice(0, -5)] = fs.readFileSync(path.join(lab, name), "utf8");
  for (const [name, text] of [["showcase-dataviz.html", dataviz(files)], ["showcase-lettering.html", lettering()],
    ["showcase-tables-svg.html", tables(files)]]) {
    fs.writeFileSync(path.join(lab, "pages", name), text);
    console.log(`wrote ${name}: ${thousands(text.length)} bytes`);
  }
}

const entry = typeof process !== "undefined" && process.argv?.[1];
if (entry && import.meta.url === (await import("node:url")).pathToFileURL(entry).href) await main();
