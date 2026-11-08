#!/usr/bin/env python3
"""Write the two generated showcase pages of foafnaut (issue 1268).

    python3 labs/demos/foafnaut/tools/showcase-pages.py

Writes pages/showcase-dataviz.html, showcase-lettering.html and showcase-tables-svg.html. The other
showcase pages are written by hand.

The pages were made before the engine drew SVG <text> (https://github.com/danbri/factoidal/issues/1270),
so every label here is a glyph outline from the bundled Noto Sans Regular, read with
fontTools at generation time and written as an SVG <path>. The layouts (bars, lines,
tidy tree, circle packing, force-directed graph) are computed here, in the manner of
D3, with no library. The data is real where it can be: line counts and the import
graph of the Lean files in this directory, day length from the solar declination.
Requires fontTools (pip install fonttools); it is not needed to view or test the pages.
"""
import math, os, random, re

from fontTools.ttLib import TTFont
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen

LAB = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PAGES = os.path.join(LAB, 'pages')
FONT = TTFont(os.path.join(LAB, '../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf'))
CMAP = FONT.getBestCmap()
GLYPHS = FONT.getGlyphSet()
UPEM = FONT['head'].unitsPerEm
HMTX = FONT['hmtx']

PALETTE = ['#3b6fb6', '#e07b39', '#3f9d6b', '#c4455a', '#7a5cb8', '#8a6d3b', '#cc6aa8', '#6b7480']
INK, MUTED, GRID = '#22303c', '#5b6876', '#d8dee6'


def fmt(v):
    s = f'{v:.2f}'.rstrip('0').rstrip('.')
    return '0' if s in ('-0', '') else s


def advance(ch, size):
    name = CMAP.get(ord(ch), '.notdef')
    return HMTX[name][0] * size / UPEM


def width(text, size):
    return sum(advance(c, size) for c in text)


def glyph_d(ch, matrix):
    """Outline of one character, transformed by matrix (a, b, c, d, e, f) from font units."""
    name = CMAP.get(ord(ch))
    if name is None or ch == ' ':
        return ''
    pen = SVGPathPen(GLYPHS, ntos=fmt)
    GLYPHS[name].draw(TransformPen(pen, matrix))
    return pen.getCommands()


def paths(parts, fill):
    """Glyph outlines as paths. The engine takes at most 128 subpaths in one path."""
    out, current, count = [], [], 0
    for d in parts:
        n = d.count('M')
        if not d:
            continue
        if current and count + n > 120:
            out.append(f'<path fill="{fill}" d="{"".join(current)}"/>')
            current, count = [], 0
        current.append(d)
        count += n
    if current:
        out.append(f'<path fill="{fill}" d="{"".join(current)}"/>')
    return ''.join(out)


def label(text, x, y, size, fill=INK, anchor='start', angle=0.0):
    """A line of text as one path: baseline at (x, y), rotated by angle degrees about (x, y)."""
    w = width(text, size)
    start = {'start': 0, 'middle': -w / 2, 'end': -w}[anchor]
    k = size / UPEM
    ca, sa = math.cos(math.radians(angle)), math.sin(math.radians(angle))
    parts, pen_x = [], start
    for ch in text:
        # Font units (u, v) to page: scale, flip y, move along the baseline, rotate, translate.
        ox, oy = pen_x * ca + x, pen_x * sa + y
        parts.append(glyph_d(ch, (k * ca, k * sa, k * sa, -k * ca, ox, oy)))
        pen_x += advance(ch, size)
    return paths(parts, fill)


def on_curve(text, size, point_at, length, offset=0.0, fill=INK, spacing=0.0):
    """Text along a curve: point_at(s) gives (x, y, angle in radians) at arc length s."""
    k = size / UPEM
    total = width(text, size) + spacing * (len(text) - 1)
    s = offset + (length - total) / 2
    parts = []
    for ch in text:
        a = advance(ch, size)
        mid = s + a / 2
        if 0 <= mid <= length:
            px, py, t = point_at(mid)
            ca, sa = math.cos(t), math.sin(t)
            # The glyph's centre of advance sits on the curve; its baseline follows the tangent.
            ox, oy = px - a / 2 * ca, py - a / 2 * sa
            parts.append(glyph_d(ch, (k * ca, k * sa, k * sa, -k * ca, ox, oy)))
        s += a + spacing
    return paths(parts, fill)


def sampled(fn, n=800):
    """Arc-length parameterisation of a curve fn(t), t in [0, 1]."""
    pts = [fn(i / n) for i in range(n + 1)]
    acc = [0.0]
    for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
        acc.append(acc[-1] + math.hypot(x1 - x0, y1 - y0))

    def at(s):
        lo, hi = 0, n
        while hi - lo > 1:
            m = (lo + hi) // 2
            if acc[m] <= s:
                lo = m
            else:
                hi = m
        x0, y0 = pts[lo]
        x1, y1 = pts[hi]
        f = 0 if acc[hi] == acc[lo] else (s - acc[lo]) / (acc[hi] - acc[lo])
        return x0 + (x1 - x0) * f, y0 + (y1 - y0) * f, math.atan2(y1 - y0, x1 - x0)
    return at, acc[-1], 'M' + ' L'.join(f'{fmt(x)} {fmt(y)}' for x, y in pts[::8] + [pts[-1]])


# ---------------------------------------------------------------- data

def lean_files():
    out = {}
    for name in sorted(os.listdir(LAB)):
        if name.endswith('.lean'):
            text = open(os.path.join(LAB, name), encoding='utf-8').read()
            out[name[:-5]] = text
    return out


def group_of(module):
    for prefix, group in [('SVG', 'SVG'), ('Web', 'HTML and CSS'), ('Font', 'Fonts'), ('Foaf', 'FOAF'),
                          ('Solving', 'Solving'), ('Image', 'Images'), ('Render', 'GPU plan'), ('Scene', 'GPU plan')]:
        if module.startswith(prefix):
            return group
    return 'Other'


GROUPS = ['SVG', 'HTML and CSS', 'Fonts', 'FOAF', 'Solving', 'Images', 'GPU plan', 'Other']
COLOUR = dict(zip(GROUPS, PALETTE))


def day_length(lat, day):
    decl = -23.44 * math.cos(2 * math.pi * (day + 10) / 365)
    x = -math.tan(math.radians(lat)) * math.tan(math.radians(decl))
    return 24.0 if x < -1 else 0.0 if x > 1 else 24 * math.acos(x) / math.pi


# ---------------------------------------------------------------- charts

def bar_chart(files):
    lines = {g: 0 for g in GROUPS}
    for m, text in files.items():
        lines[group_of(m)] += text.count('\n')
    data = sorted(((g, n) for g, n in lines.items() if n), key=lambda p: -p[1])
    W, H, L, B, T = 760, 340, 64, 300, 20
    top = math.ceil(max(n for _, n in data) / 2000) * 2000
    step = (W - L - 16) / len(data)
    out = [f'<svg width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    for v in range(0, top + 1, 2000):
        y = B - (B - T) * v / top
        out.append(f'<line x1="{L}" y1="{fmt(y)}" x2="{W - 8}" y2="{fmt(y)}" stroke="{GRID}" stroke-width="1"/>')
        out.append(label(f'{v:,}', L - 8, y + 4, 11, MUTED, 'end'))
    for i, (g, n) in enumerate(data):
        x = L + i * step + step * 0.15
        h = (B - T) * n / top
        out.append(f'<rect x="{fmt(x)}" y="{fmt(B - h)}" width="{fmt(step * 0.7)}" height="{fmt(h)}" rx="3" fill="{COLOUR[g]}"/>')
        out.append(label(f'{n:,}', x + step * 0.35, B - h - 6, 11, INK, 'middle'))
        out.append(label(g, x + step * 0.35, B + 18, 12, INK, 'middle'))
    out.append(f'<line x1="{L}" y1="{B}" x2="{W - 8}" y2="{B}" stroke="{INK}" stroke-width="1.5"/>')
    out.append('</svg>')
    return '\n'.join(out), sum(n for _, n in data), len(files)


def line_chart():
    W, H, L, B, T, R = 760, 330, 52, 290, 16, 120
    series = [('Equator', 0, PALETTE[2]), ('Lisbon 38.7° N', 38.7, PALETTE[1]),
              ('London 51.5° N', 51.5, PALETTE[0]), ('Tromsø 69.6° N', 69.6, PALETTE[3])]
    sx = lambda d: L + (W - L - R) * d / 364
    sy = lambda h: B - (B - T) * h / 24
    out = [f'<svg width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    for h in range(0, 25, 6):
        out.append(f'<line x1="{L}" y1="{fmt(sy(h))}" x2="{W - R}" y2="{fmt(sy(h))}" stroke="{GRID}" stroke-width="1" stroke-dasharray="3 3"/>')
        out.append(label(f'{h} h', L - 8, sy(h) + 4, 11, MUTED, 'end'))
    months = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec']
    for i, m in enumerate(months):
        d = i * 365 / 12
        out.append(f'<line x1="{fmt(sx(d))}" y1="{B}" x2="{fmt(sx(d))}" y2="{B + 5}" stroke="{INK}" stroke-width="1"/>')
        out.append(label(m, sx(d + 15), B + 20, 11, MUTED, 'middle'))
    # London as an area under its curve, as a D3 area generator would make it.
    london = [(sx(d), sy(day_length(51.5, d))) for d in range(0, 365, 4)] + [(sx(364), sy(day_length(51.5, 364)))]
    area = f'M{fmt(london[0][0])} {B} ' + ' '.join(f'L{fmt(x)} {fmt(y)}' for x, y in london) + f' L{fmt(london[-1][0])} {B} Z'
    out.append(f'<path d="{area}" fill="{PALETTE[0]}" fill-opacity="0.12"/>')
    for name, lat, colour in series:
        pts = [(sx(d), sy(day_length(lat, d))) for d in range(0, 365, 4)] + [(sx(364), sy(day_length(lat, 364)))]
        out.append(f'<path d="M{" L".join(f"{fmt(x)} {fmt(y)}" for x, y in pts)}" fill="none" stroke="{colour}" stroke-width="2.5" stroke-linejoin="round"/>')
        mid = [(sx(d), sy(day_length(lat, d))) for d in (172, 355)]
        for x, y in mid:
            out.append(f'<circle cx="{fmt(x)}" cy="{fmt(y)}" r="3.5" fill="white" stroke="{colour}" stroke-width="2"/>')
        out.append(label(name, W - R + 8, pts[-1][1] + 4 + {0: 0, 38.7: -4, 51.5: 4, 69.6: 0}[lat], 11, colour))
    out.append(f'<line x1="{L}" y1="{B}" x2="{W - R}" y2="{B}" stroke="{INK}" stroke-width="1.5"/>')
    out.append('</svg>')
    return '\n'.join(out)


TREE = ('foafnaut', [
    ('HTML', [('tokenizer', []), ('tree builder', []), ('DOM arena', [])]),
    ('CSS', [('selectors', []), ('cascade', []), ('block layout', []), ('inline layout', [])]),
    ('SVG', [('paths', []), ('strokes', []), ('dashes', []), ('gradients', []), ('clips', [])]),
    ('text', [('sfnt tables', []), ('shaper', []), ('outlines', [])]),
    ('GPU', [('render plan', []), ('WGSL', []), ('tiles', [])]),
])


def tree_chart():
    W, H = 760, 330
    leaves = []

    def walk(node, depth):
        name, kids = node
        rec = {'name': name, 'depth': depth, 'kids': [walk(k, depth + 1) for k in kids]}
        if not kids:
            rec['x'] = len(leaves)
            leaves.append(rec)
        else:
            rec['x'] = sum(k['x'] for k in rec['kids']) / len(rec['kids'])
        return rec
    root = walk(TREE, 0)
    n = len(leaves)
    sx = lambda i: 24 + (W - 48) * i / (n - 1)
    sy = lambda d: 30 + d * 110
    out = [f'<svg width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    links, nodes = [], []

    def draw(rec, colour):
        x, y = sx(rec['x']), sy(rec['depth'])
        for i, k in enumerate(rec['kids']):
            c = PALETTE[i] if rec['depth'] == 0 else colour
            kx, ky = sx(k['x']), sy(k['depth'])
            my = (y + ky) / 2
            links.append(f'<path d="M{fmt(x)} {fmt(y)} C{fmt(x)} {fmt(my)} {fmt(kx)} {fmt(my)} {fmt(kx)} {fmt(ky)}" fill="none" stroke="{c}" stroke-opacity="0.55" stroke-width="1.5"/>')
            draw(k, c)
        r = 7 if rec['depth'] < 2 else 4.5
        nodes.append(f'<circle cx="{fmt(x)}" cy="{fmt(y)}" r="{r}" fill="{colour if rec["kids"] else "white"}" stroke="{colour}" stroke-width="2"/>')
        if rec['depth'] == 2:
            nodes.append(label(rec['name'], x + 3, y + 12, 11, INK, 'start', 55))
        else:
            nodes.append(label(rec['name'], x + 11, y - 9, 13 if rec['depth'] == 0 else 12, INK))
    draw(root, INK)
    out += links + nodes + ['</svg>']
    return '\n'.join(out)


def pack(radii):
    """Front-chain-free greedy circle packing: each circle goes to the free tangent
    position nearest the centre. Deterministic; good enough for a picture."""
    placed = []
    for r in radii:
        if not placed:
            placed.append((0.0, 0.0, r))
            continue
        if len(placed) == 1:
            x0, y0, r0 = placed[0]
            placed.append((x0 + r0 + r, y0, r))
            continue
        best = None
        for i, (xa, ya, ra) in enumerate(placed):
            for (xb, yb, rb) in placed[i + 1:]:
                d = math.hypot(xb - xa, yb - ya)
                p, q = ra + r, rb + r
                if d == 0 or d > p + q or d < abs(p - q):
                    continue
                a = (p * p - q * q + d * d) / (2 * d)
                h = math.sqrt(max(0.0, p * p - a * a))
                mx, my = xa + a * (xb - xa) / d, ya + a * (yb - ya) / d
                for sgn in (1, -1):
                    cx, cy = mx + sgn * h * (yb - ya) / d, my - sgn * h * (xb - xa) / d
                    if all(math.hypot(cx - x, cy - y) >= rr + r - 1e-6 for x, y, rr in placed):
                        dist = math.hypot(cx, cy)
                        if best is None or dist < best[0]:
                            best = (dist, cx, cy)
        placed.append((best[1], best[2], r))
    cx = sum(x for x, _, _ in placed) / len(placed)
    cy = sum(y for _, y, _ in placed) / len(placed)
    placed = [(x - cx, y - cy, r) for x, y, r in placed]
    return placed, max(math.hypot(x, y) + r for x, y, r in placed)


def pack_chart(files):
    W, H = 760, 420
    groups = {}
    for m, text in files.items():
        groups.setdefault(group_of(m), []).append((m, text.count('\n')))
    inner = []
    for g in GROUPS:
        if g not in groups:
            continue
        items = sorted(groups[g], key=lambda p: -p[1])
        circles, R = pack([math.sqrt(n) * 0.9 for _, n in items])
        inner.append((g, items, circles, R + 4))
    outer, big = pack([R for _, _, _, R in inner])
    scale = (H / 2 - 12) / big
    out = [f'<svg width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
           f'<circle cx="{fmt(W / 2 - 120)}" cy="{H / 2}" r="{fmt(big * scale)}" fill="#f3f5f8" stroke="{GRID}"/>']
    ox0 = W / 2 - 120
    legend_y = 40
    for (g, items, circles, R), (gx, gy, _) in zip(inner, outer):
        colour = COLOUR[g]
        cx, cy = ox0 + gx * scale, H / 2 + gy * scale
        out.append(f'<circle cx="{fmt(cx)}" cy="{fmt(cy)}" r="{fmt(R * scale)}" fill="{colour}" fill-opacity="0.10" stroke="{colour}" stroke-opacity="0.5"/>')
        for (m, n), (x, y, r) in zip(items, circles):
            out.append(f'<circle cx="{fmt(cx + x * scale)}" cy="{fmt(cy + y * scale)}" r="{fmt(r * scale)}" fill="{colour}" fill-opacity="0.75"/>')
        out.append(f'<circle cx="{W - 250}" cy="{legend_y - 4}" r="6" fill="{colour}" fill-opacity="0.75"/>')
        out.append(label(f'{g}: {len(items)} files, {sum(n for _, n in items):,} lines', W - 238, legend_y, 12, INK))
        legend_y += 22
    out.append('</svg>')
    return '\n'.join(out)


def force_chart(files):
    W, H = 760, 460
    names = sorted(files)
    index = {m: i for i, m in enumerate(names)}
    edges = set()
    for m, text in files.items():
        for imp in re.findall(r'^import\s+(\S+)', text, re.M):
            if imp in index and imp != m:
                edges.add(tuple(sorted((index[m], index[imp]))))
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    seen, best = set(), []
    for start in sorted(adj):
        if start in seen:
            continue
        comp, todo = [], [start]
        seen.add(start)
        while todo:
            v = todo.pop()
            comp.append(v)
            for w in adj[v]:
                if w not in seen:
                    seen.add(w)
                    todo.append(w)
        if len(comp) > len(best):
            best = comp
    linked = sorted(best)
    edges = {e for e in edges if e[0] in best}
    rng = random.Random(1268)
    pos = {i: [rng.uniform(-1, 1) * 200, rng.uniform(-1, 1) * 150] for i in linked}
    degree = {i: 0 for i in linked}
    for a, b in edges:
        degree[a] += 1
        degree[b] += 1
    # A spring-electric simulation with cooling, in the manner of d3-force: link springs,
    # many-body repulsion, a weak pull to the centre, velocity decay.
    vel = {i: [0.0, 0.0] for i in linked}
    alpha = 1.0
    for _ in range(400):
        f = {i: [0.0, 0.0] for i in linked}
        for ii, i in enumerate(linked):
            for j in linked[ii + 1:]:
                dx, dy = pos[j][0] - pos[i][0], pos[j][1] - pos[i][1]
                d2 = dx * dx + dy * dy + 0.01
                k = 900 / d2
                f[i][0] -= dx * k; f[i][1] -= dy * k
                f[j][0] += dx * k; f[j][1] += dy * k
        for a, b in edges:
            dx, dy = pos[b][0] - pos[a][0], pos[b][1] - pos[a][1]
            d = math.hypot(dx, dy) + 1e-9
            k = (d - 46) * 0.08 / d
            f[a][0] += dx * k; f[a][1] += dy * k
            f[b][0] -= dx * k; f[b][1] -= dy * k
        for i in linked:
            f[i][0] -= pos[i][0] * 0.03
            f[i][1] -= pos[i][1] * 0.05
            vel[i][0] = (vel[i][0] + f[i][0] * alpha) * 0.6
            vel[i][1] = (vel[i][1] + f[i][1] * alpha) * 0.6
            pos[i][0] += vel[i][0]
            pos[i][1] += vel[i][1]
        alpha *= 0.99
    xs = [p[0] for p in pos.values()]
    ys = [p[1] for p in pos.values()]
    sc = min((W - 80) / (max(xs) - min(xs)), (H - 60) / (max(ys) - min(ys)))
    px = lambda i: 40 + (pos[i][0] - min(xs)) * sc
    py = lambda i: 30 + (pos[i][1] - min(ys)) * sc
    out = [f'<svg width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    for a, b in sorted(edges):
        out.append(f'<line x1="{fmt(px(a))}" y1="{fmt(py(a))}" x2="{fmt(px(b))}" y2="{fmt(py(b))}" stroke="#9aa5b1" stroke-opacity="0.6" stroke-width="1"/>')
    for i in linked:
        r = 3 + 1.6 * math.sqrt(degree[i])
        out.append(f'<circle cx="{fmt(px(i))}" cy="{fmt(py(i))}" r="{fmt(r)}" fill="{COLOUR[group_of(names[i])]}" stroke="white" stroke-width="1.5"/>')
    for i in linked:
        if degree[i] >= 5:
            out.append(label(names[i], px(i) + 8, py(i) - 6, 11, INK))
    out.append('</svg>')
    return '\n'.join(out), len(linked), len(edges)


# ---------------------------------------------------------------- pages

STYLE = ('body{margin:16px;font-size:14px;line-height:20px;color:#22303c;background:white}'
         'h1{margin:0;font-size:24px;line-height:32px;color:#184078}'
         'h2{margin:0;padding-top:18px;font-size:18px;line-height:26px;color:#184078}'
         'p{margin:0;padding-top:6px}svg{display:block}'
         '.note{color:#5b6876;font-size:13px}.figure{padding-top:8px}')


def page(title, body):
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>{title}</title>'
            f'<style>{STYLE}</style></head><body><main>\n'
            f'<p><a href="showcase.html">Showcase</a> · <a href="index.html">Demo index</a></p>\n'
            f'<h1>{title}</h1>\n{body}\n</main></body></html>\n')


def dataviz():
    files = lean_files()
    bars, total, count = bar_chart(files)
    force, nodes, links = force_chart(files)
    body = f'''<p>Five chart layouts in the manner of D3, made with no library. A Python program
(<code>tools/showcase-pages.py</code>) computes each layout and writes plain SVG; the Lean engine
draws it. The labels are glyph outlines from Noto Sans, made before the engine drew SVG text
(<a href="https://github.com/danbri/factoidal/issues/1270">issue 1270</a>).</p>
<p class="note">The page does not use script. The desktop window refuses a page with a script,
and the script binding has no timers, so the charts can not animate yet; see
<a href="showcase-dataviz-script.html">the scripted version</a> and
<a href="https://github.com/danbri/factoidal/issues/1271">issue 1271</a>.</p>
<h2>Bar chart: lines of Lean in this browser, by part</h2>
<p class="note">{count} Lean files in labs/demos/foafnaut, {total:,} lines in all.</p>
<div class="figure">{bars}</div>
<h2>Line chart: hours of daylight through the year</h2>
<p class="note">From the solar declination, no refraction. The shaded area is London.</p>
<div class="figure">{line_chart()}</div>
<h2>Tidy tree: the parts of the engine</h2>
<p class="note">Leaves at equal spacing, each parent over the mean of its children, links as cubic Bézier curves.</p>
<div class="figure">{tree_chart()}</div>
<h2>Circle packing: each Lean file, sized by its lines</h2>
<p class="note">Circle area is proportional to the line count. Files are packed in their group, and the groups are packed together.</p>
<div class="figure">{pack_chart(files)}</div>
<h2>Force-directed graph: which Lean file imports which</h2>
<p class="note">The largest connected part: {nodes} files, {links} import links. 400 steps of a spring-electric simulation with cooling; files with five or more links are named.</p>
<div class="figure">{force}</div>'''
    return page('Data visualisation', body)


def lettering():
    # 1. A badge: text around a circle, outside and inside.
    cx, cy, R = 190, 190, 150
    ring = lambda r, start, sweep: (lambda t: (cx + r * math.cos(start + sweep * t), cy + r * math.sin(start + sweep * t)))
    at_top, len_top, _ = sampled(ring(R, math.pi, math.pi))
    at_bottom, len_bottom, _ = sampled(ring(R - 28, math.pi, -math.pi))
    badge = [f'<svg width="380" height="380" viewBox="0 0 380 380">',
             f'<circle cx="{cx}" cy="{cy}" r="{R + 22}" fill="#184078"/>',
             f'<circle cx="{cx}" cy="{cy}" r="{R - 50}" fill="#f7f3e8"/>',
             f'<circle cx="{cx}" cy="{cy}" r="{R + 14}" fill="none" stroke="#f0c75e" stroke-width="2"/>',
             f'<circle cx="{cx}" cy="{cy}" r="{R - 42}" fill="none" stroke="#f0c75e" stroke-width="2"/>',
             on_curve('FOAFNAUT · A BROWSER IN LEAN', 26, at_top, len_top, fill='#f7f3e8', spacing=1.5),
             on_curve('HTML · CSS · SVG · WEBGPU', 17, at_bottom, len_bottom, fill='#f0c75e', spacing=2),
             label('2525', cx, cy + 22, 64, '#184078', 'middle'),
             '</svg>']
    # 2. A wave.
    wave = lambda t: (20 + 700 * t, 110 + 55 * math.sin(t * 2 * math.pi * 1.5))
    at_w, len_w, d_w = sampled(wave)
    wave_svg = ['<svg width="740" height="220" viewBox="0 0 740 220">',
                f'<path d="{d_w}" fill="none" stroke="#c9d6e8" stroke-width="22" stroke-linecap="round"/>',
                f'<path d="{d_w}" fill="none" stroke="#3b6fb6" stroke-width="1" stroke-dasharray="4 4"/>',
                on_curve('Each glyph sits on the curve and turns with its tangent, as SVG textPath would place it.', 17, at_w, len_w, offset=0, fill='#22303c'),
                '</svg>']
    # 3. A spiral.
    spiral = lambda t: (190 + (16 + 150 * (1 - t)) * math.cos(6 * math.pi * t - math.pi / 2),
                        190 + (16 + 150 * (1 - t)) * math.sin(6 * math.pi * t - math.pi / 2))
    at_s, len_s, d_s = sampled(spiral, 2000)
    words = ('The Resource Description Framework is a framework for representing information in the Web. '
             'An RDF graph is a set of RDF triples. An RDF triple has a subject, a predicate and an object. '
             'The set of nodes of an RDF graph is the set of subjects and objects of the triples in the graph. ')
    spiral_svg = ['<svg width="380" height="380" viewBox="0 0 380 380">',
                  f'<path d="{d_s}" fill="none" stroke="#efe3cc" stroke-width="1"/>',
                  on_curve(words, 13, at_s, len_s, fill='#8a3b2b'), '</svg>']
    # 4. A sunburst of rotated words.
    burst = ['<svg width="380" height="380" viewBox="0 0 380 380">',
             '<circle cx="190" cy="190" r="34" fill="#e07b39"/>']
    rays = ['subject', 'predicate', 'object', 'graph', 'triple', 'literal', 'IRI', 'blank node',
            'dataset', 'datatype', 'language', 'quad']
    for i, w in enumerate(rays):
        a = i * 360 / len(rays)
        u = (math.cos(math.radians(a)), math.sin(math.radians(a)))
        n = (math.cos(math.radians(a + 90)), math.sin(math.radians(a + 90)))
        r0, size = 48, 15
        if 90 < a <= 270:
            # Keep the words upright: turn them half round and write from the outer end inwards.
            r1 = r0 + width(w, size)
            burst.append(label(w, 190 + r1 * u[0] - 5 * n[0], 190 + r1 * u[1] - 5 * n[1], size, PALETTE[i % 8], 'start', a + 180))
        else:
            burst.append(label(w, 190 + r0 * u[0] + 5 * n[0], 190 + r0 * u[1] + 5 * n[1], size, PALETTE[i % 8], 'start', a))
    burst.append('</svg>')
    # 5. Vertical and stepped lettering.
    stack = ['<svg width="740" height="150" viewBox="0 0 740 150">']
    for i, ch in enumerate('VERTICAL'):
        stack.append(label(ch, 30, 22 + i * 16, 16, '#3f9d6b', 'middle'))
    stack.append(label('rotated 90°', 70, 20, 16, '#7a5cb8', 'start', 90))
    stack.append(label('rotated −90°', 110, 128, 16, '#7a5cb8', 'start', -90))
    x = 150
    for i, size in enumerate([12, 16, 21, 28, 36, 46]):
        stack.append(label('Aa', x, 120, size, PALETTE[i % 8]))
        x += width('Aa', size) + 14
    stack.append(label('rotated −12°', 540, 80, 22, '#c4455a', 'start', -12))
    stack.append('</svg>')
    body = f'''<p>Lettering on circles, waves and spirals, and rotated words. Each letter is a
glyph outline from Noto Sans, placed and turned by <code>tools/showcase-pages.py</code> and drawn
by the Lean SVG path renderer.</p>
<p class="note">This page was the workaround before the engine drew SVG <code>text</code> and
<code>textPath</code> (<a href="https://github.com/danbri/factoidal/issues/1270">issue 1270</a>). The page
<a href="showcase-textpath.html">showcase-textpath.html</a> has the same lettering as real SVG text, for comparison.</p>
<h2>A badge: text around a circle</h2>
<div class="figure">{"".join(badge)}</div>
<h2>A wave</h2>
<div class="figure">{"".join(wave_svg)}</div>
<h2>A spiral</h2>
<div class="figure">{"".join(spiral_svg)}</div>
<h2>Rotated words</h2>
<div class="figure">{"".join(burst)}</div>
<h2>Vertical, rotated and scaled</h2>
<div class="figure">{"".join(stack)}</div>'''
    return page('Lettering on curves', body)


def svg_table(caption, columns, rows, foot=None, spans=()):
    """A table drawn in SVG: columns are (heading, width, 'left' or 'right'); rows are lists of
    cells. spans maps (row, column) to a column count, as colspan would."""
    W = sum(w for _, w, _ in columns)
    pad, row_h, head_h, cap_h = 10, 30, 34, 38
    H = cap_h + head_h + row_h * (len(rows) + (1 if foot else 0)) + 2
    out = [f'<svg width="{W + 2}" height="{H}" viewBox="-1 0 {W + 2} {H}">',
           f'<rect x="0" y="0" width="{W}" height="{cap_h}" rx="6" fill="#184078"/>',
           f'<rect x="0" y="{cap_h - 8}" width="{W}" height="8" fill="#184078"/>',
           label(caption, pad + 2, 25, 15, 'white'),
           f'<rect x="0" y="{cap_h}" width="{W}" height="{head_h}" fill="#dfe7f1"/>']
    x = 0
    for heading, w, align in columns:
        tx = x + (w - pad if align == 'right' else pad)
        out.append(label(heading, tx, cap_h + 22, 13, '#184078', 'end' if align == 'right' else 'start'))
        x += w
    y = cap_h + head_h
    out.append(f'<line x1="0" y1="{y}" x2="{W}" y2="{y}" stroke="#184078" stroke-width="2"/>')
    body = [(r, False) for r in rows] + ([(foot, True)] if foot else [])
    for i, (row, is_foot) in enumerate(body):
        fill = '#fff4d6' if is_foot else ('#f6f8fb' if i % 2 == 0 else 'white')
        out.append(f'<rect x="0" y="{y}" width="{W}" height="{row_h}" fill="{fill}"/>')
        if is_foot:
            out.append(f'<line x1="0" y1="{y}" x2="{W}" y2="{y}" stroke="#184078" stroke-width="2"/>')
        x, c = 0, 0
        while c < len(columns):
            span = dict(spans).get((i, c), 1)
            w = sum(cw for _, cw, _ in columns[c:c + span])
            align = columns[c][2]
            cell = row[c] if c < len(row) else ''
            if span > 1:
                out.append(f'<rect x="{x + 1}" y="{y + 1}" width="{w - 2}" height="{row_h - 2}" fill="#eef3e9"/>')
                out.append(label(cell, x + w / 2, y + 20, 13, '#2d6a3e', 'middle'))
            else:
                tx = x + (w - pad if align == 'right' else pad)
                out.append(label(cell, tx, y + 20, 13, INK, 'end' if align == 'right' else 'start'))
            if c > 0:
                out.append(f'<line x1="{x}" y1="{y + 6}" x2="{x}" y2="{y + row_h - 6}" stroke="#d8dee6" stroke-width="1"/>')
            x += w
            c += span
        y += row_h
        out.append(f'<line x1="0" y1="{y}" x2="{W}" y2="{y}" stroke="#e3e8ee" stroke-width="1"/>')
    out.append(f'<rect x="0" y="{cap_h}" width="{W}" height="{H - cap_h - 2}" fill="none" stroke="#c9d2dc" stroke-width="1"/>')
    out.append('</svg>')
    return ''.join(out)


def tables():
    files = lean_files()
    counts = {g: [0, 0] for g in GROUPS}
    for m, text in files.items():
        counts[group_of(m)][0] += 1
        counts[group_of(m)][1] += text.count('\n')
    total = sum(n for _, n in counts.values())
    rows = [[g, str(f), f'{n:,}', f'{100 * n / total:.1f}%'] for g, (f, n) in sorted(counts.items(), key=lambda p: -p[1][1]) if f]
    first = svg_table('Lean files in the foafnaut lab, by part',
                      [('Part', 220, 'left'), ('Files', 110, 'right'), ('Lines', 130, 'right'), ('Share', 110, 'right')],
                      rows, ['Total', str(len(files)), f'{total:,}', '100.0%'])
    second = svg_table('What the engine draws, by layer',
                       [('Layer', 110, 'left'), ('HTML page, in Lean', 250, 'left'), ('SVG document, in Lean', 250, 'left')],
                       [['Parse', 'HTML5 tokenizer, tree builder', 'XML namespace view'],
                        ['Style', 'CSS cascade, small profile', 'attributes and CSS'],
                        ['Layout', 'block and inline boxes', 'paths, strokes, dashes'],
                        ['Paint', 'one WGSL program from Lean draws every primitive, in tiles', '']],
                       spans=[((3, 1), 2)])
    body = f'''<p>The tables of <a href="showcase-tables.html">showcase-tables.html</a>, drawn as SVG:
a caption bar, a header row with a rule, zebra rows, numbers aligned right on their last digit, a cell
that spans two columns, and a totals row. <code>tools/showcase-pages.py</code> computes the column
positions; the labels are glyph outlines from Noto Sans.</p>
<p class="note">This is the workaround. HTML table layout is not implemented
(<a href="https://github.com/danbri/factoidal/issues/1272">issue 1272</a>). The labels were made
before the engine drew SVG text (<a href="https://github.com/danbri/factoidal/issues/1270">issue 1270</a>).</p>
<h2>Numbers aligned right, with a total</h2>
<div class="figure">{first}</div>
<h2>A cell that spans two columns</h2>
<div class="figure">{second}</div>'''
    return page('Tables drawn as SVG', body)


for name, text in [('showcase-dataviz.html', dataviz()), ('showcase-lettering.html', lettering()),
                   ('showcase-tables-svg.html', tables())]:
    open(os.path.join(PAGES, name), 'w', encoding='utf-8').write(text)
    print(f'wrote {name}: {len(text):,} bytes')
