#!/usr/bin/env python3
"""Write article.html: an original encyclopedia-style page (our own text, no copied content)
with the shapes of a long reference article: a header bar, a contents box, an infobox table,
24 sections of prose with links and citations, data tables, small inline SVG figures and a
reference list. Used as the text-heavy page of gpu_kernel_diff.ts and the frame timings of
core issue 398. Deterministic: the same file every run.

  python3 make_article.py > article.html
"""
import random

R = random.Random(398)
WORDS = ("lamp keeper harbour beacon tower lens light signal coast rock tide shipping chart survey "
         "granite iron brass clockwork weight rotation flash period range nautical mile channel pier "
         "breakwater storm fog horn station keeper's cottage oil paraffin acetylene electric automatic "
         "lantern gallery stair course mortar foundation reef sandbank estuary pilot vessel mariner "
         "record register inspection board commission decade century restoration museum trust "
         "visitors footpath headland cliff gull").split()
TOPICS = ["Early beacons", "The first stone tower", "Lens and lantern", "Keepers and their families",
          "Signals in fog", "The storm of the long winter", "Rebuilding the breakwater", "Paraffin to acetylene",
          "Clockwork and rotation", "Charts and surveys", "Electric light", "Automation",
          "The keeper's cottage", "Shipping lanes", "Wrecks on the outer reef", "Pilots of the estuary",
          "Inspection records", "Restoration", "The museum", "Wildlife of the headland",
          "Footpaths and visitors", "In local stories", "Comparisons with other towers", "Present day"]

def sentence():
    n = R.randint(9, 22)
    ws = [R.choice(WORDS) for _ in range(n)]
    for i in range(len(ws)):
        if R.random() < 0.06:
            ws[i] = f'<a href="#s{R.randint(1, len(TOPICS))}">{ws[i]}</a>'
    s = " ".join(ws)
    s = s[0].upper() + s[1:]
    if R.random() < 0.25:
        s += f'<sup class="ref"><a href="#ref{R.randint(1, 40)}">[{R.randint(1, 40)}]</a></sup>'
    return s + "."

def para():
    return "<p>" + " ".join(sentence() for _ in range(R.randint(4, 8))) + "</p>"

def figure(i):
    bars = "".join(f'<rect x="{10 + 18 * j}" y="{110 - h}" width="14" height="{h}" fill="#{R.randint(0x305080, 0x6090c0):06x}"/>'
                   for j, h in enumerate(R.randint(10, 100) for _ in range(10)))
    return (f'<figure class="thumb"><svg width="200" height="120" viewBox="0 0 200 120" role="img" aria-label="Figure {i}">'
            f'<rect width="200" height="120" fill="#f4f6f8"/>{bars}<path d="M10 112 H190" stroke="#333"/>'
            f'<circle cx="170" cy="25" r="12" fill="#f2c94c" stroke="#a07c10"/></svg>'
            f'<figcaption>Figure {i}. Light periods recorded by decade (invented data).</figcaption></figure>')

def table(i):
    rows = "".join(f"<tr><td>{1850 + 10 * j}</td><td>{R.randint(3, 30)} s</td><td>{R.randint(8, 24)} nmi</td><td>{R.choice(['oil', 'paraffin', 'acetylene', 'electric'])}</td></tr>"
                   for j in range(8))
    return (f'<table class="data"><caption>Table {i}. Characteristics by decade</caption>'
            f"<tr><th>Year</th><th>Period</th><th>Range</th><th>Source</th></tr>{rows}</table>")

out = ['<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Harbour lights of the Imaginary Coast</title>',
       "<style>body{font-family:'Noto Sans',sans-serif;margin:0;color:#202122;background:#fff}"
       "header{background:#eaecf0;padding:8px 16px;border-bottom:1px solid #a2a9b1}main{max-width:960px;margin:0 auto;padding:0 16px}"
       "h1{font-weight:normal;border-bottom:1px solid #a2a9b1}h2{font-weight:normal;border-bottom:1px solid #c8ccd1;margin-top:1.4em}"
       ".infobox{float:right;width:280px;margin:0 0 12px 16px;border:1px solid #a2a9b1;background:#f8f9fa;font-size:88%;border-collapse:collapse}"
       ".infobox th,.infobox td{padding:3px 6px;text-align:left;vertical-align:top}.toc{display:inline-block;border:1px solid #a2a9b1;background:#f8f9fa;padding:6px 14px}"
       ".thumb{float:right;clear:right;margin:4px 0 8px 14px;border:1px solid #c8ccd1;padding:3px;background:#f8f9fa;font-size:85%;width:206px}"
       "table.data{border-collapse:collapse;margin:8px 0}table.data td,table.data th{border:1px solid #a2a9b1;padding:2px 8px}"
       "sup.ref{font-size:75%}a{color:#3366cc;text-decoration:none}.refs{font-size:90%;columns:2}</style></head><body>",
       '<header><b>Imaginary Encyclopedia</b> · <a href="#">Main page</a> · <a href="#">Random article</a></header><main>',
       "<h1>Harbour lights of the Imaginary Coast</h1>",
       '<table class="infobox"><tr><th colspan="2" style="text-align:center;font-size:110%">Harbour lights</th></tr>']
for k, v in [("Location", "Imaginary Coast"), ("Built", "1838"), ("Height", "31 m"), ("Focal height", "44 m"),
             ("Lens", "First order"), ("Range", "22 nmi"), ("Characteristic", "Fl W 10s"), ("Automated", "1979"),
             ("Managed by", "Coast Lights Trust")]:
    out.append(f"<tr><th>{k}</th><td>{v}</td></tr>")
out.append("</table>")
out.append(para())
out.append(para())
out.append('<div class="toc"><b>Contents</b><ol>' + "".join(f'<li><a href="#s{i + 1}">{t}</a></li>' for i, t in enumerate(TOPICS)) + "</ol></div>")
for i, t in enumerate(TOPICS):
    out.append(f'<h2 id="s{i + 1}">{t}</h2>')
    if i % 3 == 0:
        out.append(figure(i // 3 + 1))
    for _ in range(R.randint(2, 4)):
        out.append(para())
    if i % 5 == 2:
        out.append(table(i // 5 + 1))
    if i % 4 == 1:
        out.append("<ul>" + "".join(f"<li>{sentence()}</li>" for _ in range(5)) + "</ul>")
out.append('<h2 id="refs">References</h2><ol class="refs">')
for i in range(1, 41):
    out.append(f'<li id="ref{i}">Register of coast lights, volume {R.randint(1, 12)}, page {R.randint(1, 400)} (invented).</li>')
out.append("</ol></main></body></html>")
print("\n".join(out))
