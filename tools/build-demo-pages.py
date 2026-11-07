#!/usr/bin/env python3
"""Build the foafnaut2525 demo pages from their sources.

    tools/build-demo-pages.py          rewrite labs/demos/foafnaut/pages/*.html
    tools/build-demo-pages.py --check  exit 1 if a page differs

Markdown goes through tools/status-to-html.py. An SVG source is embedded in a
small HTML page. manifest.json lists every page, with what the engine must do.
"""
import html, json, os, subprocess, sys, tempfile

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PAGES = os.path.join(ROOT, 'labs/demos/foafnaut/pages')
manifest = json.load(open(os.path.join(PAGES, 'manifest.json'), encoding='utf-8'))
STYLE = ('body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:white}'
         'h1{margin:0;font-size:21px;line-height:28px;color:#184078}p{margin:0;padding-top:6px}svg{display:block}')


def markdown(path):
    with tempfile.TemporaryDirectory() as temp:
        out = os.path.join(temp, 'page.html')
        subprocess.run([sys.executable, os.path.join(ROOT, 'tools/status-to-html.py'), path, out], check=True)
        return open(out, encoding='utf-8').read()


def svg(path, title):
    text = open(path, encoding='utf-8').read()
    if text.startswith('<?xml'):
        text = text[text.index('?>') + 2:].lstrip()
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>{html.escape(title)}</title>'
            f'<style>{STYLE}</style></head><body><main>\n<p><a href="index.html">Demo index</a></p>\n'
            f'<h1>{html.escape(title)}</h1>\n{text}\n</main></body></html>\n')


# The SVG pages that draw well, linked first from the start page (owner, 2026-11-07:
# "please get the cool svg enriched demo pages linked into our start page").
FEATURED = ['showcase-dataviz.html', 'showcase-lettering.html', 'showcase-tables-svg.html',
            'svg-gallery.html', 'solving-showcase.html', 'books-svg.xml']
# Text and layout pages, linked next (owner, 2026-11-07, on the writing systems page).
TEXT = ['showcase-scripts.html', 'showcase-tables.html', 'showcase-emoji.html', 'print-showcase.html']
SVG_TINY_SCORES = 'https://danbri.github.io/factoidal/web/hub/render-scores/#svg-tiny-pixels'


def index():
    # foafnaut:graph is a built-in page: the interactive graph, run by the Lean app.
    titles = {p['page']: p['title'] for p in manifest['pages']}
    missing = [page for page in FEATURED + TEXT if page not in titles]
    if missing:
        raise SystemExit(f'featured pages not in manifest.json: {missing}')
    link = lambda page: f'<p><a href="{page}">{html.escape(titles[page])}</a></p>'
    featured = '\n'.join(link(page) for page in FEATURED)
    text = '\n'.join(link(page) for page in TEXT)
    rest = '\n'.join(link(p['page']) for p in manifest['pages']
                     if p['page'] != 'index.html' and not p.get('showcase') and p['page'] not in FEATURED + TEXT)
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>Demo pages</title>'
            f'<style>{STYLE}h2{{margin:0;padding-top:14px;font-size:17px;line-height:24px;color:#184078}}</style></head><body><main>\n<h1>foafnaut2525 demo pages</h1>\n'
            f'<p>Every page here is rendered by the Lean engine with WebGPU.</p>\n'
            f'<p><a href="foafnaut:graph">Interactive FOAF graph</a></p>\n'
            f'<h2>Drawn with SVG</h2>\n{featured}\n'
            f'<p><a href="{SVG_TINY_SCORES}">SVG Tiny 1.2 test suite results (web)</a></p>\n'
            f'<h2>Text and layout</h2>\n{text}\n'
            f'<h2>More pages</h2>\n{rest}\n</main></body></html>\n')


pages = {}
for page in manifest['pages']:
    source = page.get('source')
    if page['page'].endswith('.xml'):
        continue  # An XML page is its own source; the engine runs its stylesheet.
    if page.get('handwritten') or page.get('generator'):
        continue  # Written by hand, or by its generator (which needs fontTools): not rebuilt here.
    if source is None:
        pages[page['page']] = index()
    else:
        path = os.path.normpath(os.path.join(PAGES, source))
        pages[page['page']] = markdown(path) if source.endswith('.md') else svg(path, page['title'])
stale = 0
for name, text in pages.items():
    target = os.path.join(PAGES, name)
    if '--check' in sys.argv:
        if not os.path.exists(target) or open(target, encoding='utf-8').read() != text:
            print(f'stale: {name}')
            stale += 1
    else:
        open(target, 'w', encoding='utf-8').write(text)
sys.exit(1 if stale else 0)
