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


def index():
    links = '\n'.join(f'<p><a href="{p["page"]}">{html.escape(p["title"])}</a></p>' for p in manifest['pages'] if p['page'] != 'index.html')
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>Demo pages</title>'
            f'<style>{STYLE}</style></head><body><main>\n<h1>foafnaut2525 demo pages</h1>\n'
            f'<p>Every page here is rendered by the Lean engine with WebGPU.</p>\n{links}\n</main></body></html>\n')


pages = {}
for page in manifest['pages']:
    source = page.get('source')
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
