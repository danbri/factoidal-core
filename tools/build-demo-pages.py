#!/usr/bin/env python3
"""Build the foafnaut2525 demo pages from their sources.

    tools/build-demo-pages.py          rewrite labs/demos/foafnaut/pages/*.html and feed.xml
    tools/build-demo-pages.py --check  exit 1 if a page differs

Markdown goes through tools/status-to-html.py. An SVG source is embedded in a
small HTML page. manifest.json lists every page, with what the engine must do.
feed.xml is written from the Foafnaut notes of the Hub (see feed() below).
"""
import html, json, os, re, subprocess, sys, tempfile

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PAGES = os.path.join(ROOT, 'labs/demos/foafnaut/pages')
manifest = json.load(open(os.path.join(PAGES, 'manifest.json'), encoding='utf-8'))
# The tab icon of the built-in pages (HTML §4.6.7.8): the FOAF graph of the app icon.
ICON = '<link rel="icon" type="image/svg+xml" href="foafnaut-icon.svg">'
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
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>{html.escape(title)}</title>{ICON}'
            f'<style>{STYLE}</style></head><body><main>\n<p><a href="index.html">Demo index</a></p>\n'
            f'<h1>{html.escape(title)}</h1>\n{text}\n</main></body></html>\n')


# The SVG pages that draw well, linked first from the start page (owner, 2026-11-07:
# "please get the cool svg enriched demo pages linked into our start page").
FEATURED = ['showcase-dataviz.html', 'showcase-lettering.html', 'showcase-tables-svg.html',
            'svg-gallery.html', 'solving-showcase.html', 'books-svg.xml']
# Text and layout pages, linked next (owner, 2026-11-07, on the writing systems page).
TEXT = ['showcase-scripts.html', 'showcase-tables.html', 'showcase-images.html', 'showcase-emoji.html', 'print-showcase.html']
# Pages that combine two or more parts: XSLT, SVG, fonts, tables, print, RDF and SPARQL (owner, 2026-11-08:
# "Think of creative demo pages and exciting combinations of our technologies!").
COMBINATIONS = ['books-xslt4.xml', 'foaf-people.xml', 'sparql-results.xml', 'feed.xml', 'sitemap.xml', 'lab-files.xml',
                'engine-pipeline.xml', 'typography-lab.xml', 'print-poster.html', 'svg-text-labels.html', 'spinal-tap-sparql.html']
# Pages written for features that are still in progress; the manifest says what each one needs.
NEXT = ['timers-and-clicks.html', 'webgpu-triangle.html', 'webgl-triangle.html', 'wasm-mandelbrot.html']
# A scripted page linked beside foafnaut:graph at the top: the same kind of graph, drawn by the page's own JavaScript.
TOP = ['foaf-explorer.html', 'js-status.html']
SVG_TINY_SCORES = 'https://danbri.github.io/factoidal/web/hub/render-scores/#svg-tiny-pixels'


def index():
    # foafnaut:graph is a built-in page: the interactive graph, run by the Lean app.
    titles = {p['page']: p['title'] for p in manifest['pages']}
    missing = [page for page in TOP + FEATURED + TEXT + COMBINATIONS + NEXT if page not in titles]
    if missing:
        raise SystemExit(f'featured pages not in manifest.json: {missing}')
    link = lambda page: f'<p><a href="{page}">{html.escape(titles[page])}</a></p>'
    featured = '\n'.join(link(page) for page in FEATURED)
    text = '\n'.join(link(page) for page in TEXT)
    combinations = '\n'.join(link(page) for page in COMBINATIONS)
    later = '\n'.join(link(page) for page in NEXT)
    rest = '\n'.join(link(p['page']) for p in manifest['pages']
                     if p['page'] != 'index.html' and not p.get('showcase') and p['page'] not in TOP + FEATURED + TEXT + COMBINATIONS + NEXT)
    return (f'<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><title>Demo pages</title>{ICON}'
            f'<style>{STYLE}h2{{margin:0;padding-top:14px;font-size:17px;line-height:24px;color:#184078}}</style></head><body><main>\n<h1>foafnaut2525 demo pages</h1>\n'
            f'<p>Every page here is rendered by the Lean engine with WebGPU.</p>\n'
            f'<p><a href="foafnaut:graph">Interactive FOAF graph</a></p>\n'
            + ''.join(link(page) + '\n' for page in TOP) +
            f'<h2>Drawn with SVG</h2>\n{featured}\n'
            f'<p><a href="{SVG_TINY_SCORES}">SVG Tiny 1.2 test suite results (web)</a></p>\n'
            f'<h2>Text and layout</h2>\n{text}\n'
            f'<h2>Combinations</h2>\n{combinations}\n'
            f'<h2>Needs the next engine</h2>\n{later}\n'
            # foafnaut:wasm is a built-in page: WebAssembly run by WasmVM, Lean's engine, in this engine (issue 1244).
            f'<h2>Engine</h2>\n<p><a href="foafnaut:wasm">WebAssembly, run by Lean (WasmVM)</a></p>\n'
            f'<h2>More pages</h2>\n{rest}\n</main></body></html>\n')


# The Foafnaut notes: one Markdown file a note, the one source of two things. Eleventy makes
# a Hub page of each (docs/web/hub/web-platform/foafnaut/notes/), and feed() makes the Atom
# feed that Foafnaut draws through feed.xsl. A note's front matter is one "key: value" a
# line; every value but the date is JSON (a quoted string, or a list of quoted strings).
NOTES = os.path.join(ROOT, 'docs/web/hub/web-platform/foafnaut/notes/posts')
NOTES_URL = 'https://danbri.github.io/factoidal/web/hub/web-platform/foafnaut/notes/'
FEED_URL = 'https://danbri.github.io/factoidal/web/hub/foafnaut/pages/feed.xml'
COMMIT_URL = 'https://github.com/danbri/factoidal-core/commit/'
# The categories feed.xsl has a colour for.
CATEGORIES = {'Canvas', 'Fonts', 'Hub', 'Layout', 'Print', 'SVG', 'Scripts', 'Tests', 'Wasm', 'Web APIs', 'XSLT'}
REQUIRED = {'title', 'date', 'category', 'commit', 'summary'}


def note(path, titles):
    name = os.path.basename(path)
    slug = name[:-len('.md')]
    bad = lambda why: SystemExit(f'{os.path.relpath(path, ROOT)}: {why}')
    # Eleventy drops a leading date from a file's slug, so a name that starts with one would
    # give the note another address than the feed says.
    if not re.fullmatch(r'[a-z0-9]+(-[a-z0-9]+)*', slug) or re.match(r'\d{4}-\d{2}-\d{2}-', slug):
        raise bad('the file name is lower-case words joined by -, with no leading date')
    text = open(path, encoding='utf-8').read()
    match = re.match(r'---\n(.*?)\n---\n', text, re.S)
    if not match:
        raise bad('no front matter')
    fields = {}
    for line in match.group(1).split('\n'):
        key, sep, value = line.partition(': ')
        if not sep or key in fields or key not in REQUIRED | {'demos'}:
            raise bad(f'front matter line not understood: {line!r}')
        try:
            fields[key] = value.strip() if key == 'date' else json.loads(value)
        except json.JSONDecodeError:
            raise bad(f'{key}: the value is not JSON (quote it)')
    if REQUIRED - fields.keys():
        raise bad(f'missing {sorted(REQUIRED - fields.keys())}')
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z', fields['date']):
        raise bad('date: write it in UTC as 2026-11-09T08:34:22Z')
    if not all(isinstance(fields[k], str) and fields[k].strip() for k in REQUIRED - {'date'}):
        raise bad('title, category, commit and summary are strings')
    if not re.fullmatch(r'[0-9a-f]{7,40}', fields['commit']):
        raise bad('commit: an abbreviated commit name of danbri/factoidal-core')
    if fields['category'] not in CATEGORIES:
        raise bad(f'category: one of {sorted(CATEGORIES)} (feed.xsl colours)')
    demos = fields.get('demos', [])
    for demo in demos if isinstance(demos, list) else [None]:
        # The Hub opens ?page=NAME only for such names (docs/web/hub/foafnaut/browser-worker.mjs).
        if not isinstance(demo, str) or not re.fullmatch(r'[a-z0-9-]+\.(html|xml)', demo) or demo not in titles:
            raise bad(f'demos: a list of pages in manifest.json, not {demo!r}')
    return {**fields, 'slug': slug, 'demos': demos}


def feed():
    titles = {p['page']: p['title'] for p in manifest['pages']}
    notes = sorted((note(os.path.join(NOTES, name), titles) for name in os.listdir(NOTES) if name.endswith('.md')),
                   key=lambda n: (n['date'], n['slug']), reverse=True)
    e = lambda text: text.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;')
    out = ['<?xml version="1.0" encoding="UTF-8"?>',
           '<?xml-stylesheet type="text/xsl" href="feed.xsl"?>',
           '<!-- An Atom 1.0 feed (RFC 4287): the Foafnaut notes of the Hub. tools/build-demo-pages.py writes it from',
           '     docs/web/hub/web-platform/foafnaut/notes/posts/*.md; do not edit it by hand. -->',
           '<feed xmlns="http://www.w3.org/2005/Atom">',
           ' <title>Foafnaut notes</title>',
           ' <subtitle>What changed in the Lean browser engine, one entry for each step</subtitle>',
           f' <id>{FEED_URL}</id>',
           f' <link rel="self" href="{FEED_URL}"/>',
           f' <link rel="alternate" type="text/html" href="{NOTES_URL}"/>',
           f' <updated>{max(n["date"] for n in notes)}</updated>',
           ' <author><name>Foafnaut demo pages</name></author>']
    for n in notes:
        out += [' <entry>',
                f'  <title>{e(n["title"])}</title>',
                f'  <id>{NOTES_URL}{n["slug"]}/</id>',
                f'  <link rel="alternate" type="text/html" href="{NOTES_URL}{n["slug"]}/"/>',
                f'  <link rel="via" href="{COMMIT_URL}{n["commit"]}"/>']
        # A demo's address is relative to this feed: the demo pages sit beside it, in Foafnaut and on the site.
        out += [f'  <link rel="related" href="{demo}" title="{e(titles[demo])}"/>' for demo in n['demos']]
        out += [f'  <updated>{n["date"]}</updated>',
                f'  <category term="{e(n["category"])}"/>',
                f'  <summary>{e(n["summary"])}</summary>',
                ' </entry>']
    return '\n'.join(out + ['</feed>']) + '\n'


pages = {}
for page in manifest['pages']:
    source = page.get('source')
    if page['page'].endswith('.xml'):
        continue  # An XML page is its own source; the engine runs its stylesheet.
    if page.get('handwritten') or page.get('generator'):
        continue  # Written by hand, or by its generator (tools/showcase-pages.mjs): not rebuilt here.
    if source is None:
        pages[page['page']] = index()
    else:
        path = os.path.normpath(os.path.join(PAGES, source))
        pages[page['page']] = markdown(path) if source.endswith('.md') else svg(path, page['title'])
pages['feed.xml'] = feed()
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
