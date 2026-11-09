#!/usr/bin/env python3
"""The Spinal Tap SPARQL page's snapshot: Wikidata results captured from QLever.

    spinal-tap-snapshot.py --capture   run the page's queries on QLever, write the snapshot
                                       (third_party/data/wikidata-spinal-tap/snapshot.json),
                                       then inline it into the page
    spinal-tap-snapshot.py             inline the stored snapshot into the page (no network)
    spinal-tap-snapshot.py --check     exit 1 if the page's queries or inlined results differ
                                       from the stored snapshot (no network)

The queries live in the page (labs/demos/foafnaut/pages/spinal-tap-sparql.html), in
<script type="application/sparql-query" id="q-NAME"> blocks. The page runs them itself when the
browser has fetch; otherwise it shows the results inlined between the snapshot markers, one
<script type="application/json" id="s-NAME"> block per query (SPARQL 1.1 Query Results JSON),
so a browser parses only the result set it shows. Wikidata is CC0 1.0.
"""
import datetime, html, json, os, re, sys, urllib.parse, urllib.request

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../..'))
PAGE = os.path.join(ROOT, 'labs/demos/foafnaut/pages/spinal-tap-sparql.html')
DATA = os.path.join(ROOT, 'third_party/data/wikidata-spinal-tap/snapshot.json')
ENDPOINT = 'https://qlever.dev/api/wikidata'
BEGIN, END = '<!-- snapshot:begin -->', '<!-- snapshot:end -->'
QUERY = re.compile(r'<script type="application/sparql-query" id="q-([a-z]+)"[^>]*>\n(.*?)</script>', re.S)


def page_queries(page):
    return {name: text.strip() for name, text in QUERY.findall(page)}


def compact(value):
    # JSON for inside a <script> element: no "</" can close it. A space after each comma and
    # colon keeps every unbroken run short: the engine's first compile of a page costs the
    # square of the longest runs in its script text (logged 2026-11-09, being looked at).
    return json.dumps(value, ensure_ascii=False, separators=(', ', ': ')).replace('</', '<\\/')


def inline_block(snapshot):
    meta = {k: snapshot['provenance'][k] for k in ('endpoint', 'retrieved', 'licence')}
    lines = [BEGIN, f'<script type="application/json" id="snapshot-meta">{compact(meta)}</script>']
    for name, entry in snapshot['queries'].items():
        lines.append(f'<script type="application/json" id="s-{name}">{compact(entry["results"])}</script>')
    lines.append(END)
    return '\n'.join(lines)


def with_block(page, snapshot):
    a, b = page.index(BEGIN), page.index(END) + len(END)
    return page[:a] + inline_block(snapshot) + page[b:]


def capture(queries):
    out = {}
    for name, text in queries.items():
        request = urllib.request.Request(ENDPOINT + '?' + urllib.parse.urlencode({'query': text}),
                                         headers={'Accept': 'application/sparql-results+json',
                                                  'User-Agent': 'factoidal spinal-tap-snapshot.py (demo page snapshot)'})
        with urllib.request.urlopen(request, timeout=120) as response:
            results = json.load(response)
        # QLever adds its own keys (timing and the like); keep the SPARQL 1.1 JSON results only.
        results = {'head': results['head'], 'results': {'bindings': results['results']['bindings']}}
        print(f'{name}: {len(results["results"]["bindings"])} rows', file=sys.stderr)
        out[name] = {'query': text, 'results': results}
    now = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0).isoformat().replace('+00:00', 'Z')
    return {'provenance': {
        'source': 'Wikidata (https://www.wikidata.org/), through the QLever SPARQL endpoint',
        'endpoint': ENDPOINT, 'method': 'HTTP GET with query=, Accept: application/sparql-results+json',
        'retrieved': now, 'licence': 'CC0 1.0', 'licenceURL': 'https://creativecommons.org/publicdomain/zero/1.0/',
        'tool': 'labs/demos/foafnaut/tools/spinal-tap-snapshot.py --capture',
        'page': 'labs/demos/foafnaut/pages/spinal-tap-sparql.html'}, 'queries': out}


def main():
    page = open(PAGE, encoding='utf-8').read()
    queries = page_queries(page)
    if len(queries) < 5:
        raise SystemExit(f'expected the page\'s sparql-query blocks, found {len(queries)}')
    if '--capture' in sys.argv:
        snapshot = capture(queries)
        os.makedirs(os.path.dirname(DATA), exist_ok=True)
        with open(DATA, 'w', encoding='utf-8') as f:
            json.dump(snapshot, f, ensure_ascii=False, indent=1)
            f.write('\n')
    snapshot = json.load(open(DATA, encoding='utf-8'))
    stored = {name: entry['query'] for name, entry in snapshot['queries'].items()}
    if '--check' in sys.argv:
        problems = []
        if stored != queries:
            problems.append('the page\'s queries differ from the snapshot\'s (run --capture)')
        if with_block(page, snapshot) != page:
            problems.append('the inlined results differ from the snapshot (run without flags)')
        for p in problems:
            print(f'spinal-tap-snapshot: {p}', file=sys.stderr)
        sys.exit(1 if problems else 0)
    if stored != queries:
        raise SystemExit('the page\'s queries differ from the snapshot\'s: run with --capture')
    new = with_block(page, snapshot)
    if new != page:
        open(PAGE, 'w', encoding='utf-8').write(new)
        print(f'wrote {os.path.relpath(PAGE, ROOT)}', file=sys.stderr)


if __name__ == '__main__':
    main()
