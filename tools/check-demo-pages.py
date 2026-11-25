#!/usr/bin/env python3
"""Render every foafnaut2525 demo page with the Lean engine and report the score.

    tools/check-demo-pages.py WEB_RENDER_NATIVE

A page marked "refused" is an expected failure with an open issue: the check
fails if the refusal text changes, or if the page starts to render.

A page can declare local checkStylesheets fixtures keyed by resolved URL.
The standalone check supplies them using the strict document API.
"""
import json, os, subprocess, sys, tempfile
from pathlib import Path

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PAGES = os.path.join(ROOT, 'labs/demos/foafnaut/pages')
manifest = json.load(open(os.path.join(PAGES, 'manifest.json'), encoding='utf-8'))
native = sys.argv[1]
def render_demo(page):
    width, height = page.get('size', [900, 700])
    argv = [native, os.path.join(PAGES, page['page']), str(width), str(height)]

    def call(args):
        result = subprocess.run(args, capture_output=True, text=True, timeout=120)
        return json.loads(result.stdout)

    fixtures = page.get('checkStylesheets')
    if not fixtures:
        return call(argv)

    # Use the same strict document API as a host that has already resolved the link.
    # Load only named fixture bytes. The release check does not fetch URLs.
    url = 'https://demo-pages.invalid/' + page['page']
    with tempfile.TemporaryDirectory() as work:
        request = Path(work) / 'document.json'

        def document(op, **fields):
            request.write_text(json.dumps(dict(op=op, url=url, liberal=False, **fields)), encoding='utf-8')
            return call([*argv, '--document', str(request)])

        inspected = document('inspect')
        if inspected.get('error'):
            return inspected
        sheets = inspected['stylesheets']
        missing = fixtures.keys() - {sheet['url'] for sheet in sheets}
        if missing:
            return {'error': 'configured demo stylesheet not linked: ' + ', '.join(sorted(missing))}
        resources = [
            dict(nodeId=sheet['nodeId'], url=sheet['url'],
                 source=(Path(PAGES) / fixtures[sheet['url']]).read_text(encoding='utf-8'))
            for sheet in sheets if sheet['url'] in fixtures
        ]
        return document('render', resources=resources)


rendered = refused = failed = 0
for page in manifest['pages']:
    result = render_demo(page)
    error = result.get('error')
    expected = page.get('refused')
    # A page that draws one primitive (the page background) shows nothing: the Settings page
    # did that for nine days, from 2026-11-16, when its <style> element lost its end tag.
    if expected is None and error is None and result.get('primitiveCount', 0) <= 1:
        failed += 1
        print(f'FAIL {page["page"]}: drew {result.get("primitiveCount")} primitive (an empty page)')
    elif expected is None and error is None:
        rendered += 1
        print(f'rendered {page["page"]}: {result["primitiveCount"]} primitives')
    elif expected is not None and error is not None and expected in error:
        refused += 1
        print(f'expected refusal {page["page"]}: {error} ({page["issue"]})')
    else:
        failed += 1
        print(f'FAIL {page["page"]}: expected {expected or "render"}, got {error or "render"}')
print(f'demo pages: {rendered} rendered, {refused} expected refusals, {failed} failed (out of {len(manifest["pages"])})')
sys.exit(1 if failed else 0)
