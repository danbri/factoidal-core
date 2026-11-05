#!/usr/bin/env python3
"""Render every foafnaut2525 demo page with the Lean engine and report the score.

    tools/check-demo-pages.py WEB_RENDER_NATIVE

A page marked "refused" is an expected failure with an open issue: the check
fails if the refusal text changes, or if the page starts to render.
"""
import json, os, subprocess, sys

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PAGES = os.path.join(ROOT, 'labs/demos/foafnaut/pages')
manifest = json.load(open(os.path.join(PAGES, 'manifest.json'), encoding='utf-8'))
native = sys.argv[1]
rendered = refused = failed = 0
for page in manifest['pages']:
    width, height = page.get('size', [900, 700])
    output = subprocess.run([native, os.path.join(PAGES, page['page']), str(width), str(height)],
                            capture_output=True, text=True, timeout=120).stdout
    result = json.loads(output)
    error = result.get('error')
    expected = page.get('refused')
    if expected is None and error is None:
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
