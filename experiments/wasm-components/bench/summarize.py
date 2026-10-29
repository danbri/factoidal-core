#!/usr/bin/env python3
"""Summarise bench/run-all.sh output (JSON lines) as the Markdown tables of
RESULTS.md: sizes, then the median over runs of each timing per (variant,
host, document). Usage: summarize.py results.jsonl"""
import json, sys, statistics as st
from collections import defaultdict
rows = []
for l in open(sys.argv[1]):
    try: rows.append(json.loads(l))
    except ValueError: pass   # a line whose run failed (its error is in stderr)
med = lambda v: st.median(v) if v else None
fmt = lambda x: '' if x is None else (f'{x:,.0f}' if x >= 100 else f'{x:.1f}')
print('| Variant | Artifact | Bytes | gzip -9 bytes |\n| --- | --- | ---: | ---: |')
for r in rows:
    if 'artifact' in r:
        print(f"| {r['variant']} | {r['artifact']} | {r['bytes']:,} | {r['gzipBytes']:,} |")
acc = defaultdict(lambda: defaultdict(list)); shas = defaultdict(set)
for r in rows:
    if 'host' not in r: continue
    k = (r['variant'], r['host'], r.get('doc', ''))
    if 'compileMs' in r: acc[k]['compileMs'].append(r['compileMs'])
    if 'wallMs' in r: acc[k]['wallMs'].append(r['wallMs'])
    for f, v in (r.get('r') or {}).items():
        if isinstance(v, (int, float)): acc[k][f].append(v)
        if f == 'answerSha': shas[r.get('doc')].add(v)
    if 'r' in r and 'answerHead' in r['r']:
        shas[(r.get('doc'), 'head')].add(r['r']['answerHead'][:60])
print('\n| Variant | Host | Document | import ms | init ms | parse ms | query ms | other |')
print('| --- | --- | --- | ---: | ---: | ---: | ---: | --- |')
for (v, h, d), m in acc.items():
    p = med(m.get('parseMs')) or (med(m.get('parseUs')) / 1000 if m.get('parseUs') else None)
    q = med(m.get('queryMs')) or (med(m.get('queryUs')) / 1000 if m.get('queryUs') else None)
    other = '; '.join(f'{f} {fmt(med(m[f]))}' for f in ('compileMs', 'wallMs') if m.get(f))
    print(f'| {v} | {h} | {d} | {fmt(med(m.get("importMs")))} | {fmt(med(m.get("initMs")))} | {fmt(p)} | {fmt(q)} | {other} |')
print('\nDistinct answers per document (SHA-256 prefixes / heads):', {str(k): sorted(v) for k, v in shas.items()})
