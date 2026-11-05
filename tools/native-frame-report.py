#!/usr/bin/env python3
"""Summarise native-html-frame JSON lines: median time per stage, in ms.

    tools/native-frame-report.py TRACE [BASELINE]

With BASELINE it also prints the change in median total frame time.
"""
import json, statistics, sys

STAGES = ('layoutMs', 'sessionMs', 'drawMs', 'totalMs')


def frames(path):
    rows = []
    for line in open(path, encoding='utf-8'):
        try:
            row = json.loads(line)
        except ValueError:
            continue
        if isinstance(row, dict) and row.get('type') == 'native-html-frame':
            rows.append(row)
    if not rows:
        sys.exit(f'{path}: no native-html-frame lines')
    return rows


def summary(rows):
    return {name: statistics.median(row[name] for row in rows) for name in STAGES}


rows = frames(sys.argv[1])
result = summary(rows)
pixels = statistics.median(row['width'] * row['height'] for row in rows)
print(json.dumps({'frames': len(rows), 'medianPixels': pixels, 'medianMs': result,
                  'drawNsPerPixel': round(result['drawMs'] * 1e6 / pixels, 1)}))
if len(sys.argv) > 2:
    base = summary(frames(sys.argv[2]))
    print(json.dumps({'totalMsChange': round(result['totalMs'] - base['totalMs'], 1),
                      'ratio': round(result['totalMs'] / base['totalMs'], 3)}))
