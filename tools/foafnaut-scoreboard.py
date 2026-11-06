#!/usr/bin/env python3
"""Write the scoreboard of one foafnaut2525 release, as JSON and as Markdown.

    tools/foafnaut-scoreboard.py --release NAME --commit SHA --out-dir DIR
        [--tiny REPORT.json] [--lab-log LOG] [--pages-log LOG] [--trace TRACE.jsonl]
        [--earlier FILE.json] [--history tools/render-dashboard/history.jsonl]

Each score names its suite, input, denominator and measured commit. A suite with
no input here takes its last measured record from --history. If it has none, it
is copied from --earlier, or from the OKR baseline, and is marked "not
re-measured". Scores from different suites are never added. Rule:
https://github.com/danbri/factoidal/issues/1245
"""
import argparse, json, re, statistics
from pathlib import Path

BASELINES = [
    ('html-tree', 'html5lib tree construction', 'tests/browser-wpt/parser-probe.py', '1,963 pass, 10 fail (out of 1,973)', '2026-11-03'),
    ('html-tokenizer', 'html5lib tokenizer', 'tests/browser-wpt/parser-probe.py', '7,047 pass, 6 fail (out of 7,053)', '2026-11-03'),
    ('wpt-images', 'WPT SVG and HTML image relations, browser WASM and WebGPU', 'run.mjs of the corpus in tests/external/svg-wpt',
     '29 match, 21 mismatch, 264 unsupported, 30 rejected, 257 unavailable (out of 601)', '2026-11-03'),
    ('wpt-scripts', 'WPT scripted documents', 'tests/browser-wpt/quickjs-probe.mjs', '0 complete passes (out of 784)', '2026-11-03'),
    ('harfbuzz', 'HarfBuzz 15.0.0 shaping suite', 'labs/demos/foafnaut/tools/run-harfbuzz-suite.py',
     '4,175 pass, 533 fail, 169 refused (out of 4,877 applicable)', '2026-11-04'),
    ('font-records', 'Font records against native HarfBuzz', 'check-lean-shaper.py', '56 same, 0 different (out of 56)', '2026-11-04'),
]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--release', required=True)
p.add_argument('--commit', required=True)
p.add_argument('--out-dir', required=True, type=Path)
p.add_argument('--measured-commit', help='commit of the suites run here, when it is not --commit')
p.add_argument('--tiny', type=Path)
p.add_argument('--lab-log', type=Path)
p.add_argument('--pages-log', type=Path)
p.add_argument('--trace', type=Path)
p.add_argument('--earlier', type=Path)
p.add_argument('--history', type=Path)
a = p.parse_args()
measured = a.measured_commit or a.commit
clean = lambda text: re.sub(r'\x1b\[[0-9;]*m', '', text)
suites = []


def score(key, suite, command, text, numbers=None):
    suites.append({'key': key, 'suite': suite, 'command': command, 'score': text, 'measuredCommit': measured,
                   'status': 'measured', **({'numbers': numbers} if numbers else {})})


if a.tiny:
    report = json.loads(a.tiny.read_text())
    counts = report['counts']
    parts = [f"{counts.get(name, 0):,} {label}" for name, label in
             [('MATCH', 'match'), ('CLOSE', 'close'), ('MISMATCH', 'mismatch'), ('REFUSED', 'refused'),
              ('UNAVAILABLE', 'not read'), ('CRASH', 'crash'), ('TIMEOUT', 'timeout'), ('GPU_ERROR', 'GPU error')]
             if counts.get(name, 0) or name in ('MATCH', 'CLOSE', 'MISMATCH')]
    assert sum(counts.values()) == report['total'], 'Tiny counts do not add up to the total'
    score('svg-tiny-pixels', 'W3C SVG Tiny 1.2, WebGPU pixels against W3C images (our bands, not a W3C verdict)',
          'tests/browser-wpt/svg-tiny-pixels.py', f"{', '.join(parts)} (out of {report['total']})",
          {'counts': counts, 'blankControl': report['blankControlCounts'], 'archiveSha256': report['archiveSha256']})
if a.lab_log:
    text = clean(a.lab_log.read_text())
    rows = re.findall(r'^(ok|FAILED) \| (\d+) passed \| (\d+) failed', text, re.M)
    coordinate = re.search(r'coordinate checks: (\d+) passed', text)
    assert rows and coordinate, 'Lab log has no test summary'
    passed = [int(row[1]) for row in rows]
    failed = sum(int(row[2]) for row in rows)
    score('lab-suite', 'Lab suite', 'labs/demos/foafnaut/test.sh --skip-build',
          f"{' and '.join(map(str, passed))} Deno tests pass, {failed} fail; {coordinate[1]} coordinate checks pass")
if a.pages_log:
    line = re.findall(r'demo pages: .*', clean(a.pages_log.read_text()))
    assert line, 'Pages log has no summary'
    score('demo-pages', 'Demo pages', 'tools/check-demo-pages.py', line[-1].replace('demo pages: ', ''))
if a.trace:
    frames = [json.loads(line) for line in a.trace.read_text().splitlines() if '"native-html-frame"' in line]
    assert frames, 'Trace has no frames'
    median = lambda key: round(statistics.median(frame[key] for frame in frames), 1)
    score('frame-time', 'Native frame trace', 'foafnaut app trace', f"median frame {median('totalMs')} ms, layout "
          f"{median('layoutMs')} ms, draw {median('drawMs')} ms ({len(frames)} frames)")
# The history names one suite by a longer key.
HISTORY_KEYS = {'wpt-images': 'wpt-images-wasm'}
if a.history:
    records = [json.loads(line) for line in a.history.read_text().splitlines() if line.strip()]
    for key, suite, command, _, _ in BASELINES:
        found = [row for row in records if row['suite'] == HISTORY_KEYS.get(key, key) and row['origin'] == 'measured']
        if found and key not in {row['key'] for row in suites}:
            row = found[-1]
            text = ', '.join(f'{value:,} {name}' for name, value in row['counts'].items())
            suites.append({'key': key, 'suite': suite, 'command': command, 'score': f"{text} (out of {row['denominator']:,})",
                           'measuredCommit': row['commit'], 'status': 'measured', 'numbers': {'counts': row['counts']}})
known = {row['key'] for row in suites}
earlier = {row['key']: row for row in json.loads(a.earlier.read_text())['suites']} if a.earlier else {}
for key, suite, command, text, date in BASELINES:
    if key in known:
        continue
    suites.append({**earlier[key], 'status': 'not re-measured'} if key in earlier else
                  {'key': key, 'suite': suite, 'command': command, 'score': text, 'measuredOn': date, 'status': 'not re-measured'})
board = {'format': 'foafnaut2525-scoreboard-v1', 'release': a.release, 'commit': a.commit, 'suites': suites}
a.out_dir.mkdir(parents=True, exist_ok=True)
(a.out_dir / f'{a.release}.json').write_text(json.dumps(board, indent=1) + '\n')
lines = [f'Commit `{a.commit[:12]}`. Scores from different suites are not added.', '']
for row in suites:
    where = f"at `{row['measuredCommit'][:9]}`" if 'measuredCommit' in row else f"on {row.get('measuredOn', 'an earlier day')}"
    mark = '' if row['status'] == 'measured' else ', not re-measured'
    lines.append(f"- {row['suite']}: {row['score']} ({where}{mark}).")
(a.out_dir / f'{a.release}.md').write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))
