#!/usr/bin/env python3
"""Write the Hub dashboard page from tools/render-dashboard/history.jsonl.

    tools/render-dashboard/page.py [--fragment FILE]

The output is generated: docs/web/hub/render-scores/index.njk. Do not edit it.
--fragment also writes the page body alone, to look at it with no site build.
Each suite stays on its own row: no number on the page adds two suites.
"""
import argparse, collections, html, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HISTORY = Path(__file__).with_name('history.jsonl')
PAGE = ROOT / 'docs/web/hub/render-scores/index.njk'
# Suite, the state that is the score, and the OKR target when there is one.
SUITES = [
    ('wpt-images-wasm', 'match', 'KR 3.4: 100 match'),
    ('wpt-images-native', 'pass', None),
    ('svg-tiny-pixels', 'match', None),
    ('svg-tiny-admission', 'admitted', 'KR 3.6: 250 admitted'),
    ('wpt-scripts', 'pass', 'KR 3.5: 50 complete PASS documents'),
    ('html-tree', 'pass', 'KR 3.1: 1,973 pass'),
    ('html-dom-tree', 'pass', None),
    ('html-tokenizer', 'pass', 'KR 3.2: 7,053 pass'),
    ('html-parse-errors', 'agree', 'KR 3.3: differ at most 100'),
    ('harfbuzz', 'pass', 'KR 3.7: 4,500 pass'),
    ('font-records', 'same', 'KR 3.8: stays 56 of 56'),
    ('old-web', 'rendered', None),
    ('demo-pages', 'rendered', None),
    ('lab-suite', 'pass', 'KR 4.1: 0 fail'),
]
# Every state has one class, the same in each suite. Pass and fail never share
# a class with unsupported, unavailable, not run or refused.
STATE_CLASS = {
    'pass': 'good', 'match': 'good', 'rendered': 'good', 'same': 'good', 'agree': 'good', 'admitted': 'good',
    'expected-refusal': 'refused', 'negative-only': 'close', 'negative_only': 'close', 'close': 'close',
    'fail': 'bad', 'mismatch': 'bad', 'different': 'bad', 'differ': 'bad', 'empty': 'bad',
    'error': 'error', 'crash': 'error', 'timeout': 'error', 'harness_error': 'error', 'gpu_error': 'error',
    'refused': 'refused', 'rejected': 'refused',
    'unsupported': 'unsupported',
    'unavailable': 'unavailable', 'incomplete': 'unavailable', 'no_assertions': 'unavailable',
}
# The order is checked for colour blindness: adjacent colours stay apart.
CLASS_LABEL = [('good', 'Pass'), ('close', 'Close or partial'), ('bad', 'Fail'), ('unsupported', 'Unsupported'),
               ('error', 'Error or timeout'), ('refused', 'Refused'), ('unavailable', 'Unavailable or incomplete')]
OUTSIDE = {'not-applicable', 'oracle-mismatch'}   # Rows outside the denominator of their suite.
EMOJI_KINDS = [('Basic_Emoji', 'Basic'), ('Emoji_Keycap_Sequence', 'Keycap'), ('RGI_Emoji_Flag_Sequence', 'Flag'),
               ('RGI_Emoji_Tag_Sequence', 'Tag'), ('RGI_Emoji_Modifier_Sequence', 'Modifier'), ('RGI_Emoji_ZWJ_Sequence', 'ZWJ')]
RUNS_SHOWN = 12
esc = lambda text: html.escape(str(text), quote=True)
num = lambda n: f'{n:,}'

STYLE = """
.rs { --s:#fcfcfb; --ink:#0b0b0b; --ink2:#52514e; --mute:#6f6d68; --line:#e1e0d9; --base:#c3c2b7;
  --good:#0ca30c; --close:#fab219; --bad:#d03b3b; --error:#ec835a; --refused:#6250d6; --unsupported:#2a78d6; --unavailable:#898781;
  color:var(--ink); font-family:system-ui,-apple-system,"Segoe UI",sans-serif; }
@media (prefers-color-scheme: dark) { :root:where(:not([data-theme="light"])) .rs { --s:#1a1a19; --ink:#f0efec; --ink2:#c3c2b7; --mute:#a3a198; --line:#2c2c2a; --base:#383835; --refused:#9085e9; --unsupported:#3987e5; } }
:root[data-theme="dark"] .rs { --s:#1a1a19; --ink:#f0efec; --ink2:#c3c2b7; --mute:#a3a198; --line:#2c2c2a; --base:#383835; --refused:#9085e9; --unsupported:#3987e5; }
.rs h2 { margin:2rem 0 .5rem; } .rs h3 { margin:0 0 .15rem; font-size:1.02rem; }
.rs p { color:var(--ink2); margin:.3rem 0 .6rem; }
.rs .card { background:var(--s); border:1px solid var(--line); border-radius:8px; padding:14px 16px; margin:12px 0; }
.rs .meta { font-size:.8rem; color:var(--mute); overflow-wrap:anywhere; }
.rs .wide { overflow-x:auto; }
.rs a { color:var(--unsupported); }
.rs table { border-collapse:collapse; width:100%; font-size:.88rem; }
.rs th { text-align:left; color:var(--mute); font-weight:500; border-bottom:1px solid var(--base); padding:4px 8px 4px 0; white-space:nowrap; }
.rs td:first-child { min-width:9em; }
.rs td { border-bottom:1px solid var(--line); padding:5px 8px 5px 0; vertical-align:top; color:var(--ink); }
.rs td.n, .rs th.n { text-align:right; font-variant-numeric:tabular-nums; white-space:nowrap; }
.rs code { font-size:.82em; }
.rs .legend { display:flex; flex-wrap:wrap; gap:4px 14px; font-size:.82rem; color:var(--ink2); margin:.4rem 0; }
.rs .key { display:inline-block; width:10px; height:10px; border-radius:3px; margin-right:5px; }
.rs .run { display:grid; grid-template-columns:minmax(120px,172px) 1fr; gap:10px; align-items:center; font-size:.8rem; padding:3px 0; }
.rs .run b { font-weight:500; font-family:ui-monospace,Menlo,monospace; color:var(--ink); }
.rs .run span.who { color:var(--mute); }
.rs .bar { display:flex; gap:2px; height:14px; }
.rs .seg { min-width:2px; height:100%; border-radius:2px; }
.rs .seg:first-child { border-radius:4px 2px 2px 4px; } .rs .seg:last-child { border-radius:2px 4px 4px 2px; }
.rs .seg:hover { outline:2px solid var(--ink); outline-offset:1px; }
.rs .c-good { background:var(--good); } .rs .c-close { background:var(--close); } .rs .c-bad { background:var(--bad); }
.rs .c-error { background:var(--error); } .rs .c-refused { background:var(--refused); }
.rs .c-unsupported { background:var(--unsupported); } .rs .c-unavailable { background:var(--unavailable); }
.rs .counts { font-size:.8rem; color:var(--ink2); grid-column:2; margin-top:-2px; }
.rs .group { display:grid; grid-template-columns:3.2em 1fr; gap:2px 8px; font-size:.84rem; padding:3px 0; }
.rs .group .c { text-align:right; font-variant-numeric:tabular-nums; }
.rs .gbar { height:6px; border-radius:0 3px 3px 0; background:var(--mute); margin-top:2px; }
.rs .ex { color:var(--mute); font-size:.76rem; overflow-wrap:anywhere; }
.rs details { margin-top:6px; } .rs summary { cursor:pointer; font-size:.84rem; color:var(--ink2); }
.rs .tag { font-size:.72rem; border:1px solid var(--base); border-radius:4px; padding:0 4px; color:var(--mute); margin-left:4px; }
.rs .up { color:#006300; } .rs .down { color:var(--bad); }
:root[data-theme="dark"] .rs .up { color:#0ca30c; }
@media (prefers-color-scheme: dark) { :root:where(:not([data-theme="light"])) .rs .up { color:#0ca30c; } }
@media (max-width:560px) { .rs .run { grid-template-columns:1fr; gap:2px; } .rs .counts { grid-column:1; } }
"""


def load():
    records = [json.loads(line) for line in HISTORY.read_text(encoding='utf-8').splitlines() if line.strip()]
    by = collections.defaultdict(list)
    for record in records:
        by[record['suite']].append(record)
    return records, by


def short(commit):
    return (commit or 'no commit')[:9]


def state_class(name):
    return STATE_CLASS.get(name.lower(), 'unavailable')


def measured(rows):
    return [row for row in rows if row['origin'] != 'not-run']


def bar(record):
    counts = {k: v for k, v in record['counts'].items() if k not in OUTSIDE and v}
    total = sum(counts.values()) or 1
    order = {name: index for index, (name, _) in enumerate(CLASS_LABEL)}
    parts = []
    for name, value in sorted(counts.items(), key=lambda item: (order[state_class(item[0])], item[0])):
        tip = f'{name}: {num(value)} of {num(record["denominator"])}'
        parts.append(f'<span class="seg c-{state_class(name)}" style="flex:{value / total:.5f} 1 0" title="{esc(tip)}"></span>')
    return '<div class="bar" role="img" aria-label="' + esc(counts_text(record)) + '">' + ''.join(parts) + '</div>'


def counts_text(record):
    parts = [f'{num(v)} {k}' for k, v in record['counts'].items() if k not in OUTSIDE]
    text = ', '.join(parts) + f' (out of {num(record["denominator"])})'
    outside = [f'{num(record["counts"][k])} {k}' for k in sorted(OUTSIDE) if k in record['counts']]
    return text + ('; outside the denominator: ' + ', '.join(outside) if outside else '')


def run_row(record):
    tag = 'measured' if record['origin'] == 'measured' else 'copied'
    return (f'<div class="run"><div><b>{esc(short(record.get("commit")))}</b> <span class="who">{esc(record["date"])}'
            f'<span class="tag">{tag}</span></span></div>{bar(record)}'
            f'<div class="counts">{esc(counts_text(record))}</div></div>')


def group_rows(record, limit=8):
    groups = record.get('groups') or []
    if not groups:
        return '<p class="meta">This record has no failure groups.</p>'
    top = groups[0]['count'] or 1
    rows = []
    for group in groups[:limit]:
        examples = ', '.join(group.get('examples') or [])
        rows.append(f'<div class="group"><div class="c">{num(group["count"])}</div><div>{esc(group["reason"])}'
                    f'<div class="gbar" style="width:{100 * group["count"] / top:.1f}%"></div>'
                    + (f'<div class="ex">{esc(examples)}</div>' if examples else '') + '</div></div>')
    return ''.join(rows)


def input_text(record):
    pin = record.get('input', {})
    value = pin.get('pin', '')
    value = value if isinstance(value, str) else 'see the history file'
    return f'{pin.get("name", "Input not recorded")}, pin {value[:16]}'


def delta(rows, key):
    done = measured(rows)
    if len(done) < 2 or done[-1]['denominator'] != done[-2]['denominator']:
        return ''
    change = done[-1]['counts'].get(key, 0) - done[-2]['counts'].get(key, 0)
    if not change:
        return '<span class="meta">no change</span>'
    return f'<span class="{"up" if change > 0 else "down"}">{"+" if change > 0 else "−"}{num(abs(change))}</span>'


def summary(by):
    rows = []
    for suite, key, target in SUITES:
        done = measured(by.get(suite, []))
        if not done:
            continue
        last = done[-1]
        # An unavailable row is a limit of the test setup, not a fix in the engine.
        group = next((g for g in last.get('groups') or [] if not g['reason'].lower().startswith('unavailable')), {})
        fix = f'{esc(group["reason"])} <span class="meta">({num(group["count"])})</span>' if group else '<span class="meta">None recorded</span>'
        tag = '' if last['origin'] == 'measured' else '<span class="tag">copied</span>'
        rows.append(f'<tr><td><a href="#{esc(suite)}">{esc(suite)}</a>{tag}</td><td class="n">{num(last["counts"].get(key, 0))} of {num(last["denominator"])}</td>'
                    f'<td class="n">{delta(by[suite], key)}</td><td><code>{esc(short(last.get("commit")))}</code></td><td>{fix}</td></tr>')
    return ('<div class="wide"><table><thead><tr><th>Suite</th><th class="n">Score</th><th class="n">Since last run</th><th>Commit</th>'
            '<th>Largest failure group: the next fix</th></tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div>')


def not_run(by):
    rows = []
    for suite, records in by.items():
        if records[-1]['origin'] == 'not-run':
            rows.append(f'<tr><td>{esc(suite)}</td><td><code>{esc(short(records[-1].get("commit")))}</code></td><td>{esc(records[-1]["reason"])}</td></tr>')
    if not rows:
        return '<p>Each suite ran in its last attempt.</p>'
    return '<div class="wide"><table><thead><tr><th>Suite</th><th>Commit</th><th>Why it did not run</th></tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div>'


def fonts(by):
    latest = [records[-1] for name, records in by.items() if name.startswith('font-coverage/') and records[-1]['origin'] == 'measured']
    latest.sort(key=lambda record: (record.get('reference', False), record['suite']))
    if not latest:
        return '<p>No measurement yet.</p>'
    heads = ''.join(f'<th class="n">{label}</th>' for _, label in EMOJI_KINDS)
    glyphs, emoji = [], []
    for record in latest:
        counts, of = record['counts'], record['denominators']
        name = record['suite'].split('/', 1)[1]
        tag = '<span class="tag">reference</span>' if record.get('reference') else '<span class="tag">in the browser</span>'
        cells = ''.join(f'<td class="n">{num(counts[key])} of {num(of[key])}</td>' for key, _ in EMOJI_KINDS)
        glyphs.append(f'<tr><td>{esc(name)}{tag}</td><td class="n">{num(counts["characters"])} of {num(of["characters"])}</td>'
                      f'<td class="n">{num(counts["scripts"])} of {num(of["scripts"])}</td><td class="n">{num(counts["scriptsComplete"])}</td>'
                      f'<td class="n">{num(counts["emojiAll"])} of {num(of["emojiAll"])}</td></tr>')
        emoji.append(f'<tr><td>{esc(name)}</td>{cells}</tr>')
    missing = latest[0].get('groups') or []
    gaps = ', '.join(f'{group["reason"]} ({num(group["count"])})' for group in missing[:6])
    return ('<div class="wide"><table><thead><tr><th>Font set</th><th class="n">Characters</th><th class="n">Scripts with a glyph</th>'
            '<th class="n">Scripts complete</th><th class="n">Emoji, all RGI</th></tr></thead><tbody>' + ''.join(glyphs) + '</tbody></table></div>'
            f'<details><summary>Emoji by type</summary><div class="wide"><table><thead><tr><th>Font set</th>{heads}</tr></thead><tbody>' + ''.join(emoji) + '</tbody></table></div></details>'
            f'<p class="meta">Totals: Unicode 18.0.0 graphic characters, Script values without Common and Inherited, and RGI emoji sequences. '
            f'A sequence counts when it shapes to one real glyph. Largest gaps for {esc(latest[0]["suite"].split("/", 1)[1])}: {esc(gaps)}.</p>')


def suite_card(suite, target, rows):
    done = measured(rows)
    last = done[-1]
    runs = ''.join(run_row(record) for record in done[-RUNS_SHOWN:])
    notes = [last[key] for key in ('notes', 'denominatorNote') if last.get(key)]
    if last.get('assertions'):
        notes.append(f'Assertions: {num(last["assertions"]["pass"])} pass, {num(last["assertions"]["fail"])} fail.')
    if last.get('blankControl'):
        notes.append('Blank white control: ' + ', '.join(f'{num(v)} {k.lower()}' for k, v in last['blankControl'].items()) + '.')
    return (f'<section class="card" id="{esc(suite)}"><h3>{esc(last["title"])}</h3>'
            f'<div class="meta"><code>{esc(suite)}</code> · {esc(last["runner"])} · {esc(input_text(last))}'
            + (f' · target {esc(target)}' if target else '') + '</div>'
            + ''.join(f'<p class="meta">{esc(note)}</p>' for note in notes) + runs +
            f'<details{" open" if last.get("groups") else ""}><summary>Failure groups at {esc(short(last.get("commit")))}</summary>{group_rows(last)}</details></section>')


def body(records, by):
    dated = [record for record in records if record['origin'] == 'measured']
    newest = max(dated, key=lambda record: record['date']) if dated else None
    legend = ''.join(f'<span><span class="key c-{name}"></span>{label}</span>' for name, label in CLASS_LABEL)
    cards = ''.join(suite_card(suite, target, by[suite]) for suite, _, target in SUITES if measured(by.get(suite, [])))
    head = (f'Last measured run: commit <code>{esc(short(newest["commit"]))}</code> on {esc(newest["date"])}.' if newest else 'No measured run yet.')
    return f"""<div class="rs">
<h1>Rendering and font scores</h1>
<p>{head} Each suite names its input, its total and its commit. Scores from different suites are never added.
Unsupported, unavailable, refused and not run stay apart from pass and fail. A "copied" row is a number from an earlier report, not measured by this tool.</p>
<h2>Where to work next</h2>
{summary(by)}
<h2>Fonts</h2>
{fonts(by)}
<h2>Suites that did not run</h2>
{not_run(by)}
<h2>Trend by commit</h2>
<div class="legend">{legend}</div>
{cards}
<p class="meta">Generated by tools/render-dashboard/page.py from tools/render-dashboard/history.jsonl. Do not edit this page.</p>
</div>"""


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--fragment', type=Path)
    a = p.parse_args()
    records, by = load()
    content = f'<style>{STYLE}</style>\n{body(records, by)}\n'
    PAGE.parent.mkdir(parents=True, exist_ok=True)
    PAGE.write_text('---\nlayout: hub.njk\ntitle: Rendering and font scores\n'
                    'description: Score of each rendering and font test suite, by commit, with the largest failure groups.\n'
                    'permalink: /web/hub/render-scores/\n---\n{% raw %}\n' + content + '{% endraw %}\n', encoding='utf-8')
    if a.fragment:
        a.fragment.write_text(content, encoding='utf-8')
    print(PAGE)


if __name__ == '__main__':
    main()
