#!/usr/bin/env python3
"""Classify the vendored WPT css/css-tables tests by kind and by the CSS features
that each reftest uses, to see which reftests a basic table layout could pass.

    tools/render-dashboard/wpt_tables_classify.py [--root third_party/testing/wpt-css-tables]
        [--output tools/render-dashboard/wpt-tables-classes.json]

Test or not, and the kind, follow the rules of WPT's manifest
(tools/manifest/sourcefile.py) in a reduced form:
  - not a test: a path with a support/, resources/, tools/ or reference/ folder,
    a name with -ref or -notref before the extension or ref- at the start, a file
    that some test names as its reference, a file that is not .html/.htm/.xht/.xhtml/.svg;
  - crashtest: a crashtests/ folder or a name ending in -crash;
  - print reftest: a name ending in -print (with a match or mismatch link);
  - testharness: a script element whose src ends in testharness.js;
  - reftest: a link with rel=match or rel=mismatch;
  - other: none of these (WPT's "visual" or "manual").
Tentative: ".tentative." in the name or a tentative/ folder.

Feature detection is by regular expressions over the test and its references,
including stylesheets they link that are inside the vendored tree. It is coarse.
It reads source text and does not compute style: a property in a rule that
matches nothing still counts.
"""
import argparse, collections, json, re, sys
from pathlib import Path, PurePosixPath

HERE = Path(__file__).resolve()
ROOT = HERE.parents[2]
CSS_TABLES = 'css/css-tables'
TEST_EXT = ('.html', '.htm', '.xht', '.xhtml', '.svg')

LINK = re.compile(r'<link\b[^>]*>', re.I)
ATTR = lambda name: re.compile(r'\b' + name + r'\s*=\s*(?:"([^"]*)"|\'([^\']*)\'|([^\s>]+))', re.I)
REL, HREF, NAME, CONTENT, SRC = ATTR('rel'), ATTR('href'), ATTR('name'), ATTR('content'), ATTR('src')
META = re.compile(r'<meta\b[^>]*>', re.I)
SCRIPT = re.compile(r'<script\b[^>]*>', re.I)


def attr(pattern, tag):
    m = pattern.search(tag)
    return None if not m else next(g for g in m.groups() if g is not None)


def strip_comments(text):
    return re.sub(r'<!--.*?-->', ' ', re.sub(r'/\*.*?\*/', ' ', text, flags=re.S), flags=re.S)


# Coarse features. Each is (name, pattern over source text, lower-cased, comments removed).
TABLE_DISPLAY = r'display\s*:\s*(?:inline-)?table(?:-[a-z-]+)?\b'
TABLE_ELEMENTS = r'<(?:table|tr|td|th|tbody|thead|tfoot|caption|col|colgroup)\b'
FEATURES = [
    ('table-elements', TABLE_ELEMENTS),
    ('display-table', TABLE_DISPLAY),
    ('border-collapse', r'border-collapse\s*:\s*collapse|\bborder\s*=\s*["\']?\d|\brules\s*='),
    ('border-spacing', r'border-spacing\s*:|\bcellspacing\s*='),
    ('colspan-rowspan', r'\b(?:colspan|rowspan)\s*=|column-span|\bspan\s*=\s*["\']?\d'),
    ('col-colgroup', r'<col(?:group)?\b|display\s*:\s*table-column'),
    ('caption', r'<caption\b|display\s*:\s*table-caption|caption-side'),
    ('table-layout-fixed', r'table-layout\s*:\s*fixed'),
    ('visibility-collapse', r'visibility\s*:\s*collapse'),
    ('writing-mode', r'writing-mode\s*:|text-orientation\s*:|\bdirection\s*:\s*rtl|\bdir\s*=\s*["\']?rtl'),
    ('flex-grid', r'display\s*:\s*(?:inline-)?(?:flex|grid)\b|\bflex(?:-[a-z]+)?\s*:|\bgrid-template'),
    ('ahem', r'\bahem\b'),
    ('images', r'<img\b|<image\b|<svg\b|<canvas\b|<video\b|<object\b|<iframe\b|url\(\s*["\']?(?!#)[^)]*\.(?:png|jpe?g|gif|svg|ico)'),
    ('gradient', r'(?:linear|radial|conic)-gradient\('),
    ('script', r'<script\b|\bon[a-z]+\s*='),
    ('position', r'position\s*:\s*(?:absolute|fixed|relative|sticky)'),
    ('float', r'\bfloat\s*:\s*(?:left|right)'),
    ('percent-size', r'(?:^|[;{\s"\'])(?:min-|max-)?(?:width|height)\s*:\s*[0-9.]+%|\b(?:width|height)\s*=\s*["\']?[0-9.]+%'),
    ('calc', r'\bcalc\(|\bmin\(|\bmax\(|\bclamp\('),
    ('vertical-align', r'vertical-align\s*:\s*(?!top\b|baseline\b)[a-z-]+|\bvalign\s*='),
    ('overflow', r'overflow(?:-[xy])?\s*:\s*(?:hidden|scroll|auto|clip)'),
    ('box-sizing', r'box-sizing\s*:'),
    ('transform-filter', r'\btransform\s*:|\bfilter\s*:|will-change\s*:|\bopacity\s*:|mix-blend-mode'),
    ('multicol-print', r'column-count\s*:|columns\s*:|@page\b|break-(?:before|after|inside)\s*:'),
    ('contain-content-visibility', r'\bcontain\s*:|content-visibility\s*:|display\s*:\s*contents'),
    ('quirks-mode', r'^(?!\s*<!doctype)'),
    ('outline-shadow', r'\boutline\s*:|box-shadow\s*:'),
    ('background-image', r'background(?:-image)?\s*:[^;]*url\('),
]
# A test can reach "basic table layout" only with none of these.
BLOCKING = {'writing-mode', 'flex-grid', 'images', 'gradient', 'script', 'visibility-collapse', 'float',
            'multicol-print', 'contain-content-visibility', 'transform-filter', 'position', 'quirks-mode',
            'background-image', 'calc'}
# Table features a basic automatic table layout covers.
BASIC_TABLE = {'table-elements', 'display-table', 'border-spacing', 'colspan-rowspan', 'col-colgroup'}


def read(path):
    return path.read_text(encoding='utf-8', errors='replace')


def wpt_path(root, path):
    return PurePosixPath(path.relative_to(root).as_posix())


def resolve(base, href):
    """A reference as a WPT path, or None when it leaves the tree or is not a path."""
    href = href.split('#')[0].split('?')[0]
    if not href or re.match(r'^[a-z][a-z0-9+.-]*:', href, re.I) or href.startswith('//'):
        return None
    parts = []
    for part in (href[1:] if href.startswith('/') else str(base.parent / href)).split('/'):
        if part in ('', '.'):
            continue
        if part == '..':
            if not parts:
                return None
            parts.pop()
        else:
            parts.append(part)
    return '/'.join(parts)


def links(text):
    out = []
    for tag in LINK.findall(text):
        rel = (attr(REL, tag) or '').lower().split()
        href = attr(HREF, tag)
        if href is not None:
            out.append((rel, href))
    return out


def fuzzy(text):
    """WPT's fuzzy meta: [[maxDifference lo, hi], [totalPixels lo, hi]], or None.
    Forms: "a-b;c-d", "maxDifference=a-b;totalPixels=c-d", "a;b", and "ref.html:..."."""
    for tag in META.findall(text):
        if (attr(NAME, tag) or '').lower() != 'fuzzy':
            continue
        value = attr(CONTENT, tag) or ''
        reference = None
        if ':' in value and not re.match(r'^\s*(maxDifference|totalPixels)', value):
            reference, value = value.split(':', 1)
        ranges = {}
        for i, part in enumerate(p.strip() for p in value.split(';') if p.strip()):
            key, _, number = part.rpartition('=')
            key = key.strip() or ('maxDifference', 'totalPixels')[min(i, 1)]
            lo, _, hi = number.strip().partition('-')
            ranges[key] = [int(lo), int(hi or lo)]
        return {'reference': reference and reference.strip(),
                'value': [ranges.get('maxDifference', [0, 0]), ranges.get('totalPixels', [0, 0])]}
    return None


def stylesheet_text(root, base, text, seen=None):
    """Text of stylesheets linked from text that are inside the vendored tree, one level deep
    plus @import. Missing files are skipped."""
    seen = set() if seen is None else seen
    out = []
    candidates = [h for rel, h in links(text) if 'stylesheet' in rel]
    candidates += re.findall(r'@import\s+(?:url\()?["\']?([^"\')\s;]+)', text)
    for href in candidates:
        target = resolve(base, href)
        if not target or target in seen:
            continue
        seen.add(target)
        path = root / target
        if path.is_file() and target.endswith('.css'):
            sheet = read(path)
            out.append(sheet)
            out.extend(stylesheet_text(root, PurePosixPath(target), sheet, seen))
    return out


def features_of(text):
    low = strip_comments(text).lower()
    found = [name for name, pattern in FEATURES if name != 'quirks-mode' and re.search(pattern, low, re.M)]
    if not re.match(r'\s*(<\?xml[^>]*>\s*)?(<!--.*?-->\s*)*<!doctype', text, re.I | re.S):
        found.append('quirks-mode')
    return found


def classify(root):
    root = Path(root)
    files = sorted(p for p in (root / CSS_TABLES).rglob('*') if p.is_file())
    texts = {wpt_path(root, p): read(p) for p in files if p.suffix in TEST_EXT}
    targets = set()
    for path, text in texts.items():
        for rel, href in links(text):
            if 'match' in rel or 'mismatch' in rel:
                target = resolve(path, href)
                if target:
                    targets.add(target)
    tests = []
    for path, text in texts.items():
        parts = path.parts
        stem = path.name.rsplit('.', 1)[0]
        if (any(p in ('support', 'resources', 'tools', 'reference') for p in parts[:-1])
                or re.search(r'-(not)?ref$', stem) or re.search(r'-(not)?ref\.', path.name) or path.name.startswith('ref-')
                or str(path) in targets):
            continue
        refs = [{'relation': 'match' if 'match' in rel else 'mismatch', 'href': href, 'path': resolve(path, href)}
                for rel, href in links(text) if 'match' in rel or 'mismatch' in rel]
        scripts = [attr(SRC, tag) or '' for tag in SCRIPT.findall(text)]
        if 'crashtests' in parts[:-1] or stem.endswith('-crash') or stem.endswith('-crash.tentative'):
            kind = 'crashtest'
        elif re.search(r'-print(\.tentative)?$', stem) and refs:
            kind = 'print-reftest'
        elif any(s.split('?')[0].endswith('testharness.js') for s in scripts):
            kind = 'testharness'
        elif refs:
            kind = 'reftest'
        elif re.search(r'-manual(\.tentative)?$', stem):
            kind = 'manual'
        else:
            kind = 'other'
        row = {'test': str(path), 'kind': kind,
               'tentative': '.tentative.' in path.name or 'tentative' in parts[:-1]}
        if kind in ('reftest', 'print-reftest'):
            row['references'] = refs
            row['fuzzy'] = fuzzy(text)
            # Features of the test, its references and the stylesheets they link in the tree.
            feats = set(features_of('\n'.join([text, *stylesheet_text(root, path, text)])))
            for ref in refs:
                if ref['path'] and (root / ref['path']).is_file():
                    rtext = read(root / ref['path'])
                    rfeats = set(features_of('\n'.join([rtext, *stylesheet_text(root, PurePosixPath(ref['path']), rtext)])))
                    ref['features'] = sorted(rfeats)
                    # A reference in quirks mode does not make the test a quirks test.
                    feats |= rfeats - {'quirks-mode'}
                else:
                    ref['missing'] = True
            row['features'] = sorted(feats)
            row['testFeatures'] = features_of('\n'.join([text, *stylesheet_text(root, path, text)]))
            # A reference with no table: the picture is drawn some other way, so
            # equal pixels need the table laid out (or a coincidence of block layout).
            row['referenceUsesTable'] = any(set(r.get('features', [])) & {'table-elements', 'display-table'} for r in refs)
            row['references_missing'] = any(r.get('missing') for r in refs)
            blocking = sorted(feats & BLOCKING)
            table = bool(feats & {'table-elements', 'display-table'})
            if kind == 'print-reftest':
                tier = 'print'
            elif row['references_missing']:
                tier = 'missing-reference'
            elif not table:
                tier = 'no-table'
            elif blocking:
                tier = 'blocked'
            elif feats & {'border-collapse', 'caption', 'table-layout-fixed', 'percent-size', 'vertical-align',
                          'box-sizing', 'overflow', 'ahem', 'outline-shadow'}:
                tier = 'table-plus'
            else:
                tier = 'basic-table'
            row['tier'] = tier
            row['blocking'] = blocking
        tests.append(row)
    tests.sort(key=lambda r: r['test'])
    return tests


TIERS = {
    'basic-table': 'Table elements or display:table* with at most border-spacing, colspan/rowspan and col/colgroup; nothing in the blocking list',
    'table-plus': 'As basic-table, but also border-collapse, caption, table-layout:fixed, percentages, vertical-align, box-sizing, overflow, outline/box-shadow or Ahem text',
    'blocked': 'Uses a feature far from table layout (see BLOCKING)',
    'no-table': 'No table element and no display:table* found in test or reference',
    'print': 'A print reftest (paged media)',
    'missing-reference': 'A reference file is not in the vendored tree',
}


def summary(tests):
    kinds = collections.Counter(r['kind'] for r in tests)
    tentative = collections.Counter(r['kind'] for r in tests if r['tentative'])
    reftests = [r for r in tests if r['kind'] == 'reftest']
    tiers = collections.Counter(r['tier'] for r in reftests)
    feats = collections.Counter(f for r in reftests for f in r['features'])
    blockers = collections.Counter(f for r in reftests for f in r['blocking'])
    return {
        'tests': len(tests), 'kinds': dict(kinds), 'tentative': dict(tentative),
        'reftests': {'total': len(reftests), 'match': sum(all(x['relation'] == 'match' for x in r['references']) for r in reftests),
                     'withMismatch': sum(any(x['relation'] == 'mismatch' for x in r['references']) for r in reftests),
                     'withFuzzy': sum(bool(r['fuzzy']) for r in reftests),
                     'tiers': dict(tiers), 'tierMeaning': TIERS,
                     'basicTableTests': sorted(r['test'] for r in reftests if r['tier'] == 'basic-table'),
                     'features': dict(feats.most_common()), 'blockingFeatures': dict(blockers.most_common())},
    }


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--root', default=ROOT / 'third_party/testing/wpt-css-tables')
    p.add_argument('--output', default=HERE.with_name('wpt-tables-classes.json'))
    a = p.parse_args()
    tests = classify(a.root)
    value = {'format': 'factoidal-wpt-tables-classes-v1', 'root': 'third_party/testing/wpt-css-tables',
             'summary': summary(tests), 'tests': tests}
    Path(a.output).write_text(json.dumps(value, indent=1, ensure_ascii=False) + '\n')
    s = value['summary']
    print(f"wpt css-tables: {s['tests']} tests, {s['kinds']}; reftests by tier {s['reftests']['tiers']}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
