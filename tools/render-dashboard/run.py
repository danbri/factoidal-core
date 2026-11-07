#!/usr/bin/env python3
"""Measure the rendering and font suites, add the results to the history, and
write the dashboard page.

    tools/render-dashboard/run.py                run all suites
    tools/render-dashboard/run.py --only html-parser,svg-tiny-pixels
    tools/render-dashboard/run.py --list         show suites and exit
    tools/render-dashboard/run.py --page-only    write the page and exit

One record per suite and run goes to tools/render-dashboard/history.jsonl. The
file only grows. A suite that can not run writes a record with origin "not-run"
and the reason, and no counts. Rule of the scores:
https://github.com/danbri/factoidal/issues/1245

The engines must exist first and must match the source (the witness is checked):
    labs/demos/foafnaut/build-web-render.sh --native
    labs/demos/foafnaut/build-web-render.sh --wasm
    labs/demos/foafnaut/build-engines.sh

Inputs that are not in this repository are named by flags. Their defaults are
the paths on the development Mac. Run files go to --cache/runs/.
"""
import argparse, collections, hashlib, json, os, re, shutil, statistics, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LAB = ROOT / 'labs/demos/foafnaut'
HISTORY = Path(__file__).with_name('history.jsonl')
DEPMAP = Path.home() / 'working/sandbox/october/tpac/depmap'
NATIVE = LAB / '.build/web-render/web-render-native'
WITNESS = LAB / '.build/web-render/source-witness.json'
TINY_SHA = '2203d6f44178cbb3853bdc7abe865f4e7e42506727ecc9e34b408b6f33e2e718'
WPT_PIN = '70dae60789ef6220d9b4e60c92c5b2107b4e2b93'
UNDATED = 'tools/render-dashboard/font_coverage.py, third_party/unicode-18.0.0'
# Paths that do not change what the suites measure.
TOOL_PATHS = ('tools/render-dashboard/', 'tools/foafnaut-scoreboard.py', 'docs/web/hub/render-scores/',
              'docs/web/hub/index.md', 'docs/20261106-render-dashboard.md', 'tests/browser-wpt/README.md',
              'third_party/unicode-18.0.0/')
# A cause for a Tiny case that does not match, first found wins. The first frame
# is the only one drawn, so time and script come before any drawing cause.
TINY_CAUSES = [
    ('Needs animation or a later frame', ('element: animate', 'element: set', 'element in text: set', 'element: animation', 'element: discard')),
    ('Needs scripts or events', ('element: script', 'element: handler', 'foreign element: listener')),
    ('Needs media: image, audio or video', ('element: image', 'element: audio', 'element: video')),
    ('Needs textArea', ('element: textArea',)),
    ('Needs gradients or solidColor', ('element: linearGradient', 'element: radialGradient', 'element: solidColor')),
    ('Needs embedded SVG fonts', ('element: font$',)),
    ('Reference to another document removed', ('removed g: external', 'removed use: external')),
    ('Path over the point limit', ('removed g: path point',)),
    ('Stroke approximated', ('approximated: stroke',)),
    ('Text anchor dropped', ('attribute: g text-anchor',)),
]


# The corpus harness of 2 November (branch codex/svg-corpus-overnight) is older
# than the engine. These edits change no fixture, reference or limit.
CORPUS_PATCHES = [
    ('Serve engine-worker.mjs and engine-core.mjs: engine.mjs now runs Lean in a worker',
     "const webNames=['web-render/engine.mjs',", "const webNames=['web-render/engine.mjs','web-render/engine-worker.mjs','web-render/engine-core.mjs',"),
    ('The magenta control shader also reads the tiles binding, which the engine now has',
     "clamp(params.rows[0],vec4f(0.0),vec4f(1.0))*0.000001;", "clamp(params.rows[0],vec4f(0.0),vec4f(1.0))*0.000001+vec4f(f32(tiles[0])*0.0);"),
]


class NotRun(Exception):
    """The suite did not run. The text is the reason."""


def sha_file(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()


def plain_reason(text, limit=110):
    """One group name for texts that differ only in a number, a name in quotes or a path."""
    text = str(text or 'No reason given').strip().splitlines()[0] if str(text or '').strip() else 'No reason given'
    text = re.sub(r"https?://[^\s)]+", 'URL', text)
    text = re.sub(r"(/[\w.@+-]+){2,}", 'PATH', text)
    text = re.sub(r"'[^']{1,60}'|\"[^\"]{1,60}\"", 'NAME', text)
    text = re.sub(r'\bU\+[0-9A-Fa-f]+', 'U+N', text)
    text = re.sub(r'\b\d+(\.\d+)?\b', 'N', text)
    return text[:limit]


def groups_of(rows, key, name, top=16):
    """Rows grouped by reason, largest first, with up to 3 examples of each."""
    found = collections.defaultdict(list)
    for row in rows:
        found[key(row)].append(name(row))
    ranked = sorted(found.items(), key=lambda item: (-len(item[1]), item[0]))
    return [{'reason': reason, 'count': len(items), 'examples': sorted(items)[:3]} for reason, items in ranked[:top]]


class Run:
    def __init__(self, args):
        self.a = args
        self.commit = git('rev-parse', 'HEAD')
        self.stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
        self.dir = Path(args.cache) / 'runs' / f'{self.commit[:9]}-{self.stamp}'
        self.dir.mkdir(parents=True)
        self.env = {**os.environ, 'PATH': f'{Path(args.python).parent}:{os.environ["PATH"]}'}
        status = subprocess.check_output(['git', '-C', str(ROOT), 'status', '--short'], text=True)
        changed = [line[3:] for line in status.splitlines() if line.strip()]
        self.dirty = [path for path in changed if not path.startswith(TOOL_PATHS)]
        self.records = []

    def need(self, path, what):
        if not Path(path).exists():
            raise NotRun(f'{what} is not at {path}')
        return Path(path)

    def native(self):
        """The native engine, after a check that it is built from this source."""
        self.need(NATIVE, 'web-render-native')
        witness = json.loads(self.need(WITNESS, 'The source witness').read_text())
        stale = [name for name, digest in witness['files'].items()
                 if not (ROOT / name).exists() or sha_file(ROOT / name) != digest]
        if stale:
            raise NotRun(f'Engine is not built from this source: {len(stale)} files differ, first {stale[0]}')
        if witness.get('nativeSha256') != sha_file(NATIVE):
            raise NotRun('web-render-native differs from its source witness')
        return NATIVE

    def wasm(self):
        witness = json.loads(self.need(WITNESS, 'The source witness').read_text())
        for name in ['web-render.mjs', 'web-render.wasm']:
            path = LAB / '.build/web-render/engines' / name
            self.need(path, name)
            if witness['engines'].get(str(path.relative_to(ROOT))) != sha_file(path):
                raise NotRun(f'{name} differs from its source witness')
        self.native()

    def call(self, name, command, timeout, **options):
        """Run one tool. Its output goes to a log. A non-zero exit is normal: suites fail."""
        log = self.dir / f'{name}.log'
        started = time.time()
        with log.open('wb') as out:
            try:
                result = subprocess.run([str(part) for part in command], stdout=out, stderr=subprocess.STDOUT,
                                        timeout=timeout, env=self.env, **options)
            except subprocess.TimeoutExpired:
                raise NotRun(f'Runner went over the {timeout} s limit, see {log}')
        print(f'  {name}: exit {result.returncode} in {time.time() - started:.0f} s', flush=True)
        return result.returncode, log

    def add(self, suite, title, runner, pin, denominator, counts, groups=None, **extra):
        self.records.append({'format': 'factoidal-render-score-v1', 'suite': suite, 'title': title, 'origin': 'measured',
                             'runner': runner, 'input': pin, 'denominator': denominator, 'commit': self.commit,
                             'date': time.strftime('%Y-%m-%d', time.gmtime()), 'counts': counts,
                             'groups': groups or [], 'host': 'Apple M1, macOS', **extra,
                             **({'dirty': self.dirty} if self.dirty else {})})

    # Suites. Each one calls add() once for each score it gives.

    def html_parser(self):
        out = self.dir / 'parser'
        self.need(ROOT / 'formal/lean4/.lake/build/lib/lean', 'The Lean module cache')
        self.call('parser', [sys.executable, 'tests/browser-wpt/parser-probe.py', '--fixtures', 'third_party/testing',
                             '--output', out, '--timeout', 900], 1800, cwd=ROOT)
        if not (out / 'parser-probe.json').exists():
            raise NotRun(f'parser-probe.py wrote no report, see {self.dir}/parser.log')
        pin = {'name': 'html5lib and WPT parser fixtures', 'pin': 'tests/browser-wpt/parser-fixtures.json',
               'sha256': sha_file(ROOT / 'tests/browser-wpt/parser-fixtures.json')}
        runner = 'tests/browser-wpt/parser-probe.py'

        def score(suite, title, log, pattern):
            text = (out / log).read_text(errors='replace')
            total = re.search(pattern, text, re.M)
            if not total:
                raise NotRun(f'No summary line in {log}')
            passed, failed, of = (int(total[n]) for n in (1, 2, 3))
            files = re.findall(r'^(\S+\.(?:dat|test)): (\d+) pass, (\d+) fail', text, re.M)
            ranked = sorted(((int(f), n) for n, _, f in files if int(f)), reverse=True)
            self.add(suite, title, runner, pin, of, {'pass': passed, 'fail': failed},
                     [{'reason': f'Failures in {name}', 'count': n, 'examples': []} for n, name in ranked[:12]])

        score('html-tree', 'html5lib tree construction', 'tree.log', r'^tree construction: (\d+) pass, (\d+) fail \(out of (\d+)\)')
        score('html-dom-tree', 'html5lib tree construction through the DOM arena', 'dom-tree.log',
              r'^tree construction through the DOM arena: (\d+) pass, (\d+) fail \(out of (\d+)\)')
        score('html-tokenizer', 'html5lib tokenizer (tokens and error codes)', 'tokenizer.log',
              r'^tokenizer \(tokens and error codes\): (\d+) pass, (\d+) fail \(out of (\d+)\)')
        audit = json.loads((out / 'error-counts-audit.json').read_text())['summary']
        buckets = sorted(audit['buckets'].items(), key=lambda item: -item[1])
        self.add('html-parse-errors', 'Parse-error counts against the fixtures', 'tests/browser-wpt/parser-error-audit.py', pin,
                 audit['documents'], {'agree': audit['equal'], 'differ': audit['different']},
                 [{'reason': name.replace('_', ' '), 'count': n, 'examples': []} for name, n in buckets])

    def svg_tiny_admission(self):
        archive = self.tiny_archive()
        self.need(LAB / '.build/web-render/olean', 'The lab Lean modules')
        self.native()
        out = self.dir / 'tiny-admission'
        self.call('tiny-admission', [sys.executable, 'tests/browser-wpt/svg-tiny-admission.py', '--archive', archive,
                                     '--output', out, '--timeout', 900], 1200, cwd=ROOT)
        path = out / 'svg-tiny-admission.json'
        if not path.exists():
            raise NotRun(f'svg-tiny-admission.py wrote no report, see {self.dir}/tiny-admission.log')
        report = json.loads(path.read_text())
        rows = [row for row in report['cases'] if row['admission'] != 'ADMITTED']
        counts = {k.lower(): v for k, v in report['allCounts'].items()}
        self.add('svg-tiny-admission', 'W3C SVG Tiny 1.2, strict Lean SVG compiler admission', 'tests/browser-wpt/svg-tiny-admission.py',
                 {'name': 'W3C SVG Tiny 1.2 archive', 'pin': TINY_SHA}, len(report['cases']), counts,
                 groups_of(rows, lambda r: plain_reason(r['error']), lambda r: r['file']),
                 notes='Admission only. Visual conformance is NOT_RUN here.')

    def tiny_archive(self):
        archive = self.need(self.a.tiny_archive, 'The W3C SVG Tiny archive')
        if sha_file(archive) != TINY_SHA:
            raise NotRun('The W3C SVG Tiny archive has a different SHA256')
        return archive

    def svg_tiny_pixels(self):
        archive, native = self.tiny_archive(), self.native()
        if shutil.which('deno') is None:
            raise NotRun('deno is not installed')
        out = self.dir / 'tiny-pixels'
        self.call('tiny-pixels', [self.a.python, 'tests/browser-wpt/svg-tiny-pixels.py', '--archive', archive, '--native', native,
                                  '--output', out], 1800, cwd=ROOT)
        path = out / 'svg-tiny-pixels.json'
        if not path.exists():
            raise NotRun(f'svg-tiny-pixels.py wrote no report, see {self.dir}/tiny-pixels.log')
        report = json.loads(path.read_text())
        self.add('svg-tiny-pixels', 'W3C SVG Tiny 1.2, WebGPU pixels against W3C images (our bands, not a W3C verdict)',
                 'tests/browser-wpt/svg-tiny-pixels.py', {'name': 'W3C SVG Tiny 1.2 archive', 'pin': TINY_SHA}, report['total'],
                 {k.lower(): v for k, v in report['counts'].items()}, tiny_groups(report['cases']),
                 blankControl=report['blankControlCounts'], exact=report['exact'], gpu=report['gpu'])

    def wpt_images_wasm(self):
        corpus = self.need(self.a.svg_wpt, 'The pinned WPT SVG corpus')
        self.wasm()
        for name in ['svg-engine.wasm', 'render-plan.wasm']:
            self.need(LAB / '.build/engines' / name, name)
        self.need(self.a.chrome, 'Chrome')
        self.need(self.a.playwright, 'playwright-core')
        out = self.dir / 'wpt-images'
        harness = self.patched_corpus(corpus)
        self.call('wpt-images', [self.a.node, harness / 'run.mjs', '--output', out, '--browser', self.a.chrome,
                                 '--playwright', self.a.playwright, '--svg-lab', LAB, '--html-lab', LAB,
                                 '--html-witness', WITNESS, '--controls'], 5400)
        path = out / 'capture/report.json'
        if not path.exists():
            raise NotRun(f'run.mjs wrote no report, see {self.dir}/wpt-images.log')
        report = json.loads(path.read_text())
        rows = report['results']
        bad = [row for row in rows if row['status'] not in ('match', 'negative-only')]
        counts = dict(report['counts'])
        self.add('wpt-images-wasm', 'WPT SVG and HTML image relations, browser WASM and WebGPU', f'{corpus.name}/run.mjs (corpus, branch codex/svg-corpus-overnight)',
                 {'name': 'WPT SVG subtree', 'pin': WPT_PIN}, report['total'], counts,
                 groups_of(bad, wpt_reason, lambda r: r['test'], top=20),
                 static=report['static'], matches=sorted(row['test'] for row in rows if row['status'] == 'match'),
                 controls=report.get('controls', {}).get('counts'), harnessPatches=[note for note, _, _ in CORPUS_PATCHES],
                 notes='The harness of 2 November is patched at run time for the current engine: see harnessPatches. Fixtures and limits are unchanged.')
        self.oracle = out / 'capture'

    def patched_corpus(self, corpus):
        """A copy of the corpus scripts in the run directory, with CORPUS_PATCHES. Data are links."""
        here = self.dir / 'harness' / corpus.name
        here.mkdir(parents=True)
        (here.parent / 'svg').symlink_to(corpus.parent / 'svg')
        for item in corpus.iterdir():
            if item.suffix in ('.mjs', '.py'):
                shutil.copy(item, here)
            elif item.name != '__pycache__':
                (here / item.name).symlink_to(item)
        text = (here / 'capture.mjs').read_text()
        for _, old, new in CORPUS_PATCHES:
            assert text.count(old) == 1, 'The corpus harness changed: ' + old
            text = text.replace(old, new)
        (here / 'capture.mjs').write_text(text)
        return here

    def wpt_images_native(self):
        corpus = self.need(self.a.svg_wpt, 'The pinned WPT SVG corpus')
        native = self.native()
        oracle = getattr(self, 'oracle', None) or self.a.oracle
        if not oracle or not (Path(oracle) / 'capture.json').exists():
            raise NotRun('No capture of the browser images: the wpt-images-wasm suite makes it, or give --oracle')
        out = self.dir / 'wpt-native'
        self.call('wpt-native', [self.a.python, 'tests/browser-wpt/native-reftests.py', '--corpus', corpus, '--oracle', oracle,
                                 '--native', native, '--output', out, '--timeout', 5], 5400, cwd=ROOT)
        path = out / 'native-reftests.json'
        if not path.exists():
            raise NotRun(f'native-reftests.py wrote no report, see {self.dir}/wpt-native.log')
        report = json.loads(path.read_text())
        bad = [row for row in report['cases'] if row['status'] != 'PASS']
        self.add('wpt-images-native', 'WPT HTML image relations, native Lean CPU sampler', 'tests/browser-wpt/native-reftests.py',
                 {'name': 'WPT SVG subtree, HTML relations', 'pin': WPT_PIN}, len(report['cases']),
                 {k.lower(): v for k, v in report['counts'].items()},
                 groups_of(bad, lambda r: r['status'] + ': ' + plain_reason(r.get('reason') or ('Pixels differ' if r['status'] == 'FAIL' else '')),
                           lambda r: r['test']))

    def wpt_scripts(self):
        corpus, native = self.need(self.a.svg_wpt, 'The pinned WPT SVG corpus'), self.native()
        self.wasm()
        self.need(LAB / '.build/script-engine/qjs-wasi-reactor.wasm', 'The QuickJS reactor')
        out = self.dir / 'wpt-scripts'
        self.call('wpt-scripts', [self.a.node, 'tests/browser-wpt/quickjs-probe.mjs', '--corpus', corpus, '--native', native,
                                  '--output', out], 3600, cwd=ROOT)
        path = out / 'quickjs-wpt.json'
        if not path.exists():
            raise NotRun(f'quickjs-probe.mjs wrote no report, see {self.dir}/wpt-scripts.log')
        report = json.loads(path.read_text())
        bad = [row for row in report['cases'] if row['status'] != 'PASS']

        def reason(row):
            first = next((t for t in row.get('results', []) if t.get('status')), {})
            return row['status'] + ': ' + plain_reason(row.get('scriptError') or row.get('reason') or first.get('message') or 'See the assertions')
        self.add('wpt-scripts', 'WPT scripted documents (synchronous QuickJS probe)', 'tests/browser-wpt/quickjs-probe.mjs',
                 {'name': 'WPT SVG subtree, script tests', 'pin': WPT_PIN}, len(report['cases']),
                 {k.lower(): v for k, v in report['counts'].items()},
                 groups_of(bad, reason, lambda r: r.get('path') or r.get('test') or '?'), assertions=report['assertions'])

    def shaper(self):
        tool = ROOT / 'formal/lean4/.lake/build/bin/l4font-shape'
        adapter = LAB / '.build/font-shape'
        self.need(tool, 'l4font-shape (lake build l4font-shape in formal/lean4)')
        self.need(adapter, 'font-shape (labs/demos/foafnaut/build-font-adapter.sh)')
        return tool, adapter

    def harfbuzz(self):
        tool, adapter = self.shaper()
        data = self.need(Path(self.a.harfbuzz) / 'test/shape/data', 'The HarfBuzz test data')
        version = subprocess.check_output(['hb-shape', '--version'], text=True).split()[2]
        if not version.startswith('15.0.0'):
            raise NotRun(f'hb-shape is {version}, the suite is pinned to 15.0.0')
        out = self.dir / 'harfbuzz.json'
        self.call('harfbuzz', [sys.executable, LAB / 'tools/run-harfbuzz-suite.py', tool, adapter, data, out], 7200)
        if not out.exists():
            raise NotRun(f'run-harfbuzz-suite.py wrote no report, see {self.dir}/harfbuzz.log')
        report = json.loads(out.read_text())
        found = report['summary']['results']
        counts = {'pass': found.get('pass', 0), 'fail': found.get('fail', 0), 'refused': found.get('lean refused', 0),
                  'not-applicable': found.get('not applicable', 0), 'oracle-mismatch': found.get('oracle mismatch', 0)}
        rows = [{'key': key, 'status': status, 'why': why, 'line': line} for key, status, why, line in report['rows']]
        self.add('harfbuzz', 'HarfBuzz 15.0.0 shaping suite', 'labs/demos/foafnaut/tools/run-harfbuzz-suite.py',
                 {'name': 'HarfBuzz test/shape/data', 'pin': '15.0.0'}, counts['pass'] + counts['fail'] + counts['refused'], counts,
                 groups_of(rows, lambda r: 'REFUSED: ' + plain_reason(r['why']) if r['status'] == 'REFUSED' else 'FAIL in ' + r['key'],
                           lambda r: r['line'].split(';')[0].split('/')[-1]),
                 denominatorNote='Applicable tests only; not-applicable and oracle-mismatch rows are outside it.')

    def font_records(self):
        tool, adapter = self.shaper()
        fonts = dict(item.split('=', 1) for item in self.a.record_font)
        for name, path in fonts.items():
            self.need(path, f'Font {name}')
        code, log = self.call('font-records', [sys.executable, LAB / 'tools/check-lean-shaper.py', tool, adapter,
                                               *[f'{name}={path}' for name, path in fonts.items()]], 600)
        text = log.read_text(errors='replace')
        total = re.search(r'complete records: (\d+) same, (\d+) different, (\d+) refused by Lean \(out of (\d+)\)', text)
        if not total:
            raise NotRun(f'check-lean-shaper.py gave no summary, see {log}')
        problems = re.findall(r'^(\S+)\s+.*: (DIFF|LEAN REFUSED)', text, re.M)
        self.add('font-records', 'Font records against native HarfBuzz', 'labs/demos/foafnaut/tools/check-lean-shaper.py',
                 {'name': 'Ahem, Arial, Lato, Liberation Sans Bold; 14 texts each',
                  'pin': {name: sha_file(path) for name, path in fonts.items()}}, int(total[4]),
                 {'same': int(total[1]), 'different': int(total[2]), 'refused': int(total[3])},
                 [{'reason': f'{kind} in {font}', 'count': n, 'examples': []}
                  for (font, kind), n in collections.Counter(problems).most_common(12)])

    def font_coverage(self):
        tool = Path(__file__).with_name('font_coverage.py')
        sets = [('web-render-5x7-ascii', ['--bitmap-source'], False)] + \
               [(name, files, True) for name, files in (item.split('=', 1) for item in self.a.reference_fonts)]
        for name, files, reference in sets:
            arguments = files if not reference else files.split(',')
            if reference and not all(Path(item.partition('#')[0]).exists() for item in arguments):
                continue
            log = self.dir / f'fonts-{name}.json'
            with log.open('w') as out:
                subprocess.run([sys.executable, tool, '--set', name, *arguments], stdout=out, check=True, timeout=1200)
            value = json.loads(log.read_text())
            counts = value['counts']
            self.add('font-coverage/' + name, ('Reference font set, not used by the browser: ' if reference else 'Browser font: ') + name,
                     'tools/render-dashboard/font_coverage.py', {'name': 'Unicode 18.0.0 and font set ' + name, 'pin': value['files']},
                     value['denominators']['characters'], counts, value['largestMissingScripts'],
                     denominators=value['denominators'], scriptsWithGlyphs=value['scriptsWithGlyphs'], reference=reference)

    def old_web(self):
        self.wasm()
        runtime = LAB / '.build/native-html/runtime'
        runtime.mkdir(parents=True, exist_ok=True)
        for name in ['web-render.mjs', 'web-render.wasm']:
            shutil.copy(LAB / '.build/web-render/engines' / name, runtime / name)
        width, height = 1000, 800
        code, log = self.call('old-web', ['deno', 'run', '--no-check', '--no-config', '--no-npm', '--node-modules-dir=none',
                                          '--unstable-webgpu', '--unstable-ffi', '--allow-read', '--allow-write', '--allow-net', '--allow-env',
                                          Path(__file__).with_name('old_web.ts'), width, height], 1200, cwd=ROOT)
        last = log.read_text(errors='replace').strip().splitlines()[-1:]
        if code or not last or not last[0].startswith('{'):
            raise NotRun(f'old_web.ts gave no result, see {log}')
        value = json.loads(last[0])
        counts = collections.Counter(row['status'].lower() for row in value['cases'])
        bad = [row for row in value['cases'] if row['status'] != 'RENDERED']
        tree = git('rev-parse', 'HEAD:third_party/testing/old-web')
        self.add('old-web', 'Old web mirror pages, browser document path at 1000x800', 'tools/render-dashboard/old_web.ts',
                 {'name': 'third_party/testing/old-web', 'pin': tree}, value['total'], dict(counts),
                 groups_of(bad, lambda r: plain_reason(r.get('reason')), lambda r: r['page']),
                 notes='Rendered means the page gave a frame with data. It does not say the frame is correct.')

    def wpt_tables(self):
        self.wasm()
        runtime = LAB / '.build/native-html/runtime'
        runtime.mkdir(parents=True, exist_ok=True)
        for name in ['web-render.mjs', 'web-render.wasm']:
            shutil.copy(LAB / '.build/web-render/engines' / name, runtime / name)
        tree = ROOT / 'third_party/testing/wpt-css-tables'
        self.need(tree / 'SHA256SUMS', 'The vendored WPT css-tables tree')
        classes = self.dir / 'wpt-tables-classes.json'
        self.call('wpt-tables-classes', [sys.executable, Path(__file__).with_name('wpt_tables_classify.py'), '--root', tree,
                                         '--output', classes], 120, cwd=ROOT)
        out = self.dir / 'wpt-tables.json'
        self.call('wpt-tables', ['deno', 'run', '--no-check', '--no-config', '--no-npm', '--node-modules-dir=none',
                                 '--unstable-webgpu', '--unstable-ffi', '--allow-read', '--allow-write', '--allow-net=127.0.0.1',
                                 '--allow-ffi', '--allow-env', Path(__file__).with_name('wpt_tables.ts'),
                                 '--classes', classes, '--output', out], 1800, cwd=ROOT)
        if not out.exists():
            raise NotRun(f'wpt_tables.ts wrote no report, see {self.dir}/wpt-tables.log')
        report = json.loads(out.read_text())
        rows = [row for row in report['cases'] if row['kind'] == 'reftest']
        bad = [row for row in rows if row['status'] != 'pass']
        counts = dict(report['reftests']['counts'])
        self.add('wpt-tables', 'WPT css/css-tables reftests, browser document path and WebGPU pixels at 800x600',
                 'tools/render-dashboard/wpt_tables.ts', {'name': 'WPT css/css-tables', 'pin': report['input']['commit']},
                 report['reftests']['total'], counts,
                 groups_of(bad, lambda r: r['status'] + ': ' + plain_reason(r.get('reason') or ('Pixels differ in ' + r['test'].rsplit('/', 1)[0])),
                           lambda r: r['test'], top=20),
                 uniformPasses=report['reftests']['uniformPasses'], brokenReferencePasses=report['reftests']['brokenReferencePasses'],
                 passes=sorted(row['test'] for row in rows if row['status'] == 'pass'),
                 reachable=report['reftests'].get('reachable'), crashtests=report.get('crashtests'),
                 failingByDroppedProperty=report.get('failingByDroppedProperty'),
                 notes='A pass is equal pixels with the reference. Some passes are coincidences; uniformPasses and '
                       'brokenReferencePasses count the weakest. Reachable reftests are those the host does not refuse '
                       '(scripts). Crash tests pass when Lean lays them out without an error.')

    def demo_pages(self):
        native = self.native()
        code, log = self.call('demo-pages', [sys.executable, 'tools/check-demo-pages.py', native], 600, cwd=ROOT)
        lines = re.findall(r'demo pages: (\d+) rendered, (\d+) expected refusals, (\d+) failed \(out of (\d+)\)', log.read_text(errors='replace'))
        if not lines:
            raise NotRun(f'check-demo-pages.py gave no summary, see {log}')
        rendered, refused, failed, total = map(int, lines[-1])
        self.add('demo-pages', 'Demo pages', 'tools/check-demo-pages.py', {'name': 'labs/demos/foafnaut/pages', 'pin': git('rev-parse', 'HEAD:labs/demos/foafnaut/pages')},
                 total, {'rendered': rendered, 'expected-refusal': refused, 'fail': failed})

    def lab_suite(self):
        self.wasm()
        self.need(LAB / '.build/engines/svg-engine.wasm', 'The lab engines (build-engines.sh)')
        code, log = self.call('lab-suite', ['bash', LAB / 'test.sh', '--skip-build'], 1800, cwd=ROOT)
        text = re.sub(r'\x1b\[[0-9;]*m', '', log.read_text(errors='replace'))
        rows = re.findall(r'^(ok|FAILED) \| (\d+) passed \| (\d+) failed', text, re.M)
        if not rows:
            raise NotRun(f'test.sh stopped before the Deno summary (exit {code}), see {log}')
        passed, failed = sum(int(row[1]) for row in rows), sum(int(row[2]) for row in rows)
        names = re.findall(r'^(.+?) \.\.\. FAILED', text, re.M)
        if code and not failed:
            raise NotRun(f'test.sh stopped with exit {code} and no failed test, see {log}')
        self.add('lab-suite', 'Lab suite, Deno tests', 'labs/demos/foafnaut/test.sh --skip-build', {'name': 'labs/demos/foafnaut tests', 'pin': self.commit},
                 passed + failed, {'pass': passed, 'fail': failed},
                 [{'reason': plain_reason(name), 'count': 1, 'examples': []} for name in sorted(set(names))[:12]])


def wpt_reason(row):
    """A mismatch has no text, so its group is the folder of the test."""
    if row['status'] == 'mismatch':
        return 'mismatch: pixels differ in ' + row['test'].rsplit('/', 1)[0]
    text = re.sub(r'^(Error: )?(page\.evaluate: )?(Error: )?(SVG profile: )?', '', str(row.get('reason') or row.get('detail') or ''))
    return row['status'] + ': ' + plain_reason(text)


def tiny_groups(cases):
    """Every case that is not MATCH in exactly one group: the first cause found."""
    def cause(row):
        if row['status'] not in ('MISMATCH', 'CLOSE', 'DRAW'):
            return row['status'] + ': ' + plain_reason(row.get('reason'))
        dropped = row.get('dropped', [])
        for name, prefixes in TINY_CAUSES:
            # A name that ends in $ is exact: every test drops font-face.
            if any(line == prefix[:-1] if prefix.endswith('$') else line.startswith(prefix) for line in dropped for prefix in prefixes):
                return row['status'] + ': ' + name
        return row['status'] + ': Nothing dropped, pixels differ'
    return groups_of([row for row in cases if row['status'] != 'MATCH'], cause, lambda r: r['file'])


SUITES = {'html-parser': Run.html_parser, 'svg-tiny-admission': Run.svg_tiny_admission, 'svg-tiny-pixels': Run.svg_tiny_pixels,
          'wpt-images-wasm': Run.wpt_images_wasm, 'wpt-images-native': Run.wpt_images_native, 'wpt-scripts': Run.wpt_scripts,
          'harfbuzz': Run.harfbuzz, 'font-records': Run.font_records, 'font-coverage': Run.font_coverage, 'old-web': Run.old_web,
          'wpt-tables': Run.wpt_tables, 'demo-pages': Run.demo_pages, 'lab-suite': Run.lab_suite}
# Suites of the OKRs this command does not run, and why. They appear as not run.
NOT_HERE = {'frame-time': 'Needs the macOS app opened in a window session; tools/native-frame-report.py reads its trace',
            'tile-equivalence': 'KR 2.2 has no runner yet',
            'real-pages': 'KR 5.3 has no pinned list of 20 pages yet',
            'browser-checks': 'KR 4.2 checks in web-render/ are not in this command yet; they need Chrome with WebGPU'}


def not_run_record(suite, commit, reason):
    return {'format': 'factoidal-render-score-v1', 'suite': suite, 'origin': 'not-run', 'commit': commit,
            'date': time.strftime('%Y-%m-%d', time.gmtime()), 'reason': reason}


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--only', help='comma-separated suite names')
    p.add_argument('--list', action='store_true')
    p.add_argument('--page-only', action='store_true')
    p.add_argument('--allow-dirty', action='store_true', help='measure source with changes; the record names them')
    p.add_argument('--cache', default=DEPMAP / 'cache/render-metrics')
    p.add_argument('--python', default=DEPMAP / 'cache/svg-tiny/venv/bin/python', help='Python with NumPy and Pillow')
    p.add_argument('--node', default='/opt/homebrew/opt/node@22/bin/node')
    p.add_argument('--svg-wpt', default=DEPMAP / 'source/factoidal-svg-corpus-overnight/tests/external/svg-wpt')
    p.add_argument('--oracle', help='directory of an earlier capture, for wpt-images-native alone')
    p.add_argument('--tiny-archive', default=DEPMAP / 'cache/svg-tiny/W3C_SVG_12_TinyTestSuite.tar.gz')
    p.add_argument('--harfbuzz', default=DEPMAP / 'cache/render-metrics/harfbuzz-15.0.0', help='HarfBuzz 15.0.0 source tree')
    p.add_argument('--chrome', default='/Applications/Google Chrome.app/Contents/MacOS/Google Chrome')
    p.add_argument('--playwright', default=DEPMAP / 'cache/browser-check/node_modules/playwright-core/index.mjs')
    p.add_argument('--record-font', action='append', default=[
        f'Ahem={DEPMAP}/source/factoidal-svg-corpus-overnight/tests/external/svg-wpt/upstream/fonts/Ahem.ttf',
        'Arial=/System/Library/Fonts/Supplemental/Arial.ttf',
        'Lato=/System/Library/Frameworks/Ruby.framework/Versions/2.6/usr/lib/ruby/2.6.0/rdoc/generator/template/darkfish/fonts/Lato-Regular.ttf',
        f'LiberationSansBold={Path.home()}/working/foafos-core-032/node_modules/pdfjs-dist/standard_fonts/LiberationSans-Bold.ttf'])
    p.add_argument('--reference-fonts', action='append', default=[
        'macos-arial=/System/Library/Fonts/Supplemental/Arial.ttf',
        'macos-apple-color-emoji=/System/Library/Fonts/Apple Color Emoji.ttc'],
        help='NAME=FILE[,FILE...]: a set to compare with, not used by the browser')
    a = p.parse_args()
    if a.list:
        print('\n'.join(SUITES))
        return 0
    if not a.page_only:
        selected = a.only.split(',') if a.only else list(SUITES)
        unknown = [name for name in selected if name not in SUITES]
        if unknown:
            raise SystemExit(f'Unknown suite: {unknown[0]}')
        run = Run(a)
        if run.dirty and not a.allow_dirty:
            raise SystemExit('Source has changes, so the commit would not name what ran:\n  ' + '\n  '.join(run.dirty))
        print(f'Measuring {run.commit[:9]}, run files in {run.dir}', flush=True)
        for name in selected:
            before = len(run.records)
            try:
                SUITES[name](run)
            except NotRun as reason:
                print(f'NOT RUN {name}: {reason}', flush=True)
                run.records.append(not_run_record(name, run.commit, str(reason)))
            with HISTORY.open('a') as out:
                for record in run.records[before:]:
                    out.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + '\n')
                    if record['origin'] == 'measured':
                        print(f"  {record['suite']}: {record['counts']} (out of {record['denominator']})", flush=True)
        if not a.only:
            with HISTORY.open('a') as out:
                for name, reason in NOT_HERE.items():
                    out.write(json.dumps(not_run_record(name, run.commit, reason), sort_keys=True) + '\n')
    subprocess.run([sys.executable, Path(__file__).with_name('page.py')], check=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
