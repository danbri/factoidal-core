#!/usr/bin/env python3
"""Run original parser fixtures through Lean, preserving all failures.

Reuses an explicitly identified read-only Lean module cache. Compiles only the
harness and code-point adapter modules into the output directory; never runs a Lake build.
"""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

p = argparse.ArgumentParser()
p.add_argument('--fixtures', required=True, help='third_party/testing directory')
p.add_argument('--output', required=True)
p.add_argument('--lean', default='lean')
p.add_argument('--timeout', type=int, default=120)
a = p.parse_args()
root = Path(__file__).resolve().parents[2]
formal = root / 'formal/lean4'
cache = formal / '.lake/build/lib/lean'
fixtures = Path(a.fixtures).resolve()
pins_path = Path(__file__).with_name('parser-fixtures.json')
pins = json.loads(pins_path.read_text())
groups = {}
for group in pins['sets']:
    directory = fixtures / group['directory']
    expected = {item['name'] for item in group['files']}
    suffix = '*.dat' if group['kind'] == 'tree' else '*.test'
    assert {p.name for p in directory.glob(suffix)} == expected, 'Fixture set differs from pinned inventory'
    for item in group['files']:
        data = (directory / item['name']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\x00' + data).hexdigest()
        assert blob == item['gitBlob'], 'Upstream fixture bytes changed: ' + item['name']
    groups[group['kind']] = sorted(directory / name for name in expected)
out = Path(a.output).resolve()
out.mkdir(parents=True, exist_ok=True)
overlay = out / 'lean'
if overlay.exists():
    raise SystemExit('Use a fresh output directory; existing cache is never overwritten')
overlay.mkdir()
report = {'format': 'factoidal-wpt-parser-v1', 'scope': 'Lean interpreter and cached production modules; fresh harness; no exclusions or expected-failure mask',
          'toolchain': (formal / 'lean-toolchain').read_text().strip(),
          'runnerSha256': sha(Path(__file__)), 'fixturePinsSha256': sha(pins_path),
          'fixturePins': pins, 'cache': [], 'fixtures': [], 'runs': []}
for source in sorted(cache.rglob('*')):
    if not source.is_file():
        continue
    target = overlay / source.relative_to(cache)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.symlink_to(source)
    report['cache'].append({'path': str(source), 'sha256': sha(source)})
env = {**os.environ, 'LEAN_PATH': str(overlay)}
modules = ['Harness/DomDump', 'L4Factoidal/HTML/XmlAgreement',
           'L4Factoidal/HTML/CodePointTokenizer', 'L4Factoidal/HTML/CodePointTokenizerTests',
           'Harness/Html5lib']
report['harnessSources'] = {}
for module in modules:
    target = overlay / (module + '.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.is_symlink():
        target.unlink()  # Only our overlay link; never the shared target.
    source = formal / (module + '.lean')
    report['harnessSources'][str(source)] = sha(source)
    subprocess.run([a.lean, '-o', str(target), str(source)], cwd=formal,
                   env=env, check=True, timeout=a.timeout)
wrapper = out / 'RunHtml5lib.lean'
wrapper.write_text('import Harness.Html5lib\n')
tree, tokens = groups['tree'], groups['tokenizer']
for source in tree + tokens:
    report['fixtures'].append({'path': str(source), 'sha256': sha(source)})
for name in ['wpt-html-parsing-PROVENANCE.md', 'html5lib-tests-PROVENANCE.md']:
    report[name] = (fixtures / name).read_text()
for mode, sources in [('tree', tree), ('dom-tree', tree), ('tokenizer', tokens), ('error-counts', tree)]:
    command = [a.lean, '--run', str(wrapper), mode, *map(str, sources)]
    result = subprocess.run(command, cwd=formal, env=env, capture_output=True, timeout=a.timeout)
    log = out / (mode + ('.jsonl' if mode == 'error-counts' else '.log'))
    log.write_bytes(result.stdout if mode == 'error-counts' else result.stdout + result.stderr)
    report['runs'].append({'mode': mode, 'command': command, 'exit': result.returncode,
                          'log': str(log), 'logSha256': sha(log)})
    if mode == 'error-counts':
        (out / 'error-counts.stderr.log').write_bytes(result.stderr)
        if result.returncode != 0:
            raise SystemExit('Diagnostic run failed: ' + str(log))
        audit_runner = Path(__file__).with_name('parser-error-audit.py')
        audit_report = out / 'error-counts-audit.json'
        subprocess.run([sys.executable, str(audit_runner), str(log), '--output', str(audit_report)], check=True)
        report['diagnosticAudit'] = {'path': str(audit_report), 'sha256': sha(audit_report),
                                     'runnerSha256': sha(audit_runner)}
    else:
        print(result.stdout.decode(errors='replace').splitlines()[-2:], flush=True)
for item in report['cache'] + report['fixtures']:
    if sha(Path(item['path'])) != item['sha256']:
        raise SystemExit('Input changed during run: ' + item['path'])
for path, expected in report['harnessSources'].items():
    if sha(Path(path)) != expected:
        raise SystemExit('Harness source changed during run: ' + path)
(out / 'parser-probe.json').write_text(json.dumps(report, indent=2) + '\n')
sys.exit(0 if all(x['exit'] == 0 for x in report['runs']) else 1)
