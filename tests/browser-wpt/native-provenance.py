#!/usr/bin/env python3
"""Audit an existing native source witness and a real pixel-producing process.

This is reproducible provenance evidence, not binary verification or a proof
that no code could hide a statically linked implementation.
"""
import argparse, hashlib, json, re, subprocess
from pathlib import Path

p = argparse.ArgumentParser()
for name in ['native', 'witness', 'input', 'output']:
    p.add_argument('--' + name, required=True)
a = p.parse_args()
root = Path(__file__).resolve().parents[2]
sha = lambda b: hashlib.sha256(b).hexdigest()
native, witness, source = map(lambda x: Path(x).resolve(), [a.native, a.witness, a.input])
out = Path(a.output).resolve(); out.mkdir(parents=True, exist_ok=True)
w = json.loads(witness.read_text())
report = {'format': 'factoidal-native-provenance-v1', 'native': str(native),
          'nativeSha256': sha(native.read_bytes()), 'witnessSha256': sha(witness.read_bytes()),
          'sourceCommit': w['commit'], 'inputSha256': sha(source.read_bytes()),
          'runnerSha256': sha(Path(__file__).read_bytes()), 'files': []}
assert report['nativeSha256'] == w['nativeSha256'], 'Binary does not match witness'
assert w['nativeProducedAfterCurrentC'], 'Witness identifies an older native binary'
for category in ['files', 'generatedC']:
    for path, expected in w[category].items():
        actual = sha((root / path).read_bytes())
        report['files'].append({'path': path, 'sha256': actual, 'category': category})
        assert actual == expected, 'Source witness mismatch: ' + path
linked = subprocess.run(['/usr/bin/otool', '-L', str(native)], capture_output=True, check=True, timeout=10)
result = subprocess.run([str(native), str(source), '800', '600', '--pixels'],
                        env={'PATH': '/nonexistent', 'DYLD_PRINT_LIBRARIES': '1'},
                        capture_output=True, check=True, timeout=10)
pixels = json.loads(result.stdout)
assert pixels['width'] == 800 and pixels['height'] == 600 and len(pixels['pixels']) == 1440000
assert len(set(pixels['pixels'])) > 1, 'Unexpected blank monochrome evidence'
report.update(linkedLibraries=linked.stdout.decode(), loadedLibraries=result.stderr.decode(),
              pixelOutputSha256=sha(result.stdout), pixelCount=480000)
report['browserLibraryMarkers'] = re.findall(r'(?i)webkit|javascriptcore|chromium|blink|gecko|firefox', report['linkedLibraries'] + report['loadedLibraries'])
report['limits'] = 'Source/C/binary hash witness and dyld observations; no independent reproducible native rebuild or formal binary proof. Cached browser expectations are separate from native image production.'
assert sha(native.read_bytes()) == report['nativeSha256'], 'Native changed during audit'
(out / 'native-provenance.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'checkedFiles': len(report['files']), 'pixelCount': report['pixelCount'], 'browserLibraryMarkers': report['browserLibraryMarkers']}))
assert not report['browserLibraryMarkers'], 'Unexpected browser library marker'
