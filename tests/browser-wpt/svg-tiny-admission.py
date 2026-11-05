#!/usr/bin/env python3
"""Inventory every original W3C SVG Tiny 1.2 case and measure Lean admission.

This deliberately makes no pixel or visual-conformance claim. Fixtures are
unaltered original svg/ files, including their labels and metadata.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile

ARCHIVE_URL = 'https://www.w3.org/Graphics/SVG/Test/20080912/W3C_SVG_12_TinyTestSuite.tar.gz'
ARCHIVE_SHA256 = '2203d6f44178cbb3853bdc7abe865f4e7e42506727ecc9e34b408b6f33e2e718'
sha = lambda data: hashlib.sha256(data).hexdigest()
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--archive', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
p.add_argument('--lean', default='lean')
p.add_argument('--timeout', type=int, default=180)
a = p.parse_args()
root = Path(__file__).resolve().parents[2]
formal = root / 'formal/lean4'
lab = root / 'labs/demos/foafnaut'
assert sha(a.archive.read_bytes()) == ARCHIVE_SHA256, 'Official archive SHA256 mismatch'
out = a.output.resolve()
out.mkdir(parents=True, exist_ok=False)
corpus = out / 'originals'
corpus.mkdir()
cases = []
with tarfile.open(a.archive) as archive:
    for member in sorted(archive.getmembers(), key=lambda item: item.name):
        name = PurePosixPath(member.name)
        if not (member.isfile() and name.parts[0] == 'svg' and name.suffix == '.svg'):
            continue
        assert len(name.parts) == 2 and name.name not in ('.', '..'), 'Unexpected archive path'
        data = archive.extractfile(member).read()
        # Metadata extraction must not require successful XML parsing: the
        # original corpus also includes an unbound-prefix compatibility case.
        # Decode metadata only. The candidate still receives original bytes,
        # so the UTF-16 case remains an explicit unsupported input boundary.
        text = data.decode('utf-16' if data[:2] in [b'\xff\xfe', b'\xfe\xff'] else 'utf-8')
        metadata = re.search(r'<SVGTestCase\b[^>]*>', text)
        approved = bool(metadata and re.search(r'approved=["\x27]yes["\x27]', metadata[0]))
        (corpus / name.name).write_bytes(data)
        cases.append({'file': name.name, 'archivePath': str(name), 'sha256': sha(data), 'approved': approved})
assert len(cases) == 496 and all(row['approved'] for row in cases), 'Official inventory changed'
driver = Path(__file__).with_name('SvgTinyProbe.lean')
cache_roots = [lab / '.build/web-render/olean', formal / '.lake/build/lib/lean']
cache = {str(path): sha(path.read_bytes()) for base in cache_roots for path in base.rglob('*.olean')}
command = [a.lean, '--run', str(driver), *(str(corpus / row['file']) for row in cases)]
result = subprocess.run(command, cwd=formal, env={**os.environ, 'LEAN_PATH': ':'.join(map(str, cache_roots))},
                        capture_output=True, timeout=a.timeout)
(out / 'lean.log').write_bytes(result.stderr)
(out / 'admission.jsonl').write_bytes(result.stdout)
if result.returncode:
    raise SystemExit('Lean admission driver failed; see ' + str(out / 'lean.log'))
actual = [json.loads(line) for line in result.stdout.splitlines()]
assert [row['file'] for row in actual] == [row['file'] for row in cases], 'Incomplete or reordered results'
for expected, row in zip(cases, actual):
    expected.update(row)
    assert sha((corpus / row['file']).read_bytes()) == expected['sha256'], 'Fixture modified during run'
for path, value in cache.items():
    assert sha(Path(path).read_bytes()) == value, 'Lean cache changed during run'
report = {'format': 'factoidal-svg-tiny-admission-v1', 'scope': 'Lean interpreter admission; visual conformance NOT_RUN',
          'archiveURL': ARCHIVE_URL, 'archiveSha256': ARCHIVE_SHA256,
          'runnerSha256': sha(Path(__file__).read_bytes()), 'driverSha256': sha(driver.read_bytes()),
          'cache': cache, 'cases': cases,
          'approvedCounts': dict(Counter(row['admission'] for row in cases if row['approved'])),
          'allCounts': dict(Counter(row['admission'] for row in cases)),
          'errors': dict(Counter(row['error'] for row in cases if row['error']))}
(out / 'svg-tiny-admission.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({key: report[key] for key in ['scope', 'approvedCounts', 'allCounts', 'errors']}))
raise SystemExit(1 if any(row['admission'] != 'ADMITTED' for row in cases) else 0)
