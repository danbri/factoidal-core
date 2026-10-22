"""Capture completed integration evidence without changing previous runs."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent
repo = root / 'integrate-core'
output = repo / 'docs/audits/final-integration-20261022'
if output.exists():
    raise SystemExit('Refusing to overwrite evidence: ' + str(output))
required = ['integration-final-library-repaired', 'integration-final-wasm',
            'integration-final-npm', 'integration-final-hub',
            'integration-final-xmpp-interop', 'integration-final-lws-host',
            'integration-final-authz-host', 'integration-final-solid-host',
            'integration-final-hygiene-repaired', 'integration-final-tail-repaired',
            'integration-final-csimp-repaired', 'integration-final-tail-controls',
            'integration-final-csimp-controls', 'integration-final-pack',
            'integration-final-owl-artifact', 'integration-ci-final']
for name in required:
    report = root / 'logs' / (name + '.json')
    if not report.is_file():
        raise SystemExit('Check not complete: ' + name)

selected = set()
for pattern in ['integration-final-*', 'integration-name-complement-before*',
                'integration-ci-86ca44f4b.*', 'integration-ci-4f11a392f.*', 'integration-ci-1a2299588.*', 'integration-ci-final*',
                'integration-owl-artifact-controls.json']:
    selected.update(p for p in (root / 'logs').glob(pattern)
                    if p.is_file() and p.suffix in {'.json', '.log'})
for directory in ['integration-ci-86ca44f4b-owl', 'integration-ci-final-assurance']:
    selected.update((root / 'logs' / directory).glob('*.json'))
selected.update(root / name for name in
                ['run-integration-check.mjs', 'run-final-api-checks.mjs',
                 'capture-integration-evidence.py', 'run-final-package-check.mjs', 'run-final-source-checks.mjs', 'check-ci-audit-closure.py', 'capture-final-ci.mjs'])
output.mkdir(parents=True)
files = []
for source in sorted(selected):
    if source.is_symlink() or not source.is_file():
        raise ValueError('Expected regular evidence file: ' + str(source))
    relative = source.relative_to(root)
    data = source.read_bytes()
    destination = output / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open('xb') as stream:
        stream.write(data)
    files.append({'path': relative.as_posix(), 'size': len(data),
                  'sha256': hashlib.sha256(data).hexdigest()})
manifest = {
    'format': 'factoidal-npm-audit-snapshot-v1',
    'captured_utc': datetime.now(timezone.utc).isoformat(),
    'scope': 'Core PRs 1–3 combined source and local artifact validation; failures retained; no npm publication',
    'capture_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
    'file_count': len(files), 'total_bytes': sum(f['size'] for f in files),
    'files': files,
}
(output / 'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
subprocess.run(['python3', str(repo / 'tools/snapshot-npm-audit.py'),
                '--verify', str(output)], check=True)
