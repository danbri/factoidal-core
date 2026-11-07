#!/usr/bin/env python3
"""Pixel comparison of all 496 W3C SVG Tiny 1.2 tests with their W3C PNGs.

Each original svg/ file goes unchanged to web-render-native --svg, which makes
the same WebGPU artifact the browser draws. svg_tiny_gpu.ts draws it on a real
GPU and reads the pixels back. They are compared with the png/ file of the same
name from the same archive. The CPU sampler is not used: it takes minutes a file.

MATCH and CLOSE are our own bands, fixed before the first run. They are not a
W3C verdict: W3C pass criteria are read by a person, and allow label text to
differ. A blank white image goes through the same bands as a control.

The test renders the first frame only. Animated and scripted tests have
references taken at a later moment, so they can not match yet.
"""
import argparse, collections, concurrent.futures, hashlib, json, os, subprocess, tarfile, time
from pathlib import Path
import numpy as np
from PIL import Image

ARCHIVE_SHA256 = '2203d6f44178cbb3853bdc7abe865f4e7e42506727ecc9e34b408b6f33e2e718'
TOLERANCE = 32            # channel difference that counts as a different pixel
MATCH = (0.005, 0.95)     # most different share, least ink recall
CLOSE = (0.05, 0.70)
INK = 24                  # distance from white that counts as ink

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--archive', required=True, type=Path)
p.add_argument('--native', required=True, type=Path)
p.add_argument('--output', required=True, type=Path)
p.add_argument('--timeout', type=float, default=120)
p.add_argument('--deno', default='deno')
p.add_argument('--jobs', type=int, default=max(1, (os.cpu_count() or 2) - 2))
p.add_argument('--only', help='run only names that contain this text')
a = p.parse_args()
sha = lambda data: hashlib.sha256(data).hexdigest()
assert sha(a.archive.read_bytes()) == ARCHIVE_SHA256, 'Official archive SHA256 mismatch'
out = a.output.resolve()
(out / 'actual').mkdir(parents=True, exist_ok=True)
(out / 'expected').mkdir(exist_ok=True)
(out / 'originals').mkdir(exist_ok=True)
pairs = {}
with tarfile.open(a.archive) as archive:
    for member in archive.getmembers():
        parts = member.name.split('/')
        if member.name == 'images/SVGFreeSans.svg':
            # The tests name this font by font-face-uri. It is the font in the PNGs.
            (out / 'SVGFreeSans.svg').write_bytes(archive.extractfile(member).read())
        if member.isfile() and len(parts) == 2 and parts[0] == 'images':
            # Raster images that the tests name by ../images/; --svg-resources keeps reads under out.
            (out / 'images').mkdir(exist_ok=True)
            (out / 'images' / parts[1]).write_bytes(archive.extractfile(member).read())
        if member.isfile() and len(parts) == 2 and parts[0] in ('svg', 'png'):
            stem = parts[1].rsplit('.', 1)[0]
            pairs.setdefault(stem, {})[parts[0]] = archive.extractfile(member).read()
assert len(pairs) == 496 and all(len(v) == 2 for v in pairs.values()), 'Official inventory changed'


def flatten(image):
    rgba = np.array(image.convert('RGBA'), dtype=np.uint16)
    alpha = rgba[:, :, 3:4]
    return ((rgba[:, :, :3] * alpha + 255 * (255 - alpha) + 127) // 255).astype(np.uint8)


def score(actual, expected):
    difference = np.abs(actual.astype(np.int16) - expected.astype(np.int16)).max(axis=2)
    different = int((difference > TOLERANCE).sum())
    share = different / difference.size
    ink = (255 - expected.astype(np.int16)).max(axis=2) > INK
    recall = float(((difference <= TOLERANCE) & ink).sum() / ink.sum()) if ink.any() else 1.0
    band = 'MATCH' if share <= MATCH[0] and recall >= MATCH[1] else \
        'CLOSE' if share <= CLOSE[0] and recall >= CLOSE[1] else 'MISMATCH'
    return {'band': band, 'differentPixels': different, 'differentShare': round(share, 6),
            'inkRecall': round(recall, 4), 'exact': int(difference.max()) == 0}


def prepare(stem):
    """Lean: original SVG to WebGPU artifact."""
    data = pairs[stem]
    source = out / 'originals' / (stem + '.svg')
    source.write_bytes(data['svg'])
    (out / 'expected' / (stem + '.png')).write_bytes(data['png'])
    with Image.open(out / 'expected' / (stem + '.png')) as image:
        expected = flatten(image)
    height, width = expected.shape[:2]
    row = {'file': stem + '.svg', 'svgSha256': sha(data['svg']), 'pngSha256': sha(data['png']),
           'width': width, 'height': height,
           'blankControl': score(np.full_like(expected, 255), expected)}
    started = time.time()
    try:
        result = subprocess.run([str(a.native), str(source), str(width), str(height), '--svg', '--svg-font', str(out / 'SVGFreeSans.svg'), '--svg-resources', str(out)],
                                capture_output=True, timeout=a.timeout, env={'PATH': '/nonexistent'})
    except subprocess.TimeoutExpired:
        return {**row, 'status': 'TIMEOUT', 'reason': f'exceeded {a.timeout}s'}
    row['leanSeconds'] = round(time.time() - started, 3)
    if result.returncode:
        reason = result.stderr.decode(errors='replace')[:400]
        return {**row, 'status': 'UNAVAILABLE' if 'invalid UTF-8' in reason or 'utf' in reason.lower() else 'CRASH', 'reason': reason}
    value = json.loads(result.stdout)
    if 'error' in value:
        return {**row, 'status': 'REFUSED', 'reason': value['error']}
    (out / 'artifact').mkdir(exist_ok=True)
    (out / 'artifact' / (stem + '.json')).write_text(json.dumps(value['artifact']))
    return {**row, 'status': 'DRAW', 'primitiveCount': value['primitiveCount'], 'dropped': value['dropped']}


def judge(row):
    if row['status'] != 'DRAW':
        return row
    stem = row['file'][:-4]
    raw = out / 'rgba' / (stem + '.rgba')
    if not raw.exists():
        failure = out / 'rgba' / (stem + '.error')
        return {**row, 'status': 'GPU_ERROR', 'reason': failure.read_text()[:400] if failure.exists() else 'no pixels'}
    height, width = row['height'], row['width']
    rgba = np.frombuffer(raw.read_bytes(), dtype=np.uint8).reshape((height, width, 4))
    actual = np.ascontiguousarray(rgba[:, :, :3])
    Image.fromarray(actual).save(out / 'actual' / (stem + '.png'), compress_level=6)
    with Image.open(out / 'expected' / (stem + '.png')) as image:
        measured = score(actual, flatten(image))
    raw.unlink()
    return {**row, 'status': measured.pop('band'), **measured}


stems = sorted(s for s in pairs if not a.only or a.only in s)
with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
    prepared = list(pool.map(prepare, stems))
(out / 'rgba').mkdir(exist_ok=True)
lab = Path(__file__).resolve().parents[2] / 'labs/demos/foafnaut'
gpu = subprocess.run([a.deno, 'run', '--no-check', '--no-config', '--no-npm', '--node-modules-dir=none', '--unstable-webgpu',
                      '--allow-read', '--allow-write', '--allow-env', '--allow-net', str(Path(__file__).with_name('svg_tiny_gpu.ts')),
                      str(out / 'artifact'), str(out / 'rgba')], cwd=lab, capture_output=True, text=True)
(out / 'gpu.log').write_text(gpu.stdout + gpu.stderr)
assert gpu.returncode == 0, gpu.stderr[-800:]
adapter = next((line for line in gpu.stdout.splitlines() if line.startswith('adapter ')), 'unknown')
cases = [judge(row) for row in prepared]
counts = collections.Counter(c['status'] for c in cases)
blank = collections.Counter(c['blankControl']['band'] for c in cases)
drops = collections.Counter(line for c in cases for line in set(c.get('dropped', [])))
report = {'format': 'factoidal-svg-tiny-pixels-v1',
          'measuredAt': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
          'scope': 'First frame, real WebGPU pixels against W3C PNG. Our bands, not a W3C verdict.',
          'gpu': adapter,
          'archiveSha256': ARCHIVE_SHA256, 'nativeSha256': sha(a.native.read_bytes()),
          'runnerSha256': sha(Path(__file__).read_bytes()),
          'tolerance': TOLERANCE, 'match': MATCH, 'close': CLOSE, 'inkThreshold': INK,
          'total': len(cases), 'counts': dict(counts), 'blankControlCounts': dict(blank),
          'exact': sum(1 for c in cases if c.get('exact')),
          'filesAffectedByDrop': dict(drops.most_common()), 'cases': cases}
(out / 'svg-tiny-pixels.json').write_text(json.dumps(report, indent=1) + '\n')
print(json.dumps({k: report[k] for k in ('total', 'counts', 'blankControlCounts', 'exact')}))
print('most common removals (files affected):')
for line, count in drops.most_common(25):
    print(f'  {count:4} {line[:90]}')
