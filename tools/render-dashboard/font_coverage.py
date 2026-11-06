#!/usr/bin/env python3
"""Count what a named font set can draw, out of Unicode 18.0.0.

    font_coverage.py --set NAME --bitmap-source      the browser's 5x7 bitmap
    font_coverage.py --set NAME FONT_FILE[#INDEX] ...

Denominators come only from third_party/unicode-18.0.0:

- characters: graphic characters (general category L, M, N, P, S or Zs).
- scripts: Script property values, without Common, Inherited and Unknown.
  A script counts when the set has at least one of its graphic characters.
  scriptsComplete counts scripts where the set has all of them.
- emoji: the RGI sets of emoji-sequences.txt and emoji-zwj-sequences.txt, by
  type. A sequence counts only when hb-shape gives one glyph that is not
  .notdef. Separate glyphs side by side do not count. A single code point
  counts when it has a glyph; for a bitmap there is no shaping, so a sequence
  of more than one code point does not count.

The set is a union: a character counts when any font in the set has it.
Prints one JSON object. The bitmap range is read from WebRender.lean, and the
run stops when that source no longer says it.
"""
import argparse, hashlib, json, re, struct, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
UCD = ROOT / 'third_party/unicode-18.0.0'
GRAPHIC = re.compile(r'^(L|M|N|P|S|Zs)')
NOT_SCRIPTS = {'Common', 'Inherited', 'Unknown'}
sha = lambda data: hashlib.sha256(data).hexdigest()


def ranges(path):
    """Yield (first, last, value) from a UCD property file."""
    for line in path.read_text(encoding='utf-8').splitlines():
        line = line.split('#', 1)[0].strip()
        if line:
            points, value = [part.strip() for part in line.split(';')[:2]]
            first, _, last = points.partition('..')
            yield int(first, 16), int(last or first, 16), value


def unicode_totals():
    graphic = set()
    for first, last, category in ranges(UCD / 'DerivedGeneralCategory.txt'):
        if GRAPHIC.match(category):
            graphic.update(range(first, last + 1))
    scripts = {}
    for first, last, script in ranges(UCD / 'Scripts.txt'):
        if script not in NOT_SCRIPTS:
            scripts.setdefault(script, set()).update(range(first, last + 1))
    scripts = {name: points & graphic for name, points in scripts.items()}
    return graphic, {name: points for name, points in scripts.items() if points}


def emoji_sequences():
    """RGI sequences by type. Checks each total against the file's own count."""
    found = {}
    for name in ['emoji-sequences.txt', 'emoji-zwj-sequences.txt']:
        text = (UCD / name).read_text(encoding='utf-8')
        stated = sum(int(n) for n in re.findall(r'^# Total elements: (\d+)', text, re.M))
        seen = 0
        for line in text.splitlines():
            line = line.split('#', 1)[0].strip()
            if not line:
                continue
            points, kind = [part.strip() for part in line.split(';')[:2]]
            if '..' in points:
                first, last = points.split('..')
                items = [(point,) for point in range(int(first, 16), int(last, 16) + 1)]
            else:
                items = [tuple(int(point, 16) for point in points.split())]
            found.setdefault(kind, []).extend(items)
            seen += len(items)
        assert seen == stated, f'{name}: read {seen} sequences, the file states {stated}'
    return found


def sfnt_offsets(data):
    if data[:4] == b'ttcf':
        count = struct.unpack('>I', data[8:12])[0]
        return list(struct.unpack(f'>{count}I', data[12:12 + 4 * count]))
    return [0]


def cmap_points(data, offset):
    """All code points of the Unicode cmap subtables of one font face."""
    count = struct.unpack('>H', data[offset + 4:offset + 6])[0]
    cmap = None
    for index in range(count):
        tag, _, start, _ = struct.unpack('>4sIII', data[offset + 12 + 16 * index:offset + 28 + 16 * index])
        if tag == b'cmap':
            cmap = start
    assert cmap is not None, 'font has no cmap table'
    points = set()
    for index in range(struct.unpack('>H', data[cmap + 2:cmap + 4])[0]):
        platform, encoding, start = struct.unpack('>HHI', data[cmap + 4 + 8 * index:cmap + 12 + 8 * index])
        if not (platform == 0 or (platform == 3 and encoding in (1, 10))):
            continue
        at = cmap + start
        form = struct.unpack('>H', data[at:at + 2])[0]
        if form == 4:
            pairs = struct.unpack('>H', data[at + 6:at + 8])[0] // 2
            word = lambda base, n: struct.unpack('>H', data[base + 2 * n:base + 2 * n + 2])[0]
            ends, starts = at + 14, at + 16 + 2 * pairs
            deltas, offsets = starts + 2 * pairs, starts + 4 * pairs
            for n in range(pairs):
                end, first, delta, shift = word(ends, n), word(starts, n), word(deltas, n), word(offsets, n)
                for point in range(first, end + 1):
                    if point == 0xFFFF:
                        continue
                    glyph = (point + delta) & 0xFFFF if shift == 0 else word(offsets + 2 * n + shift, point - first)
                    if glyph and (shift == 0 or (glyph + delta) & 0xFFFF):
                        points.add(point)
        elif form == 12 or form == 13:
            groups = struct.unpack('>I', data[at + 12:at + 16])[0]
            for n in range(groups):
                first, last, glyph = struct.unpack('>III', data[at + 16 + 12 * n:at + 28 + 12 * n])
                points.update(range(first if glyph or form == 13 else first + 1, last + 1))
        elif form == 6:
            first, entries = struct.unpack('>HH', data[at + 6:at + 10])
            ids = struct.unpack(f'>{entries}H', data[at + 10:at + 10 + 2 * entries])
            points.update(first + n for n, glyph in enumerate(ids) if glyph)
        elif form == 0:
            points.update(n for n, glyph in enumerate(data[at + 6:at + 262]) if glyph)
    return points


def one_glyph(font, index, sequence):
    """True when hb-shape draws this sequence as one real glyph."""
    text = ','.join(f'U+{point:04X}' for point in sequence)
    result = subprocess.run(['hb-shape', f'--face-index={index}', '--no-glyph-names', '--no-positions',
                             '--no-clusters', f'--unicodes={text}', font], capture_output=True, text=True, timeout=60)
    ids = result.stdout.strip().strip('[]').split('|')
    return result.returncode == 0 and len(ids) == 1 and ids[0] not in ('', '0')


def bitmap_points():
    source = (ROOT / 'labs/demos/foafnaut/WebRender.lean').read_text()
    found = re.search(r'family := "factoidal-ascii-bitmap-v1".*?admits := fun n => (\d+) <= n && n <= (\d+)', source)
    assert found, 'WebRender.lean no longer states the bitmap font range'
    return set(range(int(found[1]), int(found[2]) + 1)), sha(source.encode())


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--set', required=True, help='name of the font set')
    p.add_argument('--bitmap-source', action='store_true', help='measure the bitmap font in WebRender.lean')
    p.add_argument('fonts', nargs='*', help='font files; FILE#N selects face N of a collection')
    a = p.parse_args()
    graphic, scripts = unicode_totals()
    sequences = emoji_sequences()
    points, faces, files = set(), [], []
    if a.bitmap_source:
        points, digest = bitmap_points()
        files.append({'path': 'labs/demos/foafnaut/WebRender.lean', 'sha256': digest, 'note': 'bitmap font source'})
    for spec in a.fonts:
        path, _, face = spec.partition('#')
        data = Path(path).read_bytes()
        offsets = sfnt_offsets(data)
        index = int(face or 0)
        points |= cmap_points(data, offsets[index])
        faces.append((path, index))
        files.append({'path': path, 'face': index, 'sha256': sha(data)})
    have = points & graphic
    by_script = {name: (len(members & points), len(members)) for name, members in scripts.items()}
    counts = {'characters': len(have), 'scripts': sum(1 for got, _ in by_script.values() if got),
              'scriptsComplete': sum(1 for got, total in by_script.values() if got == total)}
    denominators = {'characters': len(graphic), 'scripts': len(scripts), 'scriptsComplete': len(scripts)}
    for kind, items in sorted(sequences.items()):
        got = 0
        for sequence in items:
            if len(sequence) == 1 and sequence[0] in points:
                got += 1
            elif len(sequence) > 1 and any(one_glyph(path, index, sequence) for path, index in faces):
                got += 1
        counts[kind] = got
        denominators[kind] = len(items)
    counts['emojiAll'] = sum(counts[kind] for kind in sequences)
    denominators['emojiAll'] = sum(len(items) for items in sequences.values())
    missing = sorted(((total - got, name) for name, (got, total) in by_script.items()), reverse=True)
    print(json.dumps({'set': a.set, 'files': files, 'counts': counts, 'denominators': denominators,
                      'scriptsWithGlyphs': sorted(name for name, (got, _) in by_script.items() if got),
                      'largestMissingScripts': [{'reason': name, 'count': n} for n, name in missing[:10]]}))


if __name__ == '__main__':
    sys.exit(main())
