#!/usr/bin/env python3
"""The Hub's fallback fonts: fetch, cut the CJK fonts into slices, and write the table.

    uvx --from fonttools python labs/demos/foafnaut/fallback_fonts.py [--cache DIR]

The script fonts are copied unchanged from notofonts.github.io. The CJK fonts are
too large to fetch for one line of Chinese, so they are cut (pyftsubset) into slices:
kana and CJK punctuation, the common Han characters, the rest of the Han characters,
and Hangul. Each file goes in third_party/fonts/<dir>/ with its OFL.txt.

Emoji come last, from Noto Emoji, the monochrome outline emoji font of google/fonts: a
variable font (weight 300 to 700, 1.98 MB) whose `gvar` deltas are half its size. The
engine draws the default outlines and reads no variations, so the font is instanced at
its default weight, 400 (fontTools varLib.instancer), and subset with the options of the
CJK slices, keeping every character and the `ccmp` ligatures of its sequences (ZWJ,
skin tones, flags, tags, keycaps).

docs/web/hub/foafnaut/fallback-fonts.mjs gets, for each font in order, the characters
it adds: those in its cmap that Noto Sans and the fonts before it lack. The Hub worker
fetches a font only when a page has one of its characters.
"""
import argparse, hashlib, os, shutil, subprocess, sys, urllib.request
from fontTools.ttLib import TTFont
from fontTools.varLib import instancer

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..', '..'))
FONTS = os.path.join(ROOT, 'third_party', 'fonts')
TABLE = os.path.join(ROOT, 'docs', 'web', 'hub', 'foafnaut', 'fallback-fonts.mjs')
NOTO = 'https://raw.githubusercontent.com/notofonts/notofonts.github.io/86ce02c0fe7890f5936c5dffb26fca0797d1be64/fonts'
CJK = 'https://raw.githubusercontent.com/notofonts/noto-cjk/f8d157532fbfaeda587e826d4cd5b21a49186f7c/Sans'
OFL = 'https://raw.githubusercontent.com/notofonts/{repo}/main/OFL.txt'
EMOJI = 'https://raw.githubusercontent.com/google/fonts/8b0a1d0f5983c89bc2b93f1b5fb55f9e252744b5/ofl/notoemoji'
# SHA-256 of NotoEmoji[wght].ttf (3.002) at that commit.
EMOJI_SHA256 = 'de6c18832938afc99caf132b39d6a30a19bac7f2e812e28db2535b4608d27551'

# (directory, family, script repository, file name); Armenian is already vendored.
SCRIPTS = [
    ('noto-sans-armenian', 'Noto Sans Armenian', None, 'NotoSansArmenian-Regular.ttf'),
    ('noto-sans-georgian', 'Noto Sans Georgian', 'georgian', 'NotoSansGeorgian-Regular.ttf'),
    ('noto-sans-ethiopic', 'Noto Sans Ethiopic', 'ethiopic', 'NotoSansEthiopic-Regular.ttf'),
    ('noto-sans-hebrew', 'Noto Sans Hebrew', 'hebrew', 'NotoSansHebrew-Regular.ttf'),
    ('noto-sans-arabic', 'Noto Sans Arabic', 'arabic', 'NotoSansArabic-Regular.ttf'),
    ('noto-sans-devanagari', 'Noto Sans Devanagari', 'devanagari', 'NotoSansDevanagari-Regular.ttf'),
    ('noto-sans-bengali', 'Noto Sans Bengali', 'bengali', 'NotoSansBengali-Regular.ttf'),
    ('noto-sans-tamil', 'Noto Sans Tamil', 'tamil', 'NotoSansTamil-Regular.ttf'),
    ('noto-sans-thai', 'Noto Sans Thai', 'thai', 'NotoSansThai-Regular.ttf'),
    ('noto-sans-math', 'Noto Sans Math', 'math', 'NotoSansMath-Regular.ttf'),
]

def han(c):
    return 0x3400 <= c <= 0x4DBF or 0x4E00 <= c <= 0x9FFF or 0xF900 <= c <= 0xFAFF or 0x20000 <= c <= 0x3FFFF

def encoded(codec, first, last, rows):
    """The characters of a two-byte EUC codec in rows `rows`, cells A1..FE."""
    out = set()
    for row in rows:
        for cell in range(0xA1, 0xFF):
            try:
                out.update(ord(ch) for ch in bytes([row, cell]).decode(codec))
            except UnicodeDecodeError:
                pass
    return {c for c in out if first <= c <= last}

# Common Han: JIS X 0208 level 1 (rows 16-47) and GB 2312 level 1 (rows 16-55).
JIS1 = encoded('euc_jp', 0x3400, 0x9FFF, range(0xB0, 0xD0))
GB1 = encoded('gb2312', 0x3400, 0x9FFF, range(0xB0, 0xD8))
GB = encoded('gb2312', 0x3400, 0x9FFF, range(0xB0, 0xF8))
# KS X 1001: the 2,350 common Hangul syllables (rows 16-40).
KS = encoded('euc_kr', 0xAC00, 0xD7A3, range(0xB0, 0xC9))
KANA = set(range(0x3000, 0x3100)) | set(range(0x31F0, 0x3200)) | set(range(0xFF00, 0xFFF0))
JAMO = set(range(0x1100, 0x1200)) | set(range(0x3130, 0x3190))

def fetch(url, path):
    if not os.path.exists(path):
        print('fetch', url, file=sys.stderr)
        with urllib.request.urlopen(url) as r, open(path + '.part', 'wb') as f:
            shutil.copyfileobj(r, f)
        os.rename(path + '.part', path)
    return path

def subset(source, unicodes, out):
    os.makedirs(os.path.dirname(out), exist_ok=True)
    listing = out + '.unicodes'
    with open(listing, 'w') as f:
        f.write('\n'.join('U+%04X' % c for c in sorted(unicodes)))
    subprocess.run([sys.executable, '-m', 'fontTools.subset', source, '--unicodes-file=' + listing,
                    '--layout-features=*', '--name-IDs=*', '--name-languages=*', '--notdef-outline',
                    '--no-hinting', '--output-file=' + out], check=True)
    os.remove(listing)

def blocks(codes):
    """The 256-character blocks that hold any of the code points."""
    return {c for b in {c >> 8 for c in codes} for c in range(b << 8, (b << 8) + 256)}

def ranges(codes):
    """Code points as 'a-b' and 'a' runs in base 36: the worker reads them back."""
    out, codes = [], sorted(codes)
    i = 0
    while i < len(codes):
        j = i
        while j + 1 < len(codes) and codes[j + 1] == codes[j] + 1:
            j += 1
        out.append(f'{codes[i]:x}' if i == j else f'{codes[i]:x}-{codes[j]:x}')
        i = j + 1
    return ','.join(out)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', default=os.path.join(ROOT, '.build', 'fallback-fonts'))
    args = ap.parse_args()
    os.makedirs(args.cache, exist_ok=True)
    fonts = []  # (directory, family, path in third_party)
    for directory, family, repo, name in SCRIPTS:
        target = os.path.join(FONTS, directory, name)
        if repo:
            os.makedirs(os.path.dirname(target), exist_ok=True)
            shutil.copy(fetch(f'{NOTO}/{name.split("-")[0]}/unhinted/ttf/{name}', os.path.join(args.cache, name)), target)
            shutil.copy(fetch(OFL.format(repo=repo), os.path.join(args.cache, f'OFL-{repo}.txt')), os.path.join(FONTS, directory, 'OFL.txt'))
        fonts.append((directory, family, target))
    jp = fetch(f'{CJK}/SubsetOTF/JP/NotoSansJP-Regular.otf', os.path.join(args.cache, 'NotoSansJP-Regular.otf'))
    sc = fetch(f'{CJK}/SubsetOTF/SC/NotoSansSC-Regular.otf', os.path.join(args.cache, 'NotoSansSC-Regular.otf'))
    kr = fetch(f'{CJK}/SubsetOTF/KR/NotoSansKR-Regular.otf', os.path.join(args.cache, 'NotoSansKR-Regular.otf'))
    cjkLicence = fetch(f'{CJK}/LICENSE', os.path.join(args.cache, 'OFL-cjk.txt'))
    jpMap, scMap, krMap = (set(TTFont(p, lazy=True).getBestCmap()) for p in (jp, sc, kr))
    jpHan, scHan = {c for c in jpMap if han(c)}, {c for c in scMap if han(c)}
    common = jpHan & (JIS1 | GB1)
    slices = [
        ('NotoSansJP-Kana.otf', 'Noto Sans JP Kana', jp, jpMap & KANA),
        ('NotoSansJP-HanCommon.otf', 'Noto Sans JP Han', jp, common),
        ('NotoSansSC-HanCommon.otf', 'Noto Sans SC Han', sc, (scHan & GB) - jpHan),
        ('NotoSansKR-Hangul.otf', 'Noto Sans KR Hangul', kr, krMap & (KS | JAMO)),
        ('NotoSansJP-HanMore.otf', 'Noto Sans JP Han More', jp, jpHan - common),
        ('NotoSansSC-HanMore.otf', 'Noto Sans SC Han More', sc, scHan - jpHan - GB),
        ('NotoSansKR-HangulMore.otf', 'Noto Sans KR Hangul More', kr, {c for c in krMap if 0xAC00 <= c <= 0xD7A3} - KS),
    ]
    cjkDir = os.path.join(FONTS, 'noto-sans-cjk')
    for name, family, source, unicodes in slices:
        subset(source, unicodes, os.path.join(cjkDir, name))
        fonts.append(('noto-sans-cjk', family, os.path.join(cjkDir, name)))
    shutil.copy(cjkLicence, os.path.join(cjkDir, 'OFL.txt'))
    # Noto Emoji at its default weight, after every other font.
    emoji = fetch(f'{EMOJI}/NotoEmoji%5Bwght%5D.ttf', os.path.join(args.cache, 'NotoEmoji-wght.ttf'))
    got = hashlib.sha256(open(emoji, 'rb').read()).hexdigest()
    if got != EMOJI_SHA256:
        sys.exit(f'NotoEmoji[wght].ttf has SHA-256 {got}, not {EMOJI_SHA256}')
    static = os.path.join(args.cache, 'NotoEmoji-400.ttf')
    font = TTFont(emoji)
    instancer.instantiateVariableFont(font, {'wght': 400}, inplace=True)
    font.save(static)
    emojiDir = os.path.join(FONTS, 'noto-emoji')
    subset(static, set(TTFont(static, lazy=True).getBestCmap()), os.path.join(emojiDir, 'NotoEmoji-Regular.ttf'))
    shutil.copy(fetch(f'{EMOJI}/OFL.txt', os.path.join(args.cache, 'OFL-emoji.txt')), os.path.join(emojiDir, 'OFL.txt'))
    fonts.append(('noto-emoji', 'Noto Emoji', os.path.join(emojiDir, 'NotoEmoji-Regular.ttf')))
    # What each font adds: its cmap less Noto Sans and the fonts before it.
    held = set(TTFont(os.path.join(FONTS, 'noto-sans', 'NotoSans-Regular.ttf'), lazy=True).getBestCmap())
    rows = []
    for directory, family, path in fonts:
        cmap = set(TTFont(path, lazy=True).getBestCmap())
        adds = {c for c in cmap - held if c > 0x20}
        held |= cmap
        data = open(path, 'rb').read()
        rows.append((directory, os.path.basename(path), family, len(data), hashlib.sha256(data).hexdigest(), adds))
        print(f'{family:28} {len(data):>9} bytes, adds {len(adds):>6} characters', file=sys.stderr)
    # Fonts of the CJK slices list blocks in the table; the characters they add are in
    # coverage.json, which the worker fetches only for a page with a character in a block.
    coverage = {}
    with open(TABLE, 'w') as f:
        f.write('// Generated by labs/demos/foafnaut/fallback_fonts.py: do not edit.\n')
        f.write('// The fonts after Noto Sans, in order. `adds` are the characters a font adds (hexadecimal\n')
        f.write('// code points and ranges): those that Noto Sans and the fonts before it lack. A font with\n')
        f.write('// `coverage` has them in that file, and `blocks` says when the file is needed.\n')
        f.write('export const fallbackFonts=[\n')
        for directory, name, family, size, sha, adds in rows:
            f.write(f"  {{path:'./fonts/{directory}/{name}',family:'{family}',bytes:{size},sha256:'{sha}',\n")
            if directory == 'noto-sans-cjk' and 'Kana' not in name:
                coverage[family] = ranges(adds)
                f.write(f"   blocks:'{ranges(blocks(adds))}',coverage:'./fonts/noto-sans-cjk/coverage.json'}},\n")
            else:
                f.write(f"   adds:'{ranges(adds)}'}},\n")
        f.write('];\n')
    with open(os.path.join(cjkDir, 'coverage.json'), 'w') as f:
        f.write('{\n' + ',\n'.join(f'"{k}":"{v}"' for k, v in coverage.items()) + '\n}\n')

if __name__ == '__main__':
    main()
