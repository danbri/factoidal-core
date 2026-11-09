#!/usr/bin/env python3
"""The Hub's fallback fonts: fetch, cut the CJK fonts into slices, and write the table.

    uvx --from fonttools python labs/demos/foafnaut/fallback_fonts.py [--cache DIR]

The script fonts are copied unchanged from notofonts.github.io. The CJK fonts are
too large to fetch for one line of Chinese, so they are cut (pyftsubset) into slices:
kana and CJK punctuation, the common Han characters, the rest of the Han characters,
and Hangul. Each file goes in third_party/fonts/<dir>/ with its OFL.txt.

Colour emoji come next, from Noto Color Emoji (google/fonts, the COLRv1 build of
googlefonts/noto-emoji, 25 MB of which 20 MB is an SVG table the engine does not read).
It is cut into slices by the groups of Unicode's emoji-test.txt, each slice holding the
glyphs of its emoji sequences (HarfBuzz, through uharfbuzz, gives the glyph of each
sequence; fontTools subsets with no layout closure, so a slice keeps only its own
ligatures), and every sequence is checked to shape to one glyph of its slice. Flags are
cut by the first letter of their regional indicator pair. A page fetches only the slices
of its emoji (`adds`; `vs16` for a symbol that a text font has, asked for with U+FE0F;
`needs` for the ZWJ slices; `regional` for flags).

Emoji come last, from Noto Emoji, the monochrome outline emoji font of google/fonts: a
variable font (weight 300 to 700, 1.98 MB) whose `gvar` deltas are half its size. The
engine draws the default outlines and reads no variations, so the font is instanced at
its default weight, 400 (fontTools varLib.instancer), and subset with the options of the
CJK slices, keeping every character and the `ccmp` ligatures of its sequences (ZWJ,
skin tones, flags, tags, keycaps). With the colour slices before it, a page fetches it
only for text presentation, U+FE0E.

    uvx --from fonttools --with uharfbuzz python labs/demos/foafnaut/fallback_fonts.py [--colour-only]

`--colour-only` cuts the colour slices again and writes the table, and takes the other
fonts as they are in third_party/fonts.

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
# Noto Color Emoji (COLRv1, OFL), google/fonts at commit c08cd288696d.
COLOUR = 'https://raw.githubusercontent.com/google/fonts/c08cd288696d8ca30bf0296dc214d80d33a65d8f/ofl/notocoloremoji'
COLOUR_SHA256 = '4d82a18d8d95f60ba883ce242bbadbf84a576e987745dd7ba38d71c67cff2d73'
UCD = os.path.join(ROOT, 'third_party', 'unicode-18.0.0')
# Colour slices: (file stem, family, emoji-test.txt groups). People & Body is cut in three
# (single people with their skin tones, ZWJ sequences, ZWJ sequences with skin tones) and
# Flags by the first letter of the pair (FLAG_LETTERS); the rest of Flags (tag sequences,
# the white, black, chequered and triangular flags) is one more slice.
COLOUR_SLICES = [
    ('Smileys', 'Noto Color Emoji Smileys', ['Smileys & Emotion']),
    ('People', 'Noto Color Emoji People', ['People & Body', 'Component']),
    ('PeopleZWJ', 'Noto Color Emoji People ZWJ', []),
    ('PeopleZWJTones', 'Noto Color Emoji People ZWJ Tones', []),
    ('Animals', 'Noto Color Emoji Animals', ['Animals & Nature']),
    ('Food', 'Noto Color Emoji Food', ['Food & Drink']),
    ('Travel', 'Noto Color Emoji Travel', ['Travel & Places']),
    ('Activities', 'Noto Color Emoji Activities', ['Activities']),
    ('Objects', 'Noto Color Emoji Objects', ['Objects']),
    ('Symbols', 'Noto Color Emoji Symbols', ['Symbols']),
    ('Flags', 'Noto Color Emoji Flags', ['Flags']),
]
FLAG_LETTERS = ['AB', 'CE', 'FK', 'LP', 'QS', 'TZ']

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

def emoji_properties():
    """Code points with Emoji_Presentation=Yes, from emoji-data.txt."""
    out = set()
    for line in open(os.path.join(UCD, 'emoji-data.txt'), encoding='utf-8'):
        f = [x.strip() for x in line.split('#')[0].split(';')]
        if len(f) == 2 and f[1] == 'Emoji_Presentation':
            r = f[0].split('..')
            out.update(range(int(r[0], 16), int(r[-1], 16) + 1))
    return out

def emoji_sequences():
    """(group, code points) of the fully-qualified emoji and the components, from emoji-test.txt."""
    out, group = [], None
    for line in open(os.path.join(UCD, 'emoji-test.txt'), encoding='utf-8'):
        if line.startswith('# group:'):
            group = line.split(':', 1)[1].strip()
            continue
        if not line.strip() or line.startswith('#'):
            continue
        cps, rest = line.split(';', 1)
        if rest.split('#')[0].strip() in ('fully-qualified', 'component'):
            out.append((group, [int(x, 16) for x in cps.split()]))
    return out

def regional(c):
    return 0x1F1E6 <= c <= 0x1F1FF

def tone(c):
    return 0x1F3FB <= c <= 0x1F3FF

# Characters that only join a sequence: they never send a page to a slice by themselves.
JOINERS = {0x200D, 0xFE0F, 0xFE0E} | set(range(0xE0020, 0xE0080))

def colour_slices(cache, held):
    """Cut Noto Color Emoji into slices; give each slice's table fields. `held`: the
    characters of the text fonts before it."""
    import uharfbuzz as hb
    from concurrent.futures import ThreadPoolExecutor
    source = fetch(f'{COLOUR}/NotoColorEmoji-Regular.ttf', os.path.join(cache, 'NotoColorEmoji-Regular.ttf'))
    got = hashlib.sha256(open(source, 'rb').read()).hexdigest()
    if got != COLOUR_SHA256:
        sys.exit(f'NotoColorEmoji-Regular.ttf has SHA-256 {got}, not {COLOUR_SHA256}')
    # The SVG table (20 MB) and the vertical metrics are not read by the engine.
    lean = os.path.join(cache, 'NotoColorEmoji-COLRv1.ttf')
    if not os.path.exists(lean):
        font = TTFont(source)
        for tag in ('SVG ', 'vhea', 'vmtx'):
            if tag in font:
                del font[tag]
        font.save(lean)
    hbFont = hb.Font(hb.Face(hb.Blob.from_file_path(lean)))
    def shape(font, cps):
        buf = hb.Buffer()
        buf.add_codepoints(cps)
        buf.guess_segment_properties()
        hb.shape(font, buf, {})
        return [g.codepoint for g in buf.glyph_infos]
    presentation = emoji_properties()
    slices = {stem: {'family': family, 'gids': {0}, 'uni': set(), 'seqs': [], 'home': set()}
              for stem, family, _ in COLOUR_SLICES}
    for letters in FLAG_LETTERS:
        slices['Flags' + letters] = {'family': f'Noto Color Emoji Flags {letters[0]}-{letters[1]}',
                                     'gids': {0}, 'uni': set(), 'seqs': [], 'home': set(), 'letters': letters}
    groupStem = {g: stem for stem, _, groups in COLOUR_SLICES for g in groups}
    for group, cps in emoji_sequences():
        glyphs = shape(hbFont, cps)
        if len(glyphs) != 1 or glyphs[0] == 0:
            continue  # a sequence the font does not have as one glyph
        stem = groupStem[group]
        if stem == 'Flags' and regional(cps[0]):
            first = chr(ord('A') + cps[0] - 0x1F1E6)
            stem = 'Flags' + next(l for l in FLAG_LETTERS if l[0] <= first <= l[1])
        elif stem == 'People' and 0x200D in cps:
            stem = 'PeopleZWJTones' if any(tone(c) for c in cps) else 'PeopleZWJ'
        s = slices[stem]
        s['gids'].add(glyphs[0])
        s['uni'].update(cps)
        s['seqs'].append(cps)
        base = [c for c in cps if c not in JOINERS and c != 0x20E3]
        if len(base) == 1 or stem.startswith('PeopleZWJ'):
            s['home'].update(c for c in base if c > 0x7F)
        if 0x20E3 in cps:
            s['home'].add(0x20E3)
    outDir = os.path.join(FONTS, 'noto-color-emoji')
    os.makedirs(outDir, exist_ok=True)
    def cut(item):
        stem, s = item
        out = os.path.join(outDir, f'NotoColorEmoji-{stem}.ttf')
        subprocess.run([sys.executable, '-m', 'fontTools.subset', lean,
                        '--gids=' + ','.join(map(str, sorted(s['gids']))),
                        '--unicodes=' + ','.join('%x' % c for c in sorted(s['uni'])),
                        '--no-layout-closure', '--layout-features=*', '--name-IDs=*', '--name-languages=*',
                        '--notdef-outline', '--no-hinting', '--output-file=' + out], check=True)
        cut = hb.Font(hb.Face(hb.Blob.from_file_path(out)))
        bad = [cps for cps in s['seqs'] if (lambda g: len(g) != 1 or g[0] == 0)(shape(cut, cps))]
        if bad:
            sys.exit(f'{stem}: {len(bad)} sequences are not one glyph, first {bad[0]}')
        return stem, out
    with ThreadPoolExecutor(6) as pool:
        paths = dict(pool.map(cut, slices.items()))
    shutil.copy(fetch(f'{COLOUR}/OFL.txt', os.path.join(cache, 'OFL-colour-emoji.txt')), os.path.join(outDir, 'OFL.txt'))
    rows = []
    for stem, s in slices.items():
        fields = {}
        if 'letters' in s:
            a, b = (0x1F1E6 + ord(l) - ord('A') for l in s['letters'])
            fields['regional'] = ranges(range(a, b + 1))
        else:
            # A symbol that a text font has draws as text unless U+FE0F asks for emoji.
            fields['adds'] = ranges({c for c in s['home'] if c in presentation or c not in held})
            vs16 = {c for c in s['home'] if c not in presentation and c in held}
            if vs16:
                fields['vs16'] = ranges(vs16)
            if stem == 'PeopleZWJ':
                fields['needs'] = ['200d']
            elif stem == 'PeopleZWJTones':
                fields['needs'] = ['200d', '1f3fb-1f3ff']
            elif stem == 'Flags':
                fields['adds'] = ranges({c for c in s['home']} | set(range(0xE0020, 0xE0080)))
        rows.append(('noto-color-emoji', paths[stem], s['family'], fields))
    return rows

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cache', default=os.path.join(ROOT, '.build', 'fallback-fonts'))
    ap.add_argument('--colour-only', action='store_true',
                    help='cut the colour slices and write the table; take the other fonts as they are')
    args = ap.parse_args()
    os.makedirs(args.cache, exist_ok=True)
    fonts = []  # (directory, family, path in third_party)
    for directory, family, repo, name in SCRIPTS:
        target = os.path.join(FONTS, directory, name)
        if repo and not args.colour_only:
            os.makedirs(os.path.dirname(target), exist_ok=True)
            shutil.copy(fetch(f'{NOTO}/{name.split("-")[0]}/unhinted/ttf/{name}', os.path.join(args.cache, name)), target)
            shutil.copy(fetch(OFL.format(repo=repo), os.path.join(args.cache, f'OFL-{repo}.txt')), os.path.join(FONTS, directory, 'OFL.txt'))
        fonts.append((directory, family, target))
    if args.colour_only:
        return write_table(args, fonts + existing_cjk(), True)
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
    write_table(args, fonts, False)

CJK_SLICES = [('NotoSansJP-Kana.otf', 'Noto Sans JP Kana'), ('NotoSansJP-HanCommon.otf', 'Noto Sans JP Han'),
    ('NotoSansSC-HanCommon.otf', 'Noto Sans SC Han'), ('NotoSansKR-Hangul.otf', 'Noto Sans KR Hangul'),
    ('NotoSansJP-HanMore.otf', 'Noto Sans JP Han More'), ('NotoSansSC-HanMore.otf', 'Noto Sans SC Han More'),
    ('NotoSansKR-HangulMore.otf', 'Noto Sans KR Hangul More')]

def existing_cjk():
    return [('noto-sans-cjk', family, os.path.join(FONTS, 'noto-sans-cjk', name)) for name, family in CJK_SLICES]

def write_table(args, fonts, colourOnly):
    """The table: the fonts in order, then the colour slices, then Noto Emoji."""
    # What each font adds: its cmap less Noto Sans and the fonts before it.
    held = set(TTFont(os.path.join(FONTS, 'noto-sans', 'NotoSans-Regular.ttf'), lazy=True).getBestCmap())
    rows = []
    def row(directory, path, family, fields):
        data = open(path, 'rb').read()
        rows.append((directory, os.path.basename(path), family, len(data), hashlib.sha256(data).hexdigest(), fields))
        print(f'{family:34} {len(data):>9} bytes', file=sys.stderr)
    for directory, family, path in fonts:
        cmap = set(TTFont(path, lazy=True).getBestCmap())
        adds = {c for c in cmap - held if c > 0x20}
        held |= cmap
        row(directory, path, family, {'adds': adds})
    for directory, path, family, fields in colour_slices(args.cache, held):
        row(directory, path, family, fields)
    # Noto Emoji draws text presentation: a page with U+FE0E fetches it.
    row('noto-emoji', os.path.join(FONTS, 'noto-emoji', 'NotoEmoji-Regular.ttf'), 'Noto Emoji', {'adds': 'fe0e'})
    # Fonts of the CJK slices list blocks in the table; the characters they add are in
    # coverage.json, which the worker fetches only for a page with a character in a block.
    coverage = {}
    with open(TABLE, 'w') as f:
        f.write('// Generated by labs/demos/foafnaut/fallback_fonts.py: do not edit.\n')
        f.write('// The fonts after Noto Sans, in order. `adds` are the characters a font adds (hexadecimal\n')
        f.write('// code points and ranges): those that Noto Sans and the fonts before it lack. A font with\n')
        f.write('// `coverage` has them in that file, and `blocks` says when the file is needed. The colour\n')
        f.write('// emoji slices also have `vs16` (characters wanted only with U+FE0F after them), `needs`\n')
        f.write('// (ranges the page must also have, each of them) and `regional` (first letters of the\n')
        f.write('// regional indicator pairs of a flag slice).\n')
        f.write('export const fallbackFonts=[\n')
        for directory, name, family, size, sha, fields in rows:
            f.write(f"  {{path:'./fonts/{directory}/{name}',family:'{family}',bytes:{size},sha256:'{sha}',\n")
            adds = fields.get('adds', set())
            if directory == 'noto-sans-cjk' and 'Kana' not in name:
                coverage[family] = ranges(adds)
                f.write(f"   blocks:'{ranges(blocks(adds))}',coverage:'./fonts/noto-sans-cjk/coverage.json'}},\n")
            else:
                parts = [f"{k}:'{v if isinstance(v, str) else ranges(v)}'" for k, v in fields.items() if k != 'needs']
                if 'needs' in fields:
                    parts.append('needs:[' + ','.join(f"'{n}'" for n in fields['needs']) + ']')
                f.write('   ' + ','.join(parts) + '},\n')
        f.write('];\n')
    if colourOnly:
        return
    with open(os.path.join(FONTS, 'noto-sans-cjk', 'coverage.json'), 'w') as f:
        f.write('{\n' + ',\n'.join(f'"{k}":"{v}"' for k, v in coverage.items()) + '\n}\n')

if __name__ == '__main__':
    main()
