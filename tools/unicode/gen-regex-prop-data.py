#!/usr/bin/env python3
"""Generate formal/lean4/L4Factoidal/Unicode/RegexPropData.lean: the code points of the
properties a RegExp property escape `\\p{…}` names (ECMA-262 §22.2.2.9, tables
"Non-binary Unicode property aliases", "Value aliases" and "Binary Unicode property aliases"),
from the vendored Unicode 17.0.0 files in third_party/unicode-17.0.0:

- General_Category: extracted/DerivedGeneralCategory.txt (every value but Cn, which is the rest)
- Script: Scripts.txt
- Script_Extensions: ScriptExtensions.txt (the code points it lists, and per script the ones
  whose list names it; any other code point has Script_Extensions = {Script})
- the binary properties: PropList.txt, DerivedCoreProperties.txt, DerivedNormalizationProps.txt
  (Changes_When_NFKC_Casefolded), extracted/DerivedBinaryProperties.txt (Bidi_Mirrored),
  emoji/emoji-data.txt
- the names: PropertyAliases.txt, PropertyValueAliases.txt
- the properties of strings: emoji/emoji-sequences.txt, emoji/emoji-zwj-sequences.txt

    python3 tools/unicode/gen-regex-prop-data.py          rewrite the module
    python3 tools/unicode/gen-regex-prop-data.py --check  exit 1 if it differs

Each set is one string of ranges in hexadecimal, `lo` or `lo-hi`, comma-separated, sorted and
disjoint (read by `L4Factoidal.JS.Re.rangesText`). A string literal compiles in constant time.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
UCD = os.path.join(ROOT, 'third_party', 'unicode-17.0.0')
OUT = os.path.join(ROOT, 'formal', 'lean4', 'L4Factoidal', 'Unicode', 'RegexPropData.lean')


def rows(name):
    for line in open(os.path.join(UCD, name), encoding='utf-8'):
        line = line.split('#')[0].strip()
        if not line:
            continue
        f = [x.strip() for x in line.split(';')]
        r = f[0].split('..')
        yield int(r[0], 16), int(r[-1], 16), f[1:]


def ranges(cps):
    out = []
    for cp in sorted(cps):
        if out and out[-1][1] == cp - 1:
            out[-1][1] = cp
        else:
            out.append([cp, cp])
    return out


def text(cps):
    return ','.join('%X' % a if a == b else '%X-%X' % (a, b) for a, b in ranges(cps))


# The binary properties of ECMA-262 (table "Binary Unicode property aliases") but Any, ASCII and
# Assigned (computed), with their files.
BINARY = ['ASCII_Hex_Digit', 'Alphabetic', 'Bidi_Control', 'Bidi_Mirrored', 'Case_Ignorable', 'Cased',
          'Changes_When_Casefolded', 'Changes_When_Casemapped', 'Changes_When_Lowercased',
          'Changes_When_NFKC_Casefolded', 'Changes_When_Titlecased', 'Changes_When_Uppercased', 'Dash',
          'Default_Ignorable_Code_Point', 'Deprecated', 'Diacritic', 'Emoji', 'Emoji_Component',
          'Emoji_Modifier', 'Emoji_Modifier_Base', 'Emoji_Presentation', 'Extended_Pictographic', 'Extender',
          'Grapheme_Base', 'Grapheme_Extend', 'Hex_Digit', 'IDS_Binary_Operator', 'IDS_Trinary_Operator',
          'ID_Continue', 'ID_Start', 'Ideographic', 'Join_Control', 'Logical_Order_Exception', 'Lowercase',
          'Math', 'Noncharacter_Code_Point', 'Pattern_Syntax', 'Pattern_White_Space', 'Quotation_Mark',
          'Radical', 'Regional_Indicator', 'Sentence_Terminal', 'Soft_Dotted', 'Terminal_Punctuation',
          'Unified_Ideograph', 'Uppercase', 'Variation_Selector', 'White_Space', 'XID_Continue', 'XID_Start']
FILES = ['PropList.txt', 'DerivedCoreProperties.txt', 'DerivedNormalizationProps.txt',
         'DerivedBinaryProperties.txt', 'emoji-data.txt']

binary = {p: set() for p in BINARY}
for fn in FILES:
    for a, b, f in rows(fn):
        if f[0] in binary and len(f) == 1:
            binary[f[0]].update(range(a, b + 1))
for p in BINARY:
    if not binary[p]:
        raise SystemExit('no code points for %s' % p)

# Property and value aliases.
prop_alias = {}
for line in open(os.path.join(UCD, 'PropertyAliases.txt'), encoding='utf-8'):
    line = line.split('#')[0].strip()
    if line:
        f = [x.strip() for x in line.split(';')]
        # every other name of the property (the short name first, then e.g. `space`)
        prop_alias[f[1]] = ','.join([f[0]] + f[2:])
gc_alias, sc_alias = [], []   # (alias, canonical short)
for line in open(os.path.join(UCD, 'PropertyValueAliases.txt'), encoding='utf-8'):
    line = line.split('#')[0].strip()
    f = [x.strip() for x in line.split(';')]
    if len(f) >= 3 and f[0] in ('gc', 'sc'):
        dst = gc_alias if f[0] == 'gc' else sc_alias
        for al in f[1:]:
            if al and (al, f[1]) not in dst:
                dst.append((al, f[1]))

gc = {}
for a, b, f in rows('DerivedGeneralCategory.txt'):
    if f[0] != 'Cn':
        gc.setdefault(f[0], set()).update(range(a, b + 1))
GC = sorted(gc)

sc = {}
for a, b, f in rows('Scripts.txt'):
    sc.setdefault(f[0], set()).update(range(a, b + 1))
long_to_short = {}
for al, short in sc_alias:
    long_to_short.setdefault(al, short)

scx_listed, scx = set(), {}
for a, b, f in rows('ScriptExtensions.txt'):
    scx_listed.update(range(a, b + 1))
    for s in f[0].split():
        scx.setdefault(s, set()).update(range(a, b + 1))

def lean_str(s):
    return '"' + s + '"'

lines = [
    '/-',
    'L4Factoidal.Unicode.RegexPropData — generated by tools/unicode/gen-regex-prop-data.py from',
    'the Unicode Character Database 17.0.0 (DerivedGeneralCategory.txt, ScriptExtensions.txt,',
    'PropList.txt, DerivedCoreProperties.txt, DerivedNormalizationProps.txt,',
    'DerivedBinaryProperties.txt, emoji-data.txt, PropertyAliases.txt, PropertyValueAliases.txt,',
    'emoji-sequences.txt, emoji-zwj-sequences.txt).',
    'Do not edit by hand. Each set: hexadecimal ranges `lo` or `lo-hi`, comma-separated, sorted.',
    '-/',
    '',
    'namespace L4Factoidal.Unicode.RegexPropData',
    '',
    '/-- The binary properties (but Any, ASCII, Assigned): long name, its other names (comma-separated),',
    'code points. -/',
    'def binary : Array (String × String × String) := #[',
]
items = []
for p in BINARY:
    short = prop_alias.get(p, p)
    items.append('  (%s, %s, %s)' % (lean_str(p), lean_str(short), lean_str(text(binary[p]))))
lines.append(',\n'.join(items))
lines += [']', '',
          '/-- General_Category values (two-letter short names, Cn not listed): code points. -/',
          'def gc : Array (String × String) := #[']
lines.append(',\n'.join('  (%s, %s)' % (lean_str(k), lean_str(text(gc[k]))) for k in GC))
lines += [']', '',
          '/-- General_Category value aliases (PropertyValueAliases.txt): alias, short name. -/',
          'def gcAliases : Array (String × String) := #[' +
          ', '.join('(%s, %s)' % (lean_str(a), lean_str(s)) for a, s in gc_alias) + ']', '',
          '/-- Script value aliases: alias (long name, short name, other aliases), ISO 15924 code. -/',
          'def scAliases : Array (String × String) := #[' +
          ', '.join('(%s, %s)' % (lean_str(a), lean_str(s)) for a, s in sc_alias) + ']', '',
          '/-- Script values (ISO 15924 codes): code points. -/',
          'def sc : Array (String × String) := #[' ]
lines_sc = ',\n'.join('  (%s, %s)' % (lean_str(long_to_short[k]), lean_str(text(v))) for k, v in sorted(sc.items()))
lines += [lines_sc, ']', '',
          '/-- The code points ScriptExtensions.txt lists (their Script_Extensions is not {Script}). -/',
          'def scxListed : String := ' + lean_str(text(scx_listed)), '',
          '/-- Per script: the listed code points whose Script_Extensions names it. -/',
          'def scx : Array (String × String) := #[']
lines.append(',\n'.join('  (%s, %s)' % (lean_str(k), lean_str(text(scx[k]))) for k in sorted(scx)))
# The properties of strings (§22.2.2.9, table "Binary Unicode properties of strings"), from
# emoji-sequences.txt and emoji-zwj-sequences.txt: single code points as ranges, the sequences.
STRPROPS = ['Basic_Emoji', 'Emoji_Keycap_Sequence', 'RGI_Emoji_Modifier_Sequence', 'RGI_Emoji_Flag_Sequence',
            'RGI_Emoji_Tag_Sequence', 'RGI_Emoji_ZWJ_Sequence']
sp = {k: (set(), set()) for k in STRPROPS}
for fn in ('emoji-sequences.txt', 'emoji-zwj-sequences.txt'):
    for line in open(os.path.join(UCD, fn), encoding='utf-8'):
        line = line.split('#')[0].strip()
        if not line:
            continue
        f = [x.strip() for x in line.split(';')]
        if f[1] not in sp:
            raise SystemExit('%s: unknown type %r' % (fn, f[1]))
        if '..' in f[0]:
            a, b = f[0].split('..')
            sp[f[1]][0].update(range(int(a, 16), int(b, 16) + 1))
        else:
            cps = [int(x, 16) for x in f[0].split()]
            if len(cps) == 1:
                sp[f[1]][0].add(cps[0])
            else:
                sp[f[1]][1].add(' '.join('%X' % c for c in cps))
# RGI_Emoji is the union of the six (UTS #51 ED-27); the engine forms it, so it is not written twice.
lines += [']', '',
          '/-- The properties of strings: name, single code points, sequences (hexadecimal code points',
          'separated by spaces, the sequences by `;`). -/',
          'def stringProps : Array (String × String × String) := #[']
lines.append(',\n'.join('  (%s, %s, %s)' % (lean_str(k), lean_str(text(v[0])), lean_str(';'.join(sorted(v[1]))))
                        for k, v in sp.items()))
lines += [']', '', 'end L4Factoidal.Unicode.RegexPropData', '']
src = '\n'.join(lines)
if '--check' in sys.argv:
    cur = open(OUT, encoding='utf-8').read() if os.path.exists(OUT) else None
    sys.exit(0 if cur == src else 1)
open(OUT, 'w', encoding='utf-8').write(src)
print('%d binary properties, %d gc values, %d scx scripts, %d bytes' % (len(BINARY), len(GC), len(scx), len(src)))
