#!/usr/bin/env python3
"""Refresh the glyph table in the "Combinations" XSLT stylesheets of foafnaut.

    python3 labs/demos/foafnaut/tools/combination-pages.py

The engine does not draw SVG <text> yet (https://github.com/danbri/factoidal/issues/1270).
The combination pages label their SVG with XSLT: each stylesheet holds a table of glyph
outlines and advance widths, and the XSLT function ty:text sets a string as one SVG <path>
for each character. Lean runs that XSLT and draws the paths. This script writes the
table, between the comments "typeset:begin" and "typeset:end", into each stylesheet
named below. The outlines come from the bundled Noto Sans Regular and Noto Sans Armenian
Regular (SIL Open Font Licence 1.1, third_party/fonts/). There is no kerning and no
shaping: one glyph for each character, placed by its advance width.
Requires fontTools (pip install fonttools); it is not needed to view or test the pages.
"""
import os, re

from fontTools.ttLib import TTFont
from fontTools.pens.svgPathPen import SVGPathPen

LAB = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
PAGES = os.path.join(LAB, 'pages')
FONTS = os.path.join(LAB, '../../../third_party/fonts')
FACES = [TTFont(os.path.join(FONTS, 'noto-sans/NotoSans-Regular.ttf')),
         TTFont(os.path.join(FONTS, 'noto-sans-armenian/NotoSansArmenian-Regular.ttf'))]
# Each stylesheet and the data file whose characters it must set, besides printable ASCII.
SHEETS = {
    'foaf-people.xsl': 'foaf-people.xml',
    'engine-pipeline.xsl': 'engine-pipeline.xml',
    'lab-files.xsl': 'lab-files.xml',
    'feed.xsl': 'feed.xml',
    'sitemap.xsl': 'sitemap.xml',
    'typography-lab.xsl': 'typography-lab.xml',
    'sparql-results.xsl': 'sparql-results.xml',
}


def glyph(ch):
    """(advance, path) in font units (1000 an em, y up), from the first face that has ch."""
    for face in FACES:
        name = face.getBestCmap().get(ord(ch))
        if name is None:
            continue
        assert face['head'].unitsPerEm == 1000
        pen = SVGPathPen(face.getGlyphSet(), ntos=lambda v: str(round(v)))
        face.getGlyphSet()[name].draw(pen)
        return face['hmtx'][name][0], pen.getCommands()
    return None


def esc(s):
    # The table is a literal result tree: its attributes are value templates.
    return s.replace('&', '&amp;').replace('"', '&quot;').replace('<', '&lt;').replace('{', '{{').replace('}', '}}')


def table(chars):
    rows = []
    for ch in sorted(chars):
        found = glyph(ch)
        if found:
            rows.append(f'<ty:g c="{esc(ch)}" a="{found[0]}" d="{found[1]}"/>')
    return '\n'.join(rows)


for sheet, data in SHEETS.items():
    path = os.path.join(PAGES, sheet)
    text = open(path, encoding='utf-8').read()
    source = open(os.path.join(PAGES, data), encoding='utf-8').read()
    chars = {chr(c) for c in range(32, 127)} | {c for c in source if ord(c) > 126 and not c.isspace()}
    block = ('<!-- typeset:begin: written by tools/combination-pages.py; glyphs from Noto Sans, OFL 1.1 -->\n'
             f'<xsl:variable name="ty:font">\n{table(chars)}\n</xsl:variable>\n<!-- typeset:end -->')
    text, n = re.subn(r'<!-- typeset:begin.*?<!-- typeset:end -->', lambda _: block, text, flags=re.S)
    assert n == 1, sheet
    open(path, 'w', encoding='utf-8').write(text)
    print(f'{sheet}: {len(chars)} characters, {len(text)} bytes')
