#!/usr/bin/env python3
"""Make WOFF2 files from the fonts in third_party/fonts with fontTools, for the WOFF2 reader
(formal/lean4/L4Factoidal/Rendering/Woff2.lean), and compare its output with fontTools.

    pip install fonttools brotli
    python3 tools/fonts/woff2_vectors.py make <out-dir>
        writes <name>.woff2 for every font and transform set, and <name>.src naming the source
    python3 tools/fonts/woff2_vectors.py compare <out-dir>
        for every <name>.woff2 with a <name>.ttf beside it (the sfnt the Lean reader made):
        every table other than glyf, loca, hmtx and head byte-equal to the source font; head
        equal but for checkSumAdjustment; hmtx equal to the source; every glyph equal to the
        source glyph as fontTools reads it (contours, flags, coordinates, components,
        instructions, bounding box); and the checksums of the sfnt valid.
"""
import os
import struct
import sys

from fontTools.ttLib import TTFont
from fontTools.ttLib import woff2

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
FONTS = os.path.join(ROOT, "third_party", "fonts")
SOURCES = [
    "fruktur/Fruktur-Regular.ttf",
    "noto-sans/NotoSans-Regular.ttf",
    "liberation-mono/LiberationMono-Regular.ttf",
    "liberation-serif/LiberationSerif-Regular.ttf",
    "noto-sans-arabic/NotoSansArabic-Regular.ttf",
    "noto-sans-hebrew/NotoSansHebrew-Regular.ttf",
    "noto-sans-thai/NotoSansThai-Regular.ttf",
    "noto-sans-armenian/NotoSansArmenian-Regular.ttf",
    "noto-sans-math/NotoSansMath-Regular.ttf",
    "noto-emoji/NotoEmoji-Regular.ttf",
    "noto-color-emoji/NotoColorEmoji-Flags.ttf",
    "noto-sans-cjk/NotoSansJP-Kana.otf",
]
TRANSFORMS = {
    "plain": set(),
    "glyf": {"glyf", "loca"},
    "hmtx": {"glyf", "loca", "hmtx"},
}


def make(out):
    os.makedirs(out, exist_ok=True)
    for rel in SOURCES:
        src = os.path.join(FONTS, rel)
        base = os.path.splitext(os.path.basename(rel))[0]
        cff = rel.endswith(".otf")
        for tname, tset in TRANSFORMS.items():
            if cff and tname != "plain":
                continue  # a CFF font has no glyf, loca or (transformable) hmtx
            name = "%s-%s" % (base, tname)
            dst = os.path.join(out, name + ".woff2")
            woff2.compress(src, dst, transform_tables=tset)
            with open(os.path.join(out, name + ".src"), "w") as f:
                f.write(rel + "\n")


def ulong_sum(b):
    b = b + b"\0" * ((4 - len(b) % 4) % 4)
    return sum(struct.unpack(">%dI" % (len(b) // 4), b)) & 0xFFFFFFFF


def glyph_key(font, name):
    g = font["glyf"][name]
    if g.numberOfContours == 0:
        return ("empty",)
    g.expand(font["glyf"])
    if g.isComposite():
        comps = []
        for c in g.components:
            comps.append((c.glyphName, c.flags & ~0x0200, getattr(c, "x", None), getattr(c, "y", None),
                          getattr(c, "transform", None) and tuple(map(tuple, c.transform))))
        prog = g.program.getBytecode() if hasattr(g, "program") else b""
        return ("composite", tuple(comps), prog, (g.xMin, g.yMin, g.xMax, g.yMax))
    coords = tuple(map(tuple, g.coordinates))
    flags = tuple(f & 0x41 for f in g.flags)  # on-curve and OVERLAP_SIMPLE
    prog = g.program.getBytecode() if hasattr(g, "program") else b""
    return ("simple", tuple(g.endPtsOfContours), coords, flags, prog, (g.xMin, g.yMin, g.xMax, g.yMax))


def compare(out):
    bad = 0
    n = 0
    for fn in sorted(os.listdir(out)):
        if not fn.endswith(".woff2"):
            continue
        name = fn[:-6]
        ttf = os.path.join(out, name + ".ttf")
        if not os.path.exists(ttf):
            continue
        n += 1
        rel = open(os.path.join(out, name + ".src")).read().strip()
        a = TTFont(os.path.join(FONTS, rel))
        data = open(ttf, "rb").read()
        b = TTFont(ttf)
        problems = []
        # checksums: each table record and the whole font
        num = struct.unpack(">H", data[4:6])[0]
        for i in range(num):
            tag, cs, off, ln = struct.unpack(">4sIII", data[12 + 16 * i:28 + 16 * i])
            t = bytearray(data[off:off + ln])
            if tag == b"head":
                t[8:12] = b"\0\0\0\0"
            if ulong_sum(bytes(t)) != cs:
                problems.append("checksum of %s" % tag)
        if "head" in b and ulong_sum(data) != 0xB1B0AFBA:
            problems.append("head checkSumAdjustment")
        if sorted(a.keys()) != sorted(b.keys()):
            problems.append("tables differ")
        for tag in a.keys():
            if tag in ("GlyphOrder", "glyf", "loca"):
                continue
            ra = a.reader[tag]
            rb = b.reader[tag]
            if tag == "head":
                # checkSumAdjustment differs; the encoder sets flags bit 11 (§5: "font data
                # has been subject to lossless modifying transform")
                ra = ra[:8] + ra[12:16] + bytes([ra[16] & 0xF7]) + ra[17:]
                rb = rb[:8] + rb[12:16] + bytes([rb[16] & 0xF7]) + rb[17:]
            if ra != rb:
                problems.append("table %s differs" % tag)
        if "glyf" in a:
            order = a.getGlyphOrder()
            diff = [g for g in order if glyph_key(a, g) != glyph_key(b, g)]
            if diff:
                problems.append("%d glyphs differ, first %s" % (len(diff), diff[0]))
        if problems:
            bad += 1
            print("FAIL", name, "; ".join(problems))
        else:
            print("ok", name)
    print("%d compared, %d failed" % (n, bad))
    return 1 if bad else 0


if __name__ == "__main__":
    if sys.argv[1] == "make":
        make(sys.argv[2])
    else:
        sys.exit(compare(sys.argv[2]))
