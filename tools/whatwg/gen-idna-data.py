#!/usr/bin/env python3
"""Write formal/lean4/L4Factoidal/WHATWG/URL/IdnaData.lean from the vendored
Unicode 18.0.0 files in third_party/unicode-18.0.0/ (provenance there).

Tables written (each a sorted list of code point ranges, as text that the Lean
module reads once):

  idnaText    IdnaMappingTable.txt (UTS #46 section 5): status v valid,
              d deviation, m mapped, i ignored, x disallowed; a mapped range
              carries its mapping as hex code points
  bidiText    DerivedBidiClass.txt with its @missing defaults; ranges whose
              class is not L
  joinText    DerivedJoiningType.txt; ranges whose type is not U
  markText    DerivedGeneralCategory.txt; ranges of Mn, Mc, Me
  viramaText  DerivedCombiningClass.txt; code points of class 9 (Virama)

  --check     exit 1 when the Lean file differs from what this script writes

https://github.com/danbri/factoidal/issues/1167, milestone 3.
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "third_party", "unicode-18.0.0")
OUT = os.path.join(ROOT, "formal", "lean4", "L4Factoidal", "WHATWG", "URL", "IdnaData.lean")

BIDI_LONG = {
    "Left_To_Right": "L", "Right_To_Left": "R", "Arabic_Letter": "AL",
    "European_Number": "EN", "European_Separator": "ES", "European_Terminator": "ET",
    "Arabic_Number": "AN", "Common_Separator": "CS", "Nonspacing_Mark": "NSM",
    "Boundary_Neutral": "BN", "Paragraph_Separator": "B", "Segment_Separator": "S",
    "White_Space": "WS", "Other_Neutral": "ON", "Left_To_Right_Embedding": "LRE",
    "Left_To_Right_Override": "LRO", "Right_To_Left_Embedding": "RLE",
    "Right_To_Left_Override": "RLO", "Pop_Directional_Format": "PDF",
    "Left_To_Right_Isolate": "LRI", "Right_To_Left_Isolate": "RLI",
    "First_Strong_Isolate": "FSI", "Pop_Directional_Isolate": "PDI",
}


def rng(field):
    field = field.strip()
    if ".." in field:
        a, b = field.split("..")
        return int(a, 16), int(b, 16)
    return int(field, 16), int(field, 16)


def data_lines(name):
    with open(os.path.join(SRC, name), encoding="utf-8") as fh:
        for line in fh:
            body = line.split("#", 1)[0].strip()
            if body:
                yield [f.strip() for f in body.split(";")]


def merge(ranges):
    """Merge adjacent ranges with equal values; input sorted by start."""
    out = []
    for a, b, v in ranges:
        if out and out[-1][1] + 1 == a and out[-1][2] == v:
            out[-1] = (out[-1][0], b, v)
        else:
            out.append((a, b, v))
    return out


def idna_table():
    code = {"valid": "v", "deviation": "d", "mapped": "m", "ignored": "i", "disallowed": "x"}
    rows = []
    for f in data_lines("IdnaMappingTable.txt"):
        a, b = rng(f[0])
        status = code[f[1]]
        mapping = ""
        if status == "m" or (status == "d" and len(f) > 2 and f[2]):
            mapping = " ".join(x for x in f[2].split() if x) if len(f) > 2 else ""
        rows.append((a, b, status + (":" + mapping if mapping else "")))
    rows.sort()
    # A mapped range maps each code point to the same sequence, so equal
    # neighbours can merge only when the value has no mapping.
    out = []
    for a, b, v in rows:
        if out and out[-1][1] + 1 == a and out[-1][2] == v and ":" not in v:
            out[-1] = (out[-1][0], b, v)
        else:
            out.append((a, b, v))
    return out


def bidi_table():
    cls = {}
    with open(os.path.join(SRC, "DerivedBidiClass.txt"), encoding="utf-8") as fh:
        missing = []
        for line in fh:
            if line.startswith("# @missing:"):
                body = line[len("# @missing:"):].strip()
                r, v = body.split(";")
                missing.append((rng(r), BIDI_LONG[v.strip()]))
    explicit = [(rng(f[0]), f[1]) for f in data_lines("DerivedBidiClass.txt")]
    arr = bytearray(0x110000)
    names = sorted(set(BIDI_LONG.values()))
    idx = {n: i for i, n in enumerate(names)}
    for (a, b), v in missing + explicit:
        for c in range(a, b + 1):
            arr[c] = idx[v]
    out = []
    start = 0
    for c in range(1, 0x110001):
        if c == 0x110000 or arr[c] != arr[start]:
            v = names[arr[start]]
            if v != "L":
                out.append((start, c - 1, v))
            start = c
    return out


def simple_table(name, keep):
    rows = []
    for f in data_lines(name):
        a, b = rng(f[0])
        if keep(f[1]):
            rows.append((a, b, f[1]))
    rows.sort()
    return merge(rows)


def text_of(rows, with_value=True):
    def one(a, b, v):
        r = "%X" % a if a == b else "%X-%X" % (a, b)
        return r + (":" + v if with_value else "")
    return [one(*r) for r in rows]


def lean_string(name, doc, items, chunk=120):
    lines = ["/-- %s -/" % doc, "def %s : String := String.join [" % name]
    for i in range(0, len(items), chunk):
        part = ";".join(items[i:i + chunk]) + ";"
        lines.append('  "%s",' % part)
    if lines[-1].endswith(","):
        lines[-1] = lines[-1][:-1]
    lines.append("  ]")
    return "\n".join(lines)


def render():
    idna = idna_table()
    bidi = bidi_table()
    join = simple_table("DerivedJoiningType.txt", lambda v: v != "U")
    mark = simple_table("DerivedGeneralCategory.txt", lambda v: v in ("Mn", "Mc", "Me"))
    mark = merge([(a, b, "M") for a, b, _ in mark])
    virama = simple_table("DerivedCombiningClass.txt", lambda v: v == "9")
    parts = [
        "/-",
        "L4Factoidal.WHATWG.URL.IdnaData — generated by tools/whatwg/gen-idna-data.py",
        "from the Unicode Character Database 18.0.0 and the UTS #46 data of the same",
        "version (third_party/unicode-18.0.0/: IdnaMappingTable.txt,",
        "DerivedBidiClass.txt, DerivedJoiningType.txt, DerivedGeneralCategory.txt,",
        "DerivedCombiningClass.txt). Do not edit by hand.",
        "-/",
        "namespace L4Factoidal.WHATWG.URL.IdnaData",
        "",
        lean_string("idnaText", "UTS #46 IdnaMappingTable (18.0.0): `RANGE:STATUS[:MAPPING];` with "
                    "STATUS v valid, d deviation, m mapped, i ignored, x disallowed.", text_of(idna)),
        "",
        lean_string("bidiText", "Bidi_Class (18.0.0, @missing defaults applied): `RANGE:CLASS;` "
                    "for every range whose class is not L.", text_of(bidi)),
        "",
        lean_string("joinText", "Joining_Type (18.0.0): `RANGE:TYPE;` for every range whose type "
                    "is not U.", text_of(join)),
        "",
        lean_string("markText", "General_Category Mn, Mc or Me (18.0.0): `RANGE;`.",
                    text_of(mark, False)),
        "",
        lean_string("viramaText", "Canonical_Combining_Class 9, Virama (18.0.0): `RANGE;`.",
                    text_of(virama, False)),
        "",
        "end L4Factoidal.WHATWG.URL.IdnaData",
        "",
    ]
    return "\n".join(parts)


def main():
    text = render()
    if "--check" in sys.argv[1:]:
        with open(OUT, encoding="utf-8") as fh:
            if fh.read() != text:
                print("gen-idna-data: %s is stale; run tools/whatwg/gen-idna-data.py" % OUT,
                      file=sys.stderr)
                sys.exit(1)
        print("gen-idna-data: up to date")
        return
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write(text)
    print("gen-idna-data: wrote %s (%d bytes)" % (OUT, len(text)))


if __name__ == "__main__":
    main()
