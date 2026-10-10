#!/usr/bin/env python3
"""Generate formal/lean4/L4Factoidal/Text/CaseMapData.lean from the Unicode
Character Database.

The tables describe Unicode default case mapping, which is what XPath and
XQuery Functions and Operators 3.1 section 5.4.7 and 5.4.8 (fn:upper-case,
fn:lower-case), SPARQL 1.1 section 17.4.3.8 and 17.4.3.9 (UCASE, LCASE) and
Java String.toUpperCase / toLowerCase with the root locale use.

Inputs, all from ONE pinned Unicode version (UNICODE_VERSION below):

  UnicodeData.txt            simple upper, lower mappings (fields 12 and 13)
  SpecialCasing.txt          unconditional full mappings (lines with no
                             condition column); the one language-independent
                             conditional line, Final_Sigma, is applied by the
                             algorithm in CaseMap.lean, not by a table
  CaseFolding.txt            simple case folding, statuses C and S
  DerivedCoreProperties.txt  the derived properties Cased and Case_Ignorable,
                             which the Final_Sigma context rule of Unicode
                             section 3.13 reads

Every input file is checked against the SHA-256 recorded below. A file that is
absent from --ucd-dir is downloaded from unicode.org first. The generated file
repeats the URLs and the digests in its header.

Usage (from the repository root):

    python3 tools/gen_casemap.py                  # write the generated file
    python3 tools/gen_casemap.py --check          # exit 1 if the file differs
    python3 tools/gen_casemap.py --ucd-dir DIR    # keep the UCD files in DIR

The generator uses the Python standard library only.
"""

import argparse
import hashlib
import os
import sys
import tempfile
import urllib.request

UNICODE_VERSION = "15.1.0"
BASE_URL = "https://www.unicode.org/Public/%s/ucd/" % UNICODE_VERSION

# File name -> SHA-256 of the file as published for UNICODE_VERSION.
PINNED = {
    "UnicodeData.txt":
        "2fc713e6a31a87c4850a37fe2caffa4218180fadb5de86b43a143ddb4581fb86",
    "SpecialCasing.txt":
        "55a477efd933a52cd27e6a9bf70265bb2d8814af31aab07767abc8eb421f27ef",
    "CaseFolding.txt":
        "4e55acfdc32825a22e87670e9056a3bf94ad7c5400065778e9e10f8314372bcf",
    "DerivedCoreProperties.txt":
        "f55d0db69123431a7317868725b1fcbf1eab6b265d756d1bd7f0f6d9f9ee108b",
}

DEFAULT_OUT = os.path.join(
    "formal", "lean4", "L4Factoidal", "Text", "CaseMapData.lean")


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def fetch(ucd_dir):
    """Make sure every pinned file is in ucd_dir with the pinned digest."""
    os.makedirs(ucd_dir, exist_ok=True)
    for name, want in PINNED.items():
        path = os.path.join(ucd_dir, name)
        if not os.path.exists(path):
            url = BASE_URL + name
            sys.stderr.write("fetching %s\n" % url)
            with urllib.request.urlopen(url, timeout=120) as r, \
                    open(path, "wb") as out:
                out.write(r.read())
        got = sha256_of(path)
        if got != want:
            sys.exit("%s: sha256 %s does not match the pinned %s"
                     % (path, got, want))


def data_lines(path):
    """Yield the fields of every non-comment line, split on ';'."""
    with open(path, encoding="utf-8") as f:
        for line in f:
            body = line.split("#", 1)[0].strip()
            if body:
                yield [x.strip() for x in body.split(";")]


def parse_unicode_data(path):
    upper, lower = {}, {}
    for f in data_lines(path):
        cp = int(f[0], 16)
        # The "<..., First>" / "<..., Last>" range lines carry no mapping.
        if f[12]:
            upper[cp] = int(f[12], 16)
        if f[13]:
            lower[cp] = int(f[13], 16)
    return upper, lower


def parse_special_casing(path):
    """Unconditional full mappings, and the list of conditional lines."""
    full_upper, full_lower, conditional = {}, {}, []
    for f in data_lines(path):
        cp = int(f[0], 16)
        lo = [int(x, 16) for x in f[1].split()]
        up = [int(x, 16) for x in f[3].split()]
        cond = f[4] if len(f) > 4 else ""
        if cond:
            conditional.append((cp, cond))
        else:
            full_upper[cp] = up
            full_lower[cp] = lo
    return full_upper, full_lower, conditional


def parse_case_folding(path):
    fold = {}
    for f in data_lines(path):
        if f[1] in ("C", "S"):
            fold[int(f[0], 16)] = int(f[2], 16)
    return fold


def parse_property(path, prop):
    """Sorted, merged (lo, hi) ranges of one derived property."""
    ranges = []
    for f in data_lines(path):
        if f[1] != prop:
            continue
        span = f[0].split("..")
        lo = int(span[0], 16)
        hi = int(span[-1], 16)
        ranges.append((lo, hi))
    ranges.sort()
    merged = []
    for lo, hi in ranges:
        if merged and lo <= merged[-1][1] + 1:
            merged[-1] = (merged[-1][0], max(merged[-1][1], hi))
        else:
            merged.append((lo, hi))
    return merged


def compress(mapping):
    """Group a code point -> code point mapping into stride runs.

    A run is (lo, hi, stride, delta): the keys lo, lo+stride, ..., hi all map
    to key + delta. Runs are made from consecutive keys in sorted order, so
    their spans are disjoint and sorted by lo.
    """
    keys = sorted(mapping)
    runs = []
    i = 0
    while i < len(keys):
        k0 = keys[i]
        delta = mapping[k0] - k0
        stride = 1
        j = i
        if i + 1 < len(keys):
            k1 = keys[i + 1]
            if mapping[k1] - k1 == delta and k1 - k0 in (1, 2):
                stride = k1 - k0
                j = i + 1
                while (j + 1 < len(keys)
                       and keys[j + 1] - keys[j] == stride
                       and mapping[keys[j + 1]] - keys[j + 1] == delta):
                    j += 1
        runs.append((k0, keys[j], stride, delta))
        i = j + 1
    # Self-check: the runs expand back to exactly the input mapping.
    back = {}
    for lo, hi, stride, delta in runs:
        for k in range(lo, hi + 1, stride):
            back[k] = k + delta
    assert back == mapping, "compress: runs do not reproduce the mapping"
    return runs


def hexlist(cps):
    return "[" + ", ".join("0x%X" % c for c in cps) + "]"


def render(files, upper, lower, full_upper, full_lower, conditional, fold,
           cased, ignorable):
    # Entries of SpecialCasing that differ from the simple mapping. The
    # simple tables answer for every other code point.
    special_upper = {}
    for cp, up in sorted(full_upper.items()):
        simple = [upper.get(cp, cp)]
        if up != simple:
            special_upper[cp] = up
    special_lower = {}
    for cp, lo in sorted(full_lower.items()):
        simple = [lower.get(cp, cp)]
        if lo != simple:
            special_lower[cp] = lo

    # The only conditional lines that are not language-specific are the
    # Final_Sigma lines. They are applied by the algorithm. Any other
    # condition without a language tag would need new code, so stop.
    langs = {"lt", "tr", "az"}
    for cp, cond in conditional:
        words = cond.split()
        if words[0] in langs:
            continue
        if cond != "Final_Sigma" or cp != 0x3A3:
            sys.exit("unhandled SpecialCasing condition %r on U+%04X"
                     % (cond, cp))

    up_runs = compress(upper)
    lo_runs = compress(lower)
    fold_runs = compress(fold)

    out = []
    w = out.append
    w("/-")
    w("L4Factoidal.Text.CaseMapData -- GENERATED. Do not edit by hand.")
    w("")
    w("Generator: tools/gen_casemap.py. Regenerate with")
    w("")
    w("    python3 tools/gen_casemap.py")
    w("")
    w("and check that the committed file is current with")
    w("")
    w("    python3 tools/gen_casemap.py --check")
    w("")
    w("Unicode version: %s." % UNICODE_VERSION)
    w("")
    w("Source files (Unicode Character Database), with SHA-256:")
    w("")
    for name in PINNED:
        w("  %s%s" % (BASE_URL, name))
        w("    sha256 %s" % files[name])
    w("")
    w("What the tables hold:")
    w("")
    w("  upperRanges, lowerRanges  simple case mappings of UnicodeData.txt,")
    w("                            fields 12 and 13 (%d and %d code points)."
      % (len(upper), len(lower)))
    w("  specialUpper, specialLower")
    w("                            the unconditional full mappings of")
    w("                            SpecialCasing.txt that differ from the simple")
    w("                            mapping (%d and %d code points)."
      % (len(special_upper), len(special_lower)))
    w("  foldRanges                simple case folding, CaseFolding.txt statuses")
    w("                            C and S (%d code points)." % len(fold))
    w("  casedRanges, caseIgnorableRanges")
    w("                            the derived properties Cased and")
    w("                            Case_Ignorable of DerivedCoreProperties.txt.")
    w("")
    w("SpecialCasing.txt conditional lines that this file leaves out, and why:")
    w("the language-specific ones (lt, tr, az) because the mappings here are")
    w("language-independent; the Final_Sigma line because it is a context rule")
    w("that CaseMap.lean applies by algorithm (Unicode section 3.13).")
    w("-/")
    w("")
    w("namespace L4Factoidal.Text.CaseMapData")
    w("")
    w('/-- The Unicode version every table below was generated from. -/')
    w('def unicodeVersion : String := "%s"' % UNICODE_VERSION)
    w("")
    w("/-- A run of one-to-one mappings: every code point `lo`, `lo + stride`,")
    w("..., `hi` maps to itself plus `delta`. Runs are sorted by `lo` and their")
    w("spans are disjoint. -/")
    w("structure MapRange where")
    w("  lo : Nat")
    w("  hi : Nat")
    w("  stride : Nat")
    w("  delta : Int")
    w("")

    def ranges_def(name, doc, runs):
        w("/-- %s (%d runs). -/" % (doc, len(runs)))
        w("def %s : Array MapRange := #[" % name)
        for n, (lo, hi, stride, delta) in enumerate(runs):
            sep = "," if n + 1 < len(runs) else ""
            w("  ⟨0x%X, 0x%X, %d, %d⟩%s" % (lo, hi, stride, delta, sep))
        w("]")
        w("")

    ranges_def("upperRanges",
               "Simple uppercase mapping, UnicodeData.txt field 12", up_runs)
    ranges_def("lowerRanges",
               "Simple lowercase mapping, UnicodeData.txt field 13", lo_runs)
    ranges_def("foldRanges",
               "Simple case folding, CaseFolding.txt statuses C and S",
               fold_runs)

    def special_def(name, doc, table):
        w("/-- %s (%d code points, sorted). -/" % (doc, len(table)))
        w("def %s : Array (Nat × List Nat) := #[" % name)
        items = sorted(table.items())
        for n, (cp, cps) in enumerate(items):
            sep = "," if n + 1 < len(items) else ""
            w("  (0x%X, %s)%s" % (cp, hexlist(cps), sep))
        w("]")
        w("")

    special_def("specialUpper",
                "Unconditional full uppercase mappings that differ from the"
                " simple one, SpecialCasing.txt", special_upper)
    special_def("specialLower",
                "Unconditional full lowercase mappings that differ from the"
                " simple one, SpecialCasing.txt", special_lower)

    def prop_def(name, doc, rs):
        w("/-- %s (%d ranges, sorted and disjoint). -/" % (doc, len(rs)))
        w("def %s : Array (Nat × Nat) := #[" % name)
        for n, (lo, hi) in enumerate(rs):
            sep = "," if n + 1 < len(rs) else ""
            w("  (0x%X, 0x%X)%s" % (lo, hi, sep))
        w("]")
        w("")

    prop_def("casedRanges",
             "Derived property Cased, DerivedCoreProperties.txt", cased)
    prop_def("caseIgnorableRanges",
             "Derived property Case_Ignorable, DerivedCoreProperties.txt",
             ignorable)

    w("end L4Factoidal.Text.CaseMapData")
    return "\n".join(out) + "\n"


def build(ucd_dir):
    fetch(ucd_dir)
    files = {name: sha256_of(os.path.join(ucd_dir, name)) for name in PINNED}
    upper, lower = parse_unicode_data(os.path.join(ucd_dir, "UnicodeData.txt"))
    full_upper, full_lower, conditional = parse_special_casing(
        os.path.join(ucd_dir, "SpecialCasing.txt"))
    fold = parse_case_folding(os.path.join(ucd_dir, "CaseFolding.txt"))
    dcp = os.path.join(ucd_dir, "DerivedCoreProperties.txt")
    cased = parse_property(dcp, "Cased")
    ignorable = parse_property(dcp, "Case_Ignorable")
    return render(files, upper, lower, full_upper, full_lower, conditional,
                  fold, cased, ignorable)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--ucd-dir",
                    help="directory holding (or receiving) the UCD files")
    ap.add_argument("--out", default=DEFAULT_OUT, help="output file")
    ap.add_argument("--check", action="store_true",
                    help="compare with the existing output file; write nothing")
    args = ap.parse_args()

    tmp = None
    ucd_dir = args.ucd_dir
    if ucd_dir is None:
        tmp = tempfile.TemporaryDirectory(prefix="ucd-%s-" % UNICODE_VERSION)
        ucd_dir = tmp.name
    text = build(ucd_dir)

    if args.check:
        with open(args.out, encoding="utf-8") as f:
            have = f.read()
        if have != text:
            sys.exit("%s is not what tools/gen_casemap.py generates" % args.out)
        print("%s is current" % args.out)
    else:
        os.makedirs(os.path.dirname(args.out), exist_ok=True)
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text)
        print("wrote %s" % args.out)


if __name__ == "__main__":
    main()
