#!/usr/bin/env python3
"""Independent count of the SBM11 dictionary of an N-Triples file.

https://github.com/danbri/factoidal/issues/788. Reads an N-Triples file with
a regular expression (not the Lean parser), applies the SBM11 rules of
`L4Factoidal/Storage/Sbm11/TermId.lean` and `TermKey.lean`:

  * a language tag is folded to lower case;
  * a literal with no datatype is an xsd:string literal;
  * a literal is INLINE (no dictionary entry) when it is xsd:boolean with
    lexical form "true" or "false", or one of the 13 integer datatypes with
    the canonical lexical form of a value inside the datatype's value space
    and inside [-2^55, 2^55);

and prints the number of distinct dictionary terms and of distinct inline
terms. `l4sbm11-dict-pack` must report the same `terms=`, and its `--check`
the same `distinct-inline-terms=`.

Usage: dict_reference.py FILE.nt
"""
import re
import sys

XSD = "http://www.w3.org/2001/XMLSchema#"
INT_TYPES = {
    "integer": (None, None), "long": (-2**63, 2**63 - 1), "int": (-2**31, 2**31 - 1),
    "short": (-32768, 32767), "byte": (-128, 127), "nonNegativeInteger": (0, None),
    "positiveInteger": (1, None), "nonPositiveInteger": (None, 0),
    "negativeInteger": (None, -1), "unsignedLong": (0, 2**64 - 1),
    "unsignedInt": (0, 2**32 - 1), "unsignedShort": (0, 65535), "unsignedByte": (0, 255),
}
INT_TYPES = {XSD + k: v for k, v in INT_TYPES.items()}
BIAS = 2**55

TERM = re.compile(
    r'\s*(<[^>]*>|_:[^\s]+|"(?:[^"\\]|\\.)*"(?:@[A-Za-z0-9\-]+|\^\^<[^>]*>)?)')
ESC = re.compile(r'\\(u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8}|.)')
SIMPLE = {"t": "\t", "b": "\b", "n": "\n", "r": "\r", "f": "\f", '"': '"', "'": "'", "\\": "\\"}


def unescape(s):
    def one(m):
        e = m.group(1)
        if e[0] in "uU":
            return chr(int(e[1:], 16))
        return SIMPLE.get(e, e)
    return ESC.sub(one, s)


def canonical_int(lex):
    if not re.fullmatch(r"[+-]?[0-9]+", lex):
        return None
    v = int(lex)
    return v if str(v) == lex else None


def classify(tok):
    """('dict', key) or ('inline', key)."""
    if tok.startswith("<"):
        return "dict", ("iri", unescape(tok[1:-1]))
    if tok.startswith("_:"):
        return "dict", ("bnode", tok[2:])
    m = re.fullmatch(r'"((?:[^"\\]|\\.)*)"(?:@([A-Za-z0-9\-]+)|\^\^<([^>]*)>)?', tok, re.S)
    lex = unescape(m.group(1))
    if m.group(2) is not None:
        return "dict", ("lang", lex, m.group(2).lower())
    dt = m.group(3) or XSD + "string"
    if dt == XSD + "boolean" and lex in ("true", "false"):
        return "inline", ("bool", lex)
    if dt in INT_TYPES:
        v = canonical_int(lex)
        if v is not None:
            lo, hi = INT_TYPES[dt]
            if (lo is None or v >= lo) and (hi is None or v <= hi) and -BIAS <= v < BIAS:
                return "inline", ("int", dt, v)
    return "dict", ("lit", lex, dt)


def main():
    dict_terms, inline_terms = set(), set()
    with open(sys.argv[1], encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            pos = 0
            for _ in range(4):
                m = TERM.match(line, pos)
                if not m:
                    break
                kind, key = classify(m.group(1))
                (dict_terms if kind == "dict" else inline_terms).add(key)
                pos = m.end()
    print(f"reference: distinct-dictionary-terms={len(dict_terms)} distinct-inline-terms={len(inline_terms)}")


if __name__ == "__main__":
    main()
