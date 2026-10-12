#!/usr/bin/env python3
"""Write a synthetic N-Triples file of N lines with about 1.33 N distinct terms
(tests/sbm11/phase2_scaling.sh, https://github.com/danbri/factoidal/issues/804).

Line i: subject s<i>; predicate p<i mod 37>; object s<(i * 7919) mod N> (an
IRI that is also a subject elsewhere, so the same key occurs in many term
runs) or, for every third line, the literal "value <i>".

Usage: gen_distinct_terms.py N OUT.nt
"""
import sys


def main() -> int:
    n = int(sys.argv[1])
    out = sys.argv[2]
    with open(out, "w", encoding="utf-8") as fh:
        for i in range(n):
            if i % 3:
                obj = f"<http://example.org/s{(i * 7919) % n}>"
            else:
                obj = f'"value {i}"'
            fh.write(f"<http://example.org/s{i}> <http://example.org/p{i % 37}> {obj} .\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
