#!/usr/bin/env python3
"""Deterministic N-Quads, N-Triples and Turtle inputs for the lenient-parse
size ladder (https://github.com/danbri/factoidal/issues/716).

Each output has `--statements` statements. With `--error-every K` (K > 0),
every K-th statement is replaced by a malformed one, so errors are spread
evenly through the input; the kind of error rotates over: a missing object,
an undefined prefix (Turtle only; an unterminated IRI elsewhere), a bad
string escape, a bad language tag, a literal used as a subject. Every
malformed statement fails on its own line (N-Triples, N-Quads) or ends at a
`.` followed by a line break (Turtle), so each one is exactly one diagnostic
in lenient mode.

The generator prints one JSON line to stdout: the path, byte count, number of
statements, number of malformed statements, and the number of triples or
quads a correct lenient parse keeps.

    python3 tools/lenient-ladder-gen.py --format nquads --statements 1000000 \
        --error-every 1000 --output /tmp/ladder/nq-1m.nq
"""

import argparse
import json
from pathlib import Path

XSD = "http://www.w3.org/2001/XMLSchema#"


def good_terms(i: int):
    """Subject, predicate, object (N-Triples syntax) for statement `i`."""
    s = f"<http://example.org/s/{i // 7}>" if i % 5 else f"_:b{i // 11}"
    p = f"<http://example.org/p/{i % 13}>"
    k = i % 6
    if k == 0:
        o = f"<http://example.org/o/{(i * 31) % 100003}>"
    elif k == 1:
        o = f"\"label {i} with a \\\"quote\\\" and a tab\\t.\"@en"
    elif k == 2:
        o = f"\"{i}\"^^<{XSD}integer>"
    elif k == 3:
        o = f"\"café {i}\"@fr-CA"
    elif k == 4:
        o = f"_:b{(i * 3) // 11}"
    else:
        o = f"\"plain {i} \\u00e9\\U0001F600\""
    return s, p, o


def bad_line(i: int, fmt: str) -> str:
    """A malformed statement, one per line, terminated like a good one."""
    k = (i // 1) % 5
    if k == 0:  # missing object
        return f"<http://example.org/s/{i}> <http://example.org/p/x> ."
    if k == 1:
        if fmt == "turtle":  # undefined prefix
            return f"undefined:s{i} <http://example.org/p/x> <http://example.org/o/x> ."
        return f"<http://example.org/s/{i} <http://example.org/p/x> <http://example.org/o/x> ."
    if k == 2:  # bad string escape
        return f"<http://example.org/s/{i}> <http://example.org/p/x> \"bad \\q escape\" ."
    if k == 3:  # bad language tag
        return f"<http://example.org/s/{i}> <http://example.org/p/x> \"x\"@1bad ."
    # a literal as a subject
    return f"\"lit\" <http://example.org/p/x> <http://example.org/o/{i}> ."


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--format", choices=["nquads", "ntriples", "turtle"], required=True)
    ap.add_argument("--statements", type=int, required=True)
    ap.add_argument("--error-every", type=int, default=0)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    bad = 0
    kept = 0
    with out.open("w", encoding="utf-8", newline="\n") as h:
        if args.format == "turtle":
            h.write("@prefix ex: <http://example.org/> .\n")
            h.write("PREFIX exo: <http://example.org/o/>\n")
        for i in range(args.statements):
            if args.error_every > 0 and i % args.error_every == args.error_every - 1:
                h.write(bad_line(i, args.format) + "\n")
                bad += 1
                continue
            s, p, o = good_terms(i)
            if args.format == "nquads":
                g = "" if i % 3 == 0 else f" <http://example.org/g/{i % 17}>"
                h.write(f"{s} {p} {o}{g} .\n")
            elif args.format == "ntriples":
                h.write(f"{s} {p} {o} .\n")
            else:
                # Turtle: prefixed names, an object list, a predicate list.
                if i % 4 == 0:
                    h.write(f"{s} ex:p{i % 13} {o} , exo:x{i % 101} ;\n    a ex:T{i % 7} .\n")
                    kept += 2
                else:
                    h.write(f"{s} {p} {o} .\n")
            kept += 1
    print(json.dumps({"path": str(out), "bytes": out.stat().st_size,
                      "statements": args.statements, "malformed": bad,
                      "kept": kept}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
