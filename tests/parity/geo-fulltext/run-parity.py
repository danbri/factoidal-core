#!/usr/bin/env python3
"""Parity check: the Lean engine against the F* engine on geof:distance,
geof:envelope and text:query.

Runs every query in queries/ against both command-line engines over the
same data file and compares the answers:

  * SELECT: the multiset of solution rows (SPARQL fixes no row order
    without ORDER BY, so rows are compared as multisets),
  * ASK: the boolean,
  * a parse error: both engines must refuse the query.

A query whose answers differ is a FAILURE unless it is listed in
EXPECTED_DIVERGENCE with its reason. A listed query whose answers now
agree is also a FAILURE (a stale entry), so the list cannot outlive the
difference it records.

Usage (from the repository root):
  python3 tests/parity/geo-fulltext/run-parity.py \
      --fstar bin/linux-x86_64/factoidal \
      --lean formal/lean4/.lake/build/bin/l4factoidal

Design record: docs/designissues/2026-10-10-lean-geo-distance-fulltext.md
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

ISSUE_FSTAR_FAST_PATHS = "https://github.com/danbri/factoidal/issues/774"

# query file -> reason. Every entry names WHY the engines differ.
EXPECTED_DIVERGENCE = {
    "ft-04-field-limit.rq":
        "limit with a field: F* keeps the LAST n matches in document order (its "
        "predicate index lists a predicate's triples newest first); Lean keeps the "
        "FIRST n. Slice 1 makes no ranking claim, so both are n matches.",
    "ft-13-ask.rq":
        "F* ASK ignores text:query and answers false: " + ISSUE_FSTAR_FAST_PATHS,
    "ft-15-count.rq":
        "F* streaming COUNT(*) ignores text:query and answers 0: " + ISSUE_FSTAR_FAST_PATHS,
    "ft-19-modifier-limit.rq":
        "F* LIMIT push-down ignores text:query and answers no rows: " + ISSUE_FSTAR_FAST_PATHS,
    "geo-07-distance-mixed-crs.rq":
        "CRS: F* treats a literal with no CRS IRI as compatible with ANY stated CRS "
        "(geo_crs_compatible), so it answers a distance between a CRS84 point and an "
        "EPSG:27700 point; Lean's sameCrs refuses that pair (no CRS transformation is done).",
    "geo-03-distance-units.rq":
        "F* has no three-argument geof:distance (every call is an error); Lean answers "
        "when the unit is the unit of geom1's CRS (degree for CRS84) and refuses metre "
        "(https://github.com/danbri/factoidal/issues/772).",
}


def run(cmd):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    return p.stdout + p.stderr


def term_key(t):
    return (t.get("type"), t.get("value"), t.get("datatype"), t.get("xml:lang"))


def normalise(out):
    s = out.strip()
    if "parse error" in s.lower():
        return ("error",)
    if s in ("true", "false"):
        return ("ask", s == "true")
    try:
        j = json.loads(s)
    except json.JSONDecodeError:
        return ("unreadable", s[:200])
    if "boolean" in j:
        return ("ask", bool(j["boolean"]))
    rows = []
    for b in j["results"]["bindings"]:
        # an unbound variable is absent from the row in both engines
        rows.append(tuple(sorted((v, term_key(t)) for v, t in b.items())))
    return ("select", tuple(sorted(rows)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fstar", required=True)
    ap.add_argument("--lean", required=True)
    args = ap.parse_args()
    qdir = os.path.join(HERE, "queries")
    agree = differ_expected = 0
    failures = []
    names = sorted(os.listdir(qdir))
    for name in names:
        q = os.path.join(qdir, name)
        data = os.path.join(HERE, "ft.ttl" if name.startswith("ft-") else "geo.ttl")
        f = normalise(run([args.fstar, "query", "--data", data, "--query", q, "-o", "json"]))
        l = normalise(run([args.lean, "query", data, "--format", "turtle", "--query", q]))
        same = f == l
        if name in EXPECTED_DIVERGENCE:
            if same:
                failures.append(f"STALE {name}: the engines now agree; remove its "
                                f"EXPECTED_DIVERGENCE entry ({EXPECTED_DIVERGENCE[name]})")
            else:
                differ_expected += 1
                print(f"expected-divergence {name}: {EXPECTED_DIVERGENCE[name]}")
        elif same:
            agree += 1
            print(f"agree {name}")
        else:
            failures.append(f"DIFFER {name}\n  F*:   {f}\n  Lean: {l}")
    for msg in failures:
        print(msg)
    print(f"geo-fulltext parity: {agree} agree, {len(failures)} fail, "
          f"{differ_expected} expected divergence (out of {len(names)})")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
