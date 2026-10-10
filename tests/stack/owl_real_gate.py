#!/usr/bin/env python3
"""tests/stack/owl_real_gate.py — OWL reasoning on real ontologies finishes.

A gate over a few steps of tools/owl-real-bench.py
(docs/designissues/2026-10-10-owl-real-ontologies.md,
https://github.com/danbri/factoidal/issues/651 plan item 4). Each row runs ONE
step of the Lean command line on ONE vendored ontology under the same wall-clock
cap and address-space cap as the benchmark, and passes when the step finishes
with the stated result:

  decided   the step exits with a verdict, `true` or `false` (`unknown` is a
            budget-out and fails the row)
  true      the verdict is `true`
  done      the step exits 0 (closure)
  S         (species) l4owl-species finishes within S seconds
  N         (parse) the Lean parser reads N triples from the first source
            file; N is rdflib 7.6.0's count, recorded in the file's
            PROVENANCE.md

A row in XFAIL is a known shortfall with an open issue (CLAUDE.md, "A stated
shortfall is a failing test plus an open issue"; skills/test-suites/SKILL.md,
"Expected failures"). It still runs. While it fails it prints "XFAIL" with
its issue URL and counts as expected-fail; when it passes it prints
"UNEXPECTED PASS" and counts as a failure, so the run is red until the row
leaves XFAIL (the repair turns it into an assertion) and the issue is closed.

Exit status: 0 when every row passes or fails as expected, 1 when a row fails
or an expected failure passes, 2 when a binary or a source file is missing.
Scores print as "N pass, M fail, K expected-fail (out of T)".

Usage:  tests/stack/owl_real_gate.py [--only ROW[,ROW...]] [--cap-s 600]
Env:    L4_BIN_DIR   directory of l4factoidal (default formal/lean4/.lake/build/bin)
        OWL_REAL_FIXTURES   work directory (default /tmp/factoidal-owl-real-gate)
"""

from __future__ import annotations

import argparse
import importlib.util
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
_spec = importlib.util.spec_from_file_location("owl_real_bench", ROOT / "tools/owl-real-bench.py")
bench = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(bench)

BIN_DIR = Path(os.environ.get("L4_BIN_DIR", ROOT / "formal/lean4/.lake/build/bin"))
# The F* command line (tools/fetch-builds.sh --set native). Rows whose id ends
# in "-fstar" run it and are SKIPPED, not scored, when it is not installed.
FSTAR_BIN = Path(os.environ.get("FSTAR_BIN", ROOT / "bin/linux-x86_64/factoidal"))
WORK = Path(os.environ.get("OWL_REAL_FIXTURES", "/tmp/factoidal-owl-real-gate"))
AS_BYTES = 6_000_000_000

# row id: (ontology name in tools/owl-real-bench.py, step, expected result,
#          for an `entails` row the pair (sub, super) as IRIs)
ROWS: dict[str, tuple] = {
    "ro-parse": ("ro", "parse", 11705, None),
    "pizza-consistent": ("pizza", "consistent", "decided", None),
    "pizza-entails-american": ("pizza", "entails", "true", (
        "http://www.co-ode.org/ontologies/pizza/pizza.owl#American",
        "http://www.co-ode.org/ontologies/pizza/pizza.owl#NonVegetarianPizza")),
    "wine-consistent": ("wine", "consistent", "decided", None),
    "ro-closure": ("ro", "closure", "done", None),
    "cl-basic-closure": ("cl-basic", "closure", "done", None),
    "cl-basic-consistent": ("cl-basic", "consistent", "decided", None),
    "wine-closure-fstar": ("wine", "closure", "done", None),
    "qudt-species": ("qudt", "species", 60, None),
    "qudt-closure": ("qudt", "closure", "done", None),
    "qudt-consistent": ("qudt", "consistent", "decided", None),
}

# Rows that fail today, each with the open issue that tracks it. A row leaves
# this table in the commit that repairs it.
XFAIL: dict[str, str] = {
    # The Lean RDF/XML parser gives an xml:lang to the next sibling property
    # element, so two literals collapse into existing ones (11,703 triples).
    "ro-parse": "https://github.com/danbri/factoidal/issues/329",
    # The closure fits in 1.4 GB; printing it needs more than 6 GB resident.
    "qudt-closure": "https://github.com/danbri/factoidal/issues/758",
    # Fits in 1.4 GB resident, but mimalloc's 1 GiB arena reservations exhaust
    # the 6,000,000,000-byte address-space cap first.
    "qudt-consistent": "https://github.com/danbri/factoidal/issues/759",
    # The tableau refuter grows about 5 times per doubling of the input;
    # killed at 600 s (HermiT: 6.1 s).
    "cl-basic-consistent": "https://github.com/danbri/factoidal/issues/760",
    # The F* OWL RL closure of 2,709 triples did not finish in 300 s.
    "wine-closure-fstar": "https://github.com/danbri/factoidal/issues/765",
    # 253 s of CPU time on 130,404 triples.
    "qudt-species": "https://github.com/danbri/factoidal/issues/766",
}


def run_row(rid: str, cap_s: int) -> tuple[bool, str]:
    name, step, expect, pair = ROWS[rid]
    onto = next(o for o in bench.ONTOLOGIES if o["name"] == name)
    lean = str(BIN_DIR / "l4factoidal")
    wd = WORK / name
    wd.mkdir(parents=True, exist_ok=True)
    files = [str(ROOT / p) for p in onto["files"]]
    if step == "parse":
        out = str(wd / "parse.out")
        r = bench.run_step([lean, "parse", files[0], "--format", onto["format"]],
                           cap_s, AS_BYTES, out, str(wd))
        got = bench.first_line(out) if r["status"] == "ok" else r["status"]
        return got == str(expect), f"parse: {got} triples (rdflib {expect})"
    merged = wd / "merged.nt"
    if not merged.exists():
        prep = bench.prepare_merged(lean, files, onto["format"], str(wd))
        if prep is None:
            return False, "the source files do not parse"
    out = str(wd / f"{step}.out")
    if step == "species":
        docs = sorted(str(p) for p in wd.glob("doc*.nt"))
        r = bench.run_step([str(BIN_DIR / "l4owl-species")] + docs, int(expect), AS_BYTES,
                           out, str(wd))
        return r["status"] == "ok", (f"species: {r['status']}, {r['wall_s']:.1f} s "
                                     f"(bound {expect} s), peak RSS {r['peak_rss_mb']:.0f} MB")
    if step == "closure" and rid.endswith("-fstar"):
        cmd = [str(FSTAR_BIN), "entail", "--data", str(merged), "--regime", "OWL-RL"]
    elif step == "closure":
        cmd = [lean, "closure", str(merged), "--format", "nquads", "--regime", "owl-rl"]
    elif step == "consistent":
        cmd = [lean, "owl-consistent", str(merged), "--format", "nquads"]
    elif step == "entails":
        concl = wd / "conclusion.nt"
        concl.write_text(f"<{pair[0]}> <{bench.RDFS_SUBCLASSOF}> <{pair[1]}> .\n", encoding="utf-8")
        cmd = [lean, "owl-entails", str(merged), str(concl), "--format", "nquads"]
    else:
        return False, f"unknown step {step}"
    r = bench.run_step(cmd, cap_s, AS_BYTES, out, str(wd))
    detail = f"{step}: {r['status']}, {r['wall_s']:.2f} s, peak RSS {r['peak_rss_mb']:.0f} MB"
    if r["status"] != "ok":
        tail = r["stderr_tail"].splitlines()[-1:] if r["stderr_tail"] else []
        return False, detail + (f" ({tail[0][:120]})" if tail else "")
    verdict = bench.first_line(out) if step != "closure" else None
    if step == "closure":
        n = bench.count_lines(out)
        os.remove(out)
        return r["rc"] == 0, detail + f", {n} triples"
    detail += f", verdict {verdict}"
    if expect == "decided":
        return verdict in ("true", "false"), detail
    return verdict == expect, detail


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", default="")
    ap.add_argument("--cap-s", type=int, default=600)
    a = ap.parse_args()
    if not (BIN_DIR / "l4factoidal").exists():
        print(f"owl_real_gate: {BIN_DIR}/l4factoidal not built "
              "(cd formal/lean4 && lake build l4factoidal)", file=sys.stderr)
        return 2
    names = [r for r in a.only.split(",") if r] or list(ROWS)
    passed = failed = xfailed = skipped = 0
    print(f"OWL real-ontology gate: wall-clock cap {a.cap_s} s, address-space cap "
          f"{AS_BYTES} bytes per step; load average {os.getloadavg()[0]:.2f}")
    for rid in names:
        if rid not in ROWS:
            print(f"  unknown row {rid}", file=sys.stderr)
            return 2
        issue = XFAIL.get(rid)
        if rid.endswith("-fstar") and not FSTAR_BIN.exists():
            skipped += 1
            print(f"  SKIP {rid}: {FSTAR_BIN} not installed (tools/fetch-builds.sh --set native)")
            continue
        ok, detail = run_row(rid, a.cap_s)
        if issue and not ok:
            xfailed += 1
            print(f"  XFAIL {rid} ({issue}): {detail}")
        elif issue and ok:
            failed += 1
            print(f"  UNEXPECTED PASS {rid}: {detail}: flip it to an assertion "
                  f"(remove it from XFAIL) and close {issue}")
        else:
            passed += ok
            failed += (not ok)
            print(f"  {'PASS' if ok else 'FAIL'} {rid}: {detail}")
    print(f"owl-real: {passed} pass, {failed} fail, {xfailed} expected-fail "
          f"(out of {passed + failed + xfailed})"
          + (f"; {skipped} skipped (F* binary not installed)" if skipped else ""))
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
