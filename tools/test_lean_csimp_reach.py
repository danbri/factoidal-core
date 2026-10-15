#!/usr/bin/env python3
"""Self-test for tools/lean-csimp-reach.py (https://github.com/danbri/factoidal/issues/871).

Case 1 (real build): the tool, run on the emitted C of
formal/lean4/L4Factoidal/CsimpReachFixture.lean, must report the callers of the
specification `weightSpec` that the `@[csimp]` replacement did not reach, and
must not report `callDirect`, which it did reach. The fixture is a known-bad
example kept on purpose.

This case is an EXPECTED FAILURE until the tool exists. `xfail` runs the case; a
failure counts as an expected failure and names the issue; a pass FAILS the run
with "unexpected pass: flip to an assertion and close <issue>"
(skills/test-suites/SKILL.md, section Expected failures).

    python3 tools/test_lean_csimp_reach.py
"""

import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
TOOL = os.path.join(HERE, "lean-csimp-reach.py")
ISSUE = "https://github.com/danbri/factoidal/issues/871"
FIX = "L4Factoidal.CsimpReachFixture"

RESULTS = []  # (kind, name, detail)


def check(name, fn):
    try:
        fn()
    except Exception as e:  # noqa: BLE001 -- a test failure of any kind is a failure
        RESULTS.append(("fail", name, "%s: %s" % (type(e).__name__, e)))
    else:
        RESULTS.append(("pass", name, ""))


def xfail(name, issue, fn):
    try:
        fn()
    except Exception as e:  # noqa: BLE001
        RESULTS.append(("xfail", name, "%s (%s): %s: %s" % (name, issue, type(e).__name__, e)))
    else:
        RESULTS.append(("fail", name, "unexpected pass: flip to an assertion and close %s" % issue))


def real_build_reports_the_fixture():
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, "reach.json")
        subprocess.run([sys.executable, TOOL, "--json", out], check=True, capture_output=True, text=True)
        with open(out) as fh:
            res = json.load(fh)
    pairs = {(f["left"], f["caller"]) for f in res["findings"]}
    spec = FIX + ".weightSpec"
    for caller in ("callBefore", "callViaInstance", "callViaInline"):
        assert (spec, FIX + "." + caller) in pairs, "missing finding for " + caller
    assert (spec, FIX + ".callDirect") not in pairs, "callDirect was reached by the replacement"


xfail("real build: the tool reports the callers the replacement did not reach", ISSUE,
      real_build_reports_the_fixture)


def main():
    bad = sum(1 for r in RESULTS if r[0] == "fail")
    ok = sum(1 for r in RESULTS if r[0] == "pass")
    xf = sum(1 for r in RESULTS if r[0] == "xfail")
    for kind, name, detail in RESULTS:
        if kind != "pass":
            print("%s %s" % (kind.upper(), detail or name))
    print("%d pass, %d fail, %d xfail (out of %d)" % (ok, bad, xf, len(RESULTS)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
