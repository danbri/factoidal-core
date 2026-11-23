#!/usr/bin/env python3
"""Fail-closed audit of Lean's actual identity-precompile #print axioms output."""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMES = {
    "executeView_ofArray", "executeView_oversize", "executeView_exact",
    "executeView_underfunded", "executeView_preserves_input", "executeView_preserves_byte",
    "execute_oversize", "execute_underfunded", "execute_exact",
    "execute_preserves_input", "execute_gas_accounting",
}
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
PATTERN = re.compile(
    r"'EVMCleanroom.IdentityPrecompile\.(?P<name>[^']+)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\]]*)\]|"
    r"(?P<empty>does not depend on any axioms))"
)


def check(transcript):
    seen = {}
    for match in PATTERN.finditer(transcript):
        name = match.group("name")
        if name in seen:
            raise ValueError("duplicate theorem output: " + name)
        raw = match.group("axioms") or ""
        axioms = sorted(x.strip() for x in raw.split(",") if x.strip())
        if len(set(axioms)) != len(axioms) or not set(axioms).issubset(ALLOWED):
            raise ValueError("unpermitted theorem dependency: " + name + ": " + str(axioms))
        seen[name] = axioms
    if set(seen) != NAMES:
        raise ValueError("incomplete theorem inventory: " +
                         str(sorted(NAMES - set(seen))) + " / extra " +
                         str(sorted(set(seen) - NAMES)))
    return seen


def main():
    if "--selftest" in sys.argv:
        good = "\n".join(
            f"info: example.lean:1:0: 'EVMCleanroom.IdentityPrecompile.{name}' "
            "does not depend on any axioms"
            for name in sorted(NAMES)
        )
        assert len(check(good)) == len(NAMES)
        allowed = good.replace("does not depend on any axioms",
                               "depends on axioms: [Classical.choice, Quot.sound, propext]", 1)
        assert check(allowed)[sorted(NAMES)[0]] == sorted(ALLOWED)
        bad = {
            "proof-placeholder": good.replace("does not depend on any axioms",
                                               "depends on axioms: [sorryAx]", 1),
            "missing-theorem": good.rsplit("\n", 1)[0],
            "duplicate-theorem": good + "\n" + good.splitlines()[0],
            "extra-theorem": good + "\n'EVMCleanroom.IdentityPrecompile.unselected' "
                                    "does not depend on any axioms",
            "duplicate-axiom": good.replace("does not depend on any axioms",
                                             "depends on axioms: [propext, propext]", 1),
            "custom-axiom": good.replace("does not depend on any axioms",
                                          "depends on axioms: [EVMCleanroom.unproved]", 1),
        }
        denied = []
        for label, example in bad.items():
            try:
                check(example)
            except ValueError:
                denied.append(label)
        if len(denied) != len(bad):
            raise ValueError("bad axiom controls survived")
        print(json.dumps({"status": "negative-controls-pass", "theorems": len(NAMES),
                          "rejected": len(denied), "controls": denied}))
        return
    result = subprocess.run(
        ["lake", "env", "lean", "EVMCleanroom/IdentityPrecompile.lean"],
        cwd=ROOT, capture_output=True, text=True, timeout=120, check=False,
    )
    if result.returncode:
        raise ValueError("Lean elaboration failed: " +
                         (result.stdout + result.stderr)[-2500:])
    actual = check(result.stdout + result.stderr)
    print(json.dumps({
        "status": "actual-lean-axioms-audited",
        "theorems": len(actual), "axioms": actual,
        "source": "EVMCleanroom/IdentityPrecompile.lean",
        "allowedFoundations": sorted(ALLOWED),
    }, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print("identity axiom check failed:", exc, file=sys.stderr)
        sys.exit(1)
