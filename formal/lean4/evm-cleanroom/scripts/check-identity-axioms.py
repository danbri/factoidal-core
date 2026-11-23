#!/usr/bin/env python3
"""Fail-closed audit of Lean's actual identity-precompile #print axioms output."""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMES = {
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
        assert len(check(good)) == 5
        bad = (good.replace("does not depend on any axioms",
                            "depends on axioms: [sorryAx]", 1),
               good.rsplit("\n", 1)[0],
               good + "\n" + good.splitlines()[0])
        denied = 0
        for example in bad:
            try:
                check(example)
            except ValueError:
                denied += 1
        if denied != 3:
            raise ValueError("bad axiom controls survived")
        print(json.dumps({"status": "negative-controls-pass", "rejected": denied}))
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
