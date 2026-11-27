#!/usr/bin/env python3
"""Audit the precompile modules: allowed imports, no escape hatches, and actual kernel axioms.

Runs the Lean compiler on every module below and reads the `#print axioms`
lines it emits. Every theorem declared in a module must be printed, and may
depend only on Lean's three standard axioms. Run from the package directory.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MODULES = json.loads((Path(__file__).resolve().parent / "modules.json").read_text())
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|native_decide|unsafe|implemented_by|partial\s+def|axiom|extern|opaque)\b")
PRINTED = re.compile(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
ALLOWED_IMPORTS = re.compile(
    r"^import (EVMCleanroom\.Precompiles(\.[A-Za-z0-9]+)?|EVMCleanroom\.(Keccak|Core))$")


def strip_comments(text):
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--.*", "", text)


def audit(module):
    path = ROOT / module
    source = path.read_text()
    code = strip_comments(source)
    for line in source.splitlines():
        if line.startswith("import ") and not ALLOWED_IMPORTS.match(line.strip()):
            raise SystemExit("import outside the allowed set in %s: %s" % (module, line))
    hit = FORBIDDEN.search(code)
    if hit:
        raise SystemExit("forbidden construct in %s: %s" % (module, hit.group(0)))
    declared = re.findall(r"^(?:private\s+)?theorem\s+([A-Za-z0-9_.']+)", code, flags=re.M)
    done = subprocess.run(["lake", "-f", "lakefile-precompiles.toml", "env", "lean", module], cwd=ROOT, capture_output=True, text=True)
    if done.returncode != 0:
        raise SystemExit("Lean failed on %s:\n%s" % (module, (done.stdout + done.stderr)[-2000:]))
    printed = {}
    for name, _, axioms in PRINTED.findall(done.stdout.replace("\n ", " ")):
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        if not used <= STANDARD:
            raise SystemExit("non-standard axioms in %s: %s" % (name, sorted(used - STANDARD)))
        printed[name.split(".")[-1]] = sorted(used)
    missing = [name for name in declared if name.split(".")[-1] not in printed]
    if missing:
        raise SystemExit("theorems without an axiom print in %s: %s" % (module, missing))
    return printed


def main():
    report = {}
    for module in MODULES["modules"]:
        report[module] = audit(module)
    total = sum(len(v) for v in report.values())
    print(json.dumps({"status": "actual-lean-axioms-audited", "modules": len(report),
                      "theorems": total, "axioms": report}, indent=1))


if __name__ == "__main__":
    sys.exit(main())
