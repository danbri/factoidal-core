#!/usr/bin/env python3
"""Native gate: a wallet executable carries no proof assistant.

Reuses the symbol families and library rules of
../evm-cleanroom/scripts/check-witness-runtime.py (elaborator, Meta, compiler,
kernel, type checker, full Lean bootstrap, shared Lean libraries) on an ELF
built by this package. A static linkage check; Linux only.

usage: check-runtime.py <executable name under .lake/build/bin>... [--out report.json]
"""
import hashlib
import importlib.util
import json
import sys
from pathlib import Path


def main():
    args = sys.argv[1:]
    out = None
    if "--out" in args:
        i = args.index("--out")
        out = Path(args[i + 1])
        del args[i:i + 2]
    here = Path(__file__).resolve().parent
    source = here.parents[1] / "evm-cleanroom" / "scripts" / "check-witness-runtime.py"
    spec = importlib.util.spec_from_file_location("audit", source)
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    reports = {}
    for name in args:
        path = Path(".lake/build/bin") / name
        audit.REQUIRED_SYMBOLS[name] = {"main", "lean_initialize_runtime_module"}
        # Control: the analysis must reject a proof-engine symbol when one is present.
        good = [(symbol, "T") for symbol in audit.REQUIRED_SYMBOLS[name]]
        assert not audit.analyse_symbols(name, good)["issues"]
        assert audit.analyse_symbols(name, good + [("l_Lean_Meta_isDefEq", "T")])["issues"]
        assert audit.analyse_symbols(name, good + [("lean_initialize", "T")])["issues"]
        reports[name] = audit.inspect_binary(name, path, hashlib.sha256(path.read_bytes()).hexdigest())
    passed = bool(reports) and all(report["passed"] for report in reports.values())
    summary = {"passed": passed, "executables": {
        name: {"bytes": report["bytes"], "sha256": report["sha256"], "issues": report["issues"],
               "neededLibraries": report["neededLibraries"]}
        for name, report in reports.items()}}
    if out:
        out.write_text(json.dumps({"passed": passed, "executables": reports}, indent=2) + "\n")
    print(json.dumps(summary))
    sys.exit(0 if passed else 1)


if __name__ == "__main__":
    main()
