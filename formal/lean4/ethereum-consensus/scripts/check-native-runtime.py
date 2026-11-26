#!/usr/bin/env python3
"""Static Linux ELF evidence, not proof of runtime call behaviour."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys

# Same exact Init.MetaTypes BSS exemptions as the execution audit.
SUPPORT = {"l_Lean_Meta_Simp_defaultMaxSteps"} | {
    "l_Lean_Meta_instInhabited" + name + suffix
    for name in ("EtaStructMode", "Occurrences", "TransparencyMode")
    for suffix in ("", "_default")}
FORBIDDEN = re.compile(
    r"(?:^|_)Lean_(?:Elab|Meta|Compiler|Kernel|TypeChecker)(?:_|$)"
    r"|^initialize_Lean_Data_Json_Elab(?:_|$)"
    r"|^lean_initialize$|^initialize_Lean$|^lean_eval_(?:expr|main)$"
    r"|\blean::compiler\b|\blean::[A-Za-z_]*kernel[A-Za-z_]*\b|\blean_kernel_|type_checker")


def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True, timeout=120).stdout


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def inspect(path):
    raw = path.read_bytes()
    if len(raw) < 64 or raw[:7] != b"\x7fELF\x02\x01\x01" or struct.unpack_from("<H", raw, 16)[0] not in (2, 3):
        raise ValueError("expected Linux ELF64 little-endian executable")
    nm = run("nm", "--demangle", "--no-sort", str(path))
    dyn = run("readelf", "--dynamic", "--wide", str(path))
    rows = []
    for line in nm.splitlines():
        match = re.fullmatch(r"\s*(?:[0-9a-fA-F]+\s+)?([A-Za-z?])\s+(.+)", line)
        if not match:
            raise ValueError("unrecognised nm row: " + line[:200])
        rows.append((match[2], match[1]))
    defined = {name for name, kind in rows if kind in ("T", "t")}
    bad = sorted({name for name, kind in rows if FORBIDDEN.search(name)
                  and not (name in SUPPORT and kind in ("B", "b"))})
    needed = re.findall(r"\(NEEDED\)\s+Shared library: \[([^\]]+)\]", dyn)
    libraries = sorted(n for n in needed if (n.lower().startswith("liblean") and
                       not n.lower().startswith("libleanrt.")) or n.lower().startswith("liblake"))
    issues = ([] if "main" in defined else ["missing defined main (or stripped symbols)"])
    if bad:
        issues.append("proof-engine symbols")
    if libraries:
        issues.append("proof-engine shared libraries")
    return {"sha256": sha(raw), "bytes": len(raw), "symbols": len(rows),
            "runtimeInitializerDefined": "lean_initialize_runtime_module" in defined,
            "fullBootstrapDefined": "lean_initialize" in defined,
            "forbiddenSymbolCount": len(bad), "forbiddenExamples": bad[:30],
            "neededLibraries": needed, "forbiddenLibraries": libraries,
            "nmSha256": sha(nm.encode()), "readelfSha256": sha(dyn.encode()),
            "issues": issues, "passed": not issues}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    report = {"schema": "factoidal.consensus-native-runtime.v1", "binary": str(args.binary),
              "checkerSha256": sha(Path(__file__).read_bytes())}
    try:
        report.update(head=run("git", "rev-parse", "HEAD").strip(),
                      tree=run("git", "rev-parse", "HEAD^{tree}").strip())
        report.update(inspect(args.binary))
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        report.update(passed=False, issues=[str(exc)])
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, sort_keys=True))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
