#!/usr/bin/env python3
"""Locate a blocked SSZ module build without treating a prefix as proof evidence."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
import time

PACKAGE = Path(__file__).resolve().parents[1]
MODULES = ("BasicTypes", "ContainerRoots", "SigningDomains", "AttestationData")
NS = "EthereumConsensus.SSZ"
COMMAND = re.compile(r"^(?:/--|/-!|(?:private )?def |structure |inductive |theorem |#guard\b|#print axioms\b|end )")


def boundaries(source):
    """Cuts before complete top-level commands; keep declaration docs attached."""
    lines = source.splitlines(keepends=True)
    cuts = []
    opened = False
    for i, line in enumerate(lines):
        if line.strip() == "namespace " + NS:
            opened = True
        elif opened and COMMAND.match(line):
            if line.startswith(("#guard", "#print axioms", "end ")) or (i and not lines[i-1].strip()):
                cuts.append(i)
    return cuts


def locate(cuts, probe):
    """Return adjacent successful/failing cuts, assuming prefix monotonicity."""
    lo, hi = -1, len(cuts)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if probe(cuts[mid]):
            lo = mid
        else:
            hi = mid
    return (None if lo < 0 else cuts[lo], None if hi == len(cuts) else cuts[hi])


def run(command, seconds, log):
    started = time.monotonic()
    with log.open("w") as out:
        result = subprocess.run(["timeout", "--kill-after=5s", str(seconds), *command],
                                cwd=PACKAGE, stdout=out, stderr=subprocess.STDOUT)
    elapsed = round(time.monotonic() - started, 3)
    print(json.dumps(dict(command=command, exit=result.returncode, seconds=elapsed,
                          log=str(log))), flush=True)
    print(log.read_text(errors="replace")[-8000:], flush=True)
    return result.returncode == 0


def check_module(name, output):
    module = NS + "." + name
    source_path = PACKAGE.joinpath(*module.split(".")).with_suffix(".lean")
    if run(["lake", "build", "+" + module], 120, output / (name + "-build.log")):
        return True
    source = source_path.read_text()
    lines = source.splitlines(keepends=True)
    if run(["lake", "env", "lean", str(source_path)], 45, output / (name + "-full.log")):
        print("Direct full-source check passed; Lake target failed. Inspect build log.", flush=True)
        return False
    with tempfile.TemporaryDirectory(prefix="consensus-prefix-") as tmp:
        probe_file = Path(tmp) / "Probe.lean"
        def probe(cut):
            probe_file.write_text("".join(lines[:cut]) + "\nend " + NS + "\n")
            return run(["lake", "env", "lean", str(probe_file)], 45,
                       output / (name + "-prefix-" + str(cut) + ".log"))
        good, bad = locate(boundaries(source), probe)
    print(json.dumps(dict(module=module, last_successful_cut=good,
                          first_failing_cut=bad, source_lines=len(lines),
                          caveat="Prefix diagnostics only; timeouts can be cumulative. No proof result.")), flush=True)
    if good is not None:
        print("Candidate source range:\n" + "".join(lines[good:bad]), flush=True)
    return False


def self_test():
    source = "import Init\n\nnamespace " + NS + "\n\n/-- attached -/\ndef a := 1\n\n#guard a == 1\n#guard a ==\n  2\n\nend " + NS + "\n"
    cuts = boundaries(source)
    assert cuts == [4, 7, 8, 11], cuts
    cases = 0
    for n in range(1, 100):
        for first in range(n + 1):
            values = list(range(n))
            expected = (first-1 if first else None, first if first < n else None)
            assert locate(values, lambda i: i < first) == expected
            cases += 1
    print(f"Diagnostic self-test: {cases} synthetic monotone cut cases and one command-boundary case")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.output is None:
        parser.error("--output is required")
    args.output.mkdir(parents=True, exist_ok=True)
    for name in MODULES:
        if not check_module(name, args.output.resolve()):
            raise SystemExit("SSZ module build refused: " + name)


if __name__ == "__main__":
    main()
