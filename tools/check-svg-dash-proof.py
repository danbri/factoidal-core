#!/usr/bin/env python3
"""Check the actual dash theorem and reject an odd-list normalization mutation."""
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    root = Path(__file__).resolve().parents[1]
    sources = root / "labs/demos/foafnaut"
    implementation = (sources / "SVGDash.lean").read_text()
    proof = (sources / "SVGDashProofs.lean").read_text()
    needle = "then pattern++pattern else pattern"
    if implementation.count(needle) != 1:
        raise RuntimeError("Mutation site changed; review this control")
    with tempfile.TemporaryDirectory(prefix="solving-dash-proof-") as directory:
        for label, mutated in (("control", False), ("odd-undoubled", True)):
            target = Path(directory) / label
            target.mkdir()
            source = implementation.replace(needle, "then pattern else pattern") if mutated else implementation
            (target / "SVGDash.lean").write_text(source)
            (target / "SVGDashProofs.lean").write_text(proof)
            env = dict(os.environ, LEAN_PATH=str(target))

            def run(*args):
                return subprocess.run(
                    ["lean", "-R", str(target), *map(str, args)],
                    cwd=root / "formal/lean4", env=env,
                    capture_output=True, text=True, timeout=60,
                )

            compiled = run("-o", target / "SVGDash.olean", target / "SVGDash.lean")
            if compiled.returncode:
                raise RuntimeError(compiled.stdout + compiled.stderr)
            checked = run(target / "SVGDashProofs.lean")
            diagnostic = checked.stdout + checked.stderr
            if not mutated:
                if checked.returncode or "sorryAx" in diagnostic:
                    raise RuntimeError("Control proof failed:\n" + diagnostic)
            elif checked.returncode == 0 or "omega" not in diagnostic:
                raise RuntimeError("Mutation did not reach arithmetic rejection:\n" + diagnostic)
            print(f"{label}: {'arithmetic rejection confirmed' if mutated else 'kernel check passed'}")
            print(diagnostic.strip())


if __name__ == "__main__":
    main()
