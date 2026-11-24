#!/usr/bin/env python3
"""Falsify retained exact-source ledgers using actual Lean reports in a scratch Git repo.

Never feed synthetic positive reports into the production evidence gate.
Each negative test must be rejected by the unchanged production checker.
"""
import ast
import re
import subprocess
import sys
import tempfile
from pathlib import Path

repo = Path(__file__).resolve().parents[4]
prefix = Path("formal/lean4/ethereum-consensus/scripts")
lakefile = Path("formal/lean4/ethereum-consensus/lakefile.toml")
report_line = re.compile(r"^'([^']+)' (?:depends on axioms:|does not depend on any axioms)")

def git(root, *args):
    subprocess.run(
        ["git", "-C", str(root), "-c", "user.name=Ledger test",
         "-c", "user.email=ledger-test@example.invalid", "-c", "commit.gpgsign=false", *args],
        check=True, capture_output=True,
    )

def check(script_name, actual_log):
    script = prefix / script_name
    source = (repo / script).read_text()
    pins = next(ast.literal_eval(node.value) for node in ast.parse(source).body
                if isinstance(node, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == "pins" for t in node.targets))
    assert str(lakefile) in pins
    actual = actual_log.read_text()
    lines = actual.splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if report_line.match(line))
    name = report_line.match(lines[i]).group(1)
    with tempfile.TemporaryDirectory(prefix="ethereum-ledger-controls-") as tmp:
        root = Path(tmp) / "repo"
        root.mkdir()
        for path in [*map(Path, pins), script]:
            dst = root / path
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes((repo / path).read_bytes())
        git(root, "init", "-q")
        git(root, "add", "-A")
        git(root, "commit", "-qm", "Exact source fixture")
        transcript = Path(tmp) / "report.log"

        def verdict(log, expected_error=None):
            transcript.write_text(log)
            proc = subprocess.run([sys.executable, str(root / script), str(transcript)],
                                  cwd=root, capture_output=True, text=True)
            if expected_error is None:
                assert proc.returncode == 0, proc.stderr
            else:
                assert proc.returncode != 0 and expected_error in proc.stderr, (
                    expected_error, proc.returncode, proc.stdout, proc.stderr)

        verdict(actual)
        verdict("".join(lines[:i] + lines[i+1:]), "wrong theorem inventory")
        verdict(actual.rstrip("\n") + "\n" + lines[i].rstrip("\n") + "\n", "duplicate axiom result")
        verdict("".join(lines[:i] + ["'Unexpected.statement' does not depend on any axioms\n"] + lines[i+1:]),
                "wrong theorem inventory")
        verdict("".join(lines[:i] + [f"'{name}' depends on axioms: [sorryAx]\n"] + lines[i+1:]),
                "unpermitted axiom")
        target = root / lakefile
        good = target.read_bytes()
        target.write_bytes(good + b"\n# deliberately altered ledger fixture\n")
        verdict(actual, "source pin mismatch: " + str(lakefile))
        git(root, "add", str(lakefile))
        git(root, "commit", "-qm", "Alter committed pin")
        target.write_bytes(good)
        verdict(actual, "source pin mismatch: " + str(lakefile))
    print(f"{script_name}: exact-source control passed; 6 mutations rejected")

if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: check-retained-ledger-controls.py ATTESTATION_LOG SLASHING_LOG")
    check("check-attestation-data-axioms.py", Path(sys.argv[1]))
    check("check-attester-slashing-axioms.py", Path(sys.argv[2]))
