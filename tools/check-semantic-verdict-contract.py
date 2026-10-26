#!/usr/bin/env python3
"""Check and mutation-test the generic evidence-bearing verdict interface.

This standalone interface example is outside the product execution path.
It does not establish W3C semantics, a product checker, or adapter assurance.
"""

import argparse
from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = ROOT / "tests/assurance/CertifiedVerdictContract.lean"
LEAN_CWD = ROOT / "formal/lean4"
TIMEOUT_SECONDS = 30
AXIOM_AUDITS = (
    "CertifiedVerdictContract.erase_sound",
    "CertifiedVerdictContract.no_contradictory_booleans",
    "CertifiedVerdictContract.pipeline_sound",
    "CertifiedVerdictContract.FiniteExample.checker",
)


class CheckFailure(Exception):
    """A failed baseline, mutation control, or execution prerequisite."""


@dataclass(frozen=True)
class Mutation:
    name: str
    anchor: str
    replacement: str
    proof_start: str
    proof_end: str


MUTATIONS = (
    Mutation(
        "swap-erased-booleans",
        "  | .consistent _ => ⟨some true, none⟩\n"
        "  | .inconsistent _ => ⟨some false, none⟩\n",
        "  | .consistent _ => ⟨some false, none⟩\n"
        "  | .inconsistent _ => ⟨some true, none⟩\n",
        "theorem erase_sound ",
        "/-- Two evidence-bearing results ",
    ),
    Mutation(
        "swap-finite-regime-semantics",
        "    | .requiresTrue => input = true\n"
        "    | .requiresFalse => input = false\n",
        "    | .requiresTrue => input = false\n"
        "    | .requiresFalse => input = true\n",
        "def checker : CertificateChecker semantics where\n",
        "def modelSearch : ",
    ),
    Mutation(
        "refute-satisfiable-input",
        "  | .requiresTrue, false, .refutation => some false\n",
        "  | .requiresTrue, true, .refutation => some false\n",
        "def checker : CertificateChecker semantics where\n",
        "def modelSearch : ",
    ),
)


def unique_offset(text, anchor, label):
    count = text.count(anchor)
    if count != 1:
        raise CheckFailure(
            f"{label}: expected exactly one literal anchor, found {count}"
        )
    return text.index(anchor)


def apply_mutation(source, mutation):
    offset = unique_offset(source, mutation.anchor, mutation.name)
    return (
        source[:offset]
        + mutation.replacement
        + source[offset + len(mutation.anchor):]
    )


def proof_lines(source, mutation):
    start = unique_offset(source, mutation.proof_start, f"{mutation.name} proof start")
    end = unique_offset(source, mutation.proof_end, f"{mutation.name} proof end")
    if end <= start:
        raise CheckFailure(f"{mutation.name}: invalid proof boundaries")
    return source.count("\n", 0, start) + 1, source.count("\n", 0, end) + 1


def compiler_run(lean, arguments, label):
    try:
        result = subprocess.run(
            [str(lean), *map(str, arguments)],
            cwd=LEAN_CWD,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=TIMEOUT_SECONDS,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        partial = error.stdout or ""
        if isinstance(partial, bytes):
            partial = partial.decode("utf-8", errors="replace")
        if partial:
            print(partial, end="" if partial.endswith("\n") else "\n", flush=True)
        raise CheckFailure(f"{label}: compiler timeout after {TIMEOUT_SECONDS}s") from error
    except OSError as error:
        raise CheckFailure(f"{label}: could not execute Lean: {error}") from error
    print(f"--- {label}: compiler exit {result.returncode} ---", flush=True)
    if result.stdout:
        print(result.stdout, end="" if result.stdout.endswith("\n") else "\n", flush=True)
    return result


def check_baseline(result):
    if result.returncode != 0:
        raise CheckFailure("baseline: Lean must exit 0")
    if "sorryAx" in result.stdout:
        raise CheckFailure("baseline: axiom audit contains an admitted proof")
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    for name in AXIOM_AUDITS:
        lines = [
            line
            for line in result.stdout.splitlines()
            if line.startswith(f"'{name}' ") and "axioms" in line
        ]
        if len(lines) != 1:
            raise CheckFailure(f"baseline: missing or duplicate axiom audit for {name}")
        if lines[0] == f"'{name}' does not depend on any axioms":
            continue
        prefix = f"'{name}' depends on axioms: ["
        if not lines[0].startswith(prefix) or not lines[0].endswith("]"):
            raise CheckFailure(f"baseline: unrecognized axiom audit for {name}")
        reported = {item.strip() for item in lines[0][len(prefix):-1].split(",") if item.strip()}
        if reported - allowed_axioms:
            raise CheckFailure(f"baseline: disallowed axioms for {name}: {sorted(reported - allowed_axioms)}")


# Diagnostic parsing does not edit source. Mutations use literal anchors only.
ERROR_HEADER = re.compile(r"^.+:(\d+):\d+: error(?:\([^)]*\))?:\s*(.*)$")
SEMANTIC_DIAGNOSTICS = (
    "type mismatch",
    "unsolved goals",
    "tactic `exact` failed",
    "tactic 'exact' failed",
    "tactic `rfl` failed",
    "tactic 'rfl' failed",
)
INVALID_REJECTION = (
    "no such file or directory",
    "file not found",
    "unknown module prefix",
    "unknown module",
    "object file",
    "failed to load",
    "unknown identifier",
    "unknown constant",
    "unknown command",
    "invalid option",
    "unexpected token",
    "unexpected identifier",
    "unterminated",
    "expected token",
)


def check_rejection(result, mutated_source, mutation):
    if result.returncode == 0:
        raise CheckFailure(f"{mutation.name}: mutation unexpectedly passed")
    if result.returncode < 0:
        raise CheckFailure(f"{mutation.name}: compiler terminated by signal, not a proof rejection")
    lowered = result.stdout.casefold()
    for marker in INVALID_REJECTION:
        if marker in lowered:
            raise CheckFailure(
                f"{mutation.name}: invalid rejection (syntax/import/environment diagnostic: {marker})"
            )
    first, last = proof_lines(mutated_source, mutation)
    for line in result.stdout.splitlines():
        match = ERROR_HEADER.match(line)
        if not match:
            continue
        line_number, message = int(match.group(1)), match.group(2).casefold()
        if first <= line_number < last and any(
            marker in message for marker in SEMANTIC_DIAGNOSTICS
        ):
            return line
    raise CheckFailure(
        f"{mutation.name}: no Lean type/proof failure in the affected proof "
        f"(lines {first} to {last - 1})"
    )


def resolve_lean(value):
    if not value:
        raise CheckFailure("Lean executable is missing; supply --lean /path/to/lean")
    executable = shutil.which(value)
    if executable is None:
        raise CheckFailure(f"Lean executable is missing or not executable: {value}")
    # Keep the selected executable path: resolving an elan symlink can turn
    # its lean invocation into an elan invocation with different arguments.
    return Path(os.path.abspath(executable))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"), help="Lean executable (default: shutil.which('lean'))")
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE, help="Checked contract exemplar source")
    arguments = parser.parse_args()
    print("Scope: interface example only; NOT product verdict assurance.", flush=True)
    print("No W3C semantics, product certificate checker, or shipped adapter is certified.", flush=True)
    try:
        lean = resolve_lean(arguments.lean)
        source_path = arguments.source.resolve(strict=True)
        source_bytes = source_path.read_bytes()
        source = source_bytes.decode("utf-8")
        # Refuse missing or ambiguous anchors before invoking the compiler.
        prepared = []
        for mutation in MUTATIONS:
            mutated = apply_mutation(source, mutation)
            proof_lines(mutated, mutation)
            prepared.append((mutation, mutated))
        print(f"Lean: {lean}", flush=True)
        print(f"Source: {source_path}", flush=True)
        print(f"Source SHA-256: {hashlib.sha256(source_bytes).hexdigest()}", flush=True)
        version = compiler_run(lean, ["--version"], "Lean version")
        if version.returncode != 0:
            raise CheckFailure("Lean --version failed")
        baseline = compiler_run(lean, [source_path], "baseline")
        check_baseline(baseline)
        print("PASS baseline: Lean exit 0; all four axiom audits present and clean.", flush=True)
        with tempfile.TemporaryDirectory(prefix="factoidal-verdict-contract-") as temp:
            for mutation, mutated in prepared:
                path = Path(temp) / f"{mutation.name.replace('-', '_')}.lean"
                path.write_text(mutated, encoding="utf-8")
                result = compiler_run(lean, [path], mutation.name)
                diagnostic = check_rejection(result, mutated, mutation)
                print(f"PASS {mutation.name}: rejected in the affected proof.", flush=True)
                print(f"Proof diagnostic: {diagnostic}", flush=True)
        print("Interface-example checks: 1 baseline pass, 3 semantic mutations rejected.", flush=True)
        print("NOT product verdict assurance.", flush=True)
        return 0
    except (CheckFailure, OSError, UnicodeError) as error:
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    sys.exit(main())
