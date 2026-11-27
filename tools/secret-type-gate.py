#!/usr/bin/env python3
"""Secret-type gate: every registered secret-key type stays opaque.

Layer 1 of docs/designissues/2026-11-27-bignum-timing-and-aes.md section 6.
A secret type is a Lean structure whose bytes only HACL* calls may use. For
each entry of SECRET_TYPES this gate checks, from the source text:

  1. the structure has a private constructor (`private mk ::`) and every field
     is `private`;
  2. it has no `deriving` clause;
  3. no Lean file in the tree declares an instance for it or derives one
     (`instance ... : C <Type>`, `deriving instance ... for <Type>`);
  4. its module holds the `#check_failure` lines that fail the build if the
     type gets decidable equality, `BEq`, `ToString`, `Repr`, `Hashable` or
     `Ord`.

The Lean build enforces rule 4 itself; rules 1 to 3 catch a change before a
build runs. Pure Python over `git ls-files`; no build.

  python3 tools/secret-type-gate.py              exit 0 clean, 1 on a violation
  python3 tools/secret-type-gate.py --self-test  checks the gate refuses mutants

An empty walk is an error (anti-pattern 30).
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# (module path, type name). Add a row for each new secret type.
SECRET_TYPES = [
    ("formal/lean4/L4Factoidal/Crypto/K256Native.lean", "SecretKey"),
]

REQUIRED_CHECKS = [
    r"decide\s*\(a\s*=\s*b\)",
    r"a\s*==\s*b",
    r"toString\s+a",
    r"repr\s+a",
    r"hash\s+a",
    r"compare\s+a\s+b",
]


def structure_block(src: str, name: str):
    m = re.search(rf"^structure\s+{re.escape(name)}\b[^\n]*\n((?:[ \t]+[^\n]*\n|[ \t]*\n)*)", src, re.M)
    if not m:
        return None, None
    block = m.group(1)
    # A deriving clause may follow the indented block on its own line.
    after = src[m.end():].lstrip("\n")
    return block, after


def check_module(path: str, src: str, name: str):
    errors = []
    block, after = structure_block(src, name)
    if block is None:
        return [f"{path}: structure {name} not found"]
    lines = [l.strip() for l in block.splitlines() if l.strip() and not l.strip().startswith("--")]
    if not lines or not re.match(r"private\s+mk\s*::", lines[0]):
        errors.append(f"{path}: {name} must start with `private mk ::`")
    for l in lines[1:]:
        if l.startswith("deriving"):
            errors.append(f"{path}: {name} has a deriving clause: {l}")
        elif re.match(r"[A-Za-z_]\w*\s*:", l):
            errors.append(f"{path}: {name} field is not private: {l}")
    if re.match(r"deriving\b", after or ""):
        errors.append(f"{path}: {name} has a deriving clause")
    for pat in REQUIRED_CHECKS:
        if not re.search(rf"#check_failure\s*\(fun\s*\([^)]*:\s*{re.escape(name)}\)\s*=>\s*{pat}\)", src):
            errors.append(f"{path}: missing `#check_failure` for {pat!r} on {name}")
    return errors


def check_instances(files: dict, name: str):
    errors = []
    inst = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?instance\b[^\n]*\b{re.escape(name)}\b", re.M)
    der = re.compile(rf"deriving\s+instance\b[^\n]*\bfor\b[^\n]*\b{re.escape(name)}\b")
    for path, src in files.items():
        for m in inst.finditer(src):
            errors.append(f"{path}: instance for secret type {name}: {m.group(0).strip()}")
        for m in der.finditer(src):
            errors.append(f"{path}: derived instance for secret type {name}: {m.group(0).strip()}")
    return errors


def lean_files():
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True, text=True, check=True)
    paths = [p for p in out.stdout.splitlines() if p.startswith("formal/lean4/")]
    if not paths:
        sys.exit("secret-type-gate: no Lean files found (empty walk)")
    return {p: (ROOT / p).read_text(errors="replace") for p in paths}


def run(files: dict):
    errors = []
    for path, name in SECRET_TYPES:
        if path not in files:
            errors.append(f"{path}: registered secret-type module is missing")
            continue
        errors += check_module(path, files[path], name)
        errors += check_instances(files, name)
    return errors


def self_test(files: dict):
    path, name = SECRET_TYPES[0]
    src = files[path]
    mutants = {
        "public constructor": src.replace("  private mk ::\n", "  mk ::\n", 1),
        "public field": src.replace("  private bytes : ByteArray", "  bytes : ByteArray", 1),
        "deriving BEq": src.replace("  private bytes : ByteArray\n", "  private bytes : ByteArray\n  deriving BEq\n", 1),
        "instance elsewhere": None,
        "check removed": re.sub(r"#check_failure \(fun \(a b : SecretKey\) => a == b\)\n", "", src, count=1),
    }
    bad = 0
    for label, mutant in mutants.items():
        trial = dict(files)
        if mutant is None:
            trial["formal/lean4/Mutant.lean"] = f"instance : BEq {name} := ⟨fun _ _ => true⟩\n"
        else:
            if mutant == src:
                print(f"FAIL self-test: mutation '{label}' did not apply")
                bad += 1
                continue
            trial[path] = mutant
        found = run(trial)
        print(f"{'PASS' if found else 'FAIL'} self-test: gate refuses '{label}'")
        bad += 0 if found else 1
    clean = run(files)
    print(f"{'PASS' if not clean else 'FAIL'} self-test: unmodified tree is clean")
    return bad + (1 if clean else 0)


def main():
    files = lean_files()
    if "--self-test" in sys.argv:
        sys.exit(1 if self_test(files) else 0)
    errors = run(files)
    for e in errors:
        print(e)
    print(f"secret-type-gate: {len(SECRET_TYPES)} secret types, {len(errors)} violations, {len(files)} Lean files read")
    sys.exit(1 if errors else 0)


if __name__ == "__main__":
    main()
