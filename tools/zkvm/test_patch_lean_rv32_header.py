#!/usr/bin/env python3
"""Check the pinned transformation, real-header UBSan cases and RV32 layout.

Requires a pristine Lean source checkout and its generated config include
directory. Generated headers, diagnostics and assembly stay in --output-dir.
No runtime behaviour is mocked. The host probe uses synthetic constructor
storage; the optional RV32 probe is compilation only.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import patch_lean_rv32_header as patch


class PatchContract(unittest.TestCase):
    source: bytes

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="lean-header-contract-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.input = self.root / "pristine.h"
        self.output = self.root / "generated.h"
        self.manifest = self.root / "audit.json"
        self.input.write_bytes(self.source)

    def test_only_reviewed_edits(self) -> None:
        generated, audit = patch.patch_header(self.source)
        self.assertEqual([edit["name"] for edit in audit["edits"]], [
            "string_header", "lean_ctor_get_uint64", "lean_ctor_get_float",
            "lean_ctor_set_uint64", "lean_ctor_set_float",
        ])
        restored = generated
        for _, before, after in reversed(patch.EDITS):
            self.assertEqual(restored.count(after), 1)
            restored = restored.replace(after, before, 1)
        self.assertEqual(restored, self.source)
        self.assertEqual(audit["output_sha256"], patch.sha256(generated))
        self.assertEqual(patch.patch_header(self.source), (generated, audit))

    def test_generated_copy_preserves_input(self) -> None:
        audit = patch.generate(self.input, self.output, self.manifest)
        self.assertEqual(self.input.read_bytes(), self.source)
        self.assertEqual(self.output.read_bytes(), patch.patch_header(self.source)[0])
        self.assertEqual(json.loads(self.manifest.read_text()), audit)

    def test_upstream_drift_preserves_existing_outputs(self) -> None:
        self.input.write_bytes(self.source + b"\n")
        self.output.write_bytes(b"old generated output")
        self.manifest.write_bytes(b"old manifest")
        with self.assertRaisesRegex(patch.PatchError, "unreviewed Lean header"):
            patch.generate(self.input, self.output, self.manifest)
        self.assertEqual(self.output.read_bytes(), b"old generated output")
        self.assertEqual(self.manifest.read_bytes(), b"old manifest")

    def test_already_patched_input_is_refused(self) -> None:
        with self.assertRaises(patch.PatchError):
            patch.patch_header(patch.patch_header(self.source)[0])

    def test_in_place_output_is_refused(self) -> None:
        with self.assertRaises(patch.PatchError):
            patch.generate(self.input, self.input, self.manifest)
        self.assertEqual(self.input.read_bytes(), self.source)

    def test_symlink_output_alias_is_refused(self) -> None:
        self.output.symlink_to(self.input)
        with self.assertRaises(patch.PatchError):
            patch.generate(self.input, self.output, self.manifest)
        self.assertEqual(self.input.read_bytes(), self.source)

    def test_hardlink_output_alias_is_refused(self) -> None:
        self.output.hardlink_to(self.input)
        with self.assertRaises(patch.PatchError):
            patch.generate(self.input, self.output, self.manifest)
        self.assertEqual(self.input.read_bytes(), self.source)

    def test_manifest_aliases_are_refused(self) -> None:
        for manifest in (self.input, self.output):
            with self.assertRaises(patch.PatchError):
                patch.generate(self.input, self.output, manifest)
        self.assertEqual(self.input.read_bytes(), self.source)


def run(command: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(command, text=True, capture_output=True, timeout=60)
    if check and completed.returncode != 0:
        raise RuntimeError(f"command failed: {command!r}\n{completed.stdout}\n{completed.stderr}")
    return completed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-src", required=True, type=Path, help="Lean checkout root (contains src/)")
    parser.add_argument("--config-include", required=True, type=Path, help="contains generated lean/config.h")
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--cc", default="gcc")
    parser.add_argument("--cxx", default="g++")
    parser.add_argument("--rv32-cxx", help="optional actual RISC Zero RV32 C++ compiler")
    args = parser.parse_args()
    args.lean_src = args.lean_src.resolve()
    args.config_include = args.config_include.resolve()
    args.output_dir = args.output_dir.resolve()
    header = args.lean_src / "src/include/lean/lean.h"
    pristine = header.read_bytes()
    PatchContract.source = pristine
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(PatchContract)
    )
    if not result.wasSuccessful():
        raise SystemExit(1)

    args.output_dir.mkdir(parents=True, exist_ok=True)
    patched_include = args.output_dir / "patched/include"
    audit = patch.generate(
        header, patched_include / "lean/lean.h", args.output_dir / "header-audit.json"
    )
    sources = Path(__file__).resolve().parent
    include_variants = {
        "upstream": args.lean_src / "src/include",
        "patched": patched_include,
    }
    report = {
        "patch": audit,
        "contract_tests": result.testsRun,
        "config_sha256": patch.sha256((args.config_include / "lean/config.h").read_bytes()),
        "compiler_versions": {},
        "compile_commands": [],
        "ubsan": [],
        "rv32": [],
    }
    source_lines = {edit["name"]: edit["source_line"] for edit in audit["edits"]}
    modes = ("get_uint64", "set_uint64", "get_float", "set_float")
    for language, compiler, standard in (("c", args.cc, "gnu11"), ("c++", args.cxx, "gnu++17")):
        report["compiler_versions"][language] = run([compiler, "--version"]).stdout.splitlines()[0]
        for variant, first_include in include_variants.items():
            label = f"{language.replace('+', 'p')}-{variant}"
            executable = args.output_dir / label
            command = [
                compiler, "-x", language, f"-std={standard}", "-O2", "-g",
                "-fsanitize=undefined", "-fno-sanitize-recover=undefined",
                "-I", str(first_include), "-I", str(args.config_include),
                "-I", str(args.lean_src / "src/include"),
                str(sources / "scalar_access_probe.c"), "-o", str(executable),
            ]
            run(command)
            report["compile_commands"].append(command)
            for mode in modes + (("roundtrip",) if variant == "patched" else ()):
                completed = run([str(executable), mode], check=False)
                (args.output_dir / f"{label}-{mode}.stderr").write_text(completed.stderr)
                (args.output_dir / f"{label}-{mode}.stdout").write_text(completed.stdout)
                if variant == "upstream":
                    fault_anchor = f"lean.h:{source_lines['lean_ctor_' + mode] + 2}:"
                    passed = (
                        completed.returncode != 0 and "misaligned address" in completed.stderr
                        and fault_anchor in completed.stderr
                    )
                else:
                    passed = completed.returncode == 0 and not completed.stderr and "PASS" in completed.stdout
                if not passed:
                    raise RuntimeError(f"unexpected {label}/{mode} result: {completed}")
                report["ubsan"].append({
                    "language": language, "variant": variant, "mode": mode,
                    "exit_code": completed.returncode,
                    "expected_misalignment_reproduced": variant == "upstream",
                })
            print(f"PASS {label}: {'4 expected UBSan failures' if variant == 'upstream' else '5 clean bit-pattern/guard checks'}")

    if args.rv32_cxx:
        report["compiler_versions"]["rv32"] = run([args.rv32_cxx, "--version"]).stdout.splitlines()[0]
        for variant, first_include in include_variants.items():
            assembly = args.output_dir / f"rv32-{variant}.s"
            command = [
                args.rv32_cxx, "-march=rv32im", "-mabi=ilp32", "-std=c++17", "-O2", "-DNDEBUG",
                "-I", str(first_include), "-I", str(args.config_include),
                "-I", str(args.lean_src / "src/include"), "-I", str(args.lean_src / "src"),
                "-S", str(sources / "rv32_layout_probe.cpp"), "-o", str(assembly),
            ]
            run(command)
            report["compile_commands"].append(command)
            report["rv32"].append({"variant": variant, "assembly": str(assembly), "compiled_only": True})
            print(f"PASS RV32 {variant}: target layout assertions and accessor compilation")

    if header.read_bytes() != pristine:
        raise RuntimeError("pristine source header changed during tests")
    (args.output_dir / "test-report.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"PASS: pristine header unchanged; report {args.output_dir / 'test-report.json'}")


if __name__ == "__main__":
    main()
