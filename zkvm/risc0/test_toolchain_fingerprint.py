#!/usr/bin/env python3
"""Cache/provenance controls using small temporary compiler-tree fixtures."""
import importlib.util
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("build_runtime", Path(__file__).with_name("build-runtime.py"))
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


class FingerprintControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="factoidal-toolchain-fingerprint-")
        self.root = Path(self.temporary.name) / "cpp"
        self.root.mkdir()
        self.contents = {"bin/gcc": b"unchanged GCC version and driver",
                         "bin/as": b"assembler", "libexec/cc1": b"compiler implementation",
                         "include/runtime.h": b"header", "lib/libstdc++.a": b"archive"}
        self.populate(self.root, self.contents.items())

    def tearDown(self):
        self.temporary.cleanup()

    def populate(self, root, entries):
        for name, data in entries:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o755 if name.startswith("bin/") else 0o644)

    def fingerprint(self, root=None):
        return build.fingerprint_toolchain(root or self.root)

    def test_gcc_overrides_including_empty_values_fail_before_build_mutation(self):
        output = Path(self.temporary.name) / "must-not-be-created"
        args = ["build-runtime.py", "--toolchain", str(self.root),
                "--lean-source", str(self.root), "--cpp", str(self.root),
                "--out", str(output)]
        with patch.dict(os.environ, {}, clear=True):
            build.require_clean_compiler_environment()
        for name in ("CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH",
                     "COMPILER_PATH", "GCC_EXEC_PREFIX", "LIBRARY_PATH"):
            for value in ("", "/untracked/compiler/input"):
                with self.subTest(name=name, value=value):
                    with patch.dict(os.environ, {name: value}, clear=True), patch.object(sys, "argv", args):
                        with self.assertRaisesRegex(ValueError, name):
                            build.main()
                    self.assertFalse(output.exists())

    def test_root_location_creation_order_and_timestamps_do_not_change_digest(self):
        other = Path(self.temporary.name) / "relocated"
        other.mkdir()
        self.populate(other, reversed(list(self.contents.items())))
        for path in other.rglob("*"):
            os.utime(path, (1_600_000_000, 1_600_000_000))
        self.assertEqual(self.fingerprint()["sha256"], self.fingerprint(other)["sha256"])

    def test_non_driver_compiler_inputs_invalidate_the_tree(self):
        original = self.fingerprint()["sha256"]
        driver_hash = build.digest_file(self.root / "bin/gcc")
        for name in ("bin/as", "libexec/cc1", "include/runtime.h", "lib/libstdc++.a"):
            with self.subTest(name=name):
                path = self.root / name
                before = path.read_bytes()
                path.write_bytes(before + b" changed")
                self.assertNotEqual(self.fingerprint()["sha256"], original)
                self.assertEqual(build.digest_file(self.root / "bin/gcc"), driver_hash)
                path.write_bytes(before)
        self.assertEqual(self.fingerprint()["sha256"], original)

    def test_relative_names_and_executable_bits_are_bound(self):
        original = self.fingerprint()["sha256"]
        path = self.root / "include/runtime.h"
        renamed = self.root / "include/renamed.h"
        path.rename(renamed)
        self.assertNotEqual(self.fingerprint()["sha256"], original)
        renamed.rename(path)
        path.chmod(0o755)
        self.assertNotEqual(self.fingerprint()["sha256"], original)

    def test_symlink_targets_are_bound_without_following_directory_links(self):
        link = self.root / "compiler"
        link.symlink_to("libexec/cc1")
        first = self.fingerprint()
        link.unlink()
        link.symlink_to("./libexec/cc1")
        self.assertNotEqual(first["sha256"], self.fingerprint()["sha256"])
        (self.root / "loop").symlink_to(".", target_is_directory=True)
        result = self.fingerprint()
        self.assertEqual(result["files"], len(self.contents))
        self.assertEqual(result["symlinks"], 2)

    def test_external_and_broken_symlinks_are_refused(self):
        outside = Path(self.temporary.name) / "outside"
        outside.write_bytes(b"untracked compiler input")
        link = self.root / "external"
        link.symlink_to(outside)
        with self.assertRaises(ValueError):
            self.fingerprint()
        link.unlink()
        link.symlink_to("missing")
        with self.assertRaises(OSError):
            self.fingerprint()

    def test_large_file_bytes_are_streamed_and_counted(self):
        data = b"large-object-data" * (200_000)
        (self.root / "lib/large.a").write_bytes(data)
        result = self.fingerprint()
        self.assertEqual(result["regularBytes"], sum(map(len, self.contents.values())) + len(data))
        self.assertEqual(result["files"], len(self.contents) + 1)

    def test_special_files_and_empty_trees_are_refused(self):
        empty = Path(self.temporary.name) / "empty"
        empty.mkdir()
        with self.assertRaises(ValueError):
            self.fingerprint(empty)
        os.mkfifo(self.root / "pipe")
        with self.assertRaises(ValueError):
            self.fingerprint()

    def test_symlink_root_resolves_to_the_same_installed_tree(self):
        alias = Path(self.temporary.name) / "cpp-alias"
        alias.symlink_to(self.root, target_is_directory=True)
        self.assertEqual(self.fingerprint(), self.fingerprint(alias))


if __name__ == "__main__":
    unittest.main()
