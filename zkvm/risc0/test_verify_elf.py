#!/usr/bin/env python3
"""Adversarial binary-format controls; no compiler or guest execution needed.

Set FACTOIDAL_RISCV_READELF to run the selected tool's integration controls.
Fixtures are assembled from public ELF fields in memory and never committed.
"""

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import struct
import tempfile
import unittest


spec = importlib.util.spec_from_file_location("verify_elf", Path(__file__).with_name("verify-elf.py"))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def fixture(*, executable=True, program=1, section_name=".text", section_flags=6,
            symbol_type=0, relocation=0):
    names = b"\0.shstrtab\0" + section_name.encode() + b"\0.symtab\0.strtab\0.rela.text\0"
    text_name = names.index(section_name.encode())
    addresses = 0x200800 if executable else 0
    data = bytearray(84 if executable else 52)
    text_at = len(data)
    data.extend(bytes.fromhex("67800000"))  # RV32 ret; never executed by these tests.
    names_at = len(data)
    data.extend(names)
    while len(data) % 4:
        data.append(0)
    symbols_at = len(data)
    data.extend(bytes(16) + struct.pack("<IIIBBH", 1, addresses, 4, 0x10 | symbol_type, 0, 2))
    strings_at = len(data)
    data.extend(b"\0entry\0\0")
    relocs_at = len(data)
    data.extend(struct.pack("<IIi", addresses, (1 << 8) | relocation, 0))
    sections_at = len(data)
    sections = [
        (0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        (1, 3, 0, 0, names_at, len(names), 0, 0, 1, 0),
        (text_name, 1, section_flags, addresses, text_at, 4, 0, 0, 4, 0),
        (names.index(b".symtab"), 2, 0, 0, symbols_at, 32, 4, 1, 4, 16),
        (names.index(b".strtab"), 3, 0, 0, strings_at, 8, 0, 0, 1, 0),
        (names.index(b".rela.text"), 4, 0, 0, relocs_at, 12, 3, 2, 4, 12),
    ]
    for section in sections:
        data.extend(struct.pack("<IIIIIIIIII", *section))
    data[:16] = b"\x7fELF\x01\x01\x01" + bytes(9)
    struct.pack_into("<HHIIIIIHHHHHH", data, 16, 2 if executable else 1, 243, 1,
                     addresses, 52 if executable else 0, sections_at, 0, 52,
                     32 if executable else 0, 1 if executable else 0, 40, 6, 1)
    if executable:
        struct.pack_into("<IIIIIIII", data, 52, program, text_at, addresses, addresses, 4, 4, 5, 4)
    return bytes(data)


def member(name, payload):
    header = f"{name:<16}{0:<12}{0:<6}{0:<6}{'644':<8}{len(payload):<10}`\n".encode()
    assert len(header) == 60
    return header + payload + (b"\n" if len(payload) % 2 else b"")


def mutate(data, offset, fmt, value):
    result = bytearray(data)
    struct.pack_into(fmt, result, offset, value)
    return bytes(result)


class BinaryControls(unittest.TestCase):
    def check(self, data, executable=True):
        return gate.elf(data, "fixture", executable)

    def test_valid_executable_and_relocatable(self):
        self.assertEqual(self.check(fixture())["issues"], [])
        self.assertEqual(self.check(fixture(executable=False), False)["issues"], [])

    def test_identification_and_architecture_rejections(self):
        for offset, fmt, value in [(0, "<I", 0), (4, "B", 2), (5, "B", 2),
                                   (7, "B", 3), (16, "<H", 3), (18, "<H", 62),
                                   (20, "<I", 2), (36, "<I", 1), (40, "<H", 64)]:
            with self.subTest(offset=offset):
                with self.assertRaises(gate.GateError):
                    self.check(mutate(fixture(), offset, fmt, value))

    def test_invalid_entry_and_truncated_headers(self):
        for data in [fixture()[:51], mutate(fixture(), 24, "<I", 0),
                     mutate(fixture(), 24, "<I", 0x200802),
                     mutate(fixture(), 28, "<I", 0xfffffff0),
                     mutate(fixture(), 32, "<I", 0xfffffff0)]:
            with self.subTest(size=len(data)):
                with self.assertRaises(gate.GateError):
                    self.check(data)

    def test_dynamic_interpreter_and_tls_program_headers(self):
        # Preserve the valid LOAD and append a second, forbidden header.
        for ptype in (2, 3, 7):
            data = bytearray(fixture())
            phoff = len(data)
            data.extend(data[52:84])
            data.extend(struct.pack("<IIIIIIII", ptype, 0, 0, 0, 0, 0, 0, 1))
            struct.pack_into("<I", data, 28, phoff)
            struct.pack_into("<H", data, 44, 2)
            with self.subTest(ptype=ptype):
                self.assertTrue(self.check(bytes(data))["issues"])

    def test_tls_flag_cannot_hide_under_an_innocent_section_name(self):
        self.assertIn("TLS section .text", " ".join(self.check(fixture(section_flags=0x406))["issues"]))

    def test_tls_names_are_also_rejected(self):
        for name in (".tdata", ".tbss", ".tbss.hidden"):
            with self.subTest(name=name):
                self.assertTrue(self.check(fixture(section_name=name))["issues"])

    def test_tls_symbol_without_tls_section(self):
        self.assertIn("TLS symbol", " ".join(self.check(fixture(symbol_type=6))["issues"]))

    def test_all_tls_relocation_forms(self):
        for relocation in (6, 7, 8, 9, 10, 11, 21, 22, 29, 30, 31, 32, 49, 50, 62, 63, 64, 65):
            with self.subTest(relocation=relocation):
                self.assertIn("TLS relocation", " ".join(self.check(fixture(relocation=relocation))["issues"]))

    def test_ordinary_relocations_are_preserved(self):
        for relocation in (0, 1, 16, 17, 18, 23, 24, 25, 51):
            with self.subTest(relocation=relocation):
                self.assertEqual(self.check(fixture(relocation=relocation))["issues"], [])

    def test_truncated_sections_and_bad_table_sizes(self):
        data = fixture()
        shoff = struct.unpack_from("<I", data, 32)[0]
        for altered in (data[:-1], mutate(data, shoff + 3 * 40 + 36, "<I", 0),
                        mutate(data, shoff + 5 * 40 + 36, "<I", 8),
                        mutate(data, shoff + 1 * 40 + 16, "<I", 0xffffffff)):
            with self.assertRaises(gate.GateError):
                self.check(altered)

    def test_normal_and_long_archive_member_names(self):
        obj = fixture(executable=False)
        archive = b"!<arch>\n" + member("one.o/", obj)
        self.assertEqual(list(gate.archive_objects(archive)), [("one.o", obj)])
        name = b"long_runtime_module_name.o"
        archive = b"!<arch>\n" + member("//", name + b"/\n") + member("/0", obj)
        self.assertEqual(list(gate.archive_objects(archive)), [(name.decode(), obj)])

    def test_thin_empty_duplicate_and_truncated_archives_refused(self):
        one = member("one.o/", fixture(executable=False))
        for data in (b"!<thin>\n", b"!<arch>\n", b"!<arch>\n" + one + one,
                     b"!<arch>\n" + one[:-1], b"!<arch>\n" + member("/100", b"x")):
            with self.subTest(size=len(data)):
                with self.assertRaises(gate.GateError):
                    list(gate.archive_objects(data))

    @unittest.skipUnless(os.environ.get("FACTOIDAL_RISCV_READELF"), "explicit readelf path not supplied")
    def test_real_readelf_and_cli_controls(self):
        tool = os.environ["FACTOIDAL_RISCV_READELF"]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary, archive = root / "guest.elf", root / "runtime.a"
            binary.write_bytes(fixture())
            archive.write_bytes(b"!<arch>\n" + member("one.o/", fixture(executable=False)))
            def run(*extra):
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    code = gate.main(["--readelf", tool, "--elf", str(binary),
                                      "--runtime-archive", str(archive), *extra])
                return code, json.loads(output.getvalue())
            self.assertEqual(run()[0], 0)
            self.assertEqual(run("--readelf-sha256", "0" * 64)[0], 1)
            archive.write_bytes(b"!<arch>\n" + member("one.o/", fixture(executable=False, section_flags=0x406)))
            code, report = run()
            self.assertEqual(code, 1)
            self.assertIn("TLS section", " ".join(report["issues"]))
            archive.write_bytes(b"!<arch>\n" + member("not-elf.o/", b"unrecognised"))
            self.assertEqual(run()[0], 1)


if __name__ == "__main__":
    unittest.main()
