#!/usr/bin/env python3
"""Controls for the narrowly scoped assembly lowering and linked ELF scan.

Set FACTOIDAL_RISCV_GCC to the pinned absolute GCC path for a tiny real
assembler/linker integration test. This does not build Lean or run a proof.
"""

import contextlib
import hashlib
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


lower = load("lower_fences", "lower-fences.py")
scan = load("verify_instructions", "verify-instructions.py")


class LoweringControls(unittest.TestCase):
    def test_exact_full_fences_and_audit(self):
        before = b"\t.text\n\tfence\n\tfence\tiorw,iorw # keep this comment\n\tret\n"
        expected = b"\t.text\n\tnop\n\tnop # keep this comment\n\tret\n"
        after, audit = lower.lower_assembly(before)
        self.assertEqual(after, expected)
        self.assertEqual(audit["loweredInstructions"], 2)
        self.assertEqual(audit["instructionBytesBefore"], 8)
        self.assertEqual(audit["instructionBytesAfter"], 8)
        self.assertEqual(audit["inputSha256"], hashlib.sha256(before).hexdigest())
        self.assertEqual(audit["outputSha256"], hashlib.sha256(after).hexdigest())
        self.assertEqual([site["sourceLine"] for site in audit["sites"]], [2, 3])

    def test_operands_spacing_and_newline_preserved(self):
        before = b"  fence iorw, iorw \t# comment\r\nfence"
        after, audit = lower.lower_assembly(before)
        self.assertEqual(after, b"  nop \t# comment\r\nnop")
        self.assertEqual(audit["loweredInstructions"], 2)

    def test_comments_labels_directives_and_data_unchanged(self):
        before = (b'# fence; fence.i\n\t.ascii "fence; fence.i # still data"\n'
                  b'\t.string "quoted \\" fence"\n\t.word 0x0ff0000f\n'
                  b'\t.type fence, @function\nfence:\n\tret # fence.i\n')
        after, audit = lower.lower_assembly(before)
        self.assertEqual(after, before)
        self.assertEqual(audit["loweredInstructions"], 0)

    def test_instruction_fence_i_and_other_forms_are_refused(self):
        for instruction in ("fence.i", "fence.tso", "fence rw,rw", "fence r,w",
                            "fence iorw,iorw,iorw", "FENCE", "FENCE.I"):
            with self.subTest(instruction=instruction):
                with self.assertRaises(lower.LoweringError):
                    lower.lower_assembly(("\t" + instruction + "\n").encode())

    def test_compound_and_inline_label_fences_refused(self):
        for line in ("nop; fence", "fence; nop", "label: fence", "1: fence.i",
                     '.ascii "text"; fence'):
            with self.subTest(line=line):
                with self.assertRaises(lower.LoweringError):
                    lower.lower_assembly((line + "\n").encode())

    def test_idempotence(self):
        once, _ = lower.lower_assembly(b"\tfence\n")
        twice, audit = lower.lower_assembly(once)
        self.assertEqual(once, twice)
        self.assertEqual(audit["loweredInstructions"], 0)

    def test_refusal_does_not_write_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, output, audit = root / "in.s", root / "out.s", root / "audit.json"
            source.write_bytes(b"\tfence\n\tfence.i\n")
            with contextlib.redirect_stderr(io.StringIO()):
                code = lower.main(["--input", str(source), "--output", str(output), "--audit", str(audit)])
            self.assertEqual(code, 1)
            self.assertFalse(output.exists())
            self.assertFalse(audit.exists())
            with contextlib.redirect_stderr(io.StringIO()):
                code = lower.main(["--input", str(source), "--output", str(source), "--audit", str(audit)])
            self.assertEqual(code, 1)
            self.assertEqual(source.read_bytes(), b"\tfence\n\tfence.i\n")

    def test_scanner_uses_opcodes_including_unknown_aliases(self):
        result = scan.scan_disassembly("""Disassembly of section .text:
00200800 <_start>:
  200800: 0ff0000f fence
  200804: 0000100f fence.i
  200808: 1005202f .4byte 0x1005202f
  20080c: 00000013 addi zero,zero,0
  200810: 00008067 jalr zero,0(ra)
""")
        self.assertEqual(result["instructionsScanned"], 5)
        self.assertEqual(result["forbiddenInstructions"], 3)
        self.assertEqual(result["violations"][2]["kind"], "atomic/AMO")

    def test_scanner_refuses_empty_or_compressed_output(self):
        for text in ("", "There is no code", " 200800: 0001 c.nop\n"):
            with self.subTest(text=text):
                with self.assertRaises(scan.InstructionError):
                    scan.scan_disassembly(text)

    @unittest.skipUnless(os.environ.get("FACTOIDAL_RISCV_GCC"), "explicit pinned GCC not supplied")
    def test_real_assembly_preserves_addresses_and_omits_rodata(self):
        gcc = Path(os.environ["FACTOIDAL_RISCV_GCC"])
        objdump = gcc.with_name("riscv32-unknown-elf-objdump")
        original = (b".text\n.globl _start\n_start:\n\tfence\n\tfence iorw,iorw\n"
                    b"\taddi a0,zero,7\n\tjalr zero,ra,0\n"
                    b".section .rodata\n\t.word 0x0ff0000f\n")
        lowered, audit = lower.lower_assembly(original)
        self.assertEqual(audit["loweredInstructions"], 2)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            addresses = []
            for name, source in (("before", original), ("after", lowered)):
                assembly, binary = root / (name + ".s"), root / (name + ".elf")
                assembly.write_bytes(source)
                subprocess.run([str(gcc), "-march=rv32im", "-mabi=ilp32", "-nostdlib",
                    "-Wl,--no-relax", "-Wl,-Ttext=0x200800", "-Wl,-e,_start",
                    "-x", "assembler", str(assembly), "-o", str(binary)], check=True,
                    capture_output=True, timeout=30)
                result = scan.inspect_elf(binary.read_bytes(), objdump)
                self.assertEqual(result["forbiddenInstructions"], 2 if name == "before" else 0)
                disassembly = subprocess.check_output([str(objdump), "-d", "-M", "no-aliases", str(binary)], text=True)
                addresses.append([match[1] for line in disassembly.splitlines()
                                  if (match := scan.INSTRUCTION.match(line))])
                if name == "after":
                    self.assertEqual(result, scan.inspect_elf(binary.read_bytes(), objdump))
            self.assertEqual(addresses[0], addresses[1])


if __name__ == "__main__":
    unittest.main()
