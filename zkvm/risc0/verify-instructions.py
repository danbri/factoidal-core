#!/usr/bin/env python3
"""Refuse linked RISC-V FENCE and atomic instructions using pinned objdump.

Companion to verify-elf.py. This gate disassembles executable sections of a
final ELF32 little-endian RISC-V ET_EXEC using an explicitly selected GNU
objdump. It checks instruction words, not only disassembler aliases:
MISC-MEM opcode 0x0f (including FENCE/FENCE.I) and AMO opcode 0x2f (including
LR/SC) are refused. No instruction is modified. This is not a complete ISA
validator or an execution/proof check.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile


class InstructionError(ValueError):
    pass


INSTRUCTION = re.compile(r"^\s*([0-9a-fA-F]+):\s+([0-9a-fA-F]{8})\s+(.+)$")
SHORT_INSTRUCTION = re.compile(r"^\s*([0-9a-fA-F]+):\s+([0-9a-fA-F]{4})\s+(.+)$")
SYMBOL = re.compile(r"^[0-9a-fA-F]+ <(.+)>:$")


def scan_disassembly(text: str) -> dict:
    count, symbol, section, violations = 0, None, None, []
    for line in text.splitlines():
        if line.startswith("Disassembly of section ") and line.endswith(":"):
            section = line[len("Disassembly of section "):-1]
        match = SYMBOL.match(line)
        if match:
            symbol = match[1]
        match = INSTRUCTION.match(line)
        if match:
            count += 1
            address, word = int(match[1], 16), int(match[2], 16)
            if word & 127 in (15, 47):
                violations.append({"address": f"0x{address:08x}", "word": f"0x{word:08x}",
                    "kind": "fence/MISC-MEM" if word & 127 == 15 else "atomic/AMO",
                    "disassembly": match[3], "section": section, "symbol": symbol})
        elif SHORT_INSTRUCTION.match(line):
            raise InstructionError("compressed instructions are outside the RV32IM profile")
    if count == 0:
        raise InstructionError("objdump produced no recognisable 32-bit instructions")
    return {"instructionsScanned": count, "forbiddenInstructions": len(violations),
            "violations": violations}


def inspect_elf(data: bytes, objdump: Path) -> dict:
    if (len(data) < 52 or data[:7] != b"\x7fELF\x01\x01\x01"
            or struct.unpack_from("<HH", data, 16) != (2, 243)
            or struct.unpack_from("<I", data, 36)[0] != 0):
        raise InstructionError("require ELF32 little-endian RISC-V ET_EXEC with zero ABI flags")
    with tempfile.TemporaryDirectory(prefix="factoidal-instruction-check-") as directory:
        path = Path(directory) / "guest.elf"
        path.write_bytes(data)
        result = subprocess.run([str(objdump), "-d", "-z", "-M", "no-aliases", str(path)],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60,
            env=dict(os.environ, LC_ALL="C"))
    if result.returncode != 0 or result.stderr.strip():
        raise InstructionError("objdump refused or warned: " + result.stderr[-2000:])
    disassembly = result.stdout.replace(str(path), "<guest.elf>")
    report = scan_disassembly(disassembly)
    report.update({"elfSha256": hashlib.sha256(data).hexdigest(),
                   "disassemblySha256": hashlib.sha256(disassembly.encode()).hexdigest()})
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--objdump", required=True, type=Path)
    parser.add_argument("--objdump-sha256", help="expected hash of the selected tool")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args(argv)
    report = {"status": "refused"}
    try:
        if not args.objdump.is_absolute():
            raise InstructionError("--objdump must be an absolute pinned tool path")
        tool = args.objdump.resolve(strict=True)
        tool_hash = hashlib.sha256(tool.read_bytes()).hexdigest()
        if args.objdump_sha256 is not None and args.objdump_sha256.lower() != tool_hash:
            raise InstructionError("selected objdump does not match --objdump-sha256")
        version = subprocess.check_output([str(tool), "--version"], text=True, timeout=10,
                    env=dict(os.environ, LC_ALL="C")).splitlines()[0]
        if not version.startswith("GNU objdump "):
            raise InstructionError("require the pinned GNU objdump")
        with args.elf.open("rb") as stream:
            data = stream.read(128 * 1024**2 + 1)
        if len(data) > 128 * 1024**2:
            raise InstructionError("ELF exceeds the 128 MiB profile limit")
        report.update(inspect_elf(data, tool))
        report["objdump"] = {"path": str(tool), "sha256": tool_hash, "version": version}
        report["elf"] = str(args.elf)
        if report["forbiddenInstructions"] == 0:
            report["status"] = "ok"
    except (OSError, ValueError, subprocess.SubprocessError, struct.error) as error:
        report["error"] = str(error)
    if args.report:
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    summary = {key: value for key, value in report.items() if key != "violations"}
    if report.get("violations"):
        summary["firstViolations"] = report["violations"][:10]
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if report["status"] == "ok" else 1


if __name__ == "__main__":
    sys.exit(main())
