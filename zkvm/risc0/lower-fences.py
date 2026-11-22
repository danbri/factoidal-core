#!/usr/bin/env python3
"""Lower GCC's ordinary full FENCE to a four-byte NOP for this guest only.

The restricted RISC Zero target has one non-preemptive hart, no threads,
signal handlers or memory-mapped devices. Its ordinary memory-order fence
has no observable effect. Lowering AFTER GCC emits assembly preserves the
compiler's ordering decisions. Assemble with the original RV32IM/ILP32
flags; no compressed instructions are enabled, so `nop` is four bytes.

Only a standalone `fence` or `fence iorw,iorw` instruction is accepted.
FENCE.I, other fence forms and compound instruction lines are refused.
Directives, data and comments are preserved, including fence-like text in
strings. This is not a binary patch and is not suitable for a threaded,
device-backed or self-modifying-code target.

Build API: `lower_assembly(source: bytes) -> tuple[bytes, dict]`.
Keep the original assembly, lowered assembly and returned audit together.
The final linked ELF must also pass verify-instructions.py, because external
archives and Rust code do not pass through this source lowering.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile


class LoweringError(ValueError):
    pass


LABEL = re.compile(r"^\s*(?:(?:[A-Za-z_.$][A-Za-z0-9_.$]*|[0-9]+):\s*)+")


def statements(line: str) -> tuple[list[str], str]:
    """Split GNU assembly statements; quoted text and # comments are opaque."""
    result, start, quoted, escaped = [], 0, None, False
    for index, character in enumerate(line):
        if quoted:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == quoted:
                quoted = None
        elif character in ('"', "'"):
            quoted = character
        elif character == "#":
            result.append(line[start:index])
            return result, line[index:]
        elif character == ";":
            result.append(line[start:index])
            start = index + 1
    result.append(line[start:])
    return result, ""


def lower_assembly(source: bytes) -> tuple[bytes, dict]:
    text = source.decode("utf-8")
    output, sites = [], []
    for number, original in enumerate(text.splitlines(keepends=True), start=1):
        ending = "\r\n" if original.endswith("\r\n") else "\n" if original.endswith("\n") else ""
        line = original[:-len(ending)] if ending else original
        parts, comment = statements(line)
        fence = None
        for part in parts:
            instruction = LABEL.sub("", part).strip()
            if not instruction or instruction.startswith("."):
                continue
            opcode = instruction.split()[0]
            if opcode.lower() == "fence" or opcode.lower().startswith("fence."):
                fence = instruction
                break
        if fence is None:
            output.append(original)
            continue
        if len(parts) != 1 or LABEL.match(parts[0]):
            raise LoweringError(f"line {number}: fence must be a standalone instruction")
        words = fence.split(None, 1)
        operands = re.sub(r"\s+", "", words[1]) if len(words) > 1 else ""
        if words[0] != "fence" or operands not in ("", "iorw,iorw"):
            raise LoweringError(f"line {number}: unsupported fence form {fence!r}; FENCE.I is never lowered")
        leading = parts[0][:len(parts[0]) - len(parts[0].lstrip())]
        trailing = parts[0][len(parts[0].rstrip()):]
        output.append(leading + "nop" + trailing + comment + ending)
        sites.append({"sourceLine": number, "instruction": fence,
                      "beforeWord": "0ff0000f", "afterWord": "00000013"})
    lowered = "".join(output).encode("utf-8")
    audit = {"schema": "factoidal.risc0.single-hart-fence-lowering.v1",
             "requiredAssemblerFlags": ["-march=rv32im", "-mabi=ilp32"],
             "inputSha256": hashlib.sha256(source).hexdigest(),
             "outputSha256": hashlib.sha256(lowered).hexdigest(),
             "loweredInstructions": len(sites), "instructionBytesBefore": 4 * len(sites),
             "instructionBytesAfter": 4 * len(sites), "sites": sites}
    return lowered, audit


def aliases(first: Path, second: Path) -> bool:
    return first.resolve() == second.resolve() or (
        first.exists() and second.exists() and first.samefile(second))


def atomic_write(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix="." + path.name, dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--audit", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        paths = (args.input, args.output, args.audit)
        if any(aliases(first, second) for index, first in enumerate(paths) for second in paths[index + 1:]):
            raise LoweringError("input, output and audit must be distinct files")
        lowered, audit = lower_assembly(args.input.read_bytes())
        audit.update({"input": str(args.input.resolve()), "output": str(args.output.resolve())})
        atomic_write(args.output, lowered)
        atomic_write(args.audit, (json.dumps(audit, indent=2, sort_keys=True) + "\n").encode())
        print(json.dumps({"loweredInstructions": audit["loweredInstructions"],
                          "inputSha256": audit["inputSha256"], "outputSha256": audit["outputSha256"]}))
        return 0
    except (OSError, ValueError, UnicodeError) as error:
        print(f"Fence lowering refused: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
