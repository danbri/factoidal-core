#!/usr/bin/env python3
"""Check the restricted guest's ELF and, optionally, its runtime archive.

This is a binary-format/build gate, not a proof of runtime behaviour. Require
an ELF32 little-endian RISC-V static executable with the soft-float ABI and
no TLS metadata or relocations. The archive check examines every object,
including objects the final linker might discard. It rejects thin archives.

An explicit absolute --readelf path selects the pinned toolchain's GNU
readelf; its hash and version are recorded. --readelf-sha256 can enforce the
tool hash as well. Readelf examines an immutable temporary copy of the exact
bytes checked and hashed by this script. No build or source mutation occurs.
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


class GateError(ValueError):
    pass


# ELF32 ABI constants. Numeric checks also catch TLS with renamed sections.
PT_DYNAMIC, PT_INTERP, PT_TLS = 2, 3, 7
SHT_SYMTAB, SHT_RELA, SHT_DYNAMIC, SHT_NOBITS, SHT_REL, SHT_DYNSYM = 2, 4, 6, 8, 9, 11
SHF_TLS, STT_TLS = 0x400, 6
TLS_RELOCATIONS = frozenset({6, 7, 8, 9, 10, 11, 21, 22, 29, 30, 31, 32, 49, 50, 62, 63, 64, 65})
TLS_RELOCATION_NAME = re.compile(r"\bR_RISCV_\w*(?:TLS|TPREL|DTPREL)\w*\b")


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise GateError(message)


def region(data: bytes, offset: int, size: int, label: str) -> bytes:
    require(0 <= offset <= len(data) and 0 <= size <= len(data) - offset,
            f"{label}: truncated or out-of-range table")
    return data[offset:offset + size]


def elf(data: bytes, label: str, executable: bool) -> dict:
    require(len(data) >= 52 and data[:7] == b"\x7fELF\x01\x01\x01",
            f"{label}: require ELF32, little endian, version 1")
    require(data[7:16] == bytes(9), f"{label}: unsupported OS/ABI or identification padding")
    (kind, machine, version, entry, phoff, shoff, flags, ehsize, phentsize,
     phnum, shentsize, shnum, shstrndx) = struct.unpack_from("<HHIIIIIHHHHHH", data, 16)
    require(kind == (2 if executable else 1),
            f"{label}: require {'ET_EXEC' if executable else 'ET_REL'}")
    require(machine == 243 and version == 1 and ehsize == 52,
            f"{label}: wrong RISC-V ELF header")
    require(flags == 0, f"{label}: unsupported RISC-V ABI flags {flags:#x}")
    require(phnum != 0xffff and shstrndx != 0xffff and (shnum != 0 or shoff == 0),
            f"{label}: extended ELF numbering is outside this build profile")
    require(not phnum or (phoff >= 52 and phentsize == 32), f"{label}: invalid program table")
    require(not shnum or (shoff >= 52 and shentsize == 40), f"{label}: invalid section table")
    region(data, phoff, phentsize * phnum, label)
    region(data, shoff, shentsize * shnum, label)
    issues: list[str] = []
    loads, entry_mapped = 0, False
    for index in range(phnum):
        ptype, offset, address, _, filesz, memsz, pflags, alignment = struct.unpack_from(
            "<IIIIIIII", data, phoff + 32 * index)
        if ptype in (PT_DYNAMIC, PT_INTERP, PT_TLS):
            issues.append(f"{label}: forbidden program header { {2: 'DYNAMIC', 3: 'INTERP', 7: 'TLS'}[ptype] }")
        region(data, offset, filesz, label)
        if ptype == 1:
            loads += 1
            require(filesz <= memsz and address + memsz <= 2**32,
                    f"{label}: invalid load segment sizes")
            require(alignment in (0, 1) or
                    (alignment & (alignment - 1) == 0 and offset % alignment == address % alignment),
                    f"{label}: invalid load segment alignment")
            entry_mapped |= bool(pflags & 1 and address <= entry and entry + 4 <= address + filesz)
    if executable:
        require(loads > 0 and entry_mapped and entry % 4 == 0,
                f"{label}: entry must be a word-aligned address in executable file bytes")
    else:
        require(phnum == 0, f"{label}: relocatable object unexpectedly has program headers")

    sections = [struct.unpack_from("<IIIIIIIIII", data, shoff + 40 * i) for i in range(shnum)]
    strings = b""
    if shnum:
        require(shstrndx < shnum, f"{label}: invalid section-name table index")
        if shstrndx:
            names = sections[shstrndx]
            require(names[1] == 3, f"{label}: section names do not reference STRTAB")
            strings = region(data, names[4], names[5], label)
    symbols, relocations = 0, 0
    for index, section in enumerate(sections):
        name_at, stype, sflags, _, offset, size, link, _, _, entsize = section
        if strings:
            end = strings.find(b"\0", name_at)
            require(0 <= name_at < len(strings) and end >= name_at,
                    f"{label}: invalid section name")
            name = strings[name_at:end].decode("ascii", errors="backslashreplace")
        else:
            require(name_at == 0, f"{label}: section name without a string table")
            name = f"section {index}"
        if stype != SHT_NOBITS:
            region(data, offset, size, label)
        if sflags & SHF_TLS or re.match(r"^\.t(?:data|bss)(?:\.|$)", name):
            issues.append(f"{label}: TLS section {name}")
        if stype in (SHT_DYNAMIC, SHT_DYNSYM):
            issues.append(f"{label}: dynamic linking section {name}")
        if stype in (SHT_SYMTAB, SHT_DYNSYM):
            require(entsize == 16 and size % 16 == 0 and link < shnum and sections[link][1] == 3,
                    f"{label}: malformed symbol table {name}")
            for at in range(offset, offset + size, 16):
                _, _, _, info, _, _ = struct.unpack_from("<IIIBBH", data, at)
                symbols += 1
                if info & 15 == STT_TLS:
                    issues.append(f"{label}: TLS symbol in {name} at {(at - offset) // 16}")
        if stype in (SHT_RELA, SHT_REL):
            width = 12 if stype == SHT_RELA else 8
            require(entsize == width and size % width == 0,
                    f"{label}: malformed relocation table {name}")
            for at in range(offset, offset + size, width):
                info = struct.unpack_from("<I", data, at + 4)[0]
                relocations += 1
                if info & 255 in TLS_RELOCATIONS:
                    issues.append(f"{label}: TLS relocation {info & 255} in {name}")
    return {"label": label, "bytes": len(data), "sha256": sha256(data),
            "programHeaders": phnum, "sections": shnum, "symbols": symbols,
            "relocations": relocations, "issues": issues}


def archive_objects(data: bytes):
    require(data[:8] == b"!<arch>\n", "runtime archive: require a normal GNU archive, not a thin archive")
    offset, long_names, seen = 8, b"", set()
    while offset < len(data):
        header = region(data, offset, 60, "archive member header")
        require(header[58:] == b"`\n", "runtime archive: invalid member header")
        raw_name = header[:16].rstrip(b" ")
        length = header[48:58].strip()
        require(length.isdigit(), "runtime archive: invalid member size")
        size = int(length)
        payload = region(data, offset + 60, size, "archive member")
        offset += 60 + size
        if size % 2:
            require(region(data, offset, 1, "archive padding") == b"\n", "runtime archive: invalid padding")
            offset += 1
        if raw_name in (b"/", b"/SYM64/"):
            continue
        if raw_name == b"//":
            require(not long_names, "runtime archive: duplicate long-name table")
            long_names = payload
            continue
        if raw_name.startswith(b"/"):
            require(raw_name[1:].isdigit(), "runtime archive: invalid long-name reference")
            start = int(raw_name[1:])
            end = long_names.find(b"/\n", start)
            require(start < len(long_names) and end >= start, "runtime archive: invalid long-name offset")
            raw_name = long_names[start:end]
        else:
            require(raw_name.endswith(b"/"), "runtime archive: unsupported member-name encoding")
            raw_name = raw_name[:-1]
        name = raw_name.decode("ascii", errors="backslashreplace")
        require(name and name not in seen, f"runtime archive: duplicate/empty member name {name!r}")
        seen.add(name)
        yield name, payload
    require(seen, "runtime archive: no object members")


def readelf_check(tool: Path, data: bytes) -> list[str]:
    # The input can be concurrently rebuilt. Readelf sees precisely our snapshot.
    with tempfile.TemporaryDirectory(prefix="factoidal-elf-check-") as directory:
        path = Path(directory) / "input"
        path.write_bytes(data)
        proc = subprocess.run([str(tool), "-W", "-h", "-l", "-S", "-s", "-r", "-d", str(path)],
                              capture_output=True, text=True, encoding="utf-8", errors="replace",
                              env=dict(os.environ, LC_ALL="C"), timeout=60)
    require(proc.returncode == 0 and not proc.stderr.strip(),
            "readelf refused or warned: " + proc.stderr[-2000:])
    return sorted(set(TLS_RELOCATION_NAME.findall(proc.stdout)))


def bounded_read(path: Path, maximum: int) -> bytes:
    with path.open("rb") as stream:
        require(os.fstat(stream.fileno()).st_size <= maximum, f"{path}: file exceeds size limit")
        data = stream.read(maximum + 1)
    require(len(data) <= maximum, f"{path}: file grew beyond size limit")
    return data


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--readelf", required=True, type=Path)
    parser.add_argument("--readelf-sha256", help="expected SHA-256 of the selected readelf binary")
    parser.add_argument("--elf", required=True, type=Path)
    parser.add_argument("--runtime-archive", type=Path)
    parser.add_argument("--report", type=Path, help="write JSON evidence as well as printing it")
    args = parser.parse_args(argv)
    report = {"status": "refused", "issues": [], "objects": []}
    try:
        require(args.readelf.is_absolute(), "--readelf must be an absolute pinned tool path")
        tool = args.readelf.resolve(strict=True)
        tool_hash = sha256(bounded_read(tool, 128 * 1024**2))
        require(args.readelf_sha256 is None or args.readelf_sha256.lower() == tool_hash,
                "selected readelf does not match --readelf-sha256")
        version = subprocess.check_output([str(tool), "--version"], text=True,
                                          env=dict(os.environ, LC_ALL="C"), timeout=10).splitlines()[0]
        require(version.startswith("GNU readelf "), "require the pinned GNU readelf")
        report["readelf"] = {"path": str(tool), "sha256": tool_hash, "version": version}
        data = bounded_read(args.elf, 128 * 1024**2)
        result = elf(data, str(args.elf), executable=True)
        report["objects"].append(result)
        report["issues"].extend(result["issues"])
        report["issues"].extend("readelf: " + name for name in readelf_check(tool, data))
        if args.runtime_archive:
            data = bounded_read(args.runtime_archive, 1024**3)
            report["archive"] = {"path": str(args.runtime_archive), "sha256": sha256(data), "bytes": len(data)}
            for name, payload in archive_objects(data):
                result = elf(payload, name, executable=False)
                report["objects"].append(result)
                report["issues"].extend(result["issues"])
            report["issues"].extend("readelf archive: " + name for name in readelf_check(tool, data))
        if not report["issues"]:
            report["status"] = "ok"
    except (GateError, OSError, subprocess.SubprocessError, UnicodeError, struct.error) as error:
        report["issues"].append(str(error))
    output = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.report:
        args.report.write_text(output)
    print(output, end="")
    return 0 if report["status"] == "ok" else 1


if __name__ == "__main__":
    sys.exit(main())
