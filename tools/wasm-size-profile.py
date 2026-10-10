#!/usr/bin/env python3
"""wasm-size-profile.py -- what makes up a Lean wasm module, by Lean module.

Reads the link map that `formal/lean4/Wasm/build-wasm.sh` writes
(`wasm-ld --Map`) and sums, per input object, the bytes the linker kept in
the CODE section (function bodies) and in the DATA section (initialised
memory: string literals, constant tables). One object is one Lean module
(`L4Factoidal/SPARQL/Query.c` -> `L4Factoidal_SPARQL_Query.o`), one core
library module (`Init_...`, `Std_...`), one Lean runtime file, one HACL*
unit, or one member of an Emscripten system library.

What the numbers are, and are not:
  * They are the sizes wasm-ld wrote, BEFORE `wasm-opt -O3` (which Emscripten
    runs after the link). The script prints the code and data section sizes
    of the final .wasm too (--wasm), so the reader sees the factor between
    the two; the attribution is of the pre-optimisation bytes.
  * The linker drops every function and data segment nothing reaches
    (`--gc-sections`), so an object that appears with 0 bytes, or not at all,
    was compiled and linked and then dropped. A module whose bytes are here
    is reachable from an export.
  * At wasm-ld's default optimisation level, string literals of all objects
    are merged into one synthetic section the map names `<internal>`, so
    their bytes cannot be attributed. A map written by a link with
    `-Wl,-O0` (build-wasm.sh does one when L4_WASM_SIZE_PROFILE=1) keeps
    every object's strings apart; use that map for the data column.

Usage:
  tools/wasm-size-profile.py MAP [--wasm FILE] [--by namespace|module]
                             [--top N] [--json]
"""
import argparse
import json
import os
import re
import sys
from collections import defaultdict

RUNTIME = set("""debug thread mpz utf8 object apply exception interrupt memory
stackinfo compact init_module io hash byteslice platform alloc allocprof
sharecommon stack_overflow process object_ref mpn mutex mimalloc_static""".split())
SHIM = {"l4_shim", "l4_stubs", "l4_ext"}

LINE = re.compile(r"^\s*(\S+)\s+([0-9a-f]+)\s+([0-9a-f]+)\s(.*)$")


def parse_map(path):
    """Yield (section, input, size) for every input-section line."""
    section = None
    with open(path, encoding="utf-8", errors="replace") as f:
        header = f.readline()
        if "Addr" not in header or "Symbol" not in header:
            sys.exit(f"{path}: not a wasm-ld --Map file (header {header!r})")
        for raw in f:
            m = LINE.match(raw)
            if not m:
                continue
            rest = m.group(4)
            size = int(m.group(3), 16)
            col = len(rest) - len(rest.lstrip(" "))
            text = rest.strip()
            if col == 0:
                # An output section: CODE, DATA, CUSTOM(name), or a data
                # sub-section name such as .rodata / .data / .bss.
                section = text
                continue
            if col >= 16:
                continue  # a symbol line under an input line
            yield section, text, size


def object_of(input_text):
    """`path/to/X.o:(func)` or `lib.a(member.o):(func)` -> a label."""
    if input_text.startswith("<internal>"):
        return "<internal>"
    head = input_text.split(":(", 1)[0]
    m = re.match(r"^(.*)\(([^()]*)\)$", head)
    if m:  # an archive member
        return "sysroot:" + os.path.basename(m.group(1)) + "(" + m.group(2) + ")"
    if "/emscripten/cache/" in head or "/sysroot/" in head:
        return "sysroot:" + os.path.basename(head)
    return os.path.basename(head)


def module_of(obj):
    if obj == "<internal>":
        return "<linker: merged strings and constructors>"
    if obj.startswith("sysroot:"):
        return "Emscripten libc / libc++ / compiler-rt"
    stem = obj[:-2] if obj.endswith(".o") else obj
    if stem in RUNTIME:
        return "Lean runtime (C++) and mimalloc"
    if stem in SHIM:
        return "C shim (" + stem + ")"
    if stem.startswith("Hacl_") or stem.startswith("Lib_") or stem.startswith("l4_hacl"):
        return "HACL* crypto (C)"
    return stem.replace("_", ".")


def namespace_of(module):
    parts = module.split(".")
    if parts[0] == "L4Factoidal" and len(parts) >= 2:
        return "L4Factoidal." + parts[1]
    if parts[0] == "Wasm":
        return "Wasm (dispatch and ops)"
    if parts[0] == "Init":
        return "Init (Lean core library)"
    if parts[0] == "Std":
        return "Std (Lean standard library)"
    if parts[0] == "Lean":
        return "Lean (compiler library)"
    return module


def wasm_sections(path):
    """Section id -> byte size of a .wasm file (code is id 10, data id 11)."""
    with open(path, "rb") as f:
        b = f.read()
    if b[:4] != b"\0asm":
        sys.exit(f"{path}: not a wasm module")
    i, out = 8, defaultdict(int)

    def leb(i):
        r, s = 0, 0
        while True:
            x = b[i]
            i += 1
            r |= (x & 0x7F) << s
            s += 7
            if x < 0x80:
                return r, i

    while i < len(b):
        sid = b[i]
        n, j = leb(i + 1)
        out[sid] += n
        i = j + n
    return dict(out), len(b)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("map")
    ap.add_argument("--wasm")
    ap.add_argument("--by", choices=["namespace", "module"], default="namespace")
    ap.add_argument("--top", type=int, default=40)
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()

    code, data = defaultdict(int), defaultdict(int)
    total_code = total_data = 0
    for section, inp, size in parse_map(a.map):
        mod = module_of(object_of(inp))
        key = mod if a.by == "module" else namespace_of(mod)
        if section == "CODE":
            code[key] += size
            total_code += size
        elif section is not None and section.startswith(".") and section not in (".bss", ".tbss"):
            data[key] += size
            total_data += size
    if total_code == 0:
        sys.exit(f"{a.map}: no CODE input lines found; is this a wasm-ld map?")

    rows = sorted(set(code) | set(data), key=lambda k: -(code[k] + data[k]))
    report = {
        "map": a.map,
        "by": a.by,
        "linkedCodeBytes": total_code,
        "linkedDataBytes": total_data,
        "rows": [{"group": k, "code": code[k], "data": data[k]} for k in rows],
    }
    if a.wasm:
        secs, size = wasm_sections(a.wasm)
        report["wasm"] = {"path": a.wasm, "bytes": size,
                          "codeSection": secs.get(10, 0), "dataSection": secs.get(11, 0)}
    if a.json:
        json.dump(report, sys.stdout, indent=1)
        print()
        return
    print(f"linked (before wasm-opt): code {total_code:,} bytes, data {total_data:,} bytes")
    if a.wasm:
        w = report["wasm"]
        print(f"final {w['path']}: {w['bytes']:,} bytes; code section {w['codeSection']:,}, "
              f"data section {w['dataSection']:,}")
    print()
    print(f"| {'Lean namespace' if a.by == 'namespace' else 'Module'} | Code bytes | Data bytes | Share of linked bytes |")
    print("|---|---:|---:|---:|")
    whole = total_code + total_data
    shown = rows[: a.top]
    for k in shown:
        print(f"| {k} | {code[k]:,} | {data[k]:,} | {100.0 * (code[k] + data[k]) / whole:.1f}% |")
    rest = rows[a.top:]
    if rest:
        rc = sum(code[k] for k in rest)
        rd = sum(data[k] for k in rest)
        print(f"| {len(rest)} others | {rc:,} | {rd:,} | {100.0 * (rc + rd) / whole:.1f}% |")


if __name__ == "__main__":
    main()
