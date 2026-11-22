#!/usr/bin/env python3
"""Generate a narrowly patched copy of the pinned Lean runtime header.

The non-mimalloc RV32 small-object prefix is four bytes. Constructor UInt64
and Float payloads can consequently have only four-byte alignment, whereas
their C types require eight. Preserve the byte layout and replace just the
four constructor loads/stores with memcpy. No allocator is replaced.

Issue: https://github.com/danbri/factoidal-core/issues/745
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile


UPSTREAM_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
UPSTREAM_SHA256 = "02af0040283143b264e3a44b06b348b6973ae6037fa8f550701c83dd7a062ace"
PATCH_VERSION = 1


class PatchError(ValueError):
    """The supplied header or destination does not meet the pinned contract."""


def _accessor_edit(name: str, ctype: str, setter: bool) -> tuple[str, bytes, bytes]:
    if setter:
        signature = (
            f"static inline void {name}(b_lean_obj_arg o, unsigned offset, {ctype} v) {{\n"
        )
        old_body = f"    *(({ctype}*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset)) = v;\n"
        new_body = "    memcpy((uint8_t*)(lean_ctor_obj_cptr(o)) + offset, &v, sizeof(v));\n"
    else:
        signature = f"static inline {ctype} {name}(b_lean_obj_arg o, unsigned offset) {{\n"
        old_body = f"    return *(({ctype}*)((uint8_t*)(lean_ctor_obj_cptr(o)) + offset));\n"
        new_body = (
            f"    {ctype} result;\n"
            "    memcpy(&result, (uint8_t*)(lean_ctor_obj_cptr(o)) + offset, sizeof(result));\n"
            "    return result;\n"
        )
    prefix = signature + "    assert(offset >= lean_ctor_num_objs(o) * sizeof(void*));\n"
    return name, (prefix + old_body + "}\n").encode(), (prefix + new_body + "}\n").encode()


EDITS = (
    ("string_header", b"#include <float.h>\n", b"#include <float.h>\n#include <string.h>\n"),
    _accessor_edit("lean_ctor_get_uint64", "uint64_t", False),
    _accessor_edit("lean_ctor_get_float", "double", False),
    _accessor_edit("lean_ctor_set_uint64", "uint64_t", True),
    _accessor_edit("lean_ctor_set_float", "double", True),
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def patch_header(source: bytes) -> tuple[bytes, dict]:
    """Return the generated header and audit data; reject every other input hash."""
    actual = sha256(source)
    if actual != UPSTREAM_SHA256:
        raise PatchError(
            f"refusing unreviewed Lean header: expected SHA-256 {UPSTREAM_SHA256}, got {actual}"
        )

    output = source
    edits = []
    for name, before, after in EDITS:
        if source.count(before) != 1 or output.count(before) != 1:
            raise PatchError(f"expected exactly one source anchor for {name}")
        edits.append({
            "name": name,
            "source_line": source[:source.index(before)].count(b"\n") + 1,
            "before_sha256": sha256(before),
            "after_sha256": sha256(after),
        })
        output = output.replace(before, after, 1)

    audit = {
        "patch": "rv32-constructor-scalar-memcpy",
        "patch_version": PATCH_VERSION,
        "upstream_commit": UPSTREAM_COMMIT,
        "upstream_path": "src/include/lean/lean.h",
        "input_sha256": actual,
        "output_sha256": sha256(output),
        "edits": edits,
    }
    return output, audit


def _aliases(first: Path, second: Path) -> bool:
    return first.resolve() == second.resolve() or (
        first.exists() and second.exists() and first.samefile(second)
    )


def _atomic_write(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        temporary.chmod(0o644)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def generate(source: Path, output: Path, manifest: Path) -> dict:
    """Write a separate generated copy and audit manifest, never edit source."""
    paths = (source, output, manifest)
    for index, first in enumerate(paths):
        for second in paths[index + 1:]:
            if _aliases(first, second):
                raise PatchError(f"source, output and manifest must be distinct: {first}, {second}")
    generated, audit = patch_header(source.read_bytes())
    audit = {**audit, "input": str(source.resolve()), "output": str(output.resolve())}
    manifest_bytes = (json.dumps(audit, indent=2, sort_keys=True) + "\n").encode()
    _atomic_write(output, generated)
    _atomic_write(manifest, manifest_bytes)
    return audit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, type=Path, help="pristine pinned src/include/lean/lean.h")
    parser.add_argument("--output", required=True, type=Path, help="separate generated include/lean/lean.h")
    parser.add_argument("--manifest", type=Path, help="audit JSON; defaults to OUTPUT.audit.json")
    args = parser.parse_args()
    manifest = args.manifest or args.output.with_name(args.output.name + ".audit.json")
    try:
        audit = generate(args.input, args.output, manifest)
    except (OSError, PatchError) as error:
        parser.exit(1, f"error: {error}\n")
    print(json.dumps(audit, sort_keys=True))


if __name__ == "__main__":
    main()
