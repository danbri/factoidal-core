#!/usr/bin/env python3
"""Preserve the finite npm 0.11.0 audit evidence, without external dependencies.

Capture: python3 tools/snapshot-npm-audit.py --source REVIEWDIR --output NEWDIR
Verify:  python3 tools/snapshot-npm-audit.py --verify NEWDIR

Existing output directories are never changed. Source files are read once; the
same bytes supply the archived file, its length, and its SHA256. This is a
per-file capture, not a transaction across concurrently edited source files.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys


BASELINE = "d83100e6ec038328a71a245e9fd10fbd768a38a5"
MANIFEST = "manifest.json"
AUDIT_SUFFIXES = {".mjs", ".mts", ".py", ".lean", ".json", ".md"}
LOG_SUFFIXES = {".json", ".log", ".tap"}
SPEC_SUFFIXES = {".html", ".htm", ".xhtml", ".xml", ".txt", ".md"}


def safe_path(value):
    if not isinstance(value, str) or not value or "\\" in value:
        raise ValueError(f"invalid relative path: {value!r}")
    path = PurePosixPath(value)
    if path.is_absolute() or any(p in {".", ".."} for p in value.split("/")):
        raise ValueError(f"unsafe relative path: {value!r}")
    if path.as_posix() != value or value == MANIFEST:
        raise ValueError(f"noncanonical or reserved path: {value!r}")
    return path


def no_symlink_components(path):
    """Also check ancestors, including a supplied directory symlink."""
    path = Path(os.path.abspath(path))
    for component in [*reversed(path.parents), path]:
        try:
            mode = component.lstat().st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode):
            raise ValueError(f"symlink refused: {component}")
    return path


def read_regular(root, relative):
    """Open every component without following symlinks (macOS and Linux)."""
    parts = PurePosixPath(relative).parts
    flags = os.O_RDONLY | os.O_NOFOLLOW
    directory = os.open(root, flags | os.O_DIRECTORY)
    try:
        for part in parts[:-1]:
            child = os.open(part, flags | os.O_DIRECTORY, dir_fd=directory)
            os.close(directory)
            directory = child
        descriptor = os.open(parts[-1], flags | os.O_NONBLOCK, dir_fd=directory)
        with os.fdopen(descriptor, "rb") as stream:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                raise ValueError(f"not a regular file: {relative}")
            return stream.read()
    finally:
        os.close(directory)


def inventory(source, specification_budget):
    selected = []
    absent = []
    excluded = []

    def add_file(relative, required=False):
        path = no_symlink_components(source / relative)
        if not path.exists() and not path.is_symlink():
            if required:
                raise ValueError(f"required source file missing: {relative}")
            absent.append(relative)
            return
        if not stat.S_ISREG(path.lstat().st_mode):
            raise ValueError(f"not a regular source file: {relative}")
        selected.append(relative)

    def add_directory(relative, suffixes, required=False):
        directory = no_symlink_components(source / relative)
        if not directory.exists() and not directory.is_symlink():
            if required:
                raise ValueError(f"required source inventory missing: {relative}")
            absent.append(relative)
            return
        if not directory.is_dir():
            raise ValueError(f"not a source directory: {relative}")
        before = len(selected)
        for path in sorted(directory.iterdir()):
            license_file = path.name.upper().startswith(("LICENSE", "COPYING", "NOTICE"))
            if path.suffix in suffixes or (relative == "audit" and license_file):
                add_file(path.relative_to(source).as_posix(), required=True)
        if required and len(selected) == before:
            raise ValueError(f"empty source inventory: {relative}")

    add_file("REVIEW-0.11.0.md", required=True)
    add_file("REPAIR-NOTES.md", required=True)
    add_directory("audit", AUDIT_SUFFIXES, required=True)
    add_directory("logs", LOG_SUFFIXES, required=True)
    for relative in ("spec2lean-draft.md", "source-materials/spec2lean-draft.md",
                     "_LEAN/spec2lean-requirements.md"):
        add_file(relative)
    add_directory("_LEAN/docs", {".md"})
    add_directory("_LEAN/ledger", {".json"})
    specifications = no_symlink_components(source / "_LEAN/specifications")
    if specifications.exists() or specifications.is_symlink():
        no_symlink_components(specifications)
        used = 0
        for path in sorted(specifications.iterdir()):
            relative = path.relative_to(source).as_posix()
            if path.is_symlink():
                raise ValueError(f"symlink refused: {relative}")
            if not path.is_file() or path.suffix.lower() not in SPEC_SUFFIXES:
                excluded.append({"path": relative, "reason": "not a raw text specification file"})
                continue
            size = path.stat().st_size
            if used + size > specification_budget:
                excluded.append({"path": relative, "reason": "specification byte budget", "size": size})
                continue
            add_file(relative, required=True)
            used += size
    else:
        absent.append("_LEAN/specifications")
    return sorted(selected), absent, excluded


def capture(source, output, specification_budget):
    source = no_symlink_components(source)
    if not source.is_dir():
        raise ValueError(f"source directory missing: {source}")
    output = no_symlink_components(output)
    if output.exists():
        raise ValueError(f"output already exists: {output}")
    paths, absent, excluded = inventory(source, specification_budget)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.mkdir()  # Exclusive creation: there is no overwrite mode.
    files = []
    for relative in paths:
        safe_path(relative)
        data = read_regular(source, relative)
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(data)
        files.append({"path": relative, "sha256": hashlib.sha256(data).hexdigest(),
                      "size": len(data)})
    manifest = {
        "format": "factoidal-npm-audit-snapshot-v1",
        "capture_time_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "capture_stage": "initial",
        "baseline_source_commit": BASELINE,
        "status": {
            "evidence": "finite evidence captured from the specified source inventory",
            "external_dependencies": "not included: npm packages, node_modules, downloaded suites, binaries and caches",
            "repair_claim": "no claim that all findings are repaired",
            "repair_validation": "initial capture; repair corpus run still ongoing; does not contain all post-fix evidence",
            "log_names": "original source names retained, including setup failures and intermediate runs",
            "consistency": "each file read once; source may change between files; later changes require a new snapshot",
        },
        "specification_budget_bytes": specification_budget,
        "inventory_policy": {
            "required_reports": ["REVIEW-0.11.0.md", "REPAIR-NOTES.md"],
            "audit": "immediate regular .mjs .mts .py .lean .json .md files and LICENSE/COPYING/NOTICE files",
            "logs": "immediate regular .json .log .tap files, with original names",
            "source_materials": "optional spec2lean-draft.md, source-materials/spec2lean-draft.md, _LEAN/spec2lean-requirements.md, _LEAN/docs/*.md and _LEAN/ledger/*.json",
            "specifications": "immediate regular .html .htm .xhtml .xml .txt .md files under _LEAN/specifications, within byte budget",
            "directory_recursion": "none; package, node_modules, suite checkouts, binaries and caches excluded",
        },
        "optional_sources_absent": absent,
        "excluded_specification_entries": excluded,
        "file_count": len(files),
        "total_bytes": sum(entry["size"] for entry in files),
        "files": files,
    }
    with (output / MANIFEST).open("x", encoding="utf-8") as stream:
        json.dump(manifest, stream, indent=2, ensure_ascii=False)
        stream.write("\n")
    verify(output)
    return manifest


def verify(directory):
    directory = no_symlink_components(directory)
    manifest = json.loads(read_regular(directory, MANIFEST))
    if not isinstance(manifest, dict) or manifest.get("format") != "factoidal-npm-audit-snapshot-v1":
        raise ValueError("unknown manifest format")
    entries = manifest.get("files")
    if not isinstance(entries, list) or not entries:
        raise ValueError("manifest has no file inventory")
    expected = set()
    total = 0
    for entry in entries:
        relative = entry["path"]
        safe_path(relative)
        if relative in expected:
            raise ValueError(f"duplicate manifest path: {relative}")
        expected.add(relative)
        size, digest = entry["size"], entry["sha256"]
        if type(size) is not int or size < 0 or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError(f"invalid size or SHA256: {relative}")
        data = read_regular(directory, relative)
        if len(data) != size or hashlib.sha256(data).hexdigest() != digest:
            raise ValueError(f"size or SHA256 mismatch: {relative}")
        total += size
    actual = set()
    for root, dirs, files in os.walk(directory, followlinks=False):
        for name in dirs + files:
            path = Path(root) / name
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode) or not (stat.S_ISDIR(mode) or stat.S_ISREG(mode)):
                raise ValueError(f"symlink or special file refused: {path}")
        actual.update((Path(root) / name).relative_to(directory).as_posix() for name in files)
    actual.discard(MANIFEST)
    if actual != expected:
        raise ValueError(f"inventory mismatch: missing={sorted(expected - actual)}, unexpected={sorted(actual - expected)}")
    if manifest.get("file_count") != len(expected) or manifest.get("total_bytes") != total:
        raise ValueError("manifest count or total size mismatch")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify", type=Path)
    parser.add_argument("--specification-budget-bytes", type=int, default=8 * 1024 * 1024)
    args = parser.parse_args()
    if bool(args.verify) == bool(args.source or args.output):
        parser.error("use --verify DIR, or --source REVIEWDIR --output NEWDIR")
    if not args.verify and not (args.source and args.output):
        parser.error("capture requires both --source and --output")
    if args.specification_budget_bytes < 0:
        parser.error("specification budget must be nonnegative")
    try:
        manifest = verify(args.verify) if args.verify else capture(args.source, args.output, args.specification_budget_bytes)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"snapshot-npm-audit: {error}", file=sys.stderr)
        return 1
    print(f"{'verified' if args.verify else 'captured'} {manifest['file_count']} files, {manifest['total_bytes']} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
