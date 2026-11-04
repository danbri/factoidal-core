#!/usr/bin/env python3
"""Pinned WPT SVG audit and desktop reftest runner (Python standard library)."""
import argparse
import hashlib
import json
from pathlib import Path
import posixpath
import re
import subprocess
import tempfile
import urllib.request
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parent
STATES = ("accepted", "rejected", "unsupported", "match", "mismatch", "unavailable")


def fixtures(root=ROOT):
    manifest = json.loads((root / "manifest.json").read_text())
    source = json.loads((root / "source.json").read_text())
    errors = []
    if manifest["revision"] != source["revision"] or set(source["paths"]) != {x["path"] for x in manifest["files"]}:
        errors.append("manifest/source inventory differs")
    for entry in manifest["files"]:
        path = root / "upstream" / entry["path"]
        if not path.is_file():
            errors.append(f"missing: {entry['path']}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            errors.append(f"hash mismatch: {entry['path']}")
    if errors:
        return manifest, errors
    pairs = set()
    for entry in source["inventory"]:
        name = entry["path"]
        if not name.endswith(".svg"):
            continue
        data = (root / "upstream" / name).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != entry["gitBlob"]:
            errors.append(f"upstream git blob mismatch: {name}")
        for node in ET.fromstring(data).iter():
            if node.tag.rsplit("}", 1)[-1] == "link" and node.get("rel") == "match":
                pairs.add((name, posixpath.normpath(posixpath.join(posixpath.dirname(name), node.attrib["href"]))))
    declared = {(case["test"], case["reference"]) for case in manifest["cases"]}
    if pairs != declared or len(declared) != len(manifest["cases"]) or not pairs:
        errors.append("test denominator differs from upstream rel=match inventory")
    if any(ref not in source["paths"] for _, ref in pairs):
        errors.append("reference absent from fixture inventory")
    return manifest, errors


def fetch(root=ROOT):
    manifest = json.loads((root / "manifest.json").read_text())
    for entry in manifest["files"]:
        target = root / "upstream" / entry["path"]
        if target.is_file() and hashlib.sha256(target.read_bytes()).hexdigest() == entry["sha256"]:
            continue
        url = f"https://raw.githubusercontent.com/web-platform-tests/wpt/{manifest['revision']}/{entry['path']}"
        with urllib.request.urlopen(url, timeout=30) as response:
            data = response.read(1048577)
        if len(data) > 1048576 or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError(f"download hash mismatch: {url}")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)


def invoke(command, source, output, artifact, timeout):
    args = command + [str(source), "--no-open", "--width", "800", "--height", "600"]
    args += ["--emit-artifact", str(output)] if artifact else [str(output)]
    try:
        result = subprocess.run(args, capture_output=True, text=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        return "unavailable", str(error)
    log = (result.stdout + result.stderr)[-8000:]
    if result.returncode:
        if "GPU BLOCKED" in log:
            return "unavailable", log
        # Only a diagnostic from the actual profile is an unsupported result.
        if "SVG profile:" in log and any(word in log for word in (
                "unsupported", "foreign/non-SVG", "profile limit")):
            return "unsupported", log
        return "rejected", log
    if not output.is_file():
        return "unavailable", "successful process produced no output\n" + log
    if artifact:
        try:
            value = json.loads(output.read_text())
            if value["abi"] != "lean-svg-v1" or value["width"] != 800 or value["height"] != 600:
                raise ValueError("unexpected artifact ABI/viewport")
        except (OSError, ValueError, KeyError, TypeError) as error:
            return "unavailable", str(error)
    return "accepted", log


def ppm(path):
    """Read a strict P6 RGB image, without treating raster bytes as whitespace."""
    data = path.read_bytes()
    match = re.match(rb"P6\s+(\d+)\s+(\d+)\s+255(?:\r\n|\s)", data)
    if not match:
        raise ValueError("expected P6 RGB/255 PPM")
    width, height = int(match[1]), int(match[2])
    pixels = data[match.end():]
    if not 1 <= width <= 4096 or not 1 <= height <= 4096 or len(pixels) != width * height * 3:
        raise ValueError("invalid PPM dimensions/payload")
    return width, height, pixels


def compare(test, reference, fuzzy):
    tw, th, actual = ppm(test)
    rw, rh, expected = ppm(reference)
    if (tw, th) != (800, 600) or (rw, rh) != (tw, th):
        raise ValueError("wrong render viewport; expected 800x600")
    maximum = different = 0
    for offset in range(0, len(actual), 3):
        difference = max(abs(actual[offset+i] - expected[offset+i]) for i in range(3))
        maximum = max(maximum, difference)
        different += difference != 0
    max_range, pixel_range = fuzzy
    matches = max_range[0] <= maximum <= max_range[1] and pixel_range[0] <= different <= pixel_range[1]
    return matches, {"maxChannelDifference": maximum, "differentPixels": different}


def run(manifest, command, render=False, timeout=60, root=ROOT):
    results = []
    for case in manifest["cases"]:
        row = {"test": case["test"], "reference": case["reference"]}
        with tempfile.TemporaryDirectory(prefix="factoidal-svg-") as directory:
            directory = Path(directory)
            output = directory / ("test.ppm" if render else "artifact.json")
            state, detail = invoke(command, root / "upstream" / case["test"], output, not render, timeout)
            if state == "accepted" and render:
                # A static command cannot implement reftest-wait or fetch fonts.
                # Retain the case in the denominator, even if a permissive engine ignores these.
                if case["requiredRuntime"]:
                    state, detail = "unsupported", ", ".join(case["requiredRuntime"])
                else:
                    ref = directory / "reference.ppm"
                    state, detail = invoke(command, root / "upstream" / case["reference"], ref, False, timeout)
                    if state == "accepted":
                        try:
                            equal, detail = compare(output, ref, case["fuzzy"])
                            state = "match" if equal else "mismatch"
                        except (ValueError, OSError) as error:
                            state, detail = "unavailable", str(error)
            row.update(status=state, detail=detail)
        results.append(row)
    return {"revision": manifest["revision"], "mode": "render" if render else "acceptance-only",
            "scope": manifest["scope"], "total": len(results),
            "counts": {state: sum(row["status"] == state for row in results) for state in STATES},
            "results": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-fixtures", action="store_true")
    parser.add_argument("--inventory", action="store_true")
    parser.add_argument("--fetch", action="store_true")
    parser.add_argument("--render", action="store_true")
    parser.add_argument("--engine", help="path to native SVG CLI")
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    if args.fetch:
        try:
            fetch()
        except Exception as error:
            parser.exit(2, f"fixtures unavailable: {error}\n")
    manifest, errors = fixtures()
    if errors:
        parser.exit(2, "fixtures unavailable:\n" + "\n".join(errors) + "\n")
    if args.inventory:
        print(json.dumps(manifest, indent=2))
        return 0
    if args.check_fixtures or args.fetch:
        print(f"Verified {len(manifest['files'])} pinned files; {len(manifest['cases'])} SVG reftests; "
              f"{manifest['scope']['htmlDocuments']} HTML documents inventoried outside this runner.")
        return 0
    command = [str(Path(args.engine).resolve())] if args.engine else [str(ROOT.parents[2] / "bin/darwin-arm64/native-webgpu-svg-darwin-arm64")]
    report = run(manifest, command, args.render, args.timeout)
    value = json.dumps(report, indent=2) + "\n"
    if args.report:
        args.report.write_text(value)
    print(value, end="")
    # An acceptance audit has no image matches. Source CI uses --check-fixtures,
    # not a pretend conformance threshold. Incomplete render runs are nonzero.
    return 0 if report["counts"]["match"] == report["total"] and report["total"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
