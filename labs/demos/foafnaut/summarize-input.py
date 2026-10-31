#!/usr/bin/env python3
"""Summarize recorded native runs without treating rendering as proof of input.

Read-only by default. Optional --output writes a JSON evidence cache. Diagnostic
runs are excluded; results retain their executable hash and capture timestamp.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def parse_runs(text):
    text = re.sub(r"\x1b\[[0-9;]*[A-Za-z]", "", text).replace("\r", "")
    starts = list(re.finditer(
        r"\[(\d{4}-\d\d-\d\dT[^\]]+)\] Native demo: (springs|layout|vectors); arguments: ([^\n]*)\n",
        text))
    runs = []
    for index, start in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        body = text[start.end():end]
        if "--diagnose" in start[3].split():
            continue
        sha = re.match(r"([0-9a-f]{64})\s", body)
        sidecar = re.search(r"^([0-9a-f]{64})\s+[^\n]*/libnative-window\.dylib$", body, re.MULTILINE)
        traced = "--trace-input" in start[3].split()
        events = []
        for match in re.finditer(r"Input host → Lean \{([^}]+)\}", body):
            block = match[1]
            event = {}
            kind = re.search(r"kind: (\d+)", block)
            if not kind:
                continue
            event["kind"] = int(kind[1])
            for key in ("backing", "viewport", "selection", "dragging", "commands"):
                value = re.search(rf"{key}: (\[[^\]]*\])", block)
                if value:
                    event[key] = json.loads(value[1])
            events.append(event)
        counters = re.search(r"Persistent session counters: \{([^}]+)\}", body)
        stats = dict((key, int(value)) for key, value in
                     re.findall(r"(builds|frames|uploads|configurations): (\d+)", counters[1])) if counters else None
        negative_inside = 0
        for match in re.finditer(
                r"Input Cocoa view kind=\d+.*?local=\(([-.\d]+),([-.\d]+)\) "
                r"backing=\(([-.\d]+),([-.\d]+)\).*?bounds=\(([-.\d]+),([-.\d]+)\)", body):
            x, y, px, py, width, height = map(float, match.groups())
            if 0 <= x < width and 0 <= y < height and (px < 0 or py < 0):
                negative_inside += 1
        runs.append({
            "startedAt": start[1], "demo": start[2], "arguments": start[3],
            "executableSha256": sha[1] if sha else None,
            "sidecarSha256": sidecar[1] if sidecar else None,
            "traceEnabled": traced,
            "topLeftCoordinateMarker": "Native input: top-left framebuffer coordinates;" in body,
            "firstFramePresented": "Native surface first frame presented" in body,
            "sessionCounters": stats,
            "hostEvents": events,
            "acceptedPointerDowns": sum(e["kind"] == 2 and e.get("selection", [0, 0])[1] > 0 for e in events) if traced else None,
            "capturedDragMoves": sum(e["kind"] == 3 and e.get("dragging") == [True, True] for e in events) if traced else None,
            "captureReleases": sum(e["kind"] == 4 and e.get("dragging") == [True, False] for e in events) if traced else None,
            "insideViewEventsWithNegativePixelCoordinates": negative_inside if traced else None,
            "errors": [line for line in body.splitlines() if re.match(r"(?:\w*Error:|GPU BLOCKED:|GPU validation error:|GPU device lost:)", line)],
        })
    return runs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--directory", type=Path, help="directory containing release executables and native logs")
    args = parser.parse_args()
    directory = (args.directory or Path(__file__).resolve().parent).resolve()
    current = digest(directory / "native-webgpu-ui-darwin-arm64")
    runs = []
    for demo in ("springs", "layout", "vectors"):
        log = directory / f"native-{demo}.log"
        if log.exists():
            runs.extend(parse_runs(log.read_text(errors="replace")))
    runs.sort(key=lambda r: r["startedAt"])
    latest = {demo: next((r for r in reversed(runs) if r["demo"] == demo and
                         r["executableSha256"] == current), None)
              for demo in ("springs", "layout", "vectors")}
    latest_traced = {demo: next((r for r in reversed(runs) if r["demo"] == demo and
                         r["executableSha256"] == current and r["traceEnabled"]), None)
              for demo in ("springs", "layout", "vectors")}
    result = {"schema": "native-input-evidence-v1", "currentExecutableSha256": current,
              "currentSidecarSha256": digest(directory / "libnative-window.dylib"),
              "latestInteractiveRunsForCurrentExecutable": latest,
              "latestTracedInteractiveRunsForCurrentExecutable": latest_traced, "runs": runs,
              "limits": ["Only recorded events are counted; drag tracing records one move per gesture.",
                         "Rendering alone does not establish selection or dragging.",
                         "Input counts are unknown (null) for runs without --trace-input.",
                         "Older logs record executable hashes, not sidecar hashes."]}
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload)
    for demo, run in latest_traced.items():
        if run is None:
            print(f"{demo}: no traced interactive run of the current executable")
        else:
            print(f"{demo}: first frame={run['firstFramePresented']}, "
                  f"selected clicks={run['acceptedPointerDowns']}, "
                  f"captured drag moves={run['capturedDragMoves']}, "
                  f"releases={run['captureReleases']}, "
                  f"negative inside-view coordinates={run['insideViewEventsWithNegativePixelCoordinates']}")
    if args.output:
        print(f"Evidence cache: {args.output}")


if __name__ == "__main__":
    main()
