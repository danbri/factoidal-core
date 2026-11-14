#!/usr/bin/env python3
"""Op numbers at the script boundary: what prelude.js asks for against what Lean serves.

The page objects of prelude.js reach the engine through a few numbered imports: `node_query`
(n.query), `node_info` (n.info), `tree_op` (n.treeOp) and `web_api` (n.api). The numbers are
literals on both sides, in several Lean modules, and new ones are claimed in a log. This tool
lists, for each table, the numbers the prelude uses and the numbers each Lean module serves,
and reports

  - a number the prelude uses that no Lean module serves (the feature answers an error);
  - a number served by two Lean modules of one table (the first in the dispatch wins);
    Hosts/Page.lean, which routes ops to the others, is left out of this comparison.

It reads text, so it is a report for a reviewer, not a proof: computed op numbers
(`200 + k`) and ranges are named as such. `--check` exits 1 when the first kind is found.
Record: docs/designissues/2026-11-14-engine-integration.md, section 4.

  python3 tools/foafnaut-op-audit.py [--check] [--root DIR]
"""
import re
import sys
from pathlib import Path

root = Path(sys.argv[sys.argv.index("--root") + 1]) if "--root" in sys.argv else Path(__file__).resolve().parent.parent
HOSTS = root / "formal/lean4/L4Factoidal/WasmVM/Hosts"
PRELUDE = root / "tools/wasmvm/quickjs/prelude.js"


def region(text, start, stops=("\ndef ", "\ntheorem ", "\nprivate def ", "\nstructure ", "\nend ", "\n/-- ", "\n@[")):
    """The text of the definition that starts with `start`, up to the next top-level item."""
    at = text.find(start)
    if at < 0:
        return ""
    end = len(text)
    for stop in stops:
        i = text.find(stop, at + len(start))
        if i >= 0:
            end = min(end, i)
    return text[at:end]


def arms(text):
    """Numbers of `| N =>` and `| N | M =>` match arms, and of `x == N` tests."""
    out = set()
    for line in re.findall(r"^\s*\|((?:\s*\d+\s*\|)*\s*\d+)\s*=>", text, flags=re.M):
        out.update(int(n) for n in re.findall(r"\d+", line))
    out.update(int(n) for n in re.findall(r"\b(?:op|code|a 1|k|which)\s*==\s*(\d+)\b", text))
    return out


def ranges(text):
    """Half-open ranges `A ≤ code && code < B` (and the `op` forms)."""
    out = []
    for a, b in re.findall(r"(\d+)\s*≤\s*(?:code|op|a 1)\s*&&\s*(?:code|op|a 1)\s*<\s*(\d+)", text):
        out.append((int(a), int(b)))
    for a, b in re.findall(r"(?:code|op|a 1)\s*≥\s*(\d+)\s*&&\s*(?:code|op|a 1)\s*(?:<|≤)\s*(\d+)", text):
        out.append((int(a), int(b) + 1))
    return out


def read(path):
    return path.read_text(encoding="utf-8") if path.exists() else ""


prelude = read(PRELUDE)
dom, domops, page, webapi = (read(HOSTS / f) for f in ("Dom.lean", "DomOps.lean", "Page.lean", "WebApi.lean"))
webdoc = read(root / "labs/demos/foafnaut/WebDocument.lean")

# ---- what the prelude asks for ----------------------------------------------------------------
used = {
    "node_query": set(int(n) for n in re.findall(r"\b(?:n\.query|query|op)\(\s*[^,()]*(?:\([^()]*\))?[^,()]*,\s*(\d+)\s*[,)]", prelude))
    | set(int(n) for n in re.findall(r"\beditQuery\(\s*(\d+)\s*,", prelude)),
    "node_info": set(int(n) for n in re.findall(r"\b(?:n\.info|info)\(\s*[^,()]*(?:\([^()]*\))?[^,()]*,\s*(\d+)\s*\)", prelude)),
    "web_api": set(int(n) for n in re.findall(r"\b(?:apiCall|n0\.api|n\.api)\(\s*(\d+)\s*[,)]", prelude)),
}
computed = sorted(set(re.findall(r"n\.query\([^,]*,\s*(\d+\s*\+\s*[\w.()'\"]+)", prelude)))

# ---- what Lean serves, by module -------------------------------------------------------------
served = {
    "node_query": {
        "Hosts/Dom.lean nodeQueryOf": arms(region(dom, "def nodeQueryOf")),
        "Hosts/DomOps.lean domOpM": arms(region(domops, "def domOpM")),
        "Hosts/DomOps.lean editOpM": arms(region(domops, "def editOpM")),
        # The router: every numbered arm of the file (its ops are served in several functions).
        "Hosts/Page.lean (router)": arms(page) | set(int(n) for n in re.findall(r"a 1 == (\d+)", page)),
        "WebDocument.lean measure and readAnswer": arms(region(webdoc, "def measure")) | arms(region(webdoc, "def readAnswer")),
    },
    "node_info": {"Hosts/Dom.lean nodeInfo": arms(region(dom, "def nodeInfo"))},
    "web_api": {"Hosts/WebApi.lean": arms(webapi)},
}
served_ranges = {
    "node_query": [(200, 10**9)] if re.search(r"op ≥ 200", webdoc) else [],
    "node_info": [],
    "web_api": ranges(webapi),
}
# The postMessage answer (32) is served before nodeQueryOf, in Hosts/Dom.lean nodeQuery.
served["node_query"]["Hosts/Dom.lean nodeQueryOf"] |= set(int(n) for n in re.findall(r"arg args 1 == (\d+)", region(dom, "def nodeQuery ")))

problems = 0
for table in ("node_query", "node_info", "web_api"):
    every = set().union(*served[table].values())
    in_range = lambda n: any(a <= n < b for a, b in served_ranges[table])
    print(f"== {table}")
    print(f"   prelude.js uses {len(used[table])} numbers: {' '.join(map(str, sorted(used[table])))}")
    for module, numbers in served[table].items():
        print(f"   {module} serves {len(numbers)}: {' '.join(map(str, sorted(numbers)))}")
    if served_ranges[table]:
        print(f"   ranges served: {', '.join(f'{a}..{b - 1}' if b < 10**9 else f'{a} and up' for a, b in sorted(served_ranges[table]))}")
    missing = sorted(n for n in used[table] if n not in every and not in_range(n))
    if missing:
        problems += len(missing)
        print(f"   USED BY THE PRELUDE AND NOT SERVED: {' '.join(map(str, missing))}")
    # Hosts/Page.lean routes ops to the other modules (175 and 177 to editOpM, the layout reads
    # to the measure function), so it is not compared with them.
    names = [name for name in served[table] if "Page.lean" not in name]
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            both = sorted(served[table][a] & served[table][b])
            if both:
                print(f"   served by both {a} and {b}: {' '.join(map(str, both))} (the first in the dispatch answers)")
    unused = sorted(n for n in every if n not in used[table])
    if unused:
        print(f"   served and not named by a literal in prelude.js: {' '.join(map(str, unused))}")
if computed:
    print("== computed node_query numbers in prelude.js (not checked): " + "; ".join(computed))
print(f"\n{problems} numbers used by the prelude with no Lean arm found")
if "--check" in sys.argv and problems:
    sys.exit(1)
