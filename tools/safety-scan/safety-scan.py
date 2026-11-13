#!/usr/bin/env python3
"""Which Lean modules of the browser engine can reach I/O: driver for SafetyScan.lean.

Issue: https://github.com/danbri/factoidal-core/issues/427
Record: docs/designissues/2026-11-13-foafnaut-safety-map.md

SafetyScan.lean reads the compiled environment (.olean files) and puts each module in
one class: `io-free`, `reaches-hatch` or `effect-typed` (its header says what each
class means and what it does not mean). This driver

  * runs it with LEAN_PATH set to a build's olean directories,
  * adds source line counts per module and per area,
  * counts BUILD-TIME execution in the source (`#eval`, `run_cmd`, `run_elab`,
    `run_meta`, `include_str`, `initialize`): code that runs on the machine that
    BUILDS the tree, which the compiled environment does not show,
  * writes JSON and a Markdown summary, with the metrics of issue 427.

USAGE
    tools/safety-scan/safety-scan.py --self-test
    tools/safety-scan/safety-scan.py [--lean-path DIR[:DIR...]] [--root MOD ...] [--lab]
                                     [--json OUT.json] [--md OUT.md]

--lab adds the browser's lab modules (LAB_MODULES of labs/demos/foafnaut/build-web-render.sh,
which the build keeps equal to the import list of LabHygiene.lean) as roots. Their olean files are
in labs/demos/foafnaut/.build/web-render/olean of the build; put that directory on
--lean-path.

REACH OF THE SCAN. The scan reads only modules that the roots import in that build. The
report counts the Lean source files under formal/lean4/L4Factoidal and the lab that it did
NOT read (`files_not_scanned`, by area). A file that is not read has no class: it is not
io-free (anti-pattern 28: an audit that finds nothing is first evidence about its reach).

--self-test compiles the fixture modules in tools/safety-scan/fixtures into a temporary
directory (a few small .olean files, removed after) and checks that each one gets the
class in fixtures/expected.json. Each fixture plants one kind of hatch, so a scanner
that stops seeing a kind fails the test.

The default --lean-path is formal/lean4/.lake/build/lib/lean of this checkout. It needs
the olean files of every root; the scan itself writes nothing into the build.

Exit 0 on success, 1 on a self-test mismatch, 2 on a usage error or an empty walk.
Report-only: no class count fails the run yet (issue 427, step S3 adds the gate).
"""
import argparse, json, os, pathlib, re, shutil, subprocess, sys, tempfile, importlib.util
from collections import Counter, defaultdict

ROOT = pathlib.Path(__file__).resolve().parents[2]
HERE = pathlib.Path(__file__).resolve().parent
SCANNER = HERE / "SafetyScan.lean"
LEAN_ROOT = ROOT / "formal" / "lean4"
LAB = ROOT / "labs" / "demos" / "foafnaut"
DEFAULT_ROOTS = ["L4Factoidal", "L4Factoidal.WasmVM", "L4Factoidal.EventLoop",
                 "L4Factoidal.JS", "L4Factoidal.FrameCost", "L4Factoidal.PageGpu",
                 "L4Factoidal.PageCanvas"]
# Source tree for line counts and the not-scanned count. It must be the tree the olean
# files were built from (--source-root); the default is this checkout.
SRC_LEAN, SRC_LAB = LEAN_ROOT, LAB
FIXTURE_ORDER = ["Clean", "Trace", "Ext", "Via", "Impl", "Init", "Main"]
BUILD_TIME = re.compile(r"^\s*(#eval|run_cmd|run_elab|run_meta|initialize|builtin_initialize)\b"
                        r"|include_str", re.M)


def load_strip():
    """Reuse the comment and string stripper of tools/lean-hygiene-audit.py."""
    spec = importlib.util.spec_from_file_location("hyg", ROOT / "tools" / "lean-hygiene-audit.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.strip_comments_and_strings


def run_scan(lean_path: str, roots, out_json: pathlib.Path):
    env = dict(os.environ, LEAN_PATH=lean_path)
    cmd = ["lean", "--run", str(SCANNER), str(out_json), *roots]
    p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    msg = [l for l in (p.stdout + p.stderr).splitlines() if "warning" not in l.lower()]
    if p.returncode != 0 or not out_json.exists():
        sys.stderr.write("\n".join(msg) + "\n")
        sys.exit(2)
    return json.loads(out_json.read_text())


def self_test() -> int:
    expected = json.loads((HERE / "fixtures" / "expected.json").read_text())
    with tempfile.TemporaryDirectory(prefix="safety-scan-") as tmp:
        tmp = pathlib.Path(tmp)
        src = HERE / "fixtures"
        for name in FIXTURE_ORDER:
            mod = f"SafetyFixture/{name}"
            (tmp / "SafetyFixture").mkdir(exist_ok=True)
            p = subprocess.run(["lean", "-R", str(src), "-o", str(tmp / f"{mod}.olean"),
                                str(src / f"{mod}.lean")],
                               env=dict(os.environ, LEAN_PATH=str(tmp)),
                               capture_output=True, text=True)
            if p.returncode != 0:
                sys.stderr.write(f"fixture {mod} did not compile:\n{p.stdout}{p.stderr}")
                return 2
        data = run_scan(str(tmp), ["SafetyFixture.Main"], tmp / "out.json")
    got = {m["module"]: m["class"] for m in data["modules"]}
    bad = 0
    for mod, cls in sorted(expected.items()):
        ok = got.get(mod) == cls
        bad += not ok
        print(f"{'pass' if ok else 'FAIL'}  {mod}: expected {cls}, got {got.get(mod)}")
    extra = sorted(set(got) - set(expected))
    for mod in extra:
        bad += 1
        print(f"FAIL  {mod}: scanned but has no expectation")
    print(f"safety-scan self-test: {len(expected) - bad + len(extra)} pass, {bad} fail "
          f"(out of {len(expected) + len(extra)})")
    return 1 if bad else 0


def source_of(module: str):
    rel = module.replace(".", "/") + ".lean"
    for base in (SRC_LEAN, SRC_LAB):
        f = base / rel
        if f.exists():
            return f
    return None


def area_of(module: str) -> str:
    parts = module.split(".")
    if parts[0] == "L4Factoidal":
        return ".".join(parts[:2]) if len(parts) > 1 else "L4Factoidal"
    return "lab" if len(parts) == 1 else parts[0]


def report(data, strip):
    mods = data["modules"]
    if not mods:
        print("safety-scan: empty walk", file=sys.stderr)
        sys.exit(2)
    areas = defaultdict(lambda: {"modules": Counter(), "lines": Counter(), "build_time": 0,
                                 "not_scanned": 0})
    missing_src = 0
    for m in mods:
        f = source_of(m["module"])
        lines = 0
        if f is None:
            missing_src += 1
        else:
            text = f.read_text(errors="replace")
            lines = text.count("\n")
            m["build_time"] = len(BUILD_TIME.findall(strip(text)))
        m["lines"] = lines
        a = areas[area_of(m["module"])]
        a["modules"][m["class"]] += 1
        a["lines"][m["class"]] += lines
        a["build_time"] += m.get("build_time", 0)
    scanned = {m["module"] for m in mods}
    not_scanned = Counter()
    for base, prefix in ((SRC_LEAN / "L4Factoidal", "L4Factoidal."), (SRC_LAB, "")):
        for f in base.rglob("*.lean") if prefix else base.glob("*.lean"):
            if ".lake" in f.parts or ".build" in f.parts:
                continue
            mod = prefix + ".".join(f.relative_to(base).with_suffix("").parts)
            if mod not in scanned:
                not_scanned[area_of(mod)] += 1
    for name, n in not_scanned.items():
        areas[name]["not_scanned"] = n
    hatches = Counter()
    for m in mods:
        for h in m["hatches_reached"]:
            hatches[tuple(h)] += 1
    total = Counter()
    for m in mods:
        total[m["class"]] += m["lines"]
    all_lines = sum(total.values()) or 1
    metrics = {
        "modules": len(mods),
        "modules_without_source": missing_src,
        "io_free_line_share": round(total["io-free"] / all_lines, 4),
        "lines_by_class": dict(total),
        "modules_by_class": dict(Counter(m["class"] for m in mods)),
        "distinct_hatches_reached": len(hatches),
        "own_hatches_by_kind": dict(Counter(h[1] for m in mods for h in m["own_hatches"])),
        "build_time_execution_sites": sum(m.get("build_time", 0) for m in mods),
        "files_not_scanned": sum(not_scanned.values()),
    }
    return areas, hatches, metrics


def markdown(roots, areas, hatches, metrics) -> str:
    out = ["# Safety scan", "",
           f"Roots: {', '.join(roots)}. Issue: https://github.com/danbri/factoidal-core/issues/427.", "",
           "Classes: `io-free` (no effect in any type, no escape hatch reached), "
           "`reaches-hatch` (pure types, but the code reaches a listed hatch), "
           "`effect-typed` (some declaration has `IO` in its type).", "",
           "## Metrics", ""]
    for k, v in metrics.items():
        out.append(f"- {k}: {v}")
    out += ["", "## By area", "",
            "| Area | io-free (modules / lines) | reaches-hatch | effect-typed | build-time sites | files not scanned |",
            "|---|---|---|---|---|---|"]
    for name in sorted(areas):
        a = areas[name]
        cell = lambda c: f"{a['modules'][c]} / {a['lines'][c]}"
        out.append(f"| {name} | {cell('io-free')} | {cell('reaches-hatch')} | "
                   f"{cell('effect-typed')} | {a['build_time']} | {a['not_scanned']} |")
    out += ["", "## Hatches, by number of modules that reach each", "",
            "| Modules | Kind | Hatch | Declared in |", "|---|---|---|---|"]
    for (h, kind, mod), n in hatches.most_common():
        out.append(f"| {n} | {kind} | `{h}` | `{mod}` |")
    return "\n".join(out) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--lean-path", default=str(LEAN_ROOT / ".lake" / "build" / "lib" / "lean"))
    ap.add_argument("--root", action="append", dest="roots")
    ap.add_argument("--lab", action="store_true")
    ap.add_argument("--source-root", type=pathlib.Path, default=ROOT,
                    help="checkout the olean files were built from (default: this one)")
    ap.add_argument("--json", type=pathlib.Path)
    ap.add_argument("--md", type=pathlib.Path)
    args = ap.parse_args()
    if shutil.which("lean") is None:
        print("safety-scan: `lean` is not on PATH", file=sys.stderr)
        return 2
    if args.self_test:
        return self_test()
    global SRC_LEAN, SRC_LAB
    SRC_LEAN = args.source_root / "formal" / "lean4"
    SRC_LAB = args.source_root / "labs" / "demos" / "foafnaut"
    dirs = [pathlib.Path(d) for d in args.lean_path.split(":") if d]
    has_olean = lambda m: any((d / (m.replace(".", "/") + ".olean")).exists() for d in dirs)
    if args.roots:
        roots = args.roots
    else:
        # Default roots: the engine's lean_lib roots. A build that did not compile one
        # (CI builds `L4Factoidal l4wasm`) skips it with a warning; its files then count
        # under files_not_scanned.
        roots = [m for m in DEFAULT_ROOTS if has_olean(m)]
        if len(roots) < len(DEFAULT_ROOTS):
            print("safety-scan: no olean for default roots: " +
                  ", ".join(m for m in DEFAULT_ROOTS if m not in roots), file=sys.stderr)
    if args.lab:
        bw = (SRC_LAB / "build-web-render.sh").read_text()
        found = re.search(r"^LAB_MODULES=\(([^)]*)\)", bw, re.M)
        if not found:
            print("safety-scan: no LAB_MODULES in build-web-render.sh", file=sys.stderr)
            return 2
        lab = found.group(1).split()
        have = [m for m in lab if has_olean(m)]
        if len(have) < len(lab):
            # A lab module with no olean in this build is not read; the report counts it
            # under files_not_scanned. Name it here so the gap is visible at once.
            print("safety-scan: no olean for lab modules: " +
                  ", ".join(sorted(set(lab) - set(have))), file=sys.stderr)
        roots += have
    with tempfile.TemporaryDirectory(prefix="safety-scan-") as tmp:
        data = run_scan(args.lean_path, roots, pathlib.Path(tmp) / "scan.json")
    areas, hatches, metrics = report(data, load_strip())
    data["metrics"] = metrics
    if args.json:
        args.json.write_text(json.dumps(data, indent=1) + "\n")
    md = markdown(roots, areas, hatches, metrics)
    if args.md:
        args.md.write_text(md)
    else:
        sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
