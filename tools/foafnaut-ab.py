#!/usr/bin/env python3
"""A/B gate for Foafnaut engine changes: native builds of two commits, the CSS reftest suites
and the real-page snapshots on both, and one report of what each commit gains and loses.

Subcommands (each REF is any git commit-ish of this repository):

  build REF                 native engine library of REF, kept under the cache by commit
  suites REF [--first P]    the WPT reftest suites on REF's library, kept by commit
  compare BASE BRANCH       tests gained and lost; exit 1 when a test is lost and not accepted
  pages BASE BRANCH         the real-page snapshots on both: status, picture hash, time
  overlap BASE NEW BRANCH   files that both BASE..NEW (main moved) and BASE..BRANCH change;
                            exit 0 when there are none (the gate result still holds), 1 otherwise
  gate BASE BRANCH          build, suites (BRANCH's touched suite first), compare, pages

Results of a commit are kept, so main is built and measured once per commit, whatever branch
is compared with it. Inputs, by option or environment variable:

  --cache   FOAFNAUT_AB_CACHE      default ~/.cache/foafnaut-ab
  --manifest FOAFNAUT_AB_MANIFEST  WPT MANIFEST.json (see skills/wpt-runs, "Locally")
  --wpt     FOAFNAUT_AB_WPT        WPT checkout with css/, fonts/, common/, resources/, images/
  --realpages FOAFNAUT_AB_REALPAGES  factoidal-builds third_party/realpages (one zip per page)

Why this exists (2026-11-25): the gate was a set of scripts in a session's /tmp. Main was built
four times in one day only because main moved, and a merged change (PR 994) lost four
css-backgrounds tests that no gate had run. Record: skills/foafnaut/SKILL.md, "A/B gate".
"""
import argparse, concurrent.futures as cf, glob, json, os, struct, subprocess, sys, zipfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SUITES = ["/css/CSS2/", "/css/css-lists/", "/css/css-backgrounds/", "/css/css-transitions/",
          "/css/css-animations/", "/css/cssom/", "/css/selectors/"]
LIB_IN_TREE = "labs/demos/foafnaut/.build/web-render/engines/libweb-render.so"


def git(*args, cwd=REPO):
    return subprocess.run(["git", *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


def sha(ref):
    return git("rev-parse", "--verify", ref + "^{commit}")


def env_path():
    home = Path.home()
    return dict(os.environ, PATH=f"{home}/.elan/bin:{home}/.deno/bin:" + os.environ["PATH"])


def lib_path(cache, commit):
    return cache / "lib" / f"{commit}.so"


def build(cache, ref, side="a"):
    """Native build of `ref` in the worktree of `side` (a or b), kept between runs so Lake
    builds incrementally. Returns the library path; a kept library is not built again."""
    commit = sha(ref)
    out = lib_path(cache, commit)
    if out.exists():
        print(f"build {commit[:12]}: kept {out}")
        return out
    wt = cache / f"wt-{side}"
    if not wt.exists():
        git("worktree", "add", "--detach", str(wt), commit)
    else:
        git("checkout", "-q", "--detach", commit, cwd=wt)
    log = cache / "logs" / f"build-{commit[:12]}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    print(f"build {commit[:12]} in {wt} (log {log})", flush=True)
    with open(log, "w") as f:
        rc = subprocess.run(["labs/demos/foafnaut/build-web-render.sh", "--native"], cwd=wt,
                            env=env_path(), stdout=f, stderr=subprocess.STDOUT).returncode
    if rc != 0:
        sys.exit(f"build {commit[:12]} failed (rc {rc}); see {log}")
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_suffix(".tmp")
    tmp.write_bytes((wt / LIB_IN_TREE).read_bytes())
    tmp.rename(out)
    return out


def suite_dir(cache, commit, prefix):
    return cache / "suites" / commit / prefix.strip("/").replace("/", "_")


def suites(cache, ref, manifest, wpt, first=None, jobs=2):
    commit = sha(ref)
    lib = lib_path(cache, commit)
    if not lib.exists():
        sys.exit(f"no library for {commit[:12]}; run: build {ref}")
    order = ([first] if first in SUITES else []) + [p for p in SUITES if p != first]
    for p in order:
        d = suite_dir(cache, commit, p)
        if (d / "results.json").exists():
            print(f"suites {commit[:12]} {p}: kept")
            continue
        d.mkdir(parents=True, exist_ok=True)
        with open(d.with_suffix(".log"), "w") as f:
            rc = subprocess.run([sys.executable, "tests/browser-wpt/wpt-reftests.py", "run", "--manifest", str(manifest),
                                 "--wpt-root", str(wpt), "--native-engine", str(lib), "--prefix", p,
                                 "--out", str(d), "--jobs", str(jobs)],
                                cwd=REPO, env=env_path(), stdout=f, stderr=subprocess.STDOUT).returncode
        print(f"suites {commit[:12]} {p}: rc {rc}", flush=True)


def statuses(cache, commit, prefix):
    p = suite_dir(cache, commit, prefix) / "results.json"
    if not p.exists():
        return None
    return {t["test"]: t["status"] for t in json.load(open(p))["tests"]}


def compare(cache, base, branch, accepted):
    a_sha, b_sha = sha(base), sha(branch)
    lost_total, unaccepted = 0, []
    for p in SUITES:
        a, b = statuses(cache, a_sha, p), statuses(cache, b_sha, p)
        if a is None or b is None:
            print(f"{p}: missing results ({'base' if a is None else 'branch'})")
            unaccepted.append(f"missing {p}")
            continue
        pa = sum(s == "PASS" for s in a.values())
        pb = sum(s == "PASS" for s in b.values())
        gained = sorted(t for t in b if b[t] == "PASS" and a.get(t) != "PASS")
        lost = sorted(t for t in a if a[t] == "PASS" and b.get(t) != "PASS")
        lost_total += len(lost)
        print(f"{p}: base {pa} of {len(a)}, branch {pb} of {len(b)}; gained {len(gained)}, lost {len(lost)}")
        for t in lost:
            note = f" (accepted: {accepted[t]})" if t in accepted else ""
            print(f"   lost {t} {b.get(t)}{note}")
            if t not in accepted:
                unaccepted.append(t)
        for t in gained:
            print(f"   gained {t}")
    print(f"lost {lost_total}, not accepted {len(unaccepted)}")
    return 1 if unaccepted else 0


def render_page(z, lib, out):
    with zipfile.ZipFile(z) as f:
        m = json.loads(f.read("manifest.json"))
        png = f.read(m["reference"]["file"])
    w, h = struct.unpack(">II", png[16:24])
    d = out / m["id"]
    d.mkdir(parents=True, exist_ok=True)
    job = d / "job.jsonl"
    job.write_text(json.dumps({"url": m["url"], "width": w, "height": h, "file": "ours.png"}) + "\n")
    cmd = ["timeout", "900", "deno", "run", "-A", "--unstable-ffi", "--preload",
           "labs/demos/foafnaut/realpages/replay.ts", "tests/browser-wpt/reftest-render.ts",
           "--native-engine", str(lib), "--list", str(job), "--out", str(d)]
    p = subprocess.run(cmd, cwd=REPO, env=dict(env_path(), REALPAGES_REPLAY=str(Path(z).resolve())),
                       capture_output=True, text=True)
    (d / "log.txt").write_text(p.stdout + "\n--stderr--\n" + p.stderr[-20000:])
    done = [l for l in p.stdout.splitlines() if l.startswith("__done ")]
    r = json.loads(done[-1][7:]) if done else {"status": "nodone", "rc": p.returncode}
    r["id"] = m["id"]
    return r


def pages(cache, base, branch, realpages):
    """Both libraries render each page at the same moment, so load affects them alike. The
    times are still wall-clock: compare them only from a machine with no build running."""
    a_sha, b_sha = sha(base), sha(branch)
    libs = {"A": lib_path(cache, a_sha), "B": lib_path(cache, b_sha)}
    out = cache / "pages" / f"{a_sha[:12]}-{b_sha[:12]}"
    rows = {}
    for z in sorted(glob.glob(os.path.join(realpages, "*", "*.zip"))):
        with cf.ThreadPoolExecutor(2) as ex:
            fut = {k: ex.submit(render_page, z, libs[k], out / k) for k in libs}
            r = {k: f.result() for k, f in fut.items()}
        rows[r["A"]["id"]] = r
        a, b = r["A"], r["B"]
        pic = "same" if a.get("sha") is not None and a.get("sha") == b.get("sha") else "DIFF"
        print(f"{a['id']:28} {a.get('status')}/{b.get('status'):10} {pic:5} {a.get('ms', '-'):>7} {b.get('ms', '-'):>7}", flush=True)
    (out / "results.json").write_text(json.dumps(rows))
    same_status = sum(r["A"].get("status") == r["B"].get("status") for r in rows.values())
    same_pic = sum(r["A"].get("sha") is not None and r["A"].get("sha") == r["B"].get("sha") for r in rows.values())
    ta = sum(r["A"].get("ms", 0) or 0 for r in rows.values())
    tb = sum(r["B"].get("ms", 0) or 0 for r in rows.values())
    print(f"pages {len(rows)}; same status {same_status}; same picture {same_pic}; total ms {ta} -> {tb}")
    print(f"pictures: {out}/A and {out}/B; look at every DIFF before landing")
    return 0 if same_status == len(rows) else 1


def overlap(base, new, branch):
    """Files that main changed after the gate (BASE..NEW) and that the branch's own commits
    change. BRANCH may be the gated commit or the one rebased onto NEW: its own commits are
    NEW..BRANCH when it descends from NEW, else BASE..BRANCH."""
    def files(rng):
        return set(git("log", "--format=", "--name-only", rng).split())
    rebased = subprocess.run(["git", "merge-base", "--is-ancestor", sha(new), sha(branch)], cwd=REPO).returncode == 0
    moved = files(f"{sha(base)}..{sha(new)}")
    mine = files(f"{sha(new) if rebased else sha(base)}..{sha(branch)}")
    both = sorted(moved & mine)
    if not both:
        print("no file changed on both sides: the gate result still holds after the rebase")
        return 0
    print("changed on both sides (read these diffs; gate again if the change can meet yours):")
    for f in both:
        print("  ", f)
    return 1


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cache", type=Path, default=Path(os.environ.get("FOAFNAUT_AB_CACHE", Path.home() / ".cache/foafnaut-ab")))
    ap.add_argument("--manifest", default=os.environ.get("FOAFNAUT_AB_MANIFEST"))
    ap.add_argument("--wpt", default=os.environ.get("FOAFNAUT_AB_WPT"))
    ap.add_argument("--realpages", default=os.environ.get("FOAFNAUT_AB_REALPAGES"))
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--accept", action="append", default=[], metavar="TEST=ISSUE",
                    help="a lost test the owner accepted, with the issue that records it")
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name, refs in [("build", ["ref"]), ("suites", ["ref"]), ("compare", ["base", "branch"]),
                       ("pages", ["base", "branch"]), ("overlap", ["base", "new", "branch"]),
                       ("gate", ["base", "branch"])]:
        sp = sub.add_parser(name)
        for r in refs:
            sp.add_argument(r)
        if name in ("suites", "gate"):
            sp.add_argument("--first", help="suite prefix to run first, e.g. /css/css-backgrounds/")
        if name == "gate":
            sp.add_argument("--no-pages", action="store_true")
    a = ap.parse_args()
    a.cache.mkdir(parents=True, exist_ok=True)
    accepted = dict(x.split("=", 1) for x in a.accept)
    need = lambda *ks: [sys.exit(f"--{k} (or FOAFNAUT_AB_{k.upper()}) is required") for k in ks if not getattr(a, k)]
    if a.cmd == "build":
        build(a.cache, a.ref)
    elif a.cmd == "suites":
        need("manifest", "wpt")
        suites(a.cache, a.ref, a.manifest, a.wpt, a.first, a.jobs)
    elif a.cmd == "compare":
        sys.exit(compare(a.cache, a.base, a.branch, accepted))
    elif a.cmd == "pages":
        need("realpages")
        sys.exit(pages(a.cache, a.base, a.branch, a.realpages))
    elif a.cmd == "overlap":
        sys.exit(overlap(a.base, a.new, a.branch))
    elif a.cmd == "gate":
        need("manifest", "wpt")
        with cf.ThreadPoolExecutor(2) as ex:
            for f in [ex.submit(build, a.cache, a.base, "a"), ex.submit(build, a.cache, a.branch, "b")]:
                f.result()
        with cf.ThreadPoolExecutor(2) as ex:
            for f in [ex.submit(suites, a.cache, r, a.manifest, a.wpt, a.first, a.jobs) for r in (a.base, a.branch)]:
                f.result()
        rc = compare(a.cache, a.base, a.branch, accepted)
        if rc == 0 and not a.no_pages:
            need("realpages")
            rc = pages(a.cache, a.base, a.branch, a.realpages)
        sys.exit(rc)


if __name__ == "__main__":
    main()
