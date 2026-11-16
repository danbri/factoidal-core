#!/usr/bin/env python3
"""specs-data.py: the data of the Hub's Data and documents page (docs/web/hub/specs/).

Reads runs.csv of the wpt-scores branch of danbri/factoidal-builds (every recorded suite run)
and tests/browser-wpt/spec-suites.json (what each suite id measures), and writes three files:

  data.json     one normalised record per suite id (its newest row), the family headlines,
                the sources and the measurements that have a runner but no recorded row yet
  history.json  every row of every mapped suite as a compact time series, and the headline
                of each family per recording run
  records.csv   every mapped row of runs.csv as a normalised record (flat), for queries with
                any CSV tool (DuckDB, a spreadsheet, pandas)

Schema: docs/web/hub/specs/data.schema.json. The records are never renamed: a suite id keeps
its history, and spec-suites.json maps it to family, specification, version, technology, test
type and population. A suite id of runs.csv that the mapping does not know is listed in
data.json "unmapped" (and fails tests/hub/specs_test.mjs's check of the real mapping), so a new
suite is never dropped without notice. WPT and Test262 rows belong to the Conformance page and
are left out.

Status of a record:
  valid    the run is valid and decided every test of the population (decided = total)
  partial  the run is valid but decided fewer than the population (refused, skipped,
           unsupported, or a regime that cannot decide that test type); reason says how many
  invalid  the run is not valid (runs.csv valid=false); reason is its invalid_reason
and, separately, stale (with staleReason): an F* row (the F* runners stopped on 2026-11-15),
or a Lean suite with no row in the newest recording runs.

The l4w3c suites (RDF and SPARQL) are split into their sub-manifests when the run's meta.json
has "parts" (release-tests.py records l4w3c's score line of each included manifest); each part
is classified by the rules of spec-suites.json "parts" (SPARQL Query, Update, result formats,
protocol, ...; RDF N-Triples, Turtle, ...).

  python3 tests/browser-wpt/specs-data.py --out DIR
  python3 tests/browser-wpt/specs-data.py --runs runs.csv --meta-dir DIR --out DIR   (offline)

Network: runs.csv (about 300 kB) and the meta.json of the newest row of each l4w3c and OWL
suite (about 20 small files). --no-meta skips the meta.json files.
"""
import argparse, csv, io, json, os, re, sys, time, urllib.request
from collections import defaultdict
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
RAW = "https://raw.githubusercontent.com/danbri/factoidal-builds/wpt-scores/"
MAPPING = os.path.join(HERE, "spec-suites.json")
# A Lean suite with no row for this long before the newest Lean row is stale (dropped from the runner).
STALE_LEAN_HOURS = 36
# Suites that belong to the Conformance page (WPT, reftests, Test262).
OTHER_PAGE = re.compile(r"^(wpt|test262)")

RECORD_FIELDS = ["suite", "family", "spec", "version", "technology", "testType", "population", "manifest", "source",
                 "sourceKind", "engine", "platform", "commit", "run", "finished", "trigger", "total", "passed", "failed",
                 "decided", "undecided", "status", "reason", "stale", "staleReason", "current", "headline", "workflow"]


def get(url, tries=3):
    for attempt in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "specs-data"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except Exception as e:
            if attempt == tries - 1:
                raise RuntimeError(f"fetch {url}: {e}")
            time.sleep(2 + 3 * attempt)


def num(x, f=int):
    try:
        return f(x)
    except (TypeError, ValueError):
        return None


def ts(iso):
    return datetime.strptime(iso, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()


def status_of(row):
    """(status, reason) of a runs.csv row: valid, partial or invalid."""
    total, decided = num(row["denominator"]) or num(row["names_total"]) or 0, num(row["names_run"]) or 0
    if row["valid"] != "true":
        return "invalid", row.get("invalid_reason") or "not valid"
    if total and decided < total:
        what = []
        if num(row.get("skip")):
            what.append(f"{row['skip']} skipped, refused or unsupported")
        return "partial", f"{total - decided} of {total:,} not decided" + (f" ({'; '.join(what)})" if what else "")
    return "valid", ""


def classify(rules, label):
    base = re.sub(r"\s*\(lenient\)$", "", label)
    for pattern, spec, urls, tech in rules:
        if re.search(pattern, base):
            return spec, urls, tech
    return None, None, None


def parts_of(meta, rules, version, prefix):
    """The sub-manifest rows of an l4w3c run (meta.json "parts"), classified. Labels that occur
    twice (an umbrella manifest that lists a sub-manifest twice) are summed."""
    out, seen = [], {}
    for p in (meta or {}).get("parts") or []:
        label = p.get("label") or "?"
        spec, urls, tech = classify(rules, label)
        url = (urls or {}).get(version)
        if label in seen:
            q = seen[label]
            for k in ("passed", "failed", "skipped", "total"):
                q[k] += p.get({"passed": "pass", "failed": "fail", "skipped": "skip"}.get(k, k), 0) or 0
            continue
        # The part's specification by its W3C title: "SPARQL 1.1 Update", "RDF 1.2 Turtle".
        q = {"label": label, "spec": f"{prefix} {version} {spec}" if spec else "unclassified", "specUrl": url, "technology": tech or "unclassified",
             "version": version, "passed": p.get("pass", 0) or 0, "failed": p.get("fail", 0) or 0,
             "skipped": (p.get("skip", 0) or 0) + (p.get("unsupported", 0) or 0), "total": p.get("total", 0) or 0}
        seen[label] = q
        out.append(q)
    return out


def load_meta(row, a):
    if a.no_meta:
        return None
    if a.meta_dir:
        p = os.path.join(a.meta_dir, row["run_id"] + ".json")
        if not os.path.exists(p):
            return None
        with open(p) as f:
            return json.load(f)
    try:
        return json.loads(get(row.get("meta_url") or RAW + f"runs/{row['run_id']}/meta.json"))
    except Exception as e:
        print(f"meta.json of {row['run_id']} not read: {e}", file=sys.stderr)
        return None


def build(rows, M, a, now_iso):
    suites_map, fams = M["suites"], {f["id"]: f for f in M["families"]}
    by_suite = defaultdict(list)
    for r in rows:
        if not OTHER_PAGE.match(r["suite"]):
            by_suite[r["suite"]].append(r)
    for v in by_suite.values():
        v.sort(key=lambda r: (r["finished_utc"] or r["started_utc"], r["run_id"]))
    unmapped = sorted(s for s in by_suite if s not in suites_map)
    for s in unmapped:
        print(f"suite {s} is not in spec-suites.json: add it (skills/wpt-runs section 11)", file=sys.stderr)
    lean_newest = max((r["finished_utc"] for s, v in by_suite.items() for r in v if r["engine"] == "lean" and r["finished_utc"]), default="")

    def stale_of(sid, m, cur):
        if m["engine"] == "fstar":
            nxt = m.get("supersededBy") or m.get("coveredBy") or ", ".join(m.get("replacedBy") or [])
            how = "superseded by" if m.get("supersededBy") else "covered by" if m.get("coveredBy") else "replaced by"
            return True, f"F* runner stopped {M['fstarStopped'][:10]}" + (f"; {how} {nxt}" if nxt else "")
        if cur and lean_newest and ts(lean_newest) - ts(cur["finished_utc"]) > STALE_LEAN_HOURS * 3600:
            return True, f"no row since {cur['finished_utc'][:16].replace('T', ' ')} UTC (the newest recording is {lean_newest[:16].replace('T', ' ')} UTC)"
        return False, ""

    def record(sid, m, r, current):
        st, why = status_of(r)
        total, decided = num(r["denominator"]) or num(r["names_total"]) or 0, num(r["names_run"]) or 0
        stale, staleWhy = stale_of(sid, m, r) if current else (False, "")
        src = M["sources"].get(m.get("source"), {})
        return {"suite": sid, "family": m["family"], "spec": m["spec"], "version": m["version"], "technology": m["technology"],
                "testType": m["testType"], "population": m["population"], "manifest": m.get("manifest", ""), "source": m.get("source", ""),
                "sourceKind": src.get("kind", ""), "engine": r["engine"], "platform": r["platform"], "commit": r["factoidal_commit"],
                "run": r["run_id"], "finished": r["finished_utc"], "trigger": r["trigger"], "total": total, "passed": num(r["passed"]) or 0,
                "failed": num(r["failed"]) if r["failed"] != "" else None, "decided": decided, "undecided": max(0, total - decided),
                "status": st, "reason": why, "stale": stale, "staleReason": staleWhy, "current": current,
                "headline": bool(m.get("headline")) and m["engine"] == "lean", "workflow": r["workflow_run_url"]}

    suites, csv_rows = [], []
    for sid, m in suites_map.items():
        v = by_suite.get(sid, [])
        if a.only_recorded and not v:
            continue
        for r in v:
            csv_rows.append(record(sid, m, r, r is v[-1]))
        if not v:
            rec = {"suite": sid, "family": m["family"], "spec": m["spec"], "version": m["version"], "technology": m["technology"],
                   "testType": m["testType"], "population": m["population"], "manifest": m.get("manifest", ""), "source": m.get("source", ""),
                   "sourceKind": M["sources"].get(m.get("source"), {}).get("kind", ""), "engine": m["engine"], "platform": "",
                   "commit": "", "run": "", "finished": "", "trigger": "", "total": 0, "passed": 0, "failed": None, "decided": 0,
                   "undecided": 0, "status": "invalid", "reason": "never recorded", "stale": True, "staleReason": "never recorded",
                   "current": True, "headline": False, "workflow": ""}
        else:
            rec = record(sid, m, v[-1], True)
        rec.update(specUrl=m.get("specUrl", ""), runs=len(v),
                   **{k: m[k] for k in ("continues", "supersededBy", "coveredBy", "replacedBy", "note") if m.get(k)})
        if v and rec["status"] == "invalid":
            lv = next((r for r in reversed(v) if r["valid"] == "true"), None)
            if lv:
                rec["lastValid"] = {"passed": num(lv["passed"]) or 0, "total": num(lv["denominator"]) or 0,
                                    "finished": lv["finished_utc"], "commit": lv["factoidal_commit"], "run": lv["run_id"]}
        if v and m["engine"] == "lean" and (m.get("parts") or sid.startswith("l4-owl2-")):
            meta = load_meta(v[-1], a)
            if m.get("parts"):
                ps = parts_of(meta, M["parts"][m["parts"]], m["version"], m["spec"].split(" ")[0])
                if ps:
                    rec["parts"] = ps
            elif meta:
                sc = (meta.get("population") or {}).get("status_counts") or {}
                ap = sc.get("approved")
                if ap and ap.get("total"):
                    rec["approved"] = {"passed": ap.get("pass", 0), "total": ap["total"]}
        suites.append(rec)

    # Family headlines: the current, not stale, headline suites of each family.
    families = []
    for f in M["families"]:
        mine = [s for s in suites if s["family"] == f["id"]]
        head = [s for s in mine if s["headline"] and not s["stale"]]
        counted = [s for s in head if s["status"] != "invalid"]
        hl = {"suites": len(head), "complete": sum(1 for s in counted if s["total"] and s["passed"] == s["total"]),
              "valid": sum(1 for s in head if s["status"] == "valid"), "partial": sum(1 for s in head if s["status"] == "partial"),
              "invalid": sum(1 for s in head if s["status"] == "invalid"),
              "stale": sum(1 for s in mine if s["stale"] and s["engine"] == "lean"),
              "fstarOnly": sum(1 for s in mine if s["engine"] == "fstar" and not s.get("supersededBy") and not s.get("coveredBy") and not s.get("replacedBy")),
              "unrecorded": sum(1 for u in M.get("unrecorded", []) if u["family"] == f["id"]),
              "newest": max((s["finished"] for s in head if s["finished"]), default="")}
        if f.get("additive", True):
            hl["passed"] = sum(s["passed"] for s in counted)
            hl["decided"] = sum(s["decided"] for s in counted)
            hl["total"] = sum(s["total"] for s in counted)
        else:
            hl["passed"] = hl["decided"] = hl["total"] = None
        hl["weakest"] = [s["suite"] for s in sorted(counted, key=lambda s: (s["passed"] / s["total"]) if s["total"] else 1)[:3]
                         if s["total"] and s["passed"] < s["total"]]
        families.append({**{k: f[k] for k in ("id", "name", "summary")}, "additive": f.get("additive", True),
                         **({"additiveNote": f["additiveNote"]} if f.get("additiveNote") else {}), "headline": hl})

    # History: every row per suite; and each family's headline per recording run (workflow run).
    series = {}
    for sid in suites_map:
        if a.only_recorded and sid not in by_suite:
            continue
        series[sid] = [[r["finished_utc"], r["factoidal_commit"][:9], num(r["passed"]) or 0, num(r["names_run"]) or 0,
                        num(r["denominator"]) or 0, status_of(r)[0][0]] for r in by_suite.get(sid, [])]
    fam_series = {}
    for f in M["families"]:
        if not f.get("additive", True):
            continue
        heads = {sid for sid, m in suites_map.items() if m["family"] == f["id"] and m.get("headline") and m["engine"] == "lean"}
        batches = defaultdict(list)
        for sid in heads:
            for r in by_suite.get(sid, []):
                batches[r["workflow_run_url"] or r["run_id"]].append(r)
        pts = []
        for key, rs in batches.items():
            ok = [r for r in rs if r["valid"] == "true"]
            if not ok:
                continue
            pts.append([max(r["finished_utc"] for r in rs), ok[0]["factoidal_commit"][:9], sum(num(r["passed"]) or 0 for r in ok),
                        sum(num(r["denominator"]) or 0 for r in ok), len(ok)])
        fam_series[f["id"]] = sorted(pts)

    counts = {k: sum(1 for s in suites if s["status"] == k and not s["stale"]) for k in ("valid", "partial", "invalid")}
    counts["stale"] = sum(1 for s in suites if s["stale"])
    data = {"format": "spec-conformance-v1", "generatedAt": now_iso,
            "source": {"runs": (a.runs if "://" in a.runs else os.path.basename(a.runs)) if a.runs else RAW + "runs.csv", "rows": sum(len(v) for v in by_suite.values()),
                       "mapping": "tests/browser-wpt/spec-suites.json"},
            "fstarStopped": M["fstarStopped"], "newestLean": lean_newest, "staleLeanHours": STALE_LEAN_HOURS,
            "counts": counts, "families": families, "suites": suites, "sources": M["sources"],
            "unrecorded": M.get("unrecorded", []), "unmapped": unmapped}
    history = {"format": "spec-conformance-history-v1", "generatedAt": now_iso,
               "columns": ["finished", "commit", "passed", "decided", "total", "status"],
               "familyColumns": ["finished", "commit", "passed", "total", "suites"],
               "suites": series, "families": fam_series}
    return data, history, csv_rows


def write(out, data, history, csv_rows):
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "data.json"), "w") as f:
        json.dump(data, f, separators=(",", ":"), ensure_ascii=False)
    with open(os.path.join(out, "history.json"), "w") as f:
        json.dump(history, f, separators=(",", ":"), ensure_ascii=False)
    with open(os.path.join(out, "records.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=RECORD_FIELDS, extrasaction="ignore", lineterminator="\n")
        w.writeheader()
        for r in sorted(csv_rows, key=lambda r: (r["finished"], r["suite"])):
            w.writerow({k: ("true" if v is True else "false" if v is False else "" if v is None else v) for k, v in r.items()})


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", required=True, help="directory for data.json, history.json, records.csv")
    ap.add_argument("--runs", help="runs.csv path or URL (default: wpt-scores on GitHub)")
    ap.add_argument("--mapping", default=MAPPING)
    ap.add_argument("--meta-dir", help="read meta.json of a run from DIR/<run_id>.json instead of the network")
    ap.add_argument("--no-meta", action="store_true", help="do not read meta.json (no SPARQL/RDF parts, no OWL Approved counts)")
    ap.add_argument("--now", help="generatedAt (ISO, for reproducible test output)")
    ap.add_argument("--only-recorded", action="store_true", help="leave out mapped suites with no rows (sample data)")
    a = ap.parse_args()
    text = (get(a.runs) if a.runs and "://" in a.runs else open(a.runs, "rb").read() if a.runs else get(RAW + "runs.csv")).decode()
    rows = list(csv.DictReader(io.StringIO(text)))
    with open(a.mapping) as f:
        M = json.load(f)
    now = a.now or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    data, history, csv_rows = build(rows, M, a, now)
    write(a.out, data, history, csv_rows)
    c = data["counts"]
    print(f"{len(data['suites'])} suites ({c['valid']} valid, {c['partial']} partial, {c['invalid']} invalid, {c['stale']} stale), "
          f"{len(csv_rows)} records, {len(data['unmapped'])} unmapped -> {a.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
