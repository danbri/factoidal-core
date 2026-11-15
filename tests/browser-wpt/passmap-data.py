#!/usr/bin/env python3
"""passmap-data.py: the data of the WPT Pass Map page, from the recorded runs.

Reads the wpt-scores branch of danbri/factoidal-builds (runs.csv, rivals.csv,
runs/RUN_ID/meta.json, and the run's factoidal-wpt-full-v1 result file) and the
wpt.fyi summary_v2 files of the browsers, and writes one JSON object, the page's `D`:

  latest     the newest valid full WPT run (runs.csv: suite=wpt, valid=true, kind=full):
             run id, finish time, engine commit, platform, its share and the share
             without encoding/ on its own WPT commit's scale
  strata     per stratum (wpt-score.py's strata), at the run's WPT commit:
             [name, chrome subtests, Foafnaut, <one column per browser>, names run, names]
             Each name's passes are capped at Chrome's count for it, as wpt-full.py
             does; Foafnaut's passes of a name come from the run's "passing" table.
  tot, totEx sums of strata, all and without encoding/
  browsers   the aligned wpt.fyi runs used (rivals.csv rows at that commit, not partial)
  history    every valid full WPT run, one row per engine commit (its newest run), newest first
  test262    Test262 through WPT (the third_party/test262 stratum) and the full Test262
             runs (runs.csv suite=test262, valid=true), when there are any
  semweb     the semantic-web and data-format suites (SEMWEB below), one row per suite or
             OWL 2 population: the newest run on the built-in engine (engine lean), else the
             newest F* run, marked stale (the F* runners stopped on 2026-11-15)
  reftests   WPT reftests, per suite (runs.csv suite=wpt-reftest-svg, -css; valid=true):
             the newest run, the rival browsers on the same tests at its WPT commit
             (reftest-rivals.csv) and the history; the headline WPT share counts none of them

Everything is at the run's own WPT commit; the denominator is the Chrome run the WPT run
used (meta.json inputs.chrome_run). Other browsers come from rivals.csv rows at that commit,
and otherwise from wpt.fyi's runs at that commit (stable Chrome, Firefox, Safari, Edge;
experimental Servo, WPE WebKit, Ladybird). A browser with no run there, or a run that
reports fewer than 95% of Chrome's names, is not shown; `missing` says why. Rival data of
another commit is never used. Downloads go to --cache (default: a temporary
directory, removed at the end) and are about 10 MB.

  python3 tests/browser-wpt/passmap-data.py --out passmap-data.json
  python3 tests/browser-wpt/passmap-data.py --run RUN_ID --out passmap-data.json
  python3 tests/browser-wpt/passmap-data.py --hub docs/web/hub/conformance

--hub writes the Hub Conformance page's data.json (this object without the history lists)
and history.json (the WPT, Test262 through WPT and full Test262 histories, one compact row
per engine commit). Their schema is docs/web/hub/conformance/data.schema.json. The
conformance-data workflow of danbri/factoidal-builds runs this and commits both files to
that repository's branch hub-data; the Pages build copies them in.
"""
import argparse, csv, gzip, importlib.util, io, json, os, shutil, sys, tempfile, time, urllib.request
from collections import defaultdict
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("wptscore", os.path.join(HERE, "wpt-score.py"))
ws = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ws)

RAW = "https://raw.githubusercontent.com/danbri/factoidal-builds/wpt-scores/"
BROWSERS = ["chrome", "firefox", "safari", "edge", "servo", "wpewebkit", "ladybird"]
MILESTONES = [["M1", 32], ["M2", 45], ["M3", 65], ["M4 and Apple's bar", 90]]
T262_TARGETS = [["Apple's bar", 80], ["Goal", 90]]
PLATFORM = {"linux-x86_64": "Linux x86_64", "macos-arm64": "macOS arm64"}


def top(name):
    return name.split("?")[0].split("/")[1]


class Fetch:
    def __init__(self, cache):
        self.cache = cache

    def get(self, url, cache=True):
        path = os.path.join(self.cache, url.replace("://", "_").replace("/", "_").replace("?", "_").replace("&", "_")[-180:])
        if not cache or not os.path.exists(path):
            for attempt in range(3):
                try:
                    req = urllib.request.Request(url, headers={"User-Agent": "passmap-data"})
                    with urllib.request.urlopen(req, timeout=120) as r, open(path + ".part", "wb") as f:
                        shutil.copyfileobj(r, f)
                    os.replace(path + ".part", path)
                    break
                except Exception as e:
                    if attempt == 2:
                        raise RuntimeError(f"fetch {url}: {e}")
                    time.sleep(2 + 3 * attempt)
        with open(path, "rb") as f:
            data = f.read()
        return gzip.decompress(data) if data[:2] == b"\x1f\x8b" else data

    def json(self, url):
        return json.loads(self.get(url))

    def csv(self, url):
        return list(csv.DictReader(io.StringIO(self.get(url).decode())))


def num(x, f=float):
    try:
        return f(x)
    except (TypeError, ValueError):
        return None


def where(row):
    plat = PLATFORM.get(row["platform"], row["platform"])
    return ("local, " if row["run_id"].endswith("-local") else "cloud, ") + plat


def stamp(iso):
    return iso.replace("T", " ")[:16]


def history(rows):
    """One row per engine commit (its newest valid run), newest first."""
    best, count = {}, defaultdict(int)
    for r in rows:
        c = r["factoidal_commit"]
        count[c] += 1
        if c not in best or r["finished_utc"] > best[c]["finished_utc"]:
            best[c] = r
    out = []
    for r in sorted(best.values(), key=lambda r: r["finished_utc"], reverse=True):
        out.append({"date": stamp(r["finished_utc"]), "finished": r["finished_utc"], "engine": r["factoidal_commit"][:9],
                    "wpt": r["wpt_commit"][:10], "tests": num(r["names_run"], int), "passed": num(r["passed"], int),
                    "denominator": num(r["denominator"], int), "share": num(r["share_pct"]) / 100,
                    "shareEx": (num(r["share_ex_encoding_pct"]) or 0) / 100, "where": where(r),
                    "runs": count[r["factoidal_commit"]], "run": r["run_id"]})
    return out


WPTFYI = "https://wpt.fyi/api/runs?sha={sha}&label={label}&max-count=1" + "".join(f"&product={b}" for b in BROWSERS)
EXPERIMENTAL = {"servo", "wpewebkit", "ladybird"}


def pick_rivals(fetch, rivals, commit):
    """{browser: {version, channel, id, time, summary_url}} at exactly this WPT commit, and
    {browser: reason} for the browsers with no run there."""
    got, missing = {}, {}
    for r in rivals:
        if r["wpt_commit"] == commit and r["browser"] != "chrome" and r.get("status") == "unavailable":
            missing[r["browser"]] = r.get("reason") or "no run at this WPT commit"
            continue
        if r["wpt_commit"] == commit and r["browser"] != "chrome":
            got[r["browser"]] = {"version": r["version"].replace("Servo ", ""), "channel": r["channel"],
                                 "id": num(r["wptfyi_run_id"], int), "time": r["run_time_utc"], "summary_url": r["summary_url"],
                                 "source": "rivals.csv"}
    want = [b for b in BROWSERS if b != "chrome" and b not in got and b not in missing]
    if want:
        for label in ("stable", "experimental"):
            try:
                runs = json.loads(fetch.get(WPTFYI.format(sha=commit[:10], label=label), cache=False))
            except Exception as e:
                print(f"wpt.fyi runs at {commit[:10]} ({label}) not read: {e}", file=sys.stderr)
                for b in want:
                    missing.setdefault(b, "wpt.fyi could not be read")
                continue
            for r in sorted(runs, key=lambda r: r["time_start"], reverse=True):
                b = r["browser_name"]
                if b in want and b not in got and (label == "experimental") == (b in EXPERIMENTAL) \
                        and r.get("full_revision_hash", commit).startswith(commit[:10]):
                    got[b] = {"version": r["browser_version"], "channel": label, "id": r["id"], "time": r["time_start"],
                              "summary_url": r["results_url"], "source": "wpt.fyi"}
    for b in BROWSERS:
        if b != "chrome" and b not in got:
            missing.setdefault(b, "no run at this WPT commit")
    return got, missing


def os_of(url):
    # .../chrome-157.0.8103.78-linux-22.04-720356c15a-summary_v2.json.gz
    base = url.rsplit("/", 1)[-1]
    for o in ("linux", "mac", "win", "android", "ios"):
        if f"-{o}-" in base:
            return o
    return ""


def t262_full(fetch, rows):
    """Full Test262 runs: runs.csv suite=test262, valid=true. Directory and feature
    details are taken from meta.json when the runner writes them."""
    runs = sorted((r for r in rows if r["suite"] == "test262" and r["valid"] == "true"),
                  key=lambda r: r["finished_utc"], reverse=True)
    if not runs:
        return None
    hist = []
    for r in runs:
        den = num(r["denominator"], int) or num(r["names_total"], int)
        hist.append({"date": stamp(r["finished_utc"]), "finished": r["finished_utc"], "engine": r["factoidal_commit"][:9],
                     "where": where(r), "passed": num(r["passed"], int), "failed": num(r["failed"], int),
                     "skip": num(r["skip"], int), "total": den, "share": (num(r["share_pct"]) or 0) / 100,
                     "shareEx": (num(r.get("share_ex_features_pct")) / 100) if num(r.get("share_ex_features_pct")) is not None else None,
                     "run": r["run_id"]})
    latest = dict(hist[0])
    meta = {}
    try:
        meta = fetch.json(runs[0]["meta_url"] or RAW + f"runs/{runs[0]['run_id']}/meta.json")
    except Exception as e:
        print(f"test262 meta.json not read: {e}", file=sys.stderr)
    tot = meta.get("totals") or {}
    for k in ("share_ex_features_pct", "share_ex_features"):
        v = num(tot.get(k))
        if latest["shareEx"] is None and v is not None:
            latest["shareEx"] = v / 100 if v > 1 else v
    ex = meta.get("excluded_features") or tot.get("excluded_features") or meta.get("features_excluded")
    latest["excludedFeatures"] = ex if isinstance(ex, list) else []
    dirs = meta.get("directories") or {}
    drows = []
    for name, v in dirs.items():
        if not isinstance(v, dict):
            continue
        t = num(v.get("total")) or num(v.get("names")) or num(v.get("tests"))
        p = num(v.get("passed"))
        if t and p is not None:
            drows.append([name, int(t), int(p)])
    drows.sort(key=lambda d: -d[1])
    latest["directories"] = drows
    latest["workflow"] = runs[0]["workflow_run_url"]
    return {"latest": latest, "history": hist}


REFTEST_SUITES = [("svg", "svg/"), ("css", "css/")]


def reftests(fetch, rows):
    """WPT reftests (runs.csv suite=wpt-reftest-<dir>, valid=true; skills/wpt-runs section 10):
    for each suite with a valid run, the newest run (passed, total, share, statuses, the
    directories from its meta.json), the rival browsers on the same tests at the same WPT
    commit (reftest-rivals.csv), and one history row per engine commit (its newest run)."""
    try:
        riv = fetch.csv(RAW + "reftest-rivals.csv")
    except Exception as e:
        print(f"reftest-rivals.csv not read: {e}", file=sys.stderr)
        riv = []
    out = {}
    for key, prefix in REFTEST_SUITES:
        suite = f"wpt-reftest-{key}"
        runs = sorted((r for r in rows if r["suite"] == suite and r["valid"] == "true"), key=lambda r: r["finished_utc"], reverse=True)
        if not runs:
            continue
        r = runs[0]
        meta = {}
        try:
            meta = fetch.json(r["meta_url"] or RAW + f"runs/{r['run_id']}/meta.json")
        except Exception as e:
            print(f"{suite} meta.json not read: {e}", file=sys.stderr)
        rv = [x for x in riv if x["suite"] == suite and x["wpt_commit"] == r["wpt_commit"]]
        browsers, missing = {}, {}
        for x in rv:
            if x["status"] == "ok":
                browsers[x["browser"]] = {"version": x["version"], "passed": num(x["passed"], int), "share": (num(x["share_pct"]) or 0) / 100}
            else:
                missing[x["browser"]] = x.get("reason") or "no run at this WPT commit"
        dirs = [[d, v.get("tests"), v.get("passed"), v.get("chrome")] for d, v in (meta.get("directories") or {}).items()]
        tot = meta.get("totals") or {}
        statuses = tot.get("statuses") or {}
        chrome_by_run = {}
        for x in riv:
            if x["suite"] == suite and x["browser"] == "chrome" and x["status"] == "ok":
                chrome_by_run[x["wpt_commit"]] = (num(x["share_pct"]) or 0) / 100
        hist = []
        for h in history(runs):
            hist.append({"finished": h["finished"], "engine": h["engine"], "wpt": h["wpt"], "where": h["where"],
                         "passed": h["passed"], "total": h["denominator"], "share": round(h["share"], 6),
                         "chrome": chrome_by_run.get(next(x["wpt_commit"] for x in runs if x["run_id"] == h["run"])), "run": h["run"]})
        out[key] = {"suite": suite, "prefix": prefix,
                    "latest": {"run": r["run_id"], "finished": r["finished_utc"], "engine": r["factoidal_commit"], "where": where(r),
                               "wpt": r["wpt_commit"][:10], "passed": num(r["passed"], int), "total": num(r["denominator"], int),
                               "share": (num(r["share_pct"]) or 0) / 100, "statuses": statuses,
                               "chromePassesWeFail": tot.get("chrome_passes_we_fail"), "workflow": r["workflow_run_url"],
                               "results": r["result_url"], "directories": dirs},
                    "browsers": browsers, "missing": missing, "history": hist}
    return out


def t262_wpt_history(fetch, hist, rows):
    """Test262 through WPT for each row of the WPT history: WPT's third_party directory
    (only third_party/test262 has tests) from the run's meta.json, on its own WPT commit."""
    by_id = {r["run_id"]: r for r in rows}
    out = []
    for h in hist:
        r = by_id.get(h["run"])
        try:
            d = (fetch.json(r["meta_url"] or RAW + f"runs/{r['run_id']}/meta.json").get("directories") or {}).get("third_party")
        except Exception as e:
            print(f"meta.json of {h['run']} not read: {e}", file=sys.stderr)
            d = None
        if d and d.get("chrome"):
            out.append({"date": h["date"], "finished": h["finished"], "engine": h["engine"], "wpt": h["wpt"],
                        "passed": d.get("passed"), "total": d.get("chrome"), "share": round(d["passed"] / d["chrome"], 6),
                        "where": h["where"], "run": h["run"]})
    return out


# The semantic-web and data-format suites, by group: (label, Lean suite or None, F* suite or None).
# Lean suites are release-tests' lean-w3c and lean-semweb rows (engine lean); the F* suite is the
# same suite's row from before 2026-11-15, when automatic F* builds and their suite runs stopped.
# A suite with no Lean row shows its newest F* row, marked stale. OWL 2 is listed by population of
# the W3C OWL 2 Test Cases (release-tests/owl-populations.py in danbri/factoidal-builds).
FSTAR_STOPPED = "2026-11-15"
SEMWEB = [
    ("RDF and SPARQL", None, [
        ("RDF 1.1 syntaxes and semantics", "l4w3c-rdf11", "rdf"),
        ("RDF 1.2 syntaxes (with N-Triples/N-Quads c14n)", "l4w3c-rdf12", "rdf12"),
        ("RDF 1.2 canonical N-Triples/N-Quads (F*: its own row)", None, "rdf12c14n"),
        ("RDF 1.2 semantics (entailment)", "l4-rdf12entail", "rdf12entail"),
        ("RDF Dataset Canonicalization (RDFC-1.0)", "l4w3c-rdfc10", "rdfc10"),
        ("SPARQL 1.1", "l4w3c-sparql11", "sparql"),
        ("SPARQL 1.2", "l4w3c-sparql12", "sparql12"),
    ]),
    ("OWL 2", "W3C OWL 2 Test Cases (2009-11-18), every test case not Rejected: 489 cases, 355 Approved. "
     "W3C Document Licence. Each row is one population with its full official count; a case typed "
     "with two test types, or annotated with both semantics, is in each of those populations.", [
        ("PositiveEntailmentTest, Direct Semantics", "l4-owl2-positive-entailment-direct", None),
        ("NegativeEntailmentTest, Direct Semantics", "l4-owl2-negative-entailment-direct", None),
        ("ConsistencyTest, Direct Semantics", "l4-owl2-consistency-direct", None),
        ("InconsistencyTest, Direct Semantics", "l4-owl2-inconsistency-direct", "owl2_dl_inconsistency"),
        ("PositiveEntailmentTest, RDF-Based Semantics", "l4-owl2-positive-entailment-rdfbased", None),
        ("NegativeEntailmentTest, RDF-Based Semantics", "l4-owl2-negative-entailment-rdfbased", None),
        ("ConsistencyTest, RDF-Based Semantics", "l4-owl2-consistency-rdfbased", None),
        ("InconsistencyTest, RDF-Based Semantics", "l4-owl2-inconsistency-rdfbased", None),
        ("ProfileIdentificationTest, OWL 2 EL", "l4-owl2-profile-el", None),
        ("ProfileIdentificationTest, OWL 2 QL", "l4-owl2-profile-ql", None),
        ("ProfileIdentificationTest, OWL 2 RL", "l4-owl2-profile-rl", None),
        ("Syntax: species (OWL 2 DL or not), all cases", "l4-owl2-species-all", None),
        ("Syntax: species DL", "l4-owl2-species-dl", "owl_syntax_dl_species"),
        ("Syntax: species Full only", "l4-owl2-species-full-only", None),
        ("F*: RL closure over the profile-EL catalog (all test types)", None, "owl2_profile_el"),
        ("F*: RL closure over the profile-QL catalog (all test types)", None, "owl2_profile_ql"),
        ("F*: RL closure, PositiveEntailmentTest of the profile-RL catalog", None, "owl_rl_positive_entailment"),
    ]),
    ("SHACL", None, [
        ("SHACL Core (1.0 suite)", "l4-shacl_core", "shacl_core"),
        ("SHACL-SPARQL (1.0 suite)", "l4-shacl_sparql", "shacl_sparql"),
        ("SHACL 1.2 Core", "l4-shacl12_core", "shacl12_core"),
        ("SHACL 1.2 SPARQL", "l4-shacl12_sparql", "shacl12_sparql"),
        ("SHACL 1.2 node expressions", "l4-shacl12_node_expr", "shacl12_node_expr"),
        ("SHACL 1.2 rules (Lean: every rules manifest; F*: eval only)", "l4-shacl12_rules", "shacl12_rules"),
        ("SHACL 1.2 rules syntax (F*: its own row)", None, "shacl12_rules_syntax"),
        ("SHACL 1.2 rules well-formedness (F*: its own row)", None, "shacl12_rules_wellformed"),
        ("SHACL 1.2 rules stratification (F*: its own row)", None, "shacl12_rules_stratification"),
    ]),
    ("ShEx", None, [
        ("ShEx validation (ShExJ)", "l4-shex", "shex"),
        ("ShExC parser against the ShExJ twins", "l4-shexc_differential", None),
        ("ShExC negative syntax", "l4-shexc_negative_syntax", None),
        ("ShEx negative structure (ShEx 2.1 section 5.7)", "l4-shexc_negative_structure", None),
    ]),
    ("JSON-LD", None, [
        ("toRdf", "l4-jsonld_tordf", "jsonld_tordf"),
        ("expand", "l4-jsonld_expand", "jsonld_expand"),
        ("compact", "l4-jsonld_compact", "jsonld_compact"),
        ("flatten", "l4-jsonld_flatten", "jsonld_flatten"),
        ("fromRdf", "l4-jsonld_fromrdf", "jsonld_fromrdf"),
        ("HTML", "l4-jsonld_html", None),
        ("framing", "l4-jsonld_frame", None),
    ]),
    ("CSV on the Web", None, [
        ("csv2rdf", "l4-csvw_csv2rdf", "csvw_csv2rdf"),
        ("csv2json", "l4-csvw_csv2json", "csvw_csv2json"),
        ("validation", "l4-csvw_validation", "csvw_validation"),
    ]),
    ("RML and RIF", None, [
        ("RML-Core", "l4-rml_core", "rml_core"),
        ("RML-IO", "l4-rml_io", None),
        ("RML-CC", "l4-rml_cc", None),
        ("RML-star", "l4-rml_star", None),
        ("RML-FNML", "l4-rml_fnml", None),
        ("RIF Core", "l4-rif_core", "rif_core"),
    ]),
    ("Verifiable Credentials and DIDs", None, [
        ("VC Data Model 2.0, structural", "l4-vc_stage1", "vc_stage1"),
        ("did:key", "l4-did_key", "did_key"),
        ("Data Integrity eddsa-rdfc-2022", "l4-vc_di_eddsa_rdfc_2022", None),
        ("Data Integrity EdDSA spec vectors", "l4-vc_di_eddsa_vectors", None),
        ("Data Integrity ECDSA spec vectors", "l4-vc_di_ecdsa_vectors", None),
    ]),
    ("XML and other formats", None, [
        ("XML 1.0 conformance (xmlconf)", "l4-xml_conformance", "xml_conformance"),
        ("XSLT 1.0", "l4-xslt", "xslt"),
        ("Schematron", "l4-schematron", "schematron"),
        ("MathML (Content)", "l4-mathml", "mathml"),
        ("JSON Schema draft-07", "l4-jsonschema", "jsonschema"),
    ]),
]


def semweb(fetch, rows):
    """D.semweb: every suite of SEMWEB as its own row. The newest valid Lean row is the
    number; with none, the newest Lean row's reason (a population not run) or the newest
    valid F* row, marked stale. OWL 2 population rows also carry their Approved-only count
    from the run's meta.json."""
    newest = lambda suite, engine, valid=True: max((r for r in rows if r["suite"] == suite and r["engine"] == engine
                                                    and (r["valid"] == "true") == valid), key=lambda r: r["finished_utc"], default=None)
    groups = []
    for name, note, entries in SEMWEB:
        out = []
        for label, lean, fstar in entries:
            L = newest(lean, "lean") if lean else None
            Li = newest(lean, "lean", False) if lean else None
            F = newest(fstar, "fstar") if fstar else None
            row = {"label": label, "suite": lean or fstar,
                   "fstar": None if not F else {"suite": fstar, "passed": num(F["passed"], int), "total": num(F["denominator"], int),
                                                 "finished": F["finished_utc"]}}
            if L:
                row.update(engine="lean", passed=num(L["passed"], int), total=num(L["denominator"], int),
                           run=num(L["names_run"], int), finished=L["finished_utc"], commit=L["factoidal_commit"][:9],
                           stale=False)
                if lean.startswith("l4-owl2-") and L.get("meta_url"):
                    try:
                        sc = (fetch.json(L["meta_url"]).get("population") or {}).get("status_counts") or {}
                        ap = sc.get("approved")
                        if ap:
                            row["approved"] = {"passed": ap.get("pass"), "total": ap.get("total")}
                    except Exception as e:
                        print(f"{lean} meta.json not read: {e}", file=sys.stderr)
            elif Li and (not F or Li["finished_utc"] > F["finished_utc"]):
                row.update(engine="lean", passed=None, total=num(Li["denominator"], int) or None, run=0,
                           finished=Li["finished_utc"], commit=Li["factoidal_commit"][:9], stale=False,
                           notRun=Li["invalid_reason"])
            elif F:
                row.update(engine="fstar", passed=num(F["passed"], int), total=num(F["denominator"], int),
                           run=num(F["names_run"], int), finished=F["finished_utc"], commit=F["factoidal_commit"][:9],
                           stale=True, staleReason=f"not run since F* CI stopped ({FSTAR_STOPPED})"
                           + ("; no Lean runner" if not lean else "; the Lean run has no valid row yet"))
            else:
                row.update(engine=None, passed=None, total=None, run=0, finished=None, commit=None, stale=True,
                           staleReason="never recorded")
            out.append(row)
        groups.append({"name": name, "note": note, "rows": out})
    return {"fstarStopped": FSTAR_STOPPED, "groups": groups}


def write_hub(D, out_dir):
    """The Hub's Conformance page files: data.json (the newest runs, without the history
    lists) and history.json (one compact row per engine commit, for the charts)."""
    os.makedirs(out_dir, exist_ok=True)
    data = json.loads(json.dumps(D))
    hist = {"format": "conformance-history-v1", "generatedAt": D["generatedAt"],
            "wpt": [{k: (round(h[k], 6) if k in ("share", "shareEx") else h[k])
                     for k in ("finished", "engine", "wpt", "where", "passed", "denominator", "share", "shareEx", "run")}
                    for h in data.pop("history")],
            "test262wpt": data["test262"].pop("wptHistory", []),
            "test262": [],
            "reftests": {k: v.pop("history") for k, v in (data.get("reftests") or {}).items()}}
    full = data["test262"].get("full")
    if full:
        hist["test262"] = [{k: h[k] for k in ("finished", "engine", "where", "passed", "total", "share", "shareEx", "run")}
                           for h in full.pop("history")]
        full["runs"] = len(hist["test262"])
    data["format"] = "conformance-data-v1"
    for name, obj in (("data.json", data), ("history.json", hist)):
        with open(os.path.join(out_dir, name), "w") as f:
            json.dump(obj, f, separators=(",", ":"), sort_keys=False)
            f.write("\n")


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument("--out", help="write the page's D here (one JSON object)")
    p.add_argument("--hub", help="write the Hub Conformance page files data.json and history.json into this directory")
    p.add_argument("--run", help="run_id of the WPT run to map (default: the newest valid full run)")
    p.add_argument("--cache", help="download directory, kept (default: temporary, removed)")
    a = p.parse_args()
    if not a.out and not a.hub:
        p.error("give --out or --hub")
    cache = a.cache or tempfile.mkdtemp(prefix="passmap-")
    os.makedirs(cache, exist_ok=True)
    try:
        build(a, Fetch(cache))
    finally:
        if not a.cache:
            shutil.rmtree(cache, ignore_errors=True)


def build(a, fetch):
    t0 = time.time()
    rows = fetch.csv(RAW + "runs.csv")
    rivals = fetch.csv(RAW + "rivals.csv")
    wpt = [r for r in rows if r["suite"] == "wpt" and r["valid"] == "true" and r["kind"] == "full"]
    if not wpt:
        sys.exit("no valid full WPT run in runs.csv")
    run = max(wpt, key=lambda r: r["finished_utc"]) if not a.run else next(r for r in wpt if r["run_id"] == a.run)
    meta = fetch.json(run["meta_url"] or RAW + f"runs/{run['run_id']}/meta.json")
    res = fetch.json(run["result_url"])
    passing, missing = res["passing"], set(res.get("missing", []))
    chrome_own = fetch.json(meta["inputs"]["chrome_run"]["results_url"])
    ran = {n for n, v in chrome_own.items() if v["c"][1] > 0} - missing

    commit = run["wpt_commit"]
    cr = meta["inputs"]["chrome_run"]
    riv, missing = pick_rivals(fetch, rivals, commit)
    riv["chrome"] = {"version": cr["browser_version"], "channel": "stable", "id": cr["id"], "time": cr["time_start"],
                     "summary_url": cr["results_url"], "source": "meta.json"}
    chrome = chrome_own
    want = sorted(n for n, v in chrome.items() if v["c"][1] > 0)
    summ = {"chrome": chrome}
    for b in BROWSERS:
        if b in riv and b != "chrome":
            try:
                summ[b] = fetch.json(riv[b]["summary_url"])
            except Exception as e:
                missing[b] = f"summary file not read ({e})"
                continue
            rep = sum(1 for n in want if n in summ[b])
            if rep < 0.95 * len(want):
                missing[b] = f"partial run: {rep:,} of {len(want):,} tests reported"
                del summ[b]
    names = [b for b in BROWSERS if b in summ]

    k = len(names)
    acc = defaultdict(lambda: [0] * (k + 4))  # u, us, browsers..., run, n
    for n in want:
        ch = chrome[n]["c"][1]
        r = acc[ws.stratum(n)]
        r[0] += ch
        if n in passing:
            r[1] += min(passing[n][0], ch)
        for i, b in enumerate(names):
            s = summ[b].get(n)
            if s:
                r[2 + i] += min(s["c"][0], ch)
        if n in ran:
            r[k + 2] += 1
        r[k + 3] += 1
    strata = [[s] + v for s, v in sorted(acc.items())]
    keys = ["u", "us"] + names
    tot = {kk: sum(r[1 + i] for r in strata) for i, kk in enumerate(keys)}
    totEx = {kk: sum(r[1 + i] for r in strata if r[0].split("/")[0] != "encoding") for i, kk in enumerate(keys)}

    browsers = {}
    for b in names:
        r = riv[b]
        browsers[b] = {"id": r["id"], "browser_version": r["version"], "channel": r["channel"],
                       "os_name": os_of(r["summary_url"]), "time_start": r["time"], "source": r["source"]}

    t262row = next((r for r in strata if r[0] == "third_party/test262"), None)
    own262 = (res.get("strata") or {}).get("third_party/test262") or {}
    hist = history(wpt)
    D = {
        "format": "passmap-data-v2",
        "generatedAt": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "wptCommit": commit,
        "measuredAt": run["finished_utc"],
        "engineCommit": run["factoidal_commit"][:9],
        "engines": names,
        "missing": {b: missing[b] for b in BROWSERS if b in missing},
        "totals": {"testsRun": num(run["names_run"], int), "measured": num(run["passed"], int), "full": True},
        "denominator": tot["u"],
        "browsers": browsers,
        "tot": tot,
        "totEx": totEx,
        "strata": strata,
        "history": hist,
        "milestones": MILESTONES,
        "latest": {"run": run["run_id"], "date": run["finished_utc"][:10], "started": run["started_utc"],
                   "finished": run["finished_utc"], "where": where(run), "wpt": run["wpt_commit"][:10],
                   "engine": run["factoidal_commit"], "share": num(run["share_pct"]),
                   "shareEx": num(run["share_ex_encoding_pct"]), "passed": num(run["passed"], int),
                   "denominator": num(run["denominator"], int), "tests": num(run["names_run"], int),
                   "workflow": run["workflow_run_url"], "result": run["result_url"],
                   "outcomes": {o: num(run[o], int) for o in ("ok", "error", "timeout", "skip", "crash", "stall", "no_result")}},
        "test262": {
            "targets": T262_TARGETS,
            "wpt": None if not t262row else {
                "stratum": "third_party/test262", "u": t262row[1], "us": t262row[2],
                "browsers": {b: t262row[3 + i] for i, b in enumerate(names)}, "run": t262row[-2], "names": t262row[-1],
                "own": {"passed": own262.get("passed"), "chrome": own262.get("chrome"), "names": own262.get("names"),
                        "share": own262.get("share")}},
            "full": t262_full(fetch, rows),
            "wptHistory": t262_wpt_history(fetch, hist, wpt) if a.hub else [],
        },
        "semweb": semweb(fetch, rows),
        "reftests": reftests(fetch, rows),
    }
    if a.out:
        with open(a.out, "w") as f:
            json.dump(D, f, separators=(",", ":"))
    if a.hub:
        write_hub(D, a.hub)
    w = D["test262"]["wpt"]
    print(f"run {run['run_id']} ({run['finished_utc']}, engine {run['factoidal_commit'][:9]}): "
          f"{run['share_pct']}% ({run['share_ex_encoding_pct']}% without encoding/) at WPT {run['wpt_commit'][:10]}; "
          f"map: {100 * tot['us'] / tot['u']:.2f}% with {', '.join(names)}; missing {D['missing']}; "
          f"Test262 through WPT {100 * w['us'] / w['u']:.2f}% of {w['u']}; "
          f"full Test262 runs: {len(D['test262']['full']['history']) if D['test262']['full'] else 0}; "
          f"history {len(hist)} engine commits; {time.time() - t0:.1f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
