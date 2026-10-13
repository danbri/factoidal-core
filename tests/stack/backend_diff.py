#!/usr/bin/env python3
"""Cross-backend SPARQL differential gate.

The W3C SPARQL 1.1 QueryEvaluationTests (the real manifests, iron rule 6) are
answered by four backends over the SAME N-Quads bytes:

  lean-ref    the Lean in-memory reference evaluator (`l4factoidal query`)
  lean-store  a Shardborough collection packed from the same file
              (IBK3 + `l4block-id-v3-query` for a default graph only,
              IBK4 + `l4block-quad-query` when the test has named graphs)
  jena-tdb2   Apache Jena 6.2.0, a TDB2 database loaded from the file
  jena-mem    Apache Jena 6.2.0, the in-memory transactional dataset

Each pair of backends is compared by SPARQL 1.1 result equivalence:

  * ASK: the two booleans are equal.
  * SELECT: the two solution sequences are equal as multisets after a
    bijection of blank node labels (SPARQL 1.1 Query section 18.5 and the
    test suite's result comparison rule: results are compared up to blank
    node relabelling, and as bags unless the query has ORDER BY). For a
    query whose text has ORDER BY, the gate also reports whether the
    sequences are equal in order; ties make an order difference legal, so an
    order difference is reported apart and does not count as a
    disagreement.
  * Terms: RDF term equality, with two normalisations of the JSON result
    format only: a literal of datatype xsd:string equals the simple literal
    (RDF 1.1: simple literals ARE xsd:string literals), and language tags
    compare without case (RDF 1.1 section 3.3: language tags are
    case-insensitive).

Only SELECT and ASK tests are compared (the store tools print JSON for these
two forms); CONSTRUCT and DESCRIBE tests are counted as out of scope.

Expected disagreements are listed in tests/stack/backend_diff/expected.tsv
(pair, test IRI, issue URL or reason). The gate exits 1 when a disagreement
is not listed, or a listed one no longer disagrees (stale), so the flip to a
real assertion cannot be forgotten.

Environment: BIN (default formal/lean4/.lake/build/bin), SOTA_DL (Jena
install, as tools/sota-bench.py --install), W3C_SPARQL11 (suite directory,
default third_party/testing/w3c/sparql/sparql11), BACKEND_DIFF_WORK (scratch
directory, default a new temp dir, deleted at the end).
"""
import json, os, re, shutil, subprocess, sys, tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BIN = Path(os.environ.get("BIN", ROOT / "formal/lean4/.lake/build/bin"))
DL = Path(os.environ.get("SOTA_DL", f"/tmp/sota-dl-{ROOT.name}"))
JENA_LIB = DL / "apache-jena-6.2.0/lib"
SUITE = Path(os.environ.get("W3C_SPARQL11", ROOT / "third_party/testing/w3c/sparql/sparql11"))
EXPECTED = ROOT / "tests/stack/backend_diff/expected.tsv"
JAVA_SRC = ROOT / "tests/stack/backend_diff/JenaRunner.java"
XSD_STRING = "http://www.w3.org/2001/XMLSchema#string"
BACKENDS = ["lean-ref", "lean-store", "jena-tdb2", "jena-mem"]
PAIRS = [("lean-ref", "lean-store"), ("lean-ref", "jena-tdb2"), ("lean-ref", "jena-mem"),
         ("lean-store", "jena-tdb2"), ("jena-mem", "jena-tdb2")]

EXTRACT = """PREFIX mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#>
PREFIX qt: <http://www.w3.org/2001/sw/DataAccess/tests/test-query#>
SELECT ?t ?query ?data ?g WHERE {
  ?t a mf:QueryEvaluationTest ; mf:action ?a .
  ?a qt:query ?query .
  OPTIONAL { ?a qt:data ?data }
  OPTIONAL { ?a qt:graphData ?g }
}"""


def run(cmd, timeout=60, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return subprocess.CompletedProcess(cmd, 124, "", "timeout")


def fmt_of(path):
    return {".nt": "ntriples", ".nq": "nquads", ".trig": "trig", ".rdf": "rdfxml"}.get(
        Path(path).suffix, "turtle")


def tests_of(manifest):
    """Test rows of one manifest, read by the Lean engine."""
    p = run([str(BIN / "l4factoidal"), "query", str(manifest), "--base",
             f"file://{manifest.parent}/", "--query-string", EXTRACT])
    if p.returncode != 0:
        return {}
    out = {}
    for b in json.loads(p.stdout)["results"]["bindings"]:
        t = b["t"]["value"]
        e = out.setdefault(t, {"query": b["query"]["value"], "data": None, "graphs": set()})
        if "data" in b:
            e["data"] = b["data"]["value"]
        if "g" in b:
            e["graphs"].add(b["g"]["value"])
    return out


def nquads_of(path, graph=None):
    """N-Quads of one data file, written by the Lean engine. A graph label is
    appended to each line the Lean writer emitted (N-Quads construction)."""
    p = run([str(BIN / "l4factoidal"), "parse", path, "--format", fmt_of(path),
             "--out", "nquads", "--base", f"file://{path}"])
    if p.returncode != 0:
        return None
    lines = [l for l in p.stdout.splitlines() if l.strip()]
    if graph:
        lines = [re.sub(r" \.$", f" <{graph}> .", l) for l in lines]
    return "".join(l + "\n" for l in lines)


def last_json(text):
    for line in reversed(text.splitlines()):
        if line.startswith("{"):
            return line
    return None


def lean_ref(nq, qfile):
    p = run([str(BIN / "l4factoidal"), "query", str(nq), "--format", "nquads",
             "--base", f"file://{nq}", "--query", qfile])
    s = p.stdout.strip()
    if s in ("true", "false") and p.returncode in (0, 1):
        return {"head": {}, "boolean": s == "true"}
    if p.returncode != 0:
        return {"error": (p.stderr.strip().splitlines() or ["exit %d" % p.returncode])[-1]}
    try:
        j = json.loads(p.stdout)
    except ValueError:
        return {"error": "not SELECT or ASK"}
    return j if isinstance(j, dict) and "head" in j else {"error": "not SELECT or ASK"}


def lean_store(nq, qfile, named, work):
    store = work / "store"
    shutil.rmtree(store, ignore_errors=True)
    layout = "ibk4" if named else "ibk3"
    p = run([str(BIN / "l4block-shard-pack"), str(nq), str(store / "gen"), layout])
    if p.returncode != 0:
        return {"error": "pack: " + (p.stderr.strip().splitlines() or ["?"])[-1]}
    p = run([str(BIN / "l4block-shard-activate"), str(store), "gen"])
    if p.returncode != 0:
        return {"error": "activate: " + (p.stderr.strip().splitlines() or ["?"])[-1]}
    tool = "l4block-quad-query" if named else "l4block-id-v3-query"
    p = run([str(BIN / tool), str(store), "--json", "--query", Path(qfile).read_text()])
    shutil.rmtree(store, ignore_errors=True)
    j = last_json(p.stdout)
    if p.returncode != 0 or j is None:
        return {"error": (p.stderr.strip().splitlines() or ["exit %d" % p.returncode])[-1]}
    return json.loads(j)


# ---------------------------------------------------------------------------
# result equivalence
# ---------------------------------------------------------------------------
def term_key(t):
    ty = t.get("type")
    if ty == "uri":
        return ("u", t["value"])
    if ty == "bnode":
        return ("b", t["value"])
    if ty in ("literal", "typed-literal"):
        lang = t.get("xml:lang") or t.get("lang")
        if lang:
            return ("l", t["value"], "@" + lang.lower())
        dt = t.get("datatype") or XSD_STRING
        return ("l", t["value"], dt)
    if ty == "triple":
        v = t["value"]
        return ("t", term_key(v["subject"]), term_key(v["predicate"]), term_key(v["object"]))
    return ("?", json.dumps(t, sort_keys=True))


def rows_of(j):
    rows = []
    for b in j["results"]["bindings"]:
        rows.append(tuple(sorted((k, term_key(v)) for k, v in b.items())))
    return rows


def blank_free(row):
    return all(v[0] != "b" for _, v in row)


def shape(row):
    return tuple((k, ("b",) if v[0] == "b" else v) for k, v in row)


def bag_iso(a, b):
    """Multiset equality of solution sequences up to a bijection of blank
    node labels. Backtracking over rows that carry blank nodes; the rows
    without blank nodes must match exactly."""
    if len(a) != len(b):
        return False
    if Counter(map(shape, a)) != Counter(map(shape, b)):
        return False
    fa = [r for r in a if not blank_free(r)]
    fb = [r for r in b if not blank_free(r)]
    if Counter(r for r in a if blank_free(r)) != Counter(r for r in b if blank_free(r)):
        return False
    budget = [200000]

    def match(i, used, fwd, back):
        if i == len(fa):
            return True
        budget[0] -= 1
        if budget[0] < 0:
            return False
        ra = fa[i]
        for j, rb in enumerate(fb):
            if j in used or shape(rb) != shape(ra):
                continue
            f2, b2, ok = dict(fwd), dict(back), True
            for (ka, va), (kb, vb) in zip(ra, rb):
                if va[0] == "b":
                    x, y = va[1], vb[1]
                    if f2.setdefault(x, y) != y or b2.setdefault(y, x) != x:
                        ok = False
                        break
            if ok and match(i + 1, used | {j}, f2, b2):
                return True
        return False

    return match(0, frozenset(), {}, {})


NUMERIC = {"http://www.w3.org/2001/XMLSchema#" + d for d in (
    "double", "float", "decimal", "integer", "int", "long", "short", "byte",
    "nonNegativeInteger", "positiveInteger", "nonPositiveInteger", "negativeInteger",
    "unsignedLong", "unsignedInt", "unsignedShort", "unsignedByte")}


def by_value(row):
    """The row with each numeric literal replaced by its value (a float of the
    lexical form, keyed by the datatype's primitive family). Used only to
    classify a term-level disagreement as a lexical-form difference."""
    out = []
    for k, v in row:
        if v[0] == "l" and v[2] in NUMERIC:
            fam = "dbl" if v[2].endswith(("double", "float")) else "dec"
            try:
                out.append((k, ("n", fam, float(v[1]))))
                continue
            except ValueError:
                pass
        out.append((k, v))
    return tuple(out)


def compare(x, y, ordered):
    """('agree'|'disagree'|'error', note)"""
    if "error" in x or "error" in y:
        return "error", ""
    if "boolean" in x or "boolean" in y:
        return ("agree", "") if x.get("boolean") == y.get("boolean") else ("disagree", "boolean")
    ra, rb = rows_of(x), rows_of(y)
    if not bag_iso(ra, rb):
        if bag_iso([by_value(r) for r in ra], [by_value(r) for r in rb]):
            return "lexical", "numeric lexical forms differ, values equal"
        ca, cb = Counter(map(shape, ra)), Counter(map(shape, rb))
        only_a = list((ca - cb).elements())[:2]
        only_b = list((cb - ca).elements())[:2]
        return "disagree", f"rows {len(ra)} vs {len(rb)}; first only-left {only_a}; first only-right {only_b}"
    if ordered and [shape(r) for r in ra] != [shape(r) for r in rb]:
        return "agree", "order"
    return "agree", ""


# ---------------------------------------------------------------------------
def main():
    only = sys.argv[1:]  # optional substrings of test IRIs
    work = Path(os.environ.get("BACKEND_DIFF_WORK") or tempfile.mkdtemp(prefix="backend-diff-"))
    work.mkdir(parents=True, exist_ok=True)
    jc = work / "jc"
    jc.mkdir(exist_ok=True)
    have_jena = JENA_LIB.is_dir()
    if have_jena:
        p = run(["javac", "-proc:none", "-cp", f"{JENA_LIB}/*", "-d", str(jc), str(JAVA_SRC)], timeout=300)
        if p.returncode != 0:
            sys.exit("javac failed: " + p.stderr)
    else:
        print(f"backend_diff: no Jena at {JENA_LIB}; run tools/sota-bench.py --install with SOTA_DL set",
              file=sys.stderr)
        sys.exit(2)

    cases = []
    for manifest in sorted(SUITE.glob("*/manifest.ttl")):
        for t, e in sorted(tests_of(manifest).items()):
            if only and not any(o in t for o in only):
                continue
            cases.append((t, e))
    print(f"backend_diff: {len(cases)} QueryEvaluationTests in {SUITE}", flush=True)
    if not cases:
        sys.exit(f"backend_diff: no QueryEvaluationTest found under {SUITE} (fixtures missing?)")

    results = {}
    jena_lines = []
    for n, (t, e) in enumerate(cases):
        cdir = work / f"c{n:04d}"
        cdir.mkdir(exist_ok=True)
        qfile = e["query"][len("file://"):]
        parts = []
        if e["data"]:
            parts.append(nquads_of(e["data"][len("file://"):]))
        for g in sorted(e["graphs"]):
            parts.append(nquads_of(g[len("file://"):], g))
        if any(x is None for x in parts):
            results[t] = {"skip": "data not convertible"}
            continue
        nq = cdir / "data.nq"
        nq.write_text("".join(parts))
        ref = lean_ref(nq, qfile)
        if ref.get("error") == "not SELECT or ASK":
            results[t] = {"skip": "CONSTRUCT or DESCRIBE"}
            continue
        results[t] = {"lean-ref": ref,
                      "lean-store": lean_store(nq, qfile, bool(e["graphs"]), cdir),
                      "ordered": bool(re.search(r"ORDER\s+BY", Path(qfile).read_text(), re.I)),
                      "dir": cdir}
        jena_lines.append(f"{t}\t{nq}\t{qfile}\t{cdir}\n")

    p = subprocess.run(["java", "-cp", f"{jc}:{JENA_LIB}/*", "JenaRunner"], input="".join(jena_lines),
                       capture_output=True, text=True, timeout=3600)
    for t, r in results.items():
        if "skip" in r:
            continue
        for b in ("jena-tdb2", "jena-mem"):
            f = r["dir"] / f"{b}.json"
            try:
                r[b] = json.loads(f.read_text())
            except (OSError, ValueError):
                r[b] = {"error": "no output"}

    expected = {}
    if EXPECTED.exists():
        for line in EXPECTED.read_text().splitlines():
            if line.strip() and not line.startswith("#"):
                pair, tid, why = line.split("\t", 2)
                expected[(pair, tid)] = why

    compared = [t for t, r in results.items() if "skip" not in r]
    skipped = Counter(r["skip"] for r in results.values() if "skip" in r)
    print(f"backend_diff: {len(compared)} SELECT/ASK tests compared; skipped: {dict(skipped)}")
    errors_by_backend = Counter()
    for t in compared:
        for b in BACKENDS:
            if "error" in results[t][b]:
                errors_by_backend[b] += 1
    print("refused or failed per backend (not compared in its pairs): " +
          ", ".join(f"{b} {errors_by_backend[b]}" for b in BACKENDS))
    unexpected, stale = [], []
    print("\n| pair | agree | disagree | not comparable | of the agreements: numeric lexical form differs | order differs (ties allowed) |")
    print("|---|---|---|---|---|---|")
    detail = []
    for a, b in PAIRS:
        c = Counter()
        orders = 0
        for t in compared:
            verdict, note = compare(results[t][a], results[t][b], results[t]["ordered"])
            c[verdict] += 1
            if note == "order":
                orders += 1
            key = (f"{a}/{b}", t)
            if verdict == "disagree":
                detail.append(f"DISAGREE {a}/{b} {t} {note}")
                if key not in expected:
                    unexpected.append(key)
            elif key in expected:
                stale.append(key)
        print(f"| {a} vs {b} | {c['agree'] + c['lexical']} | {c['disagree']} | {c['error']} | {c['lexical']} | {orders} |")
    print()
    for line in detail:
        tag = "expected" if tuple(line.split(" ")[1:3]) in expected else "UNEXPECTED"
        print(f"{line}  [{tag}]")
    for a, b in PAIRS:
        for t in compared:
            for side in (a, b):
                err = results[t][side].get("error")
                if err and (a, b) == ("lean-ref", "lean-store"):
                    print(f"REFUSED {side} {t}: {err[:160]}")
    for key in stale:
        print(f"STALE expected disagreement now agrees or is not comparable: {key[0]} {key[1]}")
    if not os.environ.get("BACKEND_DIFF_WORK"):
        shutil.rmtree(work, ignore_errors=True)
    if unexpected or stale:
        print(f"backend_diff: FAIL ({len(unexpected)} unexpected, {len(stale)} stale)")
        return 1
    print("backend_diff: OK (every disagreement is listed with its issue)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
