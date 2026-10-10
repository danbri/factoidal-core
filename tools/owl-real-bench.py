#!/usr/bin/env python3
"""tools/owl-real-bench.py — OWL reasoning on real ontologies: time and memory.

https://github.com/danbri/factoidal/issues/651 (plan item 4: "Measure DL
consistency and entailment on a set of real ontologies; record time and
memory; open issues for what does not scale"). Record of the first run:
docs/designissues/2026-10-10-owl-real-ontologies.md.

For each ontology of ONTOLOGIES (files under third_party/), this script runs
the Lean command line (`l4factoidal`, formal/lean4) and, where the F* command
line has the same verb, the F* command line (`bin/<platform>/factoidal`):

  parse       each source file in its own syntax          Lean, F*
  species     OWL 2 DL or Full (l4owl-species)            Lean
  closure     the OWL 2 RL closure                        Lean, F*
  consistent  three-valued OWL DL consistency             Lean
  entails     owl-entails "A rdfs:subClassOf B" for up    Lean
              to 20 STATED pairs (the triple is in the
              ontology; the expected verdict is true) and
              up to 20 UNRELATED pairs of named classes
              (no triple links A and C; no expectation)

The F* command line has no consistency or entailment verb (the F*
owl_runner decides them only for W3C catalog cases), so those rows have no
F* column.

Every step runs as

  /usr/bin/time -v -o T timeout -s KILL CAP prlimit --as=AS -- CMD

so each row carries wall time, user and system CPU time, the peak resident
set size (ru_maxrss of the process tree) and the 1-minute load average at
its start. A step killed by the wall-clock cap is recorded as TIMEOUT; a step
that fails to allocate under the address-space cap is recorded as OOM. Neither
is ever recorded as a verdict. The resident set of the process tree is also
sampled every 0.2 s; a killed step reports that sample, because time -v then
measures only the `timeout` process.

`--rss-cap-mb MB` replaces prlimit with a watchdog that kills a step whose
resident set passes MB (status RSS_CAP). An address-space cap is not a memory
cap for a Lean executable: the Lean runtime reserves two 1 GiB thread stacks
and its heap in 1 GiB regions, so under --as=6000000000 the OWL RL closure of
QUDT failed to allocate with 1.25 GB resident (record, section 5). After the first TIMEOUT or OOM among the
entailment checks of one ontology, the remaining checks of that ontology are
recorded as NOT_RUN (each check recomputes the closure, so each would hit the
same cap).

The closure, consistency and entailment steps read one N-Triples file per
ontology, written by the Lean parser from the source files (the RDF merge of
the documents, RDF 1.1 Semantics §4.1: blank nodes of the second and later
documents get a per-document prefix; duplicate lines removed). Both engines
read that same file, so the closure rows compare the closures and not the
RDF/XML or Turtle parsers.

The address-space cap applies to native binaries only. A wasm module in Node
cannot run under it (Node reserves more address space than the cap).

Output: one JSON object per line (ontology, step, engine, ...) in
OUT/results.jsonl and a Markdown table in OUT/table.md.

Usage:
  python3 tools/owl-real-bench.py [--out DIR] [--only a,b] [--cap-s 600]
      [--fstar-cap-s S] [--as-bytes 6000000000 | --rss-cap-mb MB] [--pairs 20] [--fuel N] [--optional]
      [--no-fstar] [--lean-bin DIR] [--fstar-bin FILE] [--table-only]

Exit 0 when every step ran (a TIMEOUT or OOM is a result, not an error);
1 when a binary or a source file is missing; 2 on a usage error.
"""

import argparse
import hashlib
import json
import os
import random
import re
import shutil
import subprocess
import sys
import time
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

RDF_TYPE = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
RDFS_SUBCLASSOF = "http://www.w3.org/2000/01/rdf-schema#subClassOf"
OWL_CLASS = "http://www.w3.org/2002/07/owl#Class"
RDFS_CLASS = "http://www.w3.org/2000/01/rdf-schema#Class"
OWL_THING = "http://www.w3.org/2002/07/owl#Thing"
OWL_NOTHING = "http://www.w3.org/2002/07/owl#Nothing"

# name, source files (repository paths; the first is the ontology document,
# the rest are the documents it imports), syntax, licence (see each
# PROVENANCE.md). An entry with "url" is fetched at run time (not vendored;
# over 25 MB) and verified against "sha256"; it runs only with --optional.
ONTOLOGIES = [
    {"name": "skos", "files": ["third_party/vocabularies/skos.rdf"],
     "format": "rdfxml", "licence": "W3C"},
    {"name": "foaf", "files": ["third_party/vocabularies/foaf.rdf"],
     "format": "rdfxml", "licence": "CC BY 1.0"},
    {"name": "prov-o", "files": ["third_party/ontologies/prov-o/prov-o.ttl"],
     "format": "turtle", "licence": "W3C"},
    {"name": "bfo", "files": ["third_party/ontologies/bfo/bfo-core.owl"],
     "format": "rdfxml", "licence": "CC BY 4.0"},
    {"name": "pizza", "files": ["third_party/ontologies/pizza/pizza.owl"],
     "format": "rdfxml", "licence": "CC BY 3.0"},
    {"name": "wine", "files": ["third_party/ontologies/wine/wine.rdf",
                               "third_party/ontologies/wine/food.rdf"],
     "format": "rdfxml", "licence": "W3C"},
    {"name": "ro", "files": ["third_party/ontologies/ro/ro.owl"],
     "format": "rdfxml", "licence": "CC0 1.0"},
    {"name": "schema.org",
     "files": ["third_party/vocabularies/schemaorg-30.0-current-https.ttl"],
     "format": "turtle", "licence": "CC BY-SA 3.0"},
    {"name": "cl-basic", "files": ["third_party/ontologies/cl-basic/cl-basic.owl"],
     "format": "rdfxml", "licence": "CC BY 4.0"},
    {"name": "qudt", "files": ["third_party/qudt/QUDT-all-in-one-OWL.ttl"],
     "format": "turtle", "licence": "CC BY 4.0"},
    {"name": "go-basic", "optional": True, "format": "rdfxml", "licence": "CC BY 4.0",
     "url": "http://purl.obolibrary.org/obo/go/releases/2026-08-05/go-basic.owl",
     "sha256": "13a907d2a6586d0f7a4ba7cb556b7fe31240039268b85b01857e3f2da53e50d9",
     "files": []},
]

LINE_RE = re.compile(r'^(<[^>]*>|_:\S+) <([^>]*)> (.*) \.\s*$')


def log(msg):
    print(f"owl-real-bench: {msg}", file=sys.stderr, flush=True)


def loadavg():
    try:
        return round(os.getloadavg()[0], 2)
    except OSError:
        return None


PAGE = os.sysconf("SC_PAGE_SIZE")


def tree_rss(root):
    """(resident bytes, pids) of process ROOT and all its descendants, read
    from /proc. By parent links, not by process group: `timeout` puts its
    child in a process group of its own."""
    kids = {}
    rss = {}
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open(f"/proc/{d}/stat") as f:
                st = f.read()
            ppid = int(st[st.rindex(")") + 2:].split()[1])
            with open(f"/proc/{d}/statm") as f:
                rss[int(d)] = int(f.read().split()[1]) * PAGE
            kids.setdefault(ppid, []).append(int(d))
        except (OSError, ValueError, IndexError):
            continue
    todo, seen = [root], []
    while todo:
        x = todo.pop()
        seen.append(x)
        todo.extend(kids.get(x, []))
    return sum(rss.get(x, 0) for x in seen), seen


def run_step(cmd, cap_s, as_bytes, stdout_path, workdir, rss_cap_bytes=0):
    """Run CMD under time -v and timeout, and either prlimit --as=AS_BYTES
    (rss_cap_bytes == 0) or a watchdog that kills the process group when its
    resident set passes RSS_CAP_BYTES (polled every 0.2 s). Returns a dict."""
    tfile = os.path.join(workdir, "time.txt")
    efile = os.path.join(workdir, "stderr.txt")
    full = ["/usr/bin/time", "-v", "-o", tfile,
            "timeout", "-s", "KILL", str(cap_s)]
    if not rss_cap_bytes:
        full += ["prlimit", f"--as={as_bytes}", "--"]
    full += cmd
    la = loadavg()
    t0 = time.monotonic()
    rss_killed = False
    sampled = 0
    with open(stdout_path, "wb") as out, open(efile, "wb") as err:
        p = subprocess.Popen(full, stdout=out, stderr=err)
        while p.poll() is None:
            g, pids = tree_rss(p.pid)
            sampled = max(sampled, g)
            if rss_cap_bytes and g > rss_cap_bytes:
                rss_killed = True
                # Kill the tree below /usr/bin/time, so that time -v still
                # reports the CPU time of the killed command.
                for x in reversed(pids[1:]):
                    try:
                        os.kill(x, 9)
                    except OSError:
                        pass
                break
            time.sleep(0.2)
        rc = p.wait()
    wall = time.monotonic() - t0
    tv = {}
    try:
        with open(tfile) as f:
            for line in f:
                k, _, v = line.strip().rpartition(": ")
                tv[k.strip()] = v.strip()
    except OSError:
        pass
    with open(efile, "rb") as f:
        stderr = f.read().decode("utf-8", "replace")
    rss_kb = int(tv.get("Maximum resident set size (kbytes)", "0") or 0)
    user = float(tv.get("User time (seconds)", "0") or 0)
    syst = float(tv.get("System time (seconds)", "0") or 0)
    low = stderr.lower()
    if rss_killed:
        status = "RSS_CAP"
    elif rc == 137 and wall >= cap_s - 1:
        status = "TIMEOUT"
    elif ("out of memory" in low or "out_of_memory" in low
          or "cannot allocate" in low or "std::bad_alloc" in low):
        status = "OOM"
    elif rc in (0, 1):
        status = "ok"
    else:
        status = f"ERROR(rc={rc})"
    # ru_maxrss is lost when timeout or the watchdog kills the process tree
    # (time -v then reports the timeout process itself), so a killed step
    # reports the largest resident set sampled every 0.2 s instead.
    killed = status in ("TIMEOUT", "RSS_CAP")
    peak = (sampled if killed else rss_kb * 1024) / (1024 * 1024)
    return {"status": status, "rc": rc, "wall_s": round(wall, 3),
            "user_s": user, "sys_s": syst, "peak_rss_mb": round(peak, 1),
            "peak_rss_source": "sampled every 0.2 s" if killed else "ru_maxrss",
            "rss_sampled_mb": round(sampled / (1024 * 1024), 1),
            "load1": la, "stderr_tail": stderr.strip()[-400:],
            "cmd": " ".join(cmd)}


def count_lines(path):
    n = 0
    with open(path, "rb") as f:
        for line in f:
            if line.strip():
                n += 1
    return n


def first_line(path):
    with open(path, "rb") as f:
        for line in f:
            s = line.decode("utf-8", "replace").strip()
            if s:
                return s
    return ""


def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def prefix_bnodes(line, pre):
    m = LINE_RE.match(line)
    if not m:
        return line
    s, p, o = m.group(1), m.group(2), m.group(3)
    if s.startswith("_:"):
        s = "_:" + pre + s[2:]
    if o.startswith("_:"):
        o = "_:" + pre + o[2:]
    return f"{s} <{p}> {o} ."


def prepare_merged(lean, files, fmt, wd):
    """Write WD/doc<i>.nt (the Lean parser's N-Triples of each source file)
    and WD/merged.nt (their RDF merge: blank nodes of document i > 0 get the
    prefix d<i>_; duplicate lines removed). Returns (merged, docs, triples),
    or None when a file does not parse."""
    docs = []
    for i, f in enumerate(files):
        nt = os.path.join(wd, f"doc{i}.nt")
        # Not a measured step; capped so that a file too large for the
        # machine fails instead of exhausting it. MIMALLOC_ARENA_RESERVE keeps
        # the address-space cap from failing a parse that fits in memory
        # (https://github.com/danbri/factoidal/issues/759).
        env = dict(os.environ, MIMALLOC_ARENA_RESERVE="64MiB")
        with open(nt, "wb") as out:
            rc = subprocess.call(["timeout", "-s", "KILL", "1800", "prlimit",
                                  "--as=8000000000", "--", lean, "parse", f, "--format", fmt,
                                  "--out", "nquads"], stdout=out, env=env)
        if rc != 0:
            return None
        docs.append(nt)
    merged = os.path.join(wd, "merged.nt")
    seen = set()
    with open(merged, "w", encoding="utf-8") as out:
        for i, nt in enumerate(docs):
            with open(nt, encoding="utf-8", errors="replace") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    if i > 0:
                        line = prefix_bnodes(line, f"d{i}_")
                    if line not in seen:
                        seen.add(line)
                        out.write(line + "\n")
    return merged, docs, len(seen)


def parse_triples(path):
    out = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            m = LINE_RE.match(line)
            if m:
                out.append((m.group(1), m.group(2), m.group(3)))
    return out


def iri(term):
    return term[1:-1] if term.startswith("<") and term.endswith(">") else None


def choose_pairs(triples, n, seed):
    """Up to n stated (A, B) and n unrelated (A, C) pairs of named classes."""
    classes = set()
    linked = set()
    stated = set()
    for s, p, o in triples:
        si, oi = iri(s), iri(o)
        if p == RDF_TYPE and si and oi in (OWL_CLASS, RDFS_CLASS):
            classes.add(si)
        if si and oi:
            linked.add((si, oi))
            linked.add((oi, si))
            if p == RDFS_SUBCLASSOF and si != oi:
                stated.add((si, oi))
    classes -= {OWL_THING, OWL_NOTHING}
    stated = sorted((a, b) for (a, b) in stated
                    if a in classes and b not in (OWL_THING, OWL_NOTHING))
    rng = random.Random(seed)
    stated_pick = rng.sample(stated, min(n, len(stated)))
    cl = sorted(classes)
    unrelated = []
    seen = set()
    tries = 0
    while len(unrelated) < n and len(cl) >= 2 and tries < 20000:
        tries += 1
        a, c = rng.sample(cl, 2)
        if (a, c) in linked or (a, c) in seen:
            continue
        seen.add((a, c))
        unrelated.append((a, c))
    return {"classes": len(classes), "stated_total": len(stated),
            "stated": stated_pick, "unrelated": unrelated}


def emit(rows, results_path, row):
    rows.append(row)
    with open(results_path, "a") as f:
        f.write(json.dumps(row, sort_keys=True) + "\n")
    st = row.get("status")
    log(f"{row['ontology']:<11} {row['step']:<10} {row['engine']:<5} {st:<8} "
        f"wall={row.get('wall_s')}s rss={row.get('peak_rss_mb')}MB "
        f"{row.get('summary', '')}")


def fetch_optional(onto, cache_dir):
    os.makedirs(cache_dir, exist_ok=True)
    dest = os.path.join(cache_dir, os.path.basename(onto["url"]))
    if not os.path.exists(dest):
        log(f"fetching {onto['url']}")
        with urllib.request.urlopen(onto["url"], timeout=600) as r, open(dest + ".part", "wb") as f:
            shutil.copyfileobj(r, f)
        os.replace(dest + ".part", dest)
    got = sha256_of(dest)
    if onto["sha256"] != got:
        raise RuntimeError(f"{dest}: sha256 {got}, expected {onto['sha256']}")
    return [dest]


def bench_ontology(onto, a, rows, results_path):
    name = onto["name"]
    wd = os.path.join(a.out, name)
    os.makedirs(wd, exist_ok=True)
    lean = os.path.join(a.lean_bin, "l4factoidal")
    species = os.path.join(a.lean_bin, "l4owl-species")
    fstar = a.fstar_bin
    fmt = onto["format"]
    if onto.get("url"):
        files = fetch_optional(onto, os.path.join(a.out, "_fetched"))
    else:
        files = [os.path.join(REPO, p) for p in onto["files"]]
    base = {"ontology": name, "licence": onto["licence"],
            "files": [os.path.relpath(f, REPO) if f.startswith(REPO) else f for f in files],
            "source_bytes": sum(os.path.getsize(f) for f in files)}

    def row(step, engine, r, **kw):
        d = dict(base)
        d.update({"step": step, "engine": engine})
        d.update(r)
        d.update(kw)
        return d

    # --- parse, each engine, each file -------------------------------------
    for engine in (["lean"] + ([] if a.no_fstar else ["fstar"])):
        parts = []
        for f in files:
            out = os.path.join(wd, "parse.out")
            if engine == "lean":
                cmd = [lean, "parse", f, "--format", fmt]
            else:
                cmd = [fstar, "count", f]
            r = run_step(cmd, a.cap_s if engine == "lean" else a.fstar_cap_s, a.as_bytes, out, wd, a.rss_cap)
            txt = first_line(out)
            m = re.search(r"(\d+)", txt.split(":")[-1]) if txt else None
            r["triples"] = int(m.group(1)) if (m and r["status"] == "ok") else None
            parts.append(r)
        r = {"status": "ok" if all(p["status"] == "ok" for p in parts)
             else next(p["status"] for p in parts if p["status"] != "ok"),
             "wall_s": round(sum(p["wall_s"] for p in parts), 3),
             "user_s": round(sum(p["user_s"] for p in parts), 3),
             "sys_s": round(sum(p["sys_s"] for p in parts), 3),
             "peak_rss_mb": max(p["peak_rss_mb"] for p in parts),
             "load1": parts[0]["load1"],
             "cmd": " ; ".join(p["cmd"] for p in parts),
             "triples_per_file": [p["triples"] for p in parts]}
        tr = r["triples_per_file"]
        r["triples"] = sum(tr) if all(t is not None for t in tr) else None
        note = ("Lean: size of the parsed graph (a set)" if engine == "lean"
                else "F*: `factoidal count` counts statements as read; a repeated triple counts again")
        emit(rows, results_path, row("parse", engine, r, summary=f"triples={r['triples']}", note=note))

    # --- the merged N-Triples input (Lean parser) ---------------------------
    prep = prepare_merged(lean, files, fmt, wd)
    if prep is None:
        log(f"{name}: cannot convert the source files to N-Triples; skipping the ontology")
        return
    merged, docs, input_triples = prep
    base["input_triples"] = input_triples
    base["input_sha256"] = sha256_of(merged)

    # --- species (Lean) ------------------------------------------------------
    out = os.path.join(wd, "species.out")
    r = run_step([species] + docs, a.cap_s, a.as_bytes, out, wd, a.rss_cap)
    try:
        sp = json.loads(first_line(out))
        r.update({"species": sp["species"], "violations": int(sp["violations"]),
                  "violation_kinds": sp["kinds"], "violation_examples": sp["examples"][:5]})
        summ = f"species={sp['species']} violations={sp['violations']}"
    except (ValueError, KeyError):
        summ = "species=?"
    emit(rows, results_path, row("species", "lean", r, summary=summ))

    # --- closure --------------------------------------------------------------
    for engine in (["lean"] + ([] if a.no_fstar else ["fstar"])):
        out = os.path.join(wd, f"closure.{engine}.nq")
        if engine == "lean":
            cmd = [lean, "closure", merged, "--format", "nquads", "--regime", "owl-rl"]
        else:
            cmd = [fstar, "entail", "--data", merged, "--regime", "OWL-RL"]
        r = run_step(cmd, a.cap_s if engine == "lean" else a.fstar_cap_s, a.as_bytes, out, wd, a.rss_cap)
        if r["status"] == "ok" and r["rc"] == 0:
            n = count_lines(out)
            r["closure_triples"] = n
            r["triples_added"] = n - input_triples
            summ = f"closure={n} added={n - input_triples}"
        else:
            summ = ""
            if r["status"] == "ok":
                r["status"] = f"ERROR(rc={r['rc']})"
        os.remove(out)
        emit(rows, results_path, row("closure", engine, r, summary=summ))

    # --- consistency (Lean) ---------------------------------------------------
    out = os.path.join(wd, "consistent.out")
    cmd = [lean, "owl-consistent", merged, "--format", "nquads"]
    if a.fuel:
        cmd += ["--fuel", str(a.fuel)]
    r = run_step(cmd, a.cap_s, a.as_bytes, out, wd, a.rss_cap)
    verdict = first_line(out) if r["status"] == "ok" else None
    if r["status"] == "ok" and verdict not in ("true", "false", "unknown"):
        r["status"] = f"ERROR(rc={r['rc']})"
        verdict = None
    r["verdict"] = verdict
    emit(rows, results_path, row("consistent", "lean", r, summary=f"verdict={verdict}"))

    # --- entailment checks (Lean) ---------------------------------------------
    pairs = choose_pairs(parse_triples(merged), a.pairs, a.seed)
    base["named_classes"] = pairs["classes"]
    base["stated_subclass_pairs"] = pairs["stated_total"]
    stop = None
    for kind, plist in (("stated", pairs["stated"]), ("unrelated", pairs["unrelated"])):
        for (x, y) in plist:
            concl = os.path.join(wd, "conclusion.nt")
            with open(concl, "w", encoding="utf-8") as f:
                f.write(f"<{x}> <{RDFS_SUBCLASSOF}> <{y}> .\n")
            extra = {"pair_kind": kind, "sub": x, "super": y,
                     "expected": "true" if kind == "stated" else None}
            if stop:
                emit(rows, results_path, row("entails", "lean",
                     {"status": "NOT_RUN", "reason": stop}, **extra))
                continue
            out = os.path.join(wd, "entails.out")
            cmd = [lean, "owl-entails", merged, concl, "--format", "nquads"]
            if a.fuel:
                cmd += ["--fuel", str(a.fuel)]
            r = run_step(cmd, a.cap_s, a.as_bytes, out, wd, a.rss_cap)
            verdict = first_line(out) if r["status"] == "ok" else None
            if r["status"] == "ok" and verdict not in ("true", "false", "unknown"):
                r["status"] = f"ERROR(rc={r['rc']})"
                verdict = None
            r["verdict"] = verdict
            r["reason"] = r.pop("stderr_tail", "")[-200:] if verdict in ("false", "unknown") else ""
            emit(rows, results_path, row("entails", "lean", r, summary=f"{kind} verdict={verdict}", **extra))
            if r["status"] in ("TIMEOUT", "OOM", "RSS_CAP"):
                stop = (f"an earlier entailment check of this ontology ended {r['status']}; "
                        "each check recomputes the closure, so the rest were not run")


def fmt_cell(r, key=None):
    if r is None:
        return "—"
    if r["status"] != "ok":
        s = f"{r['status']} at {r.get('wall_s', 0):.0f} s"
        if r.get("peak_rss_source") == "sampled every 0.2 s":
            s += f", {r['peak_rss_mb']:.0f} MB sampled"
        elif r["status"] in ("TIMEOUT", "RSS_CAP"):
            s += ", memory not recorded"
        else:
            s += f", {r['peak_rss_mb']:.0f} MB"
        return s
    s = f"{r['wall_s']:.2f} s ({r.get('user_s', 0) + r.get('sys_s', 0):.2f} CPU), {r['peak_rss_mb']:.0f} MB"
    if key and r.get(key) is not None:
        s = f"{r[key]}; " + s
    return s


def write_table(rows, path):
    by = {}
    order = []
    for r in rows:
        if r["ontology"] == "_run":
            continue
        if r["ontology"] not in by:
            by[r["ontology"]] = []
            order.append(r["ontology"])
        by[r["ontology"]].append(r)

    def one(rs, step, engine):
        for r in rs:
            if r["step"] == step and r["engine"] == engine:
                return r
        return None

    lines = []
    lines.append("| Ontology | Input triples | Species (Lean) | Parse, Lean | Parse, F* | "
                 "OWL RL closure, Lean | OWL RL closure, F* | Consistent, Lean |")
    lines.append("|---|---:|---|---|---|---|---|---|")
    for o in order:
        rs = by[o]
        sp = one(rs, "species", "lean")
        spc = (f"{sp.get('species')} ({sp.get('violations')} violations)"
               if sp and sp["status"] == "ok" else fmt_cell(sp))
        inp = next((r.get("input_triples") for r in rs if r.get("input_triples")), "—")
        cl = one(rs, "closure", "lean")
        cf = one(rs, "closure", "fstar")
        lines.append(" | ".join([
            f"| {o}", str(inp), spc,
            fmt_cell(one(rs, "parse", "lean"), "triples"),
            fmt_cell(one(rs, "parse", "fstar"), "triples"),
            fmt_cell(cl, "triples_added").replace(";", " added;", 1) if cl and cl["status"] == "ok" else fmt_cell(cl),
            fmt_cell(cf, "triples_added").replace(";", " added;", 1) if cf and cf["status"] == "ok" else fmt_cell(cf),
            fmt_cell(one(rs, "consistent", "lean"), "verdict")]) + " |")
    lines.append("")
    lines.append("| Ontology | Named classes | Stated pairs: true / false / unknown / TIMEOUT / OOM / not run (out of N) | "
                 "Unrelated pairs: true / false / unknown / TIMEOUT / OOM / not run (out of N) | "
                 "Entailment check time, median and max | Peak RSS, max |")
    lines.append("|---|---:|---|---|---|---|")
    for o in order:
        if o == "(empty graph)":
            continue
        rs = [r for r in by[o] if r["step"] == "entails"]
        nc = next((r.get("named_classes") for r in by[o] if r.get("named_classes") is not None), "—")

        def tally(kind):
            ks = [r for r in rs if r.get("pair_kind") == kind]
            c = {k: 0 for k in ("true", "false", "unknown", "TIMEOUT", "OOM", "NOT_RUN", "ERROR")}
            for r in ks:
                if r["status"] == "ok":
                    c[r["verdict"]] += 1
                elif r["status"] in c:
                    c[r["status"]] += 1
                elif r["status"] == "RSS_CAP":
                    c["OOM"] += 1
                else:
                    c["ERROR"] += 1
            s = (f"{c['true']} / {c['false']} / {c['unknown']} / {c['TIMEOUT']} / {c['OOM']} / "
                 f"{c['NOT_RUN']} (out of {len(ks)})")
            if c["ERROR"]:
                s += f", {c['ERROR']} error"
            return s
        ran = sorted(r["wall_s"] for r in rs if r["status"] in ("ok", "TIMEOUT", "OOM", "RSS_CAP"))
        med = f"{ran[len(ran) // 2]:.2f} s, {ran[-1]:.2f} s" if ran else "—"
        rss = max((r.get("peak_rss_mb", 0) for r in rs), default=0)
        lines.append(f"| {o} | {nc} | {tally('stated')} | {tally('unrelated')} | {med} | {rss:.0f} MB |")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    return "\n".join(lines)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default=os.path.join(os.environ.get("TMPDIR", "/tmp"), "owl-real-bench"))
    ap.add_argument("--only", default="")
    ap.add_argument("--cap-s", type=int, default=600)
    ap.add_argument("--fstar-cap-s", type=int, default=0, help="cap for the F* steps (0: --cap-s)")
    ap.add_argument("--as-bytes", type=int, default=6_000_000_000)
    ap.add_argument("--rss-cap-mb", type=int, default=0,
                    help="instead of prlimit --as, kill a step whose resident set passes this many MB "
                         "(status RSS_CAP); see the record, section 5, for why")
    ap.add_argument("--pairs", type=int, default=20)
    ap.add_argument("--seed", type=int, default=651)
    ap.add_argument("--fuel", type=int, default=0, help="--fuel for owl-consistent / owl-entails (0: the CLI default)")
    ap.add_argument("--optional", action="store_true", help="also run the fetched-at-run-time ontologies")
    ap.add_argument("--no-fstar", action="store_true")
    ap.add_argument("--lean-bin", default=os.path.join(REPO, "formal/lean4/.lake/build/bin"))
    ap.add_argument("--fstar-bin", default=os.path.join(REPO, "bin/linux-x86_64/factoidal"))
    ap.add_argument("--table-only", action="store_true", help="rebuild OUT/table.md from OUT/results.jsonl")
    a = ap.parse_args()
    a.out = os.path.abspath(a.out)
    a.fstar_cap_s = a.fstar_cap_s or a.cap_s
    a.rss_cap = a.rss_cap_mb * 1024 * 1024
    os.makedirs(a.out, exist_ok=True)
    results = os.path.join(a.out, "results.jsonl")
    if a.table_only:
        rows = [json.loads(l) for l in open(results) if l.strip()]
        print(write_table(rows, os.path.join(a.out, "table.md")))
        return 0
    for b in [os.path.join(a.lean_bin, "l4factoidal"), os.path.join(a.lean_bin, "l4owl-species")] + \
             ([] if a.no_fstar else [a.fstar_bin]):
        if not os.access(b, os.X_OK):
            log(f"missing binary {b} (Lean: lake build l4factoidal l4owl-species in formal/lean4; "
                "F*: tools/fetch-builds.sh --set native)")
            return 1
    only = [s for s in a.only.split(",") if s]
    todo = [o for o in ONTOLOGIES
            if (not only or o["name"] in only) and (a.optional or not o.get("optional"))]
    for o in todo:
        for p in o["files"]:
            if not os.path.exists(os.path.join(REPO, p)):
                log(f"missing source file {p}")
                return 1
    if os.path.exists(results):
        os.replace(results, results + ".previous")
    meta = {"ontology": "_run", "step": "meta", "engine": "-", "status": "ok",
            "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "uname": " ".join(os.uname()), "nproc": os.cpu_count(),
            "cap_s": a.cap_s, "fstar_cap_s": a.fstar_cap_s, "as_bytes": None if a.rss_cap else a.as_bytes,
            "rss_cap_mb": a.rss_cap_mb or None, "pairs": a.pairs, "seed": a.seed,
            "fuel": a.fuel or "CLI default",
            "lean_bin_sha256": sha256_of(os.path.join(a.lean_bin, "l4factoidal")),
            "fstar_bin_sha256": None if a.no_fstar else sha256_of(a.fstar_bin),
            "git_head": subprocess.run(["git", "-C", REPO, "rev-parse", "HEAD"],
                                       capture_output=True, text=True).stdout.strip()}
    with open(results, "a") as f:
        f.write(json.dumps(meta, sort_keys=True) + "\n")
    rows = []
    # The closure of the EMPTY graph: the axiomatic triples each engine adds to
    # every closure (skills/measuring-inference § 3).
    wd = os.path.join(a.out, "_empty")
    os.makedirs(wd, exist_ok=True)
    empty = os.path.join(wd, "empty.nt")
    open(empty, "w").close()
    for engine in (["lean"] + ([] if a.no_fstar else ["fstar"])):
        out = os.path.join(wd, "closure.nq")
        cmd = ([os.path.join(a.lean_bin, "l4factoidal"), "closure", empty, "--format", "nquads",
                "--regime", "owl-rl"] if engine == "lean"
               else [a.fstar_bin, "entail", "--data", empty, "--regime", "OWL-RL"])
        r = run_step(cmd, a.cap_s, a.as_bytes, out, wd, a.rss_cap)
        r["closure_triples"] = count_lines(out) if r["status"] == "ok" else None
        emit(rows, results, dict(r, ontology="(empty graph)", step="closure", engine=engine,
                                 input_triples=0, triples_added=r["closure_triples"],
                                 summary=f"closure={r['closure_triples']}"))
    for o in todo:
        bench_ontology(o, a, rows, results)
    print(write_table(rows, os.path.join(a.out, "table.md")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
