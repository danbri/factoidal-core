#!/usr/bin/env python3
"""Three-engine benchmark driver: SBM11 (l4sbm11) and Virtuoso 7.2.

https://github.com/danbri/factoidal/issues/798. Record:
docs/designissues/2026-10-12-three-engine-benchmark.md. Called by run.sh.

Subcommands (all write JSON; nothing is written inside the repository):

  virtuoso-load --nt FILE --graph IRI --dbdir DIR --out JSON
      New Virtuoso database in DIR, bulk load FILE into graph IRI
      (ld_dir + rdf_loader_run + checkpoint), record wall time, the server's
      peak RSS (VmHWM since start), the triple count, loader errors and the
      on-disk size after shutdown.

  answers --dataset NAME --queries DIR --gen GEN --dbdir DIR --graph IRI
          --outdir DIR [--oracle DIR] --out JSON
      Every query once on SBM11 --verify none, SBM11 --verify merkle and
      Virtuoso (default threads); answers saved under outdir; each pair
      compared as multisets of solutions (normalisation: see `term_key`).

  timing --dataset NAME --queries DIR --gen GEN --dbdir DIR --graph IRI
         --answers JSON --out JSON [--rounds 7] [--cold-rounds 3] [--repeat 5]
      Timing of the queries with no answer difference. See the record,
      section "Method".

Cold run: the OS page cache cannot be dropped in this container (writing
/proc/sys/vm/drop_caches is refused). A cold run is the first run in a new
process (for Virtuoso: a new server process) after the engine's own files
were evicted from the page cache with posix_fadvise(POSIX_FADV_DONTNEED);
`resident_bytes` (mincore) records how much of the files stayed resident.
"""
import argparse
import ctypes
import ctypes.util
import glob
import http.client
import json
import mmap
import os
import re
import shutil
import signal
import statistics
import subprocess
import sys
import time
import urllib.parse
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
SBM11 = os.environ.get("SBM11_BIN", os.path.join(ROOT, "formal/lean4/.lake/build/bin/l4sbm11"))
VIRTUOSO = os.environ.get("VIRTUOSO_BIN", "/usr/bin/virtuoso-t")
ISQL = os.environ.get("ISQL_BIN", "/usr/bin/isql-vt")
VPORT = int(os.environ.get("VIRTUOSO_SQL_PORT", "1112"))
VHTTP = int(os.environ.get("VIRTUOSO_HTTP_PORT", "8891"))
QUERY_TIMEOUT_S = int(os.environ.get("QUERY_TIMEOUT_S", "600"))
LOAD_TARGET = float(os.environ.get("LOAD_TARGET", "2.0"))
LOAD_WAIT_S = int(os.environ.get("LOAD_WAIT_S", "90"))
SLOW_MS = float(os.environ.get("SLOW_MS", "5000"))
SLOW_ROUNDS = int(os.environ.get("SLOW_ROUNDS", "3"))

# Virtuoso settings. "default" is the Debian package's virtuoso.ini for the
# query threads (ThreadsPerQuery 4, AsyncQueueMaxThreads 10); "1t" sets both
# to 1. Both: 340,000 buffers (about 2.8 GB, the Virtuoso guide's value for
# a 4 GB machine; the machine is shared), no result-row cap, no
# execution-time cap (a capped Virtuoso query returns partial results).
THREAD_CONFIGS = {
    "1t": {"ThreadsPerQuery": 1, "AsyncQueueMaxThreads": 1},
    "default": {"ThreadsPerQuery": 4, "AsyncQueueMaxThreads": 10},
}


def log(*a):
    print("[bench]", *a, file=sys.stderr, flush=True)


def loadavg():
    return round(os.getloadavg()[0], 2)


def wait_for_load():
    """Wait up to LOAD_WAIT_S for the 1-minute load average to fall under
    LOAD_TARGET; return the load average when the round starts."""
    t0 = time.time()
    while loadavg() >= LOAD_TARGET and time.time() - t0 < LOAD_WAIT_S:
        time.sleep(5)
    return loadavg()


def median(xs):
    xs = [x for x in xs if x is not None]
    return round(statistics.median(xs), 3) if xs else None


# ---------------------------------------------------------------- page cache

_libc = ctypes.CDLL(ctypes.util.find_library("c"), use_errno=True)
_libc.mmap.restype = ctypes.c_void_p
_libc.mmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_int, ctypes.c_int,
                       ctypes.c_int, ctypes.c_long]
_libc.munmap.argtypes = [ctypes.c_void_p, ctypes.c_size_t]
_libc.mincore.argtypes = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p]


def resident_bytes(paths):
    """Bytes of the files resident in the page cache (mincore)."""
    total = 0
    page = os.sysconf("SC_PAGE_SIZE")
    for p in paths:
        size = os.path.getsize(p)
        if size == 0:
            continue
        with open(p, "rb") as f:
            addr = _libc.mmap(None, ctypes.c_size_t(size), mmap.PROT_READ, mmap.MAP_SHARED,
                              f.fileno(), ctypes.c_long(0))
            if addr in (None, ctypes.c_void_p(-1).value):
                continue
            try:
                n = (size + page - 1) // page
                vec = (ctypes.c_ubyte * n)()
                if _libc.mincore(ctypes.c_void_p(addr), ctypes.c_size_t(size), vec) == 0:
                    total += sum(b & 1 for b in bytes(vec)) * page
            finally:
                _libc.munmap(ctypes.c_void_p(addr), ctypes.c_size_t(size))
    return min(total, sum(os.path.getsize(p) for p in paths))


def evict(paths):
    for p in paths:
        try:
            fd = os.open(p, os.O_RDONLY)
        except OSError:
            continue
        try:
            os.fsync(fd)
            os.posix_fadvise(fd, 0, 0, os.POSIX_FADV_DONTNEED)
        finally:
            os.close(fd)


def files_under(d):
    out = []
    for dp, _, fns in os.walk(d):
        for fn in fns:
            p = os.path.join(dp, fn)
            if os.path.isfile(p) and not os.path.islink(p):
                out.append(p)
    return out


def du_bytes(paths):
    return sum(os.path.getsize(p) for p in paths)


# ---------------------------------------------------------------- SBM11


def sbm11_run(gen, rq, verify, repeat=None, capture=False):
    """One `l4sbm11 query` process. Returns dict with wall_ms, maxrss_kb,
    exec_ms, warm_median_ms (with repeat), path, rows, rc, out (bytes)."""
    cmd = [SBM11, "query", gen, "--file", rq, "--verify", verify]
    if repeat:
        cmd += ["--repeat", str(repeat)]
    out_f = subprocess.PIPE if capture else subprocess.DEVNULL
    t0 = time.monotonic()
    p = subprocess.Popen(cmd, stdout=out_f, stderr=subprocess.PIPE)
    try:
        out, err = p.communicate(timeout=QUERY_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        p.kill()
        p.communicate()
        return {"rc": "timeout", "wall_ms": QUERY_TIMEOUT_S * 1000.0}
    wall = (time.monotonic() - t0) * 1000.0
    # ru_maxrss of the child: wait4 already reaped it through communicate,
    # so read VmHWM from the engine's own summary line.
    e = err.decode("utf-8", "replace")
    rec = {"rc": p.returncode, "wall_ms": round(wall, 3)}
    m = re.search(r"VmHWM\): (\d+) kB", e)
    rec["maxrss_kb"] = int(m.group(1)) if m else None
    m = re.search(r"execution ([0-9.]+) ms", e)
    rec["exec_ms"] = float(m.group(1)) if m else None
    m = re.search(r"execution ms median ([0-9.]+)", e)
    rec["warm_median_ms"] = float(m.group(1)) if m else None
    m = re.search(r"execution ms median [0-9.]+ min ([0-9.]+)", e)
    rec["warm_min_ms"] = float(m.group(1)) if m else None
    m = re.search(r"path=(\w+)", e)
    rec["path"] = m.group(1) if m else None
    m = re.search(r"rows (\d+)", e)
    rec["rows"] = int(m.group(1)) if m else None
    if p.returncode != 0:
        rec["stderr"] = e[-2000:]
    if capture:
        rec["out"] = out
    return rec


# ---------------------------------------------------------------- Virtuoso


def write_ini(dbdir, data_dirs, threads):
    ini = os.path.join(dbdir, "virtuoso-%s.ini" % threads)
    cfg = THREAD_CONFIGS[threads]
    allowed = ", ".join(["."] + sorted(set(data_dirs)) + ["/usr/share/virtuoso-opensource-7/vad"])
    text = f"""; generated by tools/bench/three-engines/bench.py, thread config {threads}
[Database]
DatabaseFile       = {dbdir}/virtuoso.db
ErrorLogFile       = {dbdir}/virtuoso.log
LockFile           = {dbdir}/virtuoso.lck
TransactionFile    = {dbdir}/virtuoso.trx
xa_persistent_file = {dbdir}/virtuoso.pxa
ErrorLogLevel      = 7
FileExtend         = 200
MaxCheckpointRemap = 2000
Striping           = 0
TempStorage        = TempDatabase
[TempDatabase]
DatabaseFile       = {dbdir}/virtuoso-temp.db
TransactionFile    = {dbdir}/virtuoso-temp.trx
MaxCheckpointRemap = 2000
Striping           = 0
[Parameters]
ServerPort               = {VPORT}
LiteMode                 = 0
DisableUnixSocket        = 1
DisableTcpSocket         = 0
MaxClientConnections     = 10
CheckpointInterval       = 60
O_DIRECT                 = 0
CaseMode                 = 2
MaxStaticCursorRows      = 5000
CheckpointAuditTrail     = 0
AllowOSCalls             = 0
SchedulerInterval        = 10
DirsAllowed              = {allowed}
ThreadCleanupInterval    = 0
ThreadThreshold          = 10
ResourcesCleanupInterval = 0
FreeTextBatchSize        = 100000
SingleCPU                = 0
VADInstallDir            = /usr/share/virtuoso-opensource-7/vad/
PrefixResultNames        = 0
RdfFreeTextRulesSize     = 100
IndexTreeMaps            = 64
MaxMemPoolSize           = 200000000
MaxQueryMem              = 2G
VectorSize               = 1000
MaxVectorSize            = 1000000
AdjustVectorSize         = 0
ThreadsPerQuery          = {cfg['ThreadsPerQuery']}
AsyncQueueMaxThreads     = {cfg['AsyncQueueMaxThreads']}
NumberOfBuffers          = 340000
MaxDirtyBuffers          = 250000
[HTTPServer]
ServerPort                  = {VHTTP}
ServerRoot                  = /var/lib/virtuoso-opensource-7/vsp
MaxClientConnections        = 10
DavRoot                     = DAV
EnabledDavVSP               = 0
HTTPProxyEnabled            = 0
TempASPXDir                 = 0
ServerThreads               = 10
MaxKeepAlives               = 10
KeepAliveTimeout            = 10
HTTPThreadSize              = 280000
HttpPrintWarningsInOutput   = 0
Charset                     = UTF-8
EnabledGzipContent          = 0
[Client]
SQL_PREFETCH_ROWS  = 100
SQL_PREFETCH_BYTES = 16000
SQL_QUERY_TIMEOUT  = 0
SQL_TXN_TIMEOUT    = 0
[SPARQL]
ResultSetMaxRows           = 100000000
MaxQueryCostEstimationTime = 0
MaxQueryExecutionTime      = 0
DefaultQuery               = select distinct ?Concept where {{[] a ?Concept}} LIMIT 100
DeferInferenceRulesInit    = 0
"""
    with open(ini, "w") as f:
        f.write(text)
    return ini


class Virtuoso:
    def __init__(self, dbdir, data_dirs, threads):
        self.dbdir = dbdir
        self.threads = threads
        self.ini = write_ini(dbdir, data_dirs, threads)
        self.proc = None

    def db_files(self):
        return [p for p in files_under(self.dbdir)
                if re.search(r"\.(db|trx)$", p)]

    def start(self):
        logf = open(os.path.join(self.dbdir, "server-%s.out" % self.threads), "ab")
        self.proc = subprocess.Popen(
            [VIRTUOSO, "+foreground", "+configfile", self.ini],
            cwd=self.dbdir, stdout=logf, stderr=subprocess.STDOUT,
            start_new_session=True)
        t0 = time.time()
        while time.time() - t0 < 300:
            if self.proc.poll() is not None:
                raise RuntimeError("virtuoso exited during start; see %s/virtuoso.log" % self.dbdir)
            try:
                st, _ = self.http("ASK { ?s ?p ?o }", graph=None, timeout=5)
                if st == 200:
                    return
            except OSError:
                pass
            time.sleep(0.5)
        raise RuntimeError("virtuoso did not answer HTTP within 300 s")

    def isql(self, sql, timeout=7200):
        r = subprocess.run([ISQL, str(VPORT), "dba", "dba", "exec=" + sql],
                           capture_output=True, text=True, timeout=timeout)
        if r.returncode != 0 or "*** Error" in r.stdout + r.stderr:
            raise RuntimeError("isql failed: %s\n%s%s" % (sql, r.stdout[-2000:], r.stderr[-2000:]))
        return r.stdout

    def stop(self):
        if self.proc is None:
            return
        try:
            self.isql("shutdown;", timeout=600)
        except Exception as e:  # noqa: BLE001
            log("isql shutdown failed (%s); SIGTERM" % e)
            os.killpg(self.proc.pid, signal.SIGTERM)
        try:
            self.proc.wait(timeout=600)
        except subprocess.TimeoutExpired:
            os.killpg(self.proc.pid, signal.SIGKILL)
            self.proc.wait()
        self.proc = None

    def status_kb(self, field):
        with open("/proc/%d/status" % self.proc.pid) as f:
            for line in f:
                if line.startswith(field + ":"):
                    return int(line.split()[1])
        return None

    def reset_hwm(self):
        with open("/proc/%d/clear_refs" % self.proc.pid, "w") as f:
            f.write("5")

    def http(self, query, graph, timeout=QUERY_TIMEOUT_S):
        params = {"query": query, "format": "application/sparql-results+json"}
        if graph:
            params["default-graph-uri"] = graph
        body = urllib.parse.urlencode(params)
        c = http.client.HTTPConnection("127.0.0.1", VHTTP, timeout=timeout)
        try:
            c.request("POST", "/sparql", body=body, headers={
                "Content-Type": "application/x-www-form-urlencoded",
                "Accept": "application/sparql-results+json"})
            r = c.getresponse()
            data = r.read()
            hdr = {k.lower(): v for k, v in r.getheaders()}
            return r.status, (data, hdr)
        finally:
            c.close()

    def query(self, query, graph):
        """One SPARQL request; wall ms on the client from send to the last
        byte of the response; server VmHWM during the request."""
        self.reset_hwm()
        t0 = time.monotonic()
        try:
            st, (data, hdr) = self.http(query, graph)
        except OSError as e:
            return {"rc": "error: %s" % e, "wall_ms": (time.monotonic() - t0) * 1000.0}
        wall = (time.monotonic() - t0) * 1000.0
        rec = {"rc": 0 if st == 200 else st, "wall_ms": round(wall, 3),
               "maxrss_kb": self.status_kb("VmHWM"), "out": data}
        # A Virtuoso "anytime" partial answer carries X-SQL-State; the
        # execution-time cap is off, so this must never appear.
        if "x-sql-state" in hdr:
            rec["rc"] = "partial: %s %s" % (hdr.get("x-sql-state"), hdr.get("x-sql-message"))
        return rec


def virtuoso_version():
    r = subprocess.run([VIRTUOSO, "-?"], capture_output=True, text=True)
    lines = [l.strip() for l in (r.stdout + r.stderr).splitlines() if l.startswith("Version")]
    return lines[0] if lines else None


def cmd_virtuoso_load(a):
    if os.path.exists(a.dbdir):
        shutil.rmtree(a.dbdir)
    os.makedirs(a.dbdir)
    nt = os.path.abspath(a.nt)
    v = Virtuoso(a.dbdir, [os.path.dirname(nt)], a.threads)
    la0 = loadavg()
    v.start()
    t0 = time.monotonic()
    v.isql("ld_dir('%s', '%s', '%s');" % (os.path.dirname(nt), os.path.basename(nt), a.graph))
    v.isql("rdf_loader_run();")
    v.isql("checkpoint;")
    wall = (time.monotonic() - t0) * 1000.0
    hwm = v.status_kb("VmHWM")
    errs = v.isql("SELECT ll_file, ll_error FROM DB.DBA.LOAD_LIST WHERE ll_error IS NOT NULL;")
    cnt = v.isql("SPARQL SELECT COUNT(*) FROM <%s> WHERE { ?s ?p ?o };" % a.graph)
    m = re.findall(r"^\s*(\d+)\s*$", cnt, re.M)
    v.stop()
    files = v.db_files()
    rec = {"engine": "virtuoso", "version": virtuoso_version(),
           "threads": a.threads, "nt": nt, "graph": a.graph,
           "load_ms": round(wall, 1), "peak_rss_kb": hwm,
           "triples": int(m[0]) if m else None,
           "loader_errors": "no rows" not in errs.lower() and "0 Rows" not in errs and errs.strip()[-400:],
           "files": {os.path.basename(p): os.path.getsize(p) for p in files},
           "disk_bytes": du_bytes(files), "loadavg_before": la0, "loadavg_after": loadavg()}
    json.dump(rec, open(a.out, "w"), indent=1)
    log(json.dumps(rec))


# ---------------------------------------------------------------- comparison

XSD = "http://www.w3.org/2001/XMLSchema#"
NUM_TYPES = {XSD + t for t in (
    "int", "integer", "nonPositiveInteger", "negativeInteger", "long", "short", "byte",
    "nonNegativeInteger", "unsignedLong", "unsignedInt", "unsignedShort", "unsignedByte",
    "positiveInteger", "decimal", "double", "float")}


def term_key(b):
    """Normalised RDF term of a SPARQL JSON binding.

    IRIs by value; blank nodes all equal (labels are not comparable between
    engines); a literal with a language tag by lexical form and lower-cased
    tag; a numeric literal (integer types, decimal, double, float) by value,
    printed with 12 significant digits (QLever and Virtuoso do not keep the
    input datatype or lexical form of numbers); xsd:string and simple
    literals by lexical form; any other literal by lexical form and
    datatype. Virtuoso's "typed-literal" is a literal."""
    t, v = b["type"], b["value"]
    if t == "uri":
        return ("iri", v)
    if t == "bnode":
        return ("bnode",)
    if "xml:lang" in b:
        return ("lang", v, b["xml:lang"].lower())
    dt = b.get("datatype", XSD + "string")
    if dt in NUM_TYPES:
        try:
            return ("num", "%.12g" % float(v))
        except ValueError:
            return ("typed", v, dt)
    if dt == XSD + "string":
        return ("str", v)
    return ("typed", v, dt)


def solutions(data):
    j = json.loads(data)
    rows = j["results"]["bindings"]
    return Counter(frozenset((k, term_key(b)) for k, b in r.items()) for r in rows), len(rows)


def compare(a, b):
    ca, na = a
    cb, nb = b
    if ca == cb:
        return {"equal": True, "rows": [na, nb]}
    only_a = list((ca - cb).elements())[:5]
    only_b = list((cb - ca).elements())[:5]
    return {"equal": False, "rows": [na, nb],
            "only_first": [sorted(map(list, s)) for s in only_a],
            "only_second": [sorted(map(list, s)) for s in only_b],
            "count_only_first": sum((ca - cb).values()),
            "count_only_second": sum((cb - ca).values())}


def query_files(d):
    return sorted(glob.glob(os.path.join(d, "*.rq")))


def cmd_answers(a):
    os.makedirs(a.outdir, exist_ok=True)
    v = Virtuoso(a.dbdir, [], "default")
    v.start()
    res = {"dataset": a.dataset, "queries": {}}
    try:
        for rq in query_files(a.queries):
            name = os.path.basename(rq)[:-3]
            q = open(rq).read()
            r = {"name": name}
            sols = {}
            for verify in ("none", "merkle"):
                s = sbm11_run(a.gen, rq, verify, capture=True)
                r["sbm11_" + verify] = {k: s.get(k) for k in ("rc", "path", "rows", "wall_ms")}
                if s["rc"] == 0:
                    open(os.path.join(a.outdir, "%s.sbm11-%s.json" % (name, verify)), "wb").write(s["out"])
                    sols["sbm11_" + verify] = s["out"]
                else:
                    r["sbm11_" + verify]["stderr"] = s.get("stderr")
            vr = v.query(q, a.graph)
            r["virtuoso"] = {k: vr.get(k) for k in ("rc", "wall_ms")}
            if vr["rc"] == 0:
                open(os.path.join(a.outdir, "%s.virtuoso.json" % name), "wb").write(vr["out"])
                sols["virtuoso"] = vr["out"]
            else:
                r["virtuoso"]["body"] = vr.get("out", b"")[:2000].decode("utf-8", "replace")
            if a.oracle:
                srj = os.path.join(a.oracle, name + ".srj")
                if os.path.exists(srj):
                    sols["qlever"] = open(srj, "rb").read()
            if "sbm11_none" in sols and "sbm11_merkle" in sols:
                r["sbm11_none_merkle_bytes_equal"] = sols["sbm11_none"] == sols["sbm11_merkle"]
            parsed = {}
            for k, data in sols.items():
                try:
                    parsed[k] = solutions(data)
                except (ValueError, KeyError) as e:
                    r.setdefault("parse_errors", {})[k] = str(e)
            r["rows"] = {k: p[1] for k, p in parsed.items()}
            comps = {}
            ks = [k for k in ("sbm11_none", "virtuoso", "qlever") if k in parsed]
            for i in range(len(ks)):
                for j in range(i + 1, len(ks)):
                    comps["%s~%s" % (ks[i], ks[j])] = compare(parsed[ks[i]], parsed[ks[j]])
            if "sbm11_merkle" in parsed and "sbm11_none" in parsed:
                comps["sbm11_none~sbm11_merkle"] = compare(parsed["sbm11_none"], parsed["sbm11_merkle"])
            r["comparisons"] = comps
            expected = {"sbm11_none", "sbm11_merkle", "virtuoso"}
            r["all_equal"] = expected <= set(parsed) and all(c["equal"] for c in comps.values())
            res["queries"][name] = r
            log("%s: %s rows=%s" % (name, "equal" if r["all_equal"] else "DIFFERENT", r["rows"]))
    finally:
        v.stop()
    res["equal"] = sorted(n for n, r in res["queries"].items() if r["all_equal"])
    res["different"] = sorted(n for n, r in res["queries"].items() if not r["all_equal"])
    json.dump(res, open(a.out, "w"), indent=1, default=str)


# ---------------------------------------------------------------- timing


def cmd_timing(a):
    ans = json.load(open(a.answers))
    names = [n for n in ans["equal"]]
    # A query whose SBM11 run in the answer check took more than SLOW_MS
    # (the reference fallback) gets SLOW_ROUNDS warm rounds on SBM11, and its
    # warm time is the faster of 2 runs in one process (--repeat 2).
    slow = {n for n, r in ans["queries"].items()
            if (r.get("sbm11_none", {}).get("wall_ms") or 0) > SLOW_MS}
    qs = [(os.path.basename(rq)[:-3], rq) for rq in query_files(a.queries)
          if os.path.basename(rq)[:-3] in names]
    gen_files = files_under(a.gen)
    out = {"dataset": a.dataset, "rounds": a.rounds, "cold_rounds": a.cold_rounds,
           "repeat": a.repeat, "load_target": LOAD_TARGET, "queries": [n for n, _ in qs],
           "excluded": ans["different"], "slow": sorted(slow), "slow_ms": SLOW_MS,
           "slow_rounds": SLOW_ROUNDS, "phases": []}

    def save():
        json.dump(out, open(a.out, "w"), indent=1, default=str)

    for threads in a.virtuoso_threads.split(","):
        phase = {"virtuoso_threads": threads, "rounds": [], "cold": []}
        out["phases"].append(phase)
        v = Virtuoso(a.dbdir, [], threads)
        sbm_modes = ["none", "merkle"] if threads == a.virtuoso_threads.split(",")[0] else ["none"]
        # Cold: SBM11 new process after eviction of the generation files;
        # Virtuoso new server process after eviction of its database files.
        for cr in range(a.cold_rounds):
            la = wait_for_load()
            crec = {"round": cr, "loadavg": la, "q": {}}
            for name, rq in qs:
                q = open(rq).read()
                e = {}
                for verify in sbm_modes:
                    evict(gen_files)
                    e["resident_before_sbm11"] = resident_bytes(gen_files)
                    s = sbm11_run(a.gen, rq, verify)
                    e["sbm11_" + verify] = {k: s.get(k) for k in ("rc", "wall_ms", "maxrss_kb", "exec_ms")}
                evict(v.db_files())
                e["resident_before_virtuoso"] = resident_bytes(v.db_files())
                v.start()
                vr = v.query(q, a.graph)
                vr.pop("out", None)
                e["virtuoso"] = vr
                v.stop()
                crec["q"][name] = e
            crec["loadavg_end"] = loadavg()
            phase["cold"].append(crec)
            save()
            log("cold round %d (%s) load %.2f" % (cr, threads, la))
        v.start()
        try:
            # warm-up: every query once on each engine
            for name, rq in qs:
                v.query(open(rq).read(), a.graph)
                sbm11_run(a.gen, rq, "none")
            for rnd in range(a.rounds):
                la = wait_for_load()
                rrec = {"round": rnd, "loadavg": la, "q": {}}
                for qi, (name, rq) in enumerate(qs):
                    q = open(rq).read()
                    e = {}
                    modes = sbm_modes if (name not in slow or rnd < SLOW_ROUNDS) else []
                    engines = [("sbm11", m) for m in modes] + [("virtuoso", threads)]
                    k = (rnd + qi) % len(engines)
                    for eng, mode in engines[k:] + engines[:k]:
                        if eng == "sbm11":
                            s = sbm11_run(a.gen, rq, mode)
                            w = sbm11_run(a.gen, rq, mode, repeat=2 if name in slow else a.repeat)
                            e["sbm11_" + mode] = {
                                "process_ms": s.get("wall_ms"), "maxrss_kb": s.get("maxrss_kb"),
                                "exec_ms": s.get("exec_ms"), "rc": s.get("rc"),
                                "warm_ms": w.get("warm_min_ms" if name in slow else "warm_median_ms"),
                                "warm_maxrss_kb": w.get("maxrss_kb"),
                                "warm_rc": w.get("rc")}
                        else:
                            vr = v.query(q, a.graph)
                            vr.pop("out", None)
                            e["virtuoso"] = vr
                    rrec["q"][name] = e
                rrec["loadavg_end"] = loadavg()
                phase["rounds"].append(rrec)
                save()
                log("round %d (%s) load %.2f -> %.2f" % (rnd, threads, la, rrec["loadavg_end"]))
            phase["server_vmrss_kb_end"] = v.status_kb("VmRSS")
        finally:
            v.stop()
    out["summary"] = summarise(out)
    save()


def summarise(t):
    """Per phase, query and engine: medians over rounds."""
    summ = []
    for ph in t["phases"]:
        for name in t["queries"]:
            row = {"virtuoso_threads": ph["virtuoso_threads"], "query": name}
            rounds = [r["q"].get(name, {}) for r in ph["rounds"]]
            cold = [r["q"].get(name, {}) for r in ph["cold"]]
            for key in ("sbm11_none", "sbm11_merkle"):
                xs = [r[key] for r in rounds if key in r]
                if xs:
                    row[key] = {
                        "process_ms": median([x["process_ms"] for x in xs if x["rc"] == 0]),
                        "warm_ms": median([x["warm_ms"] for x in xs if x["warm_rc"] == 0]),
                        "maxrss_kb": max([x["maxrss_kb"] or 0 for x in xs]),
                        "cold_ms": median([c[key]["wall_ms"] for c in cold if key in c and c[key]["rc"] == 0]),
                        "fails": sum(1 for x in xs if x["rc"] != 0 or x["warm_rc"] != 0)}
            xs = [r["virtuoso"] for r in rounds if "virtuoso" in r]
            row["virtuoso"] = {
                "warm_ms": median([x["wall_ms"] for x in xs if x["rc"] == 0]),
                "maxrss_kb": max([x.get("maxrss_kb") or 0 for x in xs]) if xs else None,
                "cold_ms": median([c["virtuoso"]["wall_ms"] for c in cold if "virtuoso" in c and c["virtuoso"]["rc"] == 0]),
                "fails": sum(1 for x in xs if x["rc"] != 0)}
            row["loadavg"] = [r["loadavg"] for r in ph["rounds"]]
            summ.append(row)
    return summ


# ---------------------------------------------------------------- QLever (native)
#
# QLever at the commit pinned in tests/qlvr/instance.json, built natively by
# qlever-native-build.sh (no docker). Record: docs/designissues/
# 2026-10-12-three-engine-benchmark.md, section "QLever native (2026-10-12)".
# The server runs with the result cache off: a warm time that is a cache hit
# would measure the cache, not the engine.

QLEVER_BUILD = os.environ.get("QLEVER_NATIVE_BUILD", "/home/user/qlever-native/build")
QLEVER_INDEX = os.path.join(QLEVER_BUILD, "qlever-index")
QLEVER_SERVER = os.path.join(QLEVER_BUILD, "qlever-server")
QPORT = int(os.environ.get("QLEVER_PORT", "7031"))
QTOKEN = "factoidal_bench"
QLEVER_SETTINGS = {"ascii-prefixes-only": False, "num-triples-per-batch": 100000}
QLEVER_SERVER_ARGS = ["--memory-max-size", "2G", "--default-query-timeout", "600s",
                      "--cache-max-size", "0", "--cache-max-size-single-entry", "0",
                      "--cache-max-num-entries", "0",
                      "--no-metrics-log", "--no-resource-usage-log"]


def qlever_index_settings(base):
    """Write the settings file next to the index (same values as the image
    build in tools/qlvr/Qleverfile)."""
    path = base + ".settings.json"
    with open(path, "w") as f:
        json.dump(QLEVER_SETTINGS, f)
    return path


class QleverServer:
    def __init__(self, base):
        self.base = base
        self.proc = None
        self.start_ms = None

    def start(self, timeout=600):
        logf = open(self.base + ".server-%d.log" % int(time.time() * 1000), "ab")
        cmd = [QLEVER_SERVER, "-i", self.base, "-p", str(QPORT), "-a", QTOKEN] + QLEVER_SERVER_ARGS
        t0 = time.monotonic()
        self.proc = subprocess.Popen(cmd, stdout=logf, stderr=subprocess.STDOUT,
                                     start_new_session=True)
        while time.monotonic() - t0 < timeout:
            if self.proc.poll() is not None:
                raise RuntimeError("qlever-server exited during start; see %s" % logf.name)
            try:
                st, _ = self.http("ASK { ?s ?p ?o }", timeout=5)
                if st == 200:
                    self.start_ms = round((time.monotonic() - t0) * 1000.0, 1)
                    return
            except OSError:
                pass
            time.sleep(0.2)
        raise RuntimeError("qlever-server did not answer within %d s" % timeout)

    def stop(self):
        if self.proc is None:
            return
        os.killpg(self.proc.pid, signal.SIGTERM)
        try:
            self.proc.wait(timeout=300)
        except subprocess.TimeoutExpired:
            os.killpg(self.proc.pid, signal.SIGKILL)
            self.proc.wait()
        self.proc = None

    def status_kb(self, field):
        with open("/proc/%d/status" % self.proc.pid) as f:
            for line in f:
                if line.startswith(field + ":"):
                    return int(line.split()[1])
        return None

    def reset_hwm(self):
        with open("/proc/%d/clear_refs" % self.proc.pid, "w") as f:
            f.write("5")

    def http(self, query, timeout=QUERY_TIMEOUT_S):
        body = urllib.parse.urlencode({"query": query, "access-token": QTOKEN})
        c = http.client.HTTPConnection("127.0.0.1", QPORT, timeout=timeout)
        try:
            c.request("POST", "/", body=body, headers={
                "Content-Type": "application/x-www-form-urlencoded",
                "Accept": "application/sparql-results+json"})
            r = c.getresponse()
            return r.status, r.read()
        finally:
            c.close()

    def query(self, query):
        """One SPARQL request; wall ms on the client from send to the last
        byte; server VmHWM during the request."""
        self.reset_hwm()
        t0 = time.monotonic()
        try:
            st, data = self.http(query)
        except OSError as e:
            return {"rc": "error: %s" % e, "wall_ms": round((time.monotonic() - t0) * 1000.0, 3)}
        wall = (time.monotonic() - t0) * 1000.0
        return {"rc": 0 if st == 200 else st, "wall_ms": round(wall, 3),
                "maxrss_kb": self.status_kb("VmHWM"), "out": data}


def cmd_qlever_answers(a):
    """Every query once on the native server; compare with the saved SBM11
    and Virtuoso answers and, where present, the image-built QLever oracle."""
    os.makedirs(a.outdir, exist_ok=True)
    srv = QleverServer(a.index)
    srv.start()
    res = {"dataset": a.dataset, "server_start_ms": srv.start_ms,
           "build": QLEVER_BUILD, "queries": {}}
    try:
        for rq in query_files(a.queries):
            name = os.path.basename(rq)[:-3]
            r = {"name": name}
            vr = srv.query(open(rq).read())
            r["rc"] = vr["rc"]
            r["wall_ms"] = vr["wall_ms"]
            r["maxrss_kb"] = vr.get("maxrss_kb")
            if vr["rc"] != 0:
                r["body"] = vr.get("out", b"")[:2000].decode("utf-8", "replace")
                r["all_equal"] = False
                res["queries"][name] = r
                log("%s: QLever error %s" % (name, vr["rc"]))
                continue
            open(os.path.join(a.outdir, "%s.qlever.json" % name), "wb").write(vr["out"])
            qparsed = solutions(vr["out"])
            r["rows"] = {"qlever": qparsed[1]}
            refs = {"sbm11_none": os.path.join(a.answers_dir, "%s.sbm11-none.json" % name),
                    "virtuoso": os.path.join(a.answers_dir, "%s.virtuoso.json" % name)}
            if a.oracle:
                refs["oracle"] = os.path.join(a.oracle, name + ".srj")
            comps = {}
            for key, path in refs.items():
                if not os.path.exists(path):
                    r.setdefault("missing_reference", []).append(key)
                    continue
                other = solutions(open(path, "rb").read())
                r["rows"][key] = other[1]
                comps["qlever~" + key] = compare(qparsed, other)
            r["comparisons"] = comps
            r["all_equal"] = ("qlever~sbm11_none" in comps and "qlever~virtuoso" in comps
                              and all(c["equal"] for c in comps.values()))
            res["queries"][name] = r
            log("%s: %s rows=%s" % (name, "equal" if r["all_equal"] else "DIFFERENT", r["rows"]))
    finally:
        srv.stop()
    res["equal"] = sorted(n for n, r in res["queries"].items() if r.get("all_equal"))
    res["different"] = sorted(n for n, r in res["queries"].items() if not r.get("all_equal"))
    json.dump(res, open(a.out, "w"), indent=1, default=str)


def cmd_qlever_timing(a):
    """Cold: per query, a new server process after the index files were
    evicted from the page cache; the first query's client wall time. Warm: one
    server, one warm-up pass, then ROUNDS rounds of one request per query.
    Only the queries whose QLever answer equals SBM11 and Virtuoso."""
    ans = json.load(open(a.answers))
    names = set(ans["equal"])
    qs = [(os.path.basename(rq)[:-3], rq) for rq in query_files(a.queries)
          if os.path.basename(rq)[:-3] in names]
    index_dir = os.path.dirname(a.index)
    idx_files = files_under(index_dir)
    srv = QleverServer(a.index)
    out = {"dataset": a.dataset, "rounds": a.rounds, "cold_rounds": a.cold_rounds,
           "queries": [n for n, _ in qs], "excluded": ans["different"],
           "cold": [], "rounds_warm": [], "load_target": LOAD_TARGET}

    def save():
        json.dump(out, open(a.out, "w"), indent=1, default=str)

    for cr in range(a.cold_rounds):
        la = wait_for_load()
        crec = {"round": cr, "loadavg": la, "q": {}}
        for name, rq in qs:
            q = open(rq).read()
            evict(idx_files)
            resident = resident_bytes(idx_files)
            srv.start()
            r = srv.query(q)
            r.pop("out", None)
            crec["q"][name] = {"start_ms": srv.start_ms, "resident_before": resident, "qlever": r}
            srv.stop()
        crec["loadavg_end"] = loadavg()
        out["cold"].append(crec)
        save()
        log("cold round %d load %.2f" % (cr, la))
    srv.start()
    try:
        for name, rq in qs:
            srv.query(open(rq).read())
        for rnd in range(a.rounds):
            la = wait_for_load()
            rrec = {"round": rnd, "loadavg": la, "q": {}}
            for name, rq in qs:
                r = srv.query(open(rq).read())
                r.pop("out", None)
                rrec["q"][name] = {"qlever": r}
            rrec["loadavg_end"] = loadavg()
            out["rounds_warm"].append(rrec)
            save()
            log("warm round %d load %.2f -> %.2f" % (rnd, la, rrec["loadavg_end"]))
    finally:
        srv.stop()
    summ = []
    for name in out["queries"]:
        warm = [r["q"][name]["qlever"] for r in out["rounds_warm"]]
        cold = [c["q"][name] for c in out["cold"]]
        summ.append({
            "query": name,
            "warm_ms": median([w["wall_ms"] for w in warm if w["rc"] == 0]),
            "warm_fails": sum(1 for w in warm if w["rc"] != 0),
            "warm_maxrss_kb": max([w.get("maxrss_kb") or 0 for w in warm]) if warm else None,
            "cold_ms": median([c["qlever"]["wall_ms"] for c in cold if c["qlever"]["rc"] == 0]),
            "cold_fails": sum(1 for c in cold if c["qlever"]["rc"] != 0),
            "cold_maxrss_kb": max([c["qlever"].get("maxrss_kb") or 0 for c in cold]) if cold else None,
            "server_start_ms": median([c["start_ms"] for c in cold])})
    out["summary"] = summ
    out["loadavg_warm"] = [r["loadavg"] for r in out["rounds_warm"]]
    save()


def cmd_qlever_report(a):
    """Markdown tables for the record from the QLever JSON files in RES."""
    lines = []
    for ds in a.datasets:
        ans = load_json(os.path.join(a.results, "qlever-answers-%s.json" % ds))
        tim = load_json(os.path.join(a.results, "qlever-timing-%s.json" % ds))
        bld = load_json(os.path.join(a.results, "qlever-index-%s.json" % ds))
        lines.append("### %s" % ds)
        if bld:
            lines.append("Index build: wall %.1f s, peak RSS %s kB, rc %s" % (
                bld["wall_ms"] / 1000.0, bld["maxrss_kb"], bld["rc"]))
        if ans:
            lines.append("Answers: %d equal on SBM11, Virtuoso and the oracle (where present), "
                         "%d different, out of %d queries." % (
                             len(ans["equal"]), len(ans["different"]), len(ans["queries"])))
            for n in ans["different"]:
                r = ans["queries"][n]
                lines.append("- different: %s rows=%s rc=%s" % (n, r.get("rows"), r.get("rc")))
        if tim:
            lines.append("")
            lines.append("| Query | Cold ms (median) | Warm ms (median) | Warm peak RSS kB | Start ms (median) |")
            lines.append("| --- | ---: | ---: | ---: | ---: |")
            for s in tim["summary"]:
                lines.append("| %s | %s | %s | %s | %s |" % (
                    s["query"], fmt3(s["cold_ms"]), fmt3(s["warm_ms"]),
                    s["warm_maxrss_kb"], fmt3(s["server_start_ms"])))
            lines.append("Load average (1 min) at the start of each warm round: %s" % tim["loadavg_warm"])
        lines.append("")
    text = "\n".join(lines)
    print(text)


def load_json(path):
    try:
        return json.load(open(path))
    except (OSError, ValueError):
        return None


def fmt3(x):
    return "-" if x is None else "%.1f" % x


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("virtuoso-load")
    p.add_argument("--nt", required=True)
    p.add_argument("--graph", required=True)
    p.add_argument("--dbdir", required=True)
    p.add_argument("--threads", default="default")
    p.add_argument("--out", required=True)
    for nm in ("answers", "timing"):
        p = sub.add_parser(nm)
        p.add_argument("--dataset", required=True)
        p.add_argument("--queries", required=True)
        p.add_argument("--gen", required=True)
        p.add_argument("--dbdir", required=True)
        p.add_argument("--graph", required=True)
        p.add_argument("--out", required=True)
        if nm == "answers":
            p.add_argument("--outdir", required=True)
            p.add_argument("--oracle")
        else:
            p.add_argument("--answers", required=True)
            p.add_argument("--rounds", type=int, default=7)
            p.add_argument("--cold-rounds", type=int, default=3)
            p.add_argument("--repeat", type=int, default=5)
            p.add_argument("--virtuoso-threads", default="1t,default")
    p = sub.add_parser("qlever-answers")
    p.add_argument("--dataset", required=True)
    p.add_argument("--queries", required=True)
    p.add_argument("--index", required=True, help="index basename (QLever -i)")
    p.add_argument("--answers-dir", required=True, help="saved SBM11 and Virtuoso answers")
    p.add_argument("--outdir", required=True)
    p.add_argument("--oracle")
    p.add_argument("--out", required=True)
    p = sub.add_parser("qlever-timing")
    p.add_argument("--dataset", required=True)
    p.add_argument("--queries", required=True)
    p.add_argument("--index", required=True)
    p.add_argument("--answers", required=True, help="qlever-answers JSON")
    p.add_argument("--rounds", type=int, default=7)
    p.add_argument("--cold-rounds", type=int, default=3)
    p.add_argument("--out", required=True)
    p = sub.add_parser("qlever-settings")
    p.add_argument("--base", required=True)
    p = sub.add_parser("qlever-report")
    p.add_argument("--results", required=True)
    p.add_argument("datasets", nargs="+")
    a = ap.parse_args()
    if a.cmd == "qlever-settings":
        print(qlever_index_settings(a.base))
        return
    if a.cmd == "qlever-report":
        cmd_qlever_report(a)
        return
    {"virtuoso-load": cmd_virtuoso_load, "answers": cmd_answers, "timing": cmd_timing,
     "qlever-answers": cmd_qlever_answers, "qlever-timing": cmd_qlever_timing}[a.cmd](a)


if __name__ == "__main__":
    main()
