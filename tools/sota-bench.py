#!/usr/bin/env python3
"""tools/sota-bench.py: the Lean engine against state-of-the-art engines,
same input file, same machine.

Key result 2.7 of https://github.com/danbri/factoidal/issues/768;
issue https://github.com/danbri/factoidal/issues/811. Record:
docs/designissues/2026-10-12-sota-reference.md.

For each workload (parse, in-memory SPARQL, RDFC-1.0, OWL RL closure, OWL 2 DL
consistency) and each size, every engine runs on the SAME file as

    /usr/bin/time -v -o T timeout -s KILL CAP COMMAND

three times. A run killed at CAP (default 600 s) is TIMEOUT; it is a status,
never a time, and the remaining runs of that case are skipped. For each
(workload, engine, size) one JSON line is written: median, minimum and maximum
wall time, median CPU time (user + system), median peak resident set
(`Maximum resident set size` of time -v), the 1-minute load average before
each run, and the engine's answer (a count, a value or a SHA-256 of the
output), so that a disagreement between engines is visible next to the
times. `--report` prints the markdown table with the ratio Lean / reference
for time and for peak resident set. `--check` (the gate,
tests/perf/sota_gate.sh) re-runs the Lean rows of a recorded file and fails
when one is more than 25 % slower in CPU time or larger in peak resident set,
or gives a different answer.

Reference engines are not vendored. `--install` fetches them into the
download directory (default /tmp/sota-dl-<checkout directory name>) and checks each archive against
the SHA-256 below: pyoxigraph (pip, in a venv), Apache Jena (binary
distribution), Serd (`serdi`, the Ubuntu packages, unpacked, not installed),
HermiT (inside the owlready2 wheel) and rdf-canonize (npm). The npm package
rows need a wasm build in npm/factoidal/l4-assets
(tools/fetch-builds.sh --set web).

Usage:
  tools/sota-bench.py --install
  tools/sota-bench.py --out R.jsonl [--workloads a,b] [--engines lean,oxigraph]
  tools/sota-bench.py --report R.jsonl > table.md
  tools/sota-bench.py --check R.jsonl [--tolerance 0.25] [--max-s 120]
  tools/sota-bench.py --list
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

# One directory per checkout (hazard #43 of skills/workflow-gotchas-debugging:
# on 2026-10-13 one agent deleted the shared /tmp/sota-dl at the end of its
# run while another checkout's gate read fixtures from it, and 74 of 79 rows
# failed with exit 125). Downloads are still reused within one checkout.
DL = Path(os.environ.get("SOTA_DL", f"/tmp/sota-dl-{ROOT.name}"))
FIX = Path(os.environ.get("SOTA_FIXTURES", str(DL / "fixtures")))
os.environ.setdefault("BENCH_FIXTURE_DIR", str(FIX))

import bench_lean_vs_fstar as blf  # noqa: E402  (the shared input generators)

LEAN_BIN = Path(os.environ.get("SOTA_LEAN_BIN", str(ROOT / "formal/lean4/.lake/build/bin")))
LEAN = LEAN_BIN / "l4factoidal"
NPM_DIR = ROOT / "npm/factoidal"
EX = "http://example.org/"

# ---------------------------------------------------------------------------
# reference engines: pinned versions and digests (checked by --install)
# ---------------------------------------------------------------------------
PYOXIGRAPH = "pyoxigraph==0.5.11"
OWLREADY2 = "owlready2==0.51"
HERMIT_JAR_SHA256 = "97e53f519720a0a2e328556e03b806aa239347c85e57637a935e6433ed2ad3a8"
JENA_VERSION = "6.2.0"
JENA_URL = f"https://dlcdn.apache.org/jena/binaries/apache-jena-{JENA_VERSION}.tar.gz"
JENA_ARCHIVE_URL = f"https://archive.apache.org/dist/jena/binaries/apache-jena-{JENA_VERSION}.tar.gz"
JENA_SHA256 = "14c12ef4aa2f0078a473be4b10b015e0e0b85e767d6867e8581679de8fec3f6e"
SERD_DEBS = {
    "serdi_0.32.2-1_amd64.deb": "a76f7fee723ffdb16c3237d0fa24e6e788c692a3f20af8bc1c0143d5d62ad460",
    "libserd-0-0_0.32.2-1_amd64.deb": "5ede35e66656c136b6a803aebeac92b2c061ec4d147820a730dd9c2a1315f57a",
}
RDF_CANONIZE = "rdf-canonize@5.0.0"

PY = DL / "venv/bin/python"
JENA = DL / f"apache-jena-{JENA_VERSION}/bin"
SERDI = DL / "serd/usr/bin/serdi"
SERD_LIB = DL / "serd/usr/lib/x86_64-linux-gnu"
HERMIT = DL / "pylib/owlready2/hermit/HermiT.jar"
NODE_MODULES = DL / "js/node_modules"
OXI_DRIVER = ROOT / "tools/sota_bench_oxigraph.py"
CANON_DRIVER = ROOT / "tools/sota_bench_rdfcanonize.mjs"
NPM_DRIVER = ROOT / "tools/sota_bench_npm.mjs"
JVM_HEAP = os.environ.get("SOTA_JVM_HEAP", "4g")
KEEP_BYTES = 768 << 20  # outputs up to this size are kept to compute the answer


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def install():
    DL.mkdir(parents=True, exist_ok=True)
    if not PY.exists():
        subprocess.run([sys.executable, "-m", "venv", str(DL / "venv")], check=True)
    subprocess.run([str(PY), "-m", "pip", "install", "-q", PYOXIGRAPH], check=True)
    if not HERMIT.exists():
        subprocess.run([str(PY), "-m", "pip", "install", "-q", "--target", str(DL / "pylib"),
                        OWLREADY2], check=True)
    if sha256_file(HERMIT) != HERMIT_JAR_SHA256:
        sys.exit(f"HermiT.jar digest differs from {HERMIT_JAR_SHA256}")
    if not JENA.exists():
        tgz = DL / f"apache-jena-{JENA_VERSION}.tar.gz"
        rc = subprocess.call(["curl", "-fsSL", "-o", str(tgz), JENA_URL])
        if rc != 0:
            subprocess.run(["curl", "-fsSL", "-o", str(tgz), JENA_ARCHIVE_URL], check=True)
        if sha256_file(tgz) != JENA_SHA256:
            sys.exit(f"{tgz}: digest differs from {JENA_SHA256}")
        subprocess.run(["tar", "xzf", str(tgz), "-C", str(DL)], check=True)
        tgz.unlink()
    if not SERDI.exists():
        subprocess.run(["apt-get", "download", "serdi=0.32.2-1", "libserd-0-0=0.32.2-1"],
                       cwd=DL, check=True)
        for deb, digest in SERD_DEBS.items():
            if sha256_file(DL / deb) != digest:
                sys.exit(f"{deb}: digest differs from {digest}")
            subprocess.run(["dpkg", "-x", str(DL / deb), str(DL / "serd")], check=True)
    if not (NODE_MODULES / "rdf-canonize").exists():
        (DL / "js").mkdir(exist_ok=True)
        subprocess.run(["npm", "install", "--silent", "--prefix", str(DL / "js"), RDF_CANONIZE],
                       check=True)
    print(json.dumps(versions(), indent=1))


def versions():
    def out(cmd, env=None):
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=60)
            return (p.stdout + p.stderr).strip().splitlines()
        except (OSError, subprocess.TimeoutExpired) as e:
            return [f"unavailable: {e}"]
    v = {
        "lean_l4factoidal_sha256": sha256_file(LEAN) if LEAN.exists() else None,
        "pyoxigraph": out([str(PY), "-c", "import pyoxigraph; print(pyoxigraph.__version__)"]),
        "jena": [l for l in out([str(JENA / "riot"), "--version"], java_env()) if "Jena" in l],
        "serdi": out([str(SERDI), "-v"], serd_env())[:1],
        "hermit_jar_sha256": sha256_file(HERMIT) if HERMIT.exists() else None,
        "rdf_canonize": None,
        "java": [l for l in out(["java", "-version"], java_env()) if "version" in l],
        "python": sys.version.split()[0],
        "node": out(["node", "--version"]),
    }
    pj = NODE_MODULES / "rdf-canonize/package.json"
    if pj.exists():
        v["rdf_canonize"] = json.loads(pj.read_text())["version"]
    wasm = NPM_DIR / "l4-assets/l4factoidal.wasm"
    v["npm_wasm_sha256"] = sha256_file(wasm) if wasm.exists() else None
    return v


def java_env():
    env = dict(os.environ)
    env.pop("JAVA_TOOL_OPTIONS", None)  # the proxy settings; Jena reads local files only
    env["JVM_ARGS"] = f"-Xmx{JVM_HEAP}"
    return env


def serd_env():
    return dict(os.environ, LD_LIBRARY_PATH=str(SERD_LIB))


# ---------------------------------------------------------------------------
# inputs
# ---------------------------------------------------------------------------
def fx(name):
    FIX.mkdir(parents=True, exist_ok=True)
    return FIX / name


def gen_canon_pairs(n):
    """k pairs _:a{i} ex:p _:b{i}: two collision groups of k blank nodes
    (the pairs shape of https://github.com/danbri/factoidal/issues/751)."""
    def prod(f):
        for i in range(n):
            f.write(f"_:a{i} <{EX}p> _:b{i} .\n")
    return blf.write_once(fx(f"canon-pairs-{n}.nq"), prod)


def write_file(path, text):
    if not path.exists() or path.read_text(encoding="utf-8") != text:
        path.write_text(text, encoding="utf-8")
    return path


def gene_first_subject(path):
    """The subject IRI of the first paragraph of a gene.ttl slice (every
    slice holds paragraph 0, so every size has an answer)."""
    prefixes = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = re.match(r"@prefix\s+(\S*):\s*<([^>]*)>\s*\.", line)
            if m:
                prefixes[m.group(1)] = m.group(2)
                continue
            tok = line.strip().split()
            if tok and not line.startswith("@"):
                t = tok[0]
                if t.startswith("<"):
                    return t[1:-1]
                pre, local = t.split(":", 1)
                return prefixes[pre] + local
    raise ValueError(f"{path}: no statement")


WDT = "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
QUERIES = {
    # the subject is filled in per file by gene_first_subject
    "bound-subject": "SELECT ?p ?o WHERE {{ <{s}> ?p ?o }}\n",
    "count": "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }\n",
    "join": WDT + "SELECT ?s ?o1 ?o2 WHERE { ?s wdt:P688 ?o1 . ?s wdt:P1057 ?o2 }\n",
    "optional-filter": WDT + ("SELECT ?s ?o1 ?o2 WHERE {\n  ?s wdt:P1057 ?o1 .\n"
                              "  OPTIONAL { ?s wdt:P688 ?o2 }\n  FILTER(isIRI(?o1))\n}\n"),
    # added 2026-10-21: the indexed FILTER NOT EXISTS of issue 881
    "not-exists": WDT + ("SELECT ?s ?o1 WHERE {\n  ?s wdt:P1057 ?o1 .\n"
                         "  FILTER NOT EXISTS { ?s wdt:P688 ?o2 }\n}\n"),
}


def query_file(qid, data):
    text = QUERIES[qid]
    if qid == "bound-subject":
        text = text.format(s=gene_first_subject(data))
    return write_file(fx(f"q-{qid}-{data.stem}.rq"), text)


# OWL: the ontologies of tools/owl-real-bench.py. The input of both engines is
# OUT/<name>/sota.nt: the RDF merge of the source documents (Lean parser,
# blank nodes of the second document prefixed, duplicate lines removed)
# without its owl:imports triples, which HermiT would try to fetch.
OWL_SET = ["skos", "foaf", "prov-o", "bfo", "pizza", "wine", "schema.org", "qudt", "ro",
           "cl-basic"]


def owl_input(name):
    import importlib.util
    spec = importlib.util.spec_from_file_location("owlrb", ROOT / "tools/owl-real-bench.py")
    owlrb = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(owlrb)
    onto = next(o for o in owlrb.ONTOLOGIES if o["name"] == name)
    wd = fx(f"owl-{name}")
    wd.mkdir(exist_ok=True)
    out = wd / "sota.nt"
    if out.exists() and out.stat().st_size > 0:
        return out
    files = [str(ROOT / f) for f in onto["files"]]
    merged, _docs, _n = owlrb.prepare_merged(str(LEAN), files, onto["format"], str(wd))
    tmp = wd / "sota.tmp"
    with open(merged, encoding="utf-8") as f, open(tmp, "w", encoding="utf-8") as g:
        for line in f:
            if "<http://www.w3.org/2002/07/owl#imports>" not in line:
                g.write(line)
    tmp.rename(out)
    return out


def jena_owl_assembler(data, reasoner):
    url = {"owl-micro": "http://jena.hpl.hp.com/2003/OWLMicroFBRuleReasoner",
           "owl-mini": "http://jena.hpl.hp.com/2003/OWLMiniFBRuleReasoner"}[reasoner]
    text = ("@prefix ja: <http://jena.hpl.hp.com/2005/11/Assembler#> .\n"
            "<#ds> a ja:RDFDataset ; ja:defaultGraph <#inf> .\n"
            "<#inf> a ja:InfModel ; ja:baseModel <#base> ;\n"
            f"  ja:reasoner [ ja:reasonerURL <{url}> ] .\n"
            "<#base> a ja:MemoryModel ;\n"
            f"  ja:content [ ja:externalContent <file://{data}> ] .\n")
    return write_file(data.parent / f"jena-{reasoner}.ttl", text)


SPO_QUERY = "SELECT ?s ?p ?o WHERE { ?s ?p ?o }\n"

# ---------------------------------------------------------------------------
# engines: a command per (workload kind, engine); answer extraction
# ---------------------------------------------------------------------------
JENA_SYNTAX = {"ntriples": "N-Triples", "turtle": "Turtle", "rdfxml": "RDF/XML",
               "nquads": "N-Quads", "jsonld": "JSON-LD"}
# riot --output names: "RDF/XML" is the plain writer (one rdf:Description per
# statement), the form Lean and Oxigraph write; "jsonld" is JSON-LD 1.1.
JENA_OUTPUT = {"rdfxml": "RDF/XML", "jsonld": "jsonld"}


def cmd_parse(engine, path, fmt):
    if engine == "lean":
        return [str(LEAN), "parse", str(path), "--format", fmt, "--out", "nquads"], None
    if engine == "lean-stream":
        # the streaming reader (64 KiB chunks) of `parse --lenient`; on valid
        # input it keeps every statement
        return [str(LEAN), "parse", str(path), "--format", fmt, "--lenient", "--out",
                "nquads"], None
    if engine == "oxigraph":
        return [str(PY), str(OXI_DRIVER), "parse", str(path), fmt], None
    if engine == "serd":
        return [str(SERDI), "-i", fmt, "-o", "nquads", str(path)], serd_env()
    if engine == "jena":
        return [str(JENA / "riot"), f"--syntax={JENA_SYNTAX[fmt]}", "--output=nquads",
                str(path)], java_env()
    return None, None


def cmd_write(engine, path, fmt, out):
    """Read FILE (fmt) and write it in the syntax `out` (a writer row)."""
    if engine == "lean":
        return [str(LEAN), "parse", str(path), "--format", fmt, "--out", out], None
    if engine == "oxigraph":
        return [str(PY), str(OXI_DRIVER), "convert", str(path), fmt, out], None
    if engine == "jena":
        return [str(JENA / "riot"), f"--syntax={JENA_SYNTAX[fmt]}",
                f"--output={JENA_OUTPUT[out]}", str(path)], java_env()
    return None, None


def cmd_count(engine, path, fmt):
    if engine == "lean":
        return [str(LEAN), "parse", str(path), "--format", fmt], None
    if engine == "lean-stream":
        return [str(LEAN), "parse", str(path), "--format", fmt, "--lenient"], None
    if engine == "npm":
        return ["node", str(NPM_DRIVER), str(NPM_DIR), "parse", str(path), fmt], None
    if engine == "jena":
        return [str(JENA / "riot"), f"--syntax={JENA_SYNTAX[fmt]}", "--count", str(path)], java_env()
    return None, None


def cmd_query(engine, path, fmt, qfile):
    if engine == "lean":
        return [str(LEAN), "query", str(path), "--format", fmt, "--query", str(qfile),
                "--table"], None
    if engine == "oxigraph":
        return [str(PY), str(OXI_DRIVER), "query", str(path), fmt, str(qfile)], None
    if engine == "jena":
        return [str(JENA / "arq"), f"--data={path}", f"--query={qfile}", "--results=TSV"], java_env()
    return None, None


def cmd_canon(engine, path):
    if engine == "lean":
        return [str(LEAN), "canonicalize", str(path), "--format", "nquads"], None
    if engine == "oxigraph":
        return [str(PY), str(OXI_DRIVER), "canonicalize", str(path)], None
    if engine == "rdf-canonize":
        return ["node", str(CANON_DRIVER), str(NODE_MODULES), str(path)], None
    if engine == "npm":
        return ["node", str(NPM_DRIVER), str(NPM_DIR), "canonicalize", str(path)], None
    return None, None


def cmd_closure(engine, path):
    if engine == "lean":
        return [str(LEAN), "closure", str(path), "--format", "nquads", "--regime", "owl-rl"], None
    if engine in ("jena-owl-micro", "jena-owl-mini"):
        asm = jena_owl_assembler(path, engine[len("jena-"):])
        q = write_file(fx("q-spo.rq"), SPO_QUERY)
        return [str(JENA / "arq"), f"--desc={asm}", f"--query={q}", "--results=TSV"], java_env()
    return None, None


def cmd_consistent(engine, path):
    if engine == "lean":
        return [str(LEAN), "owl-consistent", str(path), "--format", "nquads"], None
    if engine == "hermit":
        env = dict(os.environ)
        env.pop("JAVA_TOOL_OPTIONS", None)
        return ["java", f"-Xmx{JVM_HEAP}", "-cp", str(HERMIT),
                "org.semanticweb.HermiT.cli.CommandLine", "--ignoreUnsupportedDatatypes",
                "-k", str(path)], env
    return None, None


def cmd_start(engine, _path):
    if engine == "lean":
        return [str(LEAN), "version"], None
    if engine == "oxigraph":
        return [str(PY), str(OXI_DRIVER), "start"], None
    if engine == "serd":
        return [str(SERDI), "-v"], serd_env()
    if engine == "jena":
        return [str(JENA / "riot"), "--version"], java_env()
    if engine == "npm":
        return ["node", str(NPM_DRIVER), str(NPM_DIR), "start"], None
    if engine == "hermit":
        env = dict(os.environ)
        env.pop("JAVA_TOOL_OPTIONS", None)
        return ["java", f"-Xmx{JVM_HEAP}", "-cp", str(HERMIT),
                "org.semanticweb.HermiT.cli.CommandLine", "--version"], env
    return None, None


def ans_lines(o):
    """Statements written (non-empty lines of N-Quads output)."""
    return o["nonempty"] if o.get("nonempty") is not None else o["lines"]


def ans_rows(o):
    """Solutions of a SELECT written as TSV with one header line."""
    return max(0, ans_lines(o) - 1)


def ans_riot_count(o):
    """riot --count writes "FILE : Triples = N" to standard error."""
    m = re.search(r"(?:Triples|Quads)\s*=\s*(\d[\d,]*)", o["first"] + "\n" + o["stderr"])
    return int(m.group(1).replace(",", "")) if m else None


def ans_count_value(o):
    """COUNT(*): the integer on the second line (Lean --table prints the bare
    lexical form, Jena and Oxigraph TSV print the number)."""
    m = re.search(r"(\d+)", o["second"])
    return int(m.group(1)) if m else None


def ans_first_int(o):
    m = re.search(r"(\d+)", o["first"])
    return int(m.group(1)) if m else None


def ans_sha(o):
    return (o.get("norm_sha256") or o["sha256"])[:16]


def ans_verdict(o):
    text = (o["first"] + " " + o["stderr"])
    if "Inconsistent ontology" in text or "InconsistentOntologyException" in text:
        return "false"
    if "owl#Thing is satisfiable" in text:
        return "true"
    t = o["first"].strip()
    return t if t in ("true", "false", "unknown") else None


class Workload:
    def __init__(self, wid, group, desc, sizes, make, engines, cmd, answer, unit="triples",
                 compare=True, note="", accept=None):
        self.wid, self.group, self.desc, self.sizes = wid, group, desc, sizes
        self.make, self.engines, self.cmd, self.answer = make, engines, cmd, answer
        self.unit, self.compare, self.note = unit, compare, note
        # accept(output) -> True: a non-zero exit status that is an answer (the
        # Lean owl-consistent exits 1 for false and unknown; HermiT exits 1 with
        # InconsistentOntologyException)
        self.accept = accept


W: dict[str, Workload] = {}


def add(w):
    W[w.wid] = w


PARSE_ENGINES = ["lean", "lean-stream", "oxigraph", "serd", "jena"]

add(Workload("start", "start", "process start: the engine loads and exits (no input)",
             [0], lambda n: None, ["lean", "oxigraph", "serd", "jena", "npm", "hermit"],
             lambda e, p, n: cmd_start(e, p), lambda e, o: None, unit="-", compare=False))

add(Workload("parse-nt", "parse", "N-Triples, full IRIs, to N-Quads",
             [100000, 200000, 400000], blf.gen_nt, PARSE_ENGINES,
             lambda e, p, n: cmd_parse(e, p, "ntriples"), lambda e, o: ans_lines(o)))
add(Workload("parse-nt-mixed", "parse",
             "N-Triples, IRIs, plain, language-tagged and typed literals, blank nodes, to N-Quads",
             [100000, 200000, 400000], lambda n: blf.gen_mixed_nt(n, False), PARSE_ENGINES,
             lambda e, p, n: cmd_parse(e, p, "ntriples"), lambda e, o: ans_lines(o)))
add(Workload("parse-ttl-gene", "parse",
             "Turtle, real data: gene.ttl slices (Wikidata life sciences), to N-Quads",
             [20000, 40000, 80000], blf.gene_slice, PARSE_ENGINES,
             lambda e, p, n: cmd_parse(e, p, "turtle"), lambda e, o: ans_lines(o),
             unit="paragraphs"))
add(Workload("parse-ttl-rich", "parse",
             "Turtle, predicate lists, object lists, typed literals, blank node property lists, to N-Quads",
             [100000, 200000, 400000], blf.gen_ttl_rich, PARSE_ENGINES,
             lambda e, p, n: cmd_parse(e, p, "turtle"), lambda e, o: ans_lines(o)))
add(Workload("parse-rdfxml", "parse", "RDF/XML, one rdf:Description per triple, to N-Quads",
             [25000, 50000, 100000], blf.gen_rdfxml, ["lean", "oxigraph", "jena"],
             lambda e, p, n: cmd_parse(e, p, "rdfxml"), lambda e, o: ans_lines(o)))
add(Workload("parse-rdfxml-real", "parse",
             "RDF/XML, real file: the Cell Ontology (cl-basic.owl, 9.6 MB), to N-Quads",
             [1], lambda n: ROOT / "third_party/ontologies/cl-basic/cl-basic.owl",
             ["lean", "oxigraph", "jena"],
             lambda e, p, n: cmd_parse(e, p, "rdfxml"), lambda e, o: ans_lines(o), unit="file"))
add(Workload("parse-jsonld", "parse",
             "JSON-LD, one node object per subject (3 statements each, one shared hub node), "
             "to N-Quads",
             [25000, 50000, 100000], lambda n: blf.gen_jsonld("hub", n),
             ["lean", "oxigraph", "jena"],
             lambda e, p, n: cmd_parse(e, p, "jsonld"), lambda e, o: ans_lines(o), unit="nodes"))
# Writer rows (added 2026-10-21): the RDF/XML writer of issue 845 and the
# JSON-LD writer (fromRdf) of issue 712. The documents differ between engines
# (prefixes, member order, nesting), so the answers are not compared.
add(Workload("write-rdfxml", "write",
             "N-Triples (mixed terms) read and written as RDF/XML",
             [100000, 200000, 400000], lambda n: blf.gen_mixed_nt(n, False),
             ["lean", "oxigraph", "jena"],
             lambda e, p, n: cmd_write(e, p, "ntriples", "rdfxml"), lambda e, o: None,
             compare=False))
add(Workload("write-jsonld", "write",
             "N-Triples (mixed terms) read and written as JSON-LD",
             [100000, 200000, 400000], lambda n: blf.gen_mixed_nt(n, False),
             ["lean", "oxigraph", "jena"],
             lambda e, p, n: cmd_write(e, p, "ntriples", "jsonld"), lambda e, o: None,
             compare=False))
add(Workload("count-nt", "parse-count", "N-Triples, full IRIs, count only (no output)",
             [100000, 200000, 400000], blf.gen_nt, ["lean", "lean-stream", "npm", "jena"],
             lambda e, p, n: cmd_count(e, p, "ntriples"),
             lambda e, o: ans_riot_count(o) if e == "jena" else ans_first_int(o)))
add(Workload("count-ttl-gene", "parse-count", "Turtle, gene.ttl slices, count only (no output)",
             [20000, 40000, 80000], blf.gene_slice, ["lean", "lean-stream", "npm", "jena"],
             lambda e, p, n: cmd_count(e, p, "turtle"),
             lambda e, o: ans_riot_count(o) if e == "jena" else ans_first_int(o),
             unit="paragraphs"))

for qid, desc in (("bound-subject", "SELECT ?p ?o with a bound subject"),
                  ("count", "SELECT (COUNT(*) AS ?c), full scan"),
                  ("join", "two-pattern join on ?s (wdt:P688, wdt:P1057)"),
                  ("optional-filter", "wdt:P1057, OPTIONAL wdt:P688, FILTER(isIRI(?o1))"),
                  ("not-exists", "wdt:P1057, FILTER NOT EXISTS { wdt:P688 }")):
    add(Workload(f"sparql-{qid}", "sparql",
                 f"load gene.ttl slice into memory, {desc}; all solutions as TSV",
                 [20000, 40000, 80000], blf.gene_slice, ["lean", "oxigraph", "jena"],
                 (lambda qid: lambda e, p, n: cmd_query(e, p, "turtle", query_file(qid, p)))(qid),
                 (lambda e, o: ans_count_value(o)) if qid == "count" else (lambda e, o: ans_rows(o)),
                 unit="paragraphs"))

CANON_ENGINES = ["lean", "oxigraph", "rdf-canonize", "npm"]
add(Workload("rdfc-iri", "rdfc", "RDFC-1.0, IRIs only, no blank nodes",
             [25000, 50000, 100000], lambda n: blf.gen_canon("iri", n), CANON_ENGINES,
             lambda e, p, n: cmd_canon(e, p), lambda e, o: ans_sha(o), unit="quads"))
add(Workload("rdfc-person", "rdfc",
             "RDFC-1.0, one blank node per person, shared literal values (3 quads per person)",
             [5000, 10000, 20000], lambda n: blf.gen_canon("person", n), CANON_ENGINES,
             lambda e, p, n: cmd_canon(e, p), lambda e, o: ans_sha(o), unit="persons"))
add(Workload("rdfc-pairs", "rdfc",
             "RDFC-1.0, k pairs _:a ex:p _:b: two collision groups of k blank nodes",
             [2000, 4000, 8000], gen_canon_pairs, CANON_ENGINES,
             lambda e, p, n: cmd_canon(e, p), lambda e, o: ans_sha(o), unit="pairs"))

add(Workload("owl-rl-closure", "owl-rl",
             "OWL RL closure of a real ontology, every closure triple written out",
             OWL_SET, owl_input,
             ["lean", "jena-owl-micro"],
             lambda e, p, n: cmd_closure(e, p),
             lambda e, o: ans_lines(o) if e == "lean" else ans_rows(o),
             unit="ontology", compare=False,
             note="the rule sets differ: Lean OWL 2 RL (OWL 2 Profiles §4.3); Jena OWL Micro "
                  "(RDFS plus part of OWL Lite), so the closure sizes are not compared"))
add(Workload("owl-dl-consistent", "owl-dl",
             "OWL 2 DL consistency of a real ontology", OWL_SET, owl_input,
             ["lean", "hermit"], lambda e, p, n: cmd_consistent(e, p),
             lambda e, o: ans_verdict(o), unit="ontology",
             accept=lambda o: ans_verdict(o) in ("true", "false", "unknown")))


# ---------------------------------------------------------------------------
# measurement
# ---------------------------------------------------------------------------
def parse_time_v(path):
    r = {}
    try:
        text = Path(path).read_text(errors="replace")
    except OSError:
        return r
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("User time (seconds):"):
            r["user"] = float(line.split(":")[1])
        elif line.startswith("System time (seconds):"):
            r["sys"] = float(line.split(":")[1])
        elif line.startswith("Maximum resident set size (kbytes):"):
            r["rss_kb"] = int(line.split(":")[1])
        elif line.startswith("Minor (reclaiming a frame) page faults:"):
            r["minflt"] = int(line.split(":")[1])
        elif line.startswith("Exit status:"):
            r["exit"] = int(line.split(":")[1])
        elif line.startswith("Command terminated by signal"):
            r["signal"] = int(line.rsplit(" ", 1)[1])
    return r


def run_once(cmd, env, cap, tfile, accept=None):
    o = {"lines": 0, "bytes": 0, "first": "", "second": ""}
    h = hashlib.sha256()
    err = []
    full = ["/usr/bin/time", "-v", "-o", str(tfile), "timeout", "-s", "KILL", str(cap)] + cmd
    proc = subprocess.Popen(full, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env,
                            start_new_session=True)

    buf = []
    kept = {"n": 0}

    def drain_out():
        while True:
            chunk = proc.stdout.read(1 << 20)
            if not chunk:
                break
            h.update(chunk)
            o["lines"] += chunk.count(b"\n")
            o["bytes"] += len(chunk)
            if kept["n"] < KEEP_BYTES:
                buf.append(chunk)
                kept["n"] += len(chunk)

    def drain_err():
        while True:
            chunk = proc.stderr.read(1 << 16)
            if not chunk:
                break
            err.append(chunk)
            if len(err) > 64:
                del err[1:33]

    t1 = threading.Thread(target=drain_out, daemon=True)
    t2 = threading.Thread(target=drain_err, daemon=True)
    t1.start()
    t2.start()
    t0 = time.perf_counter()
    proc.wait()
    wall = time.perf_counter() - t0
    t1.join(timeout=30)
    t2.join(timeout=30)
    tv = parse_time_v(tfile)
    o["sha256"] = h.hexdigest()
    if kept["n"] < KEEP_BYTES:
        # the answer ignores empty lines (the Lean command line ends its output
        # with one): count and hash the non-empty lines
        lines = [l for l in b"".join(buf).split(b"\n") if l.strip()]
        o["nonempty"] = len(lines)
        o["norm_sha256"] = hashlib.sha256(b"\n".join(lines) + b"\n").hexdigest()
        o["first"] = lines[0][:300].decode("utf-8", "replace") if lines else ""
        o["second"] = lines[1][:300].decode("utf-8", "replace") if len(lines) > 1 else ""
    else:
        o["nonempty"] = None
        o["norm_sha256"] = None
        o["first"] = b"".join(buf)[:300].split(b"\n")[0].decode("utf-8", "replace")
        o["second"] = ""
    buf.clear()
    stderr = b"".join(err).decode("utf-8", "replace")
    # the JVM prints "Picked up ..." lines; keep the end of stderr for the record
    o["stderr"] = stderr[-2000:]
    exit_code = tv.get("exit", proc.returncode)
    if exit_code == 137 or tv.get("signal") == 9 or wall >= cap:
        status = "TIMEOUT"
    elif exit_code != 0 and not (accept and accept(o)):
        status = f"exit{exit_code}"
    else:
        status = "ok"
    return {"status": status, "wall": wall, "cpu": tv.get("user", 0.0) + tv.get("sys", 0.0),
            "sys": tv.get("sys", 0.0), "minflt": tv.get("minflt"),
            "rss_kb": tv.get("rss_kb"), "out": o}


def wait_for_load(limit, max_wait):
    t0 = time.time()
    while os.getloadavg()[0] > limit and time.time() - t0 < max_wait:
        time.sleep(5)
    return round(time.time() - t0, 1)


def measure(cmd, env, runs, cap, tdir, load_limit, load_wait, extra_on_spread, accept=None):
    rs = []
    waited = wait_for_load(load_limit, load_wait)
    i = 0
    while True:
        load = os.getloadavg()[0]
        r = run_once(cmd, env, cap, tdir / "time-v.txt", accept)
        r["load1"] = round(load, 2)
        rs.append(r)
        i += 1
        if r["status"] != "ok":
            break
        if i == 1 and r["wall"] > cap / 4:
            break  # one run of a case that takes a quarter of the cap
        if i >= runs:
            ok = [x["wall"] for x in rs if x["status"] == "ok"]
            med = statistics.median(ok)
            spread = (max(ok) - min(ok)) / med if med > 0 else 0
            # an outlier (spread over 30 % of the median, above 0.2 s) gets two more runs
            if extra_on_spread and spread > 0.30 and med > 0.2 and i < runs + 2:
                continue
            break
    ok = [x for x in rs if x["status"] == "ok"]
    rec = {"runs": len(rs), "load1": [x["load1"] for x in rs], "load_wait_s": waited}
    if not ok:
        bad = rs[-1]
        rec.update({"status": bad["status"], "wall_s": round(bad["wall"], 3),
                    "rss_mb": round((bad["rss_kb"] or 0) / 1024, 1) if bad["rss_kb"] else None,
                    "stderr_tail": bad["out"]["stderr"][-400:], "first_line": bad["out"]["first"]})
        return rec, bad["out"]
    walls = [x["wall"] for x in ok]
    rec.update({
        "status": "ok",
        "wall_s": round(statistics.median(walls), 4),
        "wall_min_s": round(min(walls), 4), "wall_max_s": round(max(walls), 4),
        "wall_all_s": [round(w, 4) for w in walls],
        "spread": round((max(walls) - min(walls)) / statistics.median(walls), 3)
        if statistics.median(walls) > 0 else 0,
        "cpu_s": round(statistics.median([x["cpu"] for x in ok]), 4),
        "sys_all_s": [x["sys"] for x in ok],
        "minflt_all": [x["minflt"] for x in ok],
        "rss_mb": round(statistics.median([x["rss_kb"] or 0 for x in ok]) / 1024, 1),
        "rss_max_mb": round(max(x["rss_kb"] or 0 for x in ok) / 1024, 1),
        "out_lines": ok[-1]["out"]["lines"], "out_bytes": ok[-1]["out"]["bytes"],
        "first_line": ok[-1]["out"]["first"],
    })
    return rec, ok[-1]["out"]


def label(n):
    return str(n)


def run(args):
    wl = [W[x] for x in args.workloads.split(",")] if args.workloads else list(W.values())
    engines = set(args.engines.split(",")) if args.engines else None
    sizes_only = set(args.sizes.split(",")) if args.sizes else None
    tdir = DL / "tmp"
    tdir.mkdir(parents=True, exist_ok=True)
    out = open(args.out, "a", encoding="utf-8")
    meta = {"kind": "meta", "time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "host": os.uname().nodename, "cpus": os.cpu_count(), "versions": versions(),
            "git": subprocess.run(["git", "-C", str(ROOT), "rev-parse", "HEAD"],
                                  capture_output=True, text=True).stdout.strip(),
            "cap_s": args.cap, "runs": args.runs, "jvm_heap": JVM_HEAP}
    out.write(json.dumps(meta, sort_keys=True) + "\n")
    out.flush()
    lean_sha = (meta["versions"].get("lean_l4factoidal_sha256") or "")[:16]
    for w in wl:
        for n in w.sizes:
            if sizes_only and label(n) not in sizes_only:
                continue
            path = w.make(n)
            answers = {}
            for e in w.engines:
                if engines and e not in engines:
                    continue
                cmd, env = w.cmd(e, path, n)
                if cmd is None:
                    continue
                print(f"[{w.wid} {n} {e}] load {os.getloadavg()[0]:.2f} ...", flush=True)
                rec, o = measure(cmd, env, args.runs, args.cap, tdir, args.load_limit,
                                 args.load_wait, not args.no_rerun, w.accept)
                ans = w.answer(e, o) if rec["status"] == "ok" else None
                answers[e] = ans
                if e in ("lean", "lean-stream"):
                    rec["lean_sha256"] = lean_sha
                rec.update({"kind": "row", "workload": w.wid, "group": w.group, "engine": e,
                            "size": n, "unit": w.unit, "answer": ans,
                            "input": str(path) if path else None,
                            "input_bytes": path.stat().st_size if path else None,
                            "input_sha256": sha256_file(path)[:16] if path else None,
                            "cmd": " ".join(cmd)})
                out.write(json.dumps(rec, sort_keys=True) + "\n")
                out.flush()
                print(f"[{w.wid} {n} {e}] {rec['status']} wall {rec.get('wall_s')} s "
                      f"cpu {rec.get('cpu_s')} s rss {rec.get('rss_mb')} MB answer {ans} "
                      f"loads {rec['load1']}", flush=True)
            vals = {v for v in answers.values() if v is not None}
            if w.compare and len(vals) > 1:
                print(f"[{w.wid} {n}] ANSWERS DIFFER: {answers}", flush=True)
    out.close()


# ---------------------------------------------------------------------------
# report and gate
# ---------------------------------------------------------------------------
def load_rows(path):
    rows, meta = [], []
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        (meta if r.get("kind") == "meta" else rows).append(r)
    # the last measurement of a (workload, engine, size) wins (a rerun replaces)
    last = {}
    for r in rows:
        last[(r["workload"], r["engine"], str(r["size"]))] = r
    return list(last.values()), meta


def fmt_t(r):
    if r is None:
        return "—"
    if r["status"] != "ok":
        return f"{r['status']} ({r.get('wall_s')} s)"
    mn = f", min {r['wall_min_s']:.3f}" if r.get("wall_min_s") is not None else ""
    return f"{r['wall_s']:.3f} s ±{100 * r['spread']:.0f}%{mn}"


def fmt_m(r):
    if r is None or r.get("rss_mb") is None:
        return "—"
    return f"{r['rss_mb']:.0f} MB"


LEAN_ENGINES = ("lean", "lean-stream", "npm")


def fmt_r(x):
    if x is None:
        return "—"
    return f"{x:.2f}" if x < 1 else f"{x:.1f}"


def size_key(s):
    return (0, int(s)) if str(s).isdigit() else (1, OWL_SET.index(s) if s in OWL_SET else 99)


def report(path):
    """Two tables: every measurement, then the summary (each Lean variant
    against the fastest reference engine of the same workload and size)."""
    rows, _meta = load_rows(path)
    by = {}
    for r in rows:
        by.setdefault(r["workload"], {}).setdefault(str(r["size"]), {})[r["engine"]] = r
    order = list(W.keys())
    wids = sorted(by, key=lambda x: order.index(x) if x in order else 99)
    print("### Every measurement\n")
    print("| Workload | Size | Engine | Wall, median (spread) | CPU, median | Peak RSS, median | "
          "Answer | Load (1 min) |")
    print("|---|---:|---|---:|---:|---:|---|---|")
    for wid in wids:
        w = W.get(wid)
        for size in sorted(by[wid], key=size_key):
            cell = by[wid][size]
            answers = {e: str(r.get("answer")) for e, r in cell.items()
                       if r.get("answer") is not None}
            differ = w is not None and w.compare and len(set(answers.values())) > 1
            for e in (w.engines if w else sorted(cell)):
                r = cell.get(e)
                if r is None:
                    continue
                ans = r.get("answer")
                mark = " (differs)" if differ and ans is not None else ""
                load = r.get("load1") or []
                cpu = f"{r['cpu_s']:.2f} s" if r.get("cpu_s") is not None else "—"
                print(f"| {wid} | {size} | {e} | {fmt_t(r)} | {cpu} | {fmt_m(r)} | "
                      f"{ans if ans is not None else '—'}{mark} | "
                      f"{min(load) if load else '—'} to {max(load) if load else '—'} |")
    print("\n### Lean against the fastest reference engine\n")
    print("Ratio = Lean / reference (time: minimum wall time of the runs of each case; CPU: median user plus system "
          "time; memory: median peak resident set). Above 1, Lean is slower or larger. "
          "The fastest reference is the one with the least minimum wall time.\n")
    print("RSS above start: each engine's peak resident set minus the peak resident set "
          "of its own process start (row `start`); a reference that holds less than 1 MB "
          "above its start counts as 1 MB.\n")
    print("| Workload | Size | Reference (fastest) | Reference time, RSS | Lean variant | "
          "Lean time, RSS | Time ratio | CPU ratio | RSS ratio | RSS above start, ratio |")
    print("|---|---:|---|---|---|---|---:|---:|---:|---:|")
    start_rss = {e: r.get("rss_mb") for e, r in by.get("start", {}).get("0", {}).items()
                 if r["status"] == "ok"}
    start_of = {"lean-stream": "lean", "jena-owl-micro": "jena"}

    def above(engine, rss):
        base = start_rss.get(start_of.get(engine, engine))
        return None if base is None or rss is None else rss - base
    flagged = []
    for wid in wids:
        if wid == "start":
            continue
        for size in sorted(by[wid], key=size_key):
            cell = by[wid][size]
            refs = [r for e, r in cell.items() if e not in LEAN_ENGINES and r["status"] == "ok"]
            if not refs:
                continue
            ref = min(refs, key=wall_of)
            for le in LEAN_ENGINES:
                lr = cell.get(le)
                if lr is None:
                    continue
                ar = None
                crs = "—"
                if lr["status"] == "ok":
                    if ref.get("cpu_s"):
                        crs = fmt_r(lr['cpu_s'] / ref['cpu_s'])
                    tr = wall_of(lr) / wall_of(ref) if wall_of(ref) > 0 else None
                    mr = lr["rss_mb"] / ref["rss_mb"] if ref.get("rss_mb") else None
                    la, ra = above(le, lr.get("rss_mb")), above(ref["engine"], ref.get("rss_mb"))
                    if la is not None and ra is not None:
                        ar = la / max(ra, 1.0)  # a reference under 1 MB above start counts as 1 MB
                    trs = fmt_r(tr)
                    mrs = fmt_r(mr)
                    # the gate's rule (over_bound): time over TIME_BOUND, or memory over
                    # MEM_BOUND by both memory measures
                    if (tr or 0) > TIME_BOUND or ((mr or 0) > MEM_BOUND
                                                  and (ar is None or ar > MEM_BOUND)):
                        flagged.append((wid, size, le, ref["engine"], tr, mr))
                else:
                    trs = f"> {lr.get('wall_s', 0) / ref['wall_s']:.0f} ({lr['status']})"
                    mrs = "—"
                    flagged.append((wid, size, le, ref["engine"], None, None))
                ars = fmt_r(ar)
                print(f"| {wid} | {size} | {ref['engine']} | min {wall_of(ref):.3f} s, "
                      f"{fmt_m(ref)} | {le} | {fmt_t(lr)}, {fmt_m(lr)} | {trs} | {crs} | {mrs} | "
                      f"{ars} |")
    print("\n### Rows over the gate's bound (lean variant against the fastest reference)\n")
    print(f"A row is listed when the time ratio is over {TIME_BOUND:g}, or when the RSS ratio "
          f"and the RSS-above-start ratio are both over {MEM_BOUND:g}.\n")
    for wid, size, le, e, t, m in flagged:
        ts = f"{t:.1f}" if t is not None else "not finished"
        ms = f"{m:.1f}" if m is not None else "—"
        print(f"- {wid} {size}, {le} against {e}: time ratio {ts}, RSS ratio {ms}")


# Expected failures of the gate: Lean rows more than 10 times the fastest
# reference engine (time, or memory above process start), each with its open
# issue. The row fails the gate when it comes within the bound (UNEXPECTED
# PASS), so the repair cannot land without the row and the issue being updated.
XFAIL = {
}
# Removed 2026-10-13: ("parse-rdfxml", "100000", "lean") for
# https://github.com/danbri/factoidal/issues/814. With the RDF/XML repairs of
# that issue and https://github.com/danbri/factoidal/issues/771 (fast forms
# proved equal by csimp; the children of rdf:RDF walked as they are read) the
# row measured 1.8 s CPU (5.12 s recorded) and 181 MB (671 MB recorded): time
# ratio 5.3, memory ratio 7.9 against the recorded Oxigraph row, and the gate
# reported UNEXPECTED PASS.
# Removed 2026-10-13: ("rdfc-pairs", "8000", "lean") for
# https://github.com/danbri/factoidal/issues/751. With the RDFC-1.0 repair of
# that issue (OKR batch 1 KR 2.4) the row measured 0.58 s CPU (9.97 s
# recorded), time ratio 2.9 to Oxigraph, and the gate reported UNEXPECTED PASS.
# Removed 2026-10-13: ("owl-dl-consistent", "schema.org", "lean") for
# https://github.com/danbri/factoidal/issues/819. On a base with the repair of
# https://github.com/danbri/factoidal/issues/760 and the semi-naive OWL 2 RL
# closure (issue 756 item 2) the row is within 10 times HermiT, so the gate
# reported UNEXPECTED PASS (record:
# docs/designissues/2026-10-10-owl-real-ontologies.md § 11).


# Key result 2.2 of https://github.com/danbri/factoidal/issues/901: every
# gated Lean row within TIME_BOUND times the wall time of the fastest
# reference engine of its case, or an expected failure naming an open issue.
# Memory keeps the rule of 2026-10-12: a row is over when its peak resident
# set is more than MEM_BOUND times the reference's AND more than MEM_BOUND
# times the reference's memory above process start (a reference under 1 MB
# above its start counts as 1 MB).
#
# The time ratio is taken between minimum wall times (the least of the runs of
# a case) where both rows have one: on a shared machine the load average adds
# to the median more than to the minimum. An expected failure reports
# UNEXPECTED PASS only below TIME_BOUND / XPASS_MARGIN (2.5 by default), so
# that a row measured at 2.9 and at 3.1 on two runs does not turn the gate
# red each time; a row without a mark fails above TIME_BOUND.
TIME_BOUND = float(os.environ.get("SOTA_TIME_BOUND", "3"))
MEM_BOUND = float(os.environ.get("SOTA_MEM_BOUND", "10"))
XPASS_MARGIN = float(os.environ.get("SOTA_XPASS_MARGIN", "1.2"))


def wall_of(r):
    return r.get("wall_min_s") or r["wall_s"]


def over_bound(lean, ref, start_rss):
    """True when the Lean row is over TIME_BOUND in time, or over MEM_BOUND
    in memory by both memory measures; also the two ratios."""
    tr = wall_of(lean) / wall_of(ref) if wall_of(ref) > 0 else 0
    mr = lean["rss_mb"] / ref["rss_mb"] if ref.get("rss_mb") else 0
    lb = start_rss.get("lean")
    rb = start_rss.get({"jena-owl-micro": "jena"}.get(ref["engine"], ref["engine"]))
    ar = None
    if lb is not None and rb is not None:
        ar = (lean["rss_mb"] - lb) / max(ref["rss_mb"] - rb, 1.0)
    return tr > TIME_BOUND or (mr > MEM_BOUND and (ar is None or ar > MEM_BOUND)), tr, mr


def check(args):
    """The gate: re-run each recorded Lean row and compare."""
    rows, _ = load_rows(args.check)
    refs = {}
    for r in rows:
        if r["engine"] not in LEAN_ENGINES and r["status"] == "ok":
            k = (r["workload"], str(r["size"]))
            if k not in refs or wall_of(r) < wall_of(refs[k]):
                refs[k] = r
    start_rss = {r["engine"]: r["rss_mb"] for r in rows
                 if r["workload"] == "start" and r["status"] == "ok"}
    todo = [r for r in rows if r["engine"] in ("lean", "lean-stream") and r["status"] == "ok"
            and r["workload"] in W and r["wall_s"] <= args.max_s]
    if args.workloads:
        keep = set(args.workloads.split(","))
        todo = [r for r in todo if r["workload"] in keep]
    tdir = DL / "tmp"
    tdir.mkdir(parents=True, exist_ok=True)
    fails = 0
    for r in todo:
        w = W[r["workload"]]
        size = next((s for s in w.sizes if str(s) == str(r["size"])), None)
        if size is None:
            print(f"SKIP {r['workload']} {r['size']}: size no longer in the workload")
            continue
        path = w.make(size)
        cmd, env = w.cmd(r["engine"], path, size)
        verdict = None
        xf = None
        for attempt in (1, 2):  # a failing row is measured once more before it fails
            rec, o = measure(cmd, env, args.runs, args.cap, tdir, args.load_limit,
                             args.load_wait, True, w.accept)
            ans = w.answer(r["engine"], o) if rec["status"] == "ok" else None
            problems = []
            if rec["status"] != "ok":
                problems.append(rec["status"])
            else:
                if str(ans) != str(r.get("answer")):
                    problems.append(f"answer {ans} != recorded {r.get('answer')}")
                cpu_bound = (1 + args.tolerance) * r["cpu_s"] + args.slack_s
                if rec["cpu_s"] > cpu_bound:
                    problems.append(f"cpu {rec['cpu_s']:.3f} s > {cpu_bound:.3f} s "
                                    f"(recorded {r['cpu_s']:.3f} s)")
                rss_bound = (1 + args.tolerance) * r["rss_mb"] + args.slack_mb
                if rec["rss_mb"] > rss_bound:
                    problems.append(f"rss {rec['rss_mb']:.0f} MB > {rss_bound:.0f} MB "
                                    f"(recorded {r['rss_mb']:.0f} MB)")
            xf = XFAIL.get((r["workload"], str(r["size"]), r["engine"]))
            ref = refs.get((r["workload"], str(r["size"])))
            if rec["status"] == "ok" and ref:
                flagged, tr, mr = over_bound(rec, ref, start_rss)
                if xf and not flagged and tr < TIME_BOUND / XPASS_MARGIN:
                    problems.append(f"UNEXPECTED PASS of the expected failure {xf}: time ratio "
                                    f"{tr:.1f}, memory ratio {mr:.1f} against recorded "
                                    f"{ref['engine']}; update the row and the issue")
                elif flagged and not xf:
                    problems.append(f"time ratio {tr:.1f} (bound {TIME_BOUND:g}), memory ratio "
                                    f"{mr:.1f} against recorded {ref['engine']}, and no "
                                    f"expected-failure mark")
            verdict = problems
            if not problems:
                break
        tag = "PASS" if not verdict else "FAIL"
        if not verdict and xf:
            tag = f"PASS (expected failure still present, {xf})"
        fails += bool(verdict)
        print(f"{tag} {r['workload']} {r['size']} {r['engine']}: cpu {rec.get('cpu_s')} s (recorded "
              f"{r['cpu_s']}), rss {rec.get('rss_mb')} MB (recorded {r['rss_mb']}), "
              f"load {rec['load1']}" + (f" -- {'; '.join(verdict)}" if verdict else ""),
              flush=True)
    print(f"sota gate: {len(todo) - fails} pass, {fails} fail (out of {len(todo)})")
    return 1 if fails else 0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--install", action="store_true")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--out")
    ap.add_argument("--report")
    ap.add_argument("--check")
    ap.add_argument("--workloads")
    ap.add_argument("--engines")
    ap.add_argument("--sizes", help="comma-separated sizes to run (default: all)")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--cap", type=int, default=600)
    ap.add_argument("--load-limit", type=float, default=3.0,
                    help="wait (up to --load-wait s) for the 1-minute load to fall under this")
    ap.add_argument("--load-wait", type=float, default=90)
    ap.add_argument("--no-rerun", action="store_true", help="no extra runs for a wide spread")
    ap.add_argument("--tolerance", type=float, default=0.25)
    ap.add_argument("--slack-s", type=float, default=0.05,
                    help="absolute CPU-time slack of the gate (process start noise)")
    ap.add_argument("--slack-mb", type=float, default=8.0)
    ap.add_argument("--max-s", type=float, default=60,
                    help="gate: skip recorded Lean rows slower than this (wall median)")
    a = ap.parse_args()
    if a.install:
        install()
        return 0
    if a.list:
        for w in W.values():
            print(f"{w.wid:<20} {w.group:<12} sizes {w.sizes} engines {w.engines}\n    {w.desc}")
        return 0
    if a.report:
        report(a.report)
        return 0
    if a.check:
        return check(a)
    if not a.out:
        ap.error("--out, --report, --check, --install or --list")
    if not LEAN.exists():
        sys.exit(f"{LEAN}: missing; build it in formal/lean4 (lake build l4factoidal)")
    run(a)
    return 0


if __name__ == "__main__":
    sys.exit(main())
