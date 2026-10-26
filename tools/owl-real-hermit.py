#!/usr/bin/env python3
"""tools/owl-real-hermit.py — check the verdicts of tools/owl-real-bench.py
against HermiT, an independent OWL 2 DL reasoner.

https://github.com/danbri/factoidal/issues/651 (plan item 4). Record:
docs/designissues/2026-10-10-owl-real-ontologies.md, section 4.

For each ontology directory OUT/<name>/ that owl-real-bench.py wrote (it holds
merged.nt, the input both engines read), this script

  1. writes OUT/<name>/hermit.ttl: merged.nt without its owl:imports triples
     (HermiT would otherwise try to fetch the imports; the benchmark does not
     read them either). N-Triples is Turtle, so the OWL API reads it as such;
  2. runs `HermiT -k` (consistency of owl:Thing, that is, of the ontology);
  3. when consistent, runs `HermiT -c -o OUT/<name>/hermit.tax` (the class
     hierarchy as SubClassOf and EquivalentClasses axioms) and decides each
     entailment pair of OUT/results.jsonl: A rdfs:subClassOf B is entailed iff
     A = B, B is owl:Thing, A is equivalent to owl:Nothing, or B is reachable
     from A over the SubClassOf and EquivalentClasses edges of the taxonomy.
     When HermiT finds the ontology inconsistent, every pair is entailed.

It prints one line per ontology and writes OUT/hermit.jsonl. A pair where the
Lean verdict is `true` and HermiT's is `false` is a soundness defect of the
Lean engine; `false` against `true` is a completeness gap; both are listed.

HermiT is not vendored. The run of 2026-10-10 used HermiT 1.3.8 as shipped in
owlready2 0.51 (`pip install --target DIR owlready2`, then
DIR/owlready2/hermit/HermiT.jar), with OpenJDK 21.

Usage: python3 tools/owl-real-hermit.py OUT --hermit-jar JAR [--cap-s 600]
       [--xmx 3g]

Exit 2 when JAR is not a file or when Java cannot start HermiT from it. Until
2026-10-13 a wrong JAR path gave exit 0 and "HermiT not decided" on every
pair of every ontology, which reads like a slow reasoner, not a setup error.
"""

import argparse
import json
import os
import re
import subprocess
import sys

OWL_THING = "http://www.w3.org/2002/07/owl#Thing"
OWL_NOTHING = "http://www.w3.org/2002/07/owl#Nothing"
IRI_RE = re.compile(r"<([^>]*)>")


def hermit(jar, xmx, cap_s, args):
    cmd = ["timeout", "-s", "KILL", str(cap_s), "java", f"-Xmx{xmx}", "-cp", jar,
           "org.semanticweb.HermiT.cli.CommandLine", "--ignoreUnsupportedDatatypes"] + args
    p = subprocess.run(cmd, capture_output=True, text=True)
    out = p.stdout + "\n" + p.stderr
    return p.returncode, out


def reachable(tax_path):
    edges = {}
    nothing = set()
    with open(tax_path) as f:
        for line in f:
            line = line.strip()
            iris = IRI_RE.findall(line)
            if line.startswith("SubClassOf(") and len(iris) == 2:
                edges.setdefault(iris[0], set()).add(iris[1])
            elif line.startswith("EquivalentClasses(") and len(iris) >= 2:
                for x in iris:
                    for y in iris:
                        if x != y:
                            edges.setdefault(x, set()).add(y)
                if OWL_NOTHING in iris:
                    nothing.update(iris)

    def entailed(a, b):
        if a == b or b == OWL_THING or a in nothing:
            return True
        seen, todo = {a}, [a]
        while todo:
            x = todo.pop()
            for y in edges.get(x, ()):
                if y == b:
                    return True
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        return False
    return entailed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("--hermit-jar", required=True)
    ap.add_argument("--cap-s", type=int, default=600)
    ap.add_argument("--xmx", default="3g")
    a = ap.parse_args()
    if not os.path.isfile(a.hermit_jar):
        print(f"owl-real-hermit: {a.hermit_jar} is not a file", file=sys.stderr)
        return 2
    rows = [json.loads(l) for l in open(os.path.join(a.out, "results.jsonl")) if l.strip()]
    names = []
    for r in rows:
        if r.get("step") == "entails" or r.get("step") == "consistent":
            if r["ontology"] not in names:
                names.append(r["ontology"])
    res_path = os.path.join(a.out, "hermit.jsonl")
    with open(res_path, "w"):
        pass
    for name in names:
        wd = os.path.join(a.out, name)
        merged = os.path.join(wd, "merged.nt")
        if not os.path.exists(merged):
            continue
        ttl = os.path.join(wd, "hermit.ttl")
        with open(merged) as f, open(ttl, "w") as g:
            for line in f:
                if "<http://www.w3.org/2002/07/owl#imports>" not in line:
                    g.write(line)
        rc, out = hermit(a.hermit_jar, a.xmx, a.cap_s, ["-k", ttl])
        if "Could not find or load main class" in out or "Unable to access jarfile" in out:
            print(f"owl-real-hermit: Java cannot start HermiT from {a.hermit_jar}:\n"
                  f"{out.strip()[-300:]}", file=sys.stderr)
            return 2
        if "Inconsistent ontology" in out or "InconsistentOntologyException" in out:
            consistent = False
        elif "owl#Thing is satisfiable" in out:
            consistent = True
        else:
            consistent = None
        lean_cons = next((r.get("verdict") for r in rows
                          if r["ontology"] == name and r.get("step") == "consistent"), None)
        rec = {"ontology": name, "hermit_consistent": consistent, "lean_consistent": lean_cons,
               "hermit_rc": rc, "hermit_tail": out.strip()[-300:] if consistent is None else ""}
        pairs = [r for r in rows if r["ontology"] == name and r.get("step") == "entails"]
        decide = None
        if consistent is True and pairs:
            tax = os.path.join(wd, "hermit.tax")
            rc2, out2 = hermit(a.hermit_jar, a.xmx, a.cap_s, ["-c", "-o", tax, ttl])
            if rc2 == 0 and os.path.exists(tax):
                decide = reachable(tax)
            else:
                rec["hermit_classify_error"] = out2.strip()[-300:]
        elif consistent is False:
            decide = lambda x, y: True  # noqa: E731  everything follows from an inconsistent ontology
        tally = {"agree": 0, "lean_true_hermit_false": [], "lean_false_hermit_true": [],
                 "lean_not_decided": 0, "hermit_not_decided": 0}
        for r in pairs:
            lv = r.get("verdict") if r.get("status") == "ok" else None
            hv = decide(r["sub"], r["super"]) if decide else None
            if hv is None:
                tally["hermit_not_decided"] += 1
            elif lv not in ("true", "false"):
                tally["lean_not_decided"] += 1
            elif (lv == "true") == hv:
                tally["agree"] += 1
            elif lv == "true":
                tally["lean_true_hermit_false"].append([r["pair_kind"], r["sub"], r["super"]])
            else:
                tally["lean_false_hermit_true"].append([r["pair_kind"], r["sub"], r["super"]])
        rec["pairs"] = len(pairs)
        rec.update(tally)
        with open(res_path, "a") as f:
            f.write(json.dumps(rec, sort_keys=True) + "\n")
        print(f"{name:<11} HermiT consistent={consistent} Lean consistent={lean_cons} | "
              f"pairs {len(pairs)}: agree {tally['agree']}, Lean true/HermiT false "
              f"{len(tally['lean_true_hermit_false'])}, Lean false/HermiT true "
              f"{len(tally['lean_false_hermit_true'])}, Lean not decided {tally['lean_not_decided']}, "
              f"HermiT not decided {tally['hermit_not_decided']}", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
