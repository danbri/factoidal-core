#!/usr/bin/env python3
"""Collect the three-engine benchmark results and print markdown tables.

Usage: report.py RESULTS-DIR DATASET...

Reads machine.json, pack-<ds>.json/.log, sbm11-size-<ds>.txt,
virtuoso-load-<ds>.json, answers-<ds>.json and timing-<ds>.json from
RESULTS-DIR; writes RESULTS-DIR/results.json (everything, machine-readable)
and prints the tables of docs/designissues/2026-10-12-three-engine-benchmark.md.
"""
import json
import os
import re
import sys


def load(path):
    try:
        return json.load(open(path))
    except (OSError, ValueError):
        return None


def fmt(x, nd=1):
    if x is None:
        return "-"
    if isinstance(x, (int,)) and not isinstance(x, bool):
        return f"{x:,}"
    return f"{x:,.{nd}f}"


def mb(b):
    return "-" if b is None else f"{b / 1e6:,.1f}"


def main():
    res, datasets = sys.argv[1], sys.argv[2:]
    out = {"machine": load(os.path.join(res, "machine.json")),
           "slice": load(os.path.join(res, "slice-stats.json")), "datasets": {}}
    print("## Load\n")
    print("| Dataset | Engine | load s | peak RSS MB | on-disk MB | triples | load avg before / after |")
    print("| --- | --- | ---: | ---: | ---: | ---: | --- |")
    for ds in datasets:
        d = out["datasets"].setdefault(ds, {})
        pk = load(os.path.join(res, "pack-%s.json" % ds))
        logp = os.path.join(res, "pack-%s.log" % ds)
        log = open(logp).read() if os.path.exists(logp) else ""
        size = None
        try:
            size = int(open(os.path.join(res, "sbm11-size-%s.txt" % ds)).read())
        except (OSError, ValueError):
            pass
        rows = re.search(r"spo blocks=\d+ rows=(\d+)", log)
        la = re.findall(r"loadavg_(?:before|after) ([0-9.]+)", log)
        d["sbm11_pack"] = {"rusage": pk, "disk_bytes": size,
                           "quads": int(rows.group(1)) if rows else None, "loadavg": la}
        if pk:
            print(f"| {ds} | SBM11 l4sbm11-pack (4 workers) | {pk['wall_ms'] / 1000:,.1f} | "
                  f"{pk['maxrss_kb'] / 1024:,.0f} | {mb(size)} | {fmt(d['sbm11_pack']['quads'])} | "
                  f"{' / '.join(la)} |")
        vl = load(os.path.join(res, "virtuoso-load-%s.json" % ds))
        d["virtuoso_load"] = vl
        if vl:
            print(f"| {ds} | Virtuoso ld_dir + rdf_loader_run (1 loader) + checkpoint | "
                  f"{vl['load_ms'] / 1000:,.1f} | {vl['peak_rss_kb'] / 1024:,.0f} | "
                  f"{mb(vl['disk_bytes'])} | {fmt(vl['triples'])} | "
                  f"{vl['loadavg_before']} / {vl['loadavg_after']} |")
    for ds in datasets:
        d = out["datasets"][ds]
        ans = load(os.path.join(res, "answers-%s.json" % ds))
        d["answers"] = ans
        if not ans:
            continue
        print(f"\n## Answers, {ds}\n")
        print(f"Equal on every engine: {len(ans['equal'])} of {len(ans['queries'])}; "
              f"different: {len(ans['different'])} ({', '.join(ans['different']) or 'none'}).\n")
        print("| Query | SBM11 path | rows SBM11 | rows Virtuoso | rows QLever (oracle) | result |")
        print("| --- | --- | ---: | ---: | ---: | --- |")
        for name, r in sorted(ans["queries"].items()):
            rw = r.get("rows", {})
            bad = [k for k, c in r.get("comparisons", {}).items() if not c["equal"]]
            print(f"| {name} | {r['sbm11_none'].get('path')} | {fmt(rw.get('sbm11_none'))} | "
                  f"{fmt(rw.get('virtuoso'))} | {fmt(rw.get('qlever'))} | "
                  f"{'equal' if r['all_equal'] else 'differs: ' + ', '.join(bad)} |")
    for ds in datasets:
        d = out["datasets"][ds]
        t = load(os.path.join(res, "timing-%s.json" % ds))
        d["timing"] = t
        if not t or "summary" not in t:
            continue
        print(f"\n## Timing, {ds}\n")
        print(f"Rounds {t['rounds']} (warm), cold rounds {t['cold_rounds']}, SBM11 --repeat "
              f"{t['repeat']}. Excluded (answers differ): {', '.join(t['excluded']) or 'none'}.\n")
        for ph in t["phases"]:
            las = [r["loadavg"] for r in ph["rounds"]] + [r["loadavg"] for r in ph["cold"]]
            print(f"Virtuoso thread config `{ph['virtuoso_threads']}`: 1-minute load average at "
                  f"round start {min(las):.2f} to {max(las):.2f}.\n")
        print("| Query | SBM11 none cold / process / warm ms | RSS MB | SBM11 merkle cold / process / warm ms | RSS MB "
              "| Virtuoso 1t cold / warm ms | RSS MB | Virtuoso default cold / warm ms | RSS MB |")
        print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
        by = {}
        for row in t["summary"]:
            by.setdefault(row["query"], {})[row["virtuoso_threads"]] = row
        for name in t["queries"]:
            r1 = by.get(name, {}).get("1t", {})
            rd = by.get(name, {}).get("default", {})
            sn = r1.get("sbm11_none", {})
            sm = r1.get("sbm11_merkle", {})
            v1 = r1.get("virtuoso", {})
            vd = rd.get("virtuoso", {})

            def kb(x):
                return "-" if not x else f"{x / 1024:,.0f}"
            print(f"| {name} | {fmt(sn.get('cold_ms'))} / {fmt(sn.get('process_ms'))} / {fmt(sn.get('warm_ms'), 2)} | "
                  f"{kb(sn.get('maxrss_kb'))} | {fmt(sm.get('cold_ms'))} / {fmt(sm.get('process_ms'))} / "
                  f"{fmt(sm.get('warm_ms'), 2)} | {kb(sm.get('maxrss_kb'))} | {fmt(v1.get('cold_ms'))} / "
                  f"{fmt(v1.get('warm_ms'), 2)} | {kb(v1.get('maxrss_kb'))} | {fmt(vd.get('cold_ms'))} / "
                  f"{fmt(vd.get('warm_ms'), 2)} | {kb(vd.get('maxrss_kb'))} |")
    json.dump(out, open(os.path.join(res, "results.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
