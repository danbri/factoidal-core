#!/usr/bin/env python3
"""tools/bench/sbm11-before-after.py OUT.json BEFORE AFTER GEN:QUERY...

Two `l4sbm11` builds on the same queries, interleaved per query (written for
https://github.com/danbri/factoidal/issues/809; record:
docs/designissues/2026-10-12-sbm11-stage4.md section 11.5). Per query and
binary, all with `--verify none`: warm = execution median of `--repeat 7` in
one process; process = median wall time of 7 processes of one execution each;
RSS = median VmHWM of those 7 processes; rows decoded and blocks read from
`--explain` (the AFTER build must print the `total:` line of issue 809; for
the BEFORE build they are summed from the scan lines); the load average at the
start and end of each query. Prints one line per query and writes OUT.json.
Run it three times and take the median of the rounds, as the record does."""
import json, re, statistics, subprocess, sys, time

if len(sys.argv) < 5:
    sys.exit("usage: sbm11-before-after.py OUT.json BEFORE AFTER GEN:QUERY...")
out_path, before, after = sys.argv[1], sys.argv[2], sys.argv[3]
items = sys.argv[4:]


def load():
    return open("/proc/loadavg").read().split()[0]


def run(binary, gen, q, extra):
    t0 = time.perf_counter()
    p = subprocess.run([binary, "query", gen, "--file", q, "--verify", "none"] + extra,
                       capture_output=True, text=True)
    return (time.perf_counter() - t0) * 1000.0, p


def explain_counts(err, is_after):
    if is_after:
        m = re.search(r"total: rows decoded (\d+).*?join-key values tested (\d+); blocks read (\d+) of (\d+) selected, (\d+) skipped", err)
        if m:
            return {"rows_decoded": int(m.group(1)), "keys_tested": int(m.group(2)),
                    "blocks_read": int(m.group(3)), "blocks_selected": int(m.group(4)),
                    "blocks_skipped": int(m.group(5))}
    rows = 0; blocks = 0; sel = 0
    for line in err.splitlines():
        if not line.startswith("plan:") or "blocks" not in line:
            continue
        m = re.search(r"blocks (\d+) read of (\d+) selected", line)
        if m:
            blocks += int(m.group(1)); sel += int(m.group(2))
        m = re.search(r"; rows (\d+)", line)
        if m:
            rows += int(m.group(1))
    return {"rows_decoded": rows, "keys_tested": 0, "blocks_read": blocks, "blocks_selected": sel,
            "blocks_skipped": 0}


res = []
for item in items:
    gen, q = item.split(":", 1)
    row = {"query": q.rsplit("/", 1)[-1].rsplit(".", 1)[0], "gen": gen, "load_start": load()}
    for name, binary in (("before", before), ("after", after)):
        # warm and explain
        _, p = run(binary, gen, q, ["--repeat", "7", "--explain"])
        m = re.search(r"execution ms median ([0-9.]+) min ([0-9.]+) max ([0-9.]+)", p.stderr)
        warm = float(m.group(1)) if m else None
        counts = explain_counts(p.stderr, name == "after")
        rows = re.search(r"; rows (\d+); verify", p.stderr)
        walls, rss = [], []
        for _ in range(7):
            w, p2 = run(binary, gen, q, [])
            walls.append(w)
            mm = re.search(r"VmHWM\): (\d+) kB", p2.stderr)
            if mm:
                rss.append(int(mm.group(1)))
        row[name] = {"warm_ms": warm, "warm_min_ms": float(m.group(2)) if m else None,
                     "process_ms": statistics.median(walls), "rss_kb": statistics.median(rss) if rss else None,
                     "rows": int(rows.group(1)) if rows else None, **counts}
    row["load_end"] = load()
    res.append(row)
    b, a = row["before"], row["after"]
    print(f"{row['query']}: warm {b['warm_ms']} -> {a['warm_ms']} ms; process {b['process_ms']:.1f} -> {a['process_ms']:.1f} ms; "
          f"rss {b['rss_kb']} -> {a['rss_kb']} kB; rows decoded {b['rows_decoded']} -> {a['rows_decoded']}; "
          f"blocks read {b['blocks_read']} -> {a['blocks_read']}; load {row['load_start']}..{row['load_end']}", flush=True)
json.dump(res, open(out_path, "w"), indent=1)
