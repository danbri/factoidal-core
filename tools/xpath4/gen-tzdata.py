#!/usr/bin/env python3
"""Generate formal/lean4/L4Factoidal/XPath4/TzData.lean from the system IANA
time zone database (Python zoneinfo over /usr/share/zoneinfo).

Usage: python3 tools/xpath4/gen-tzdata.py > formal/lean4/L4Factoidal/XPath4/TzData.lean

For every zone the generator finds the instants in 1900..2100 at which the
(UTC offset, abbreviation) pair changes (sampling every two days, then
bisecting to the second) and writes a compact table. Zones with identical
tables share one table. See the header of the output for the format.
"""
import sys, os, zoneinfo
from datetime import datetime, timedelta, timezone

EPOCH = datetime(1970, 1, 1, tzinfo=timezone.utc)
START = int((datetime(1900, 1, 1, tzinfo=timezone.utc) - EPOCH).total_seconds())
END = int((datetime(2100, 1, 1, tzinfo=timezone.utc) - EPOCH).total_seconds())
STEP = 2 * 86400

def b36(n):
    d = "0123456789abcdefghijklmnopqrstuvwxyz"
    if n == 0:
        return "0"
    s = ""
    while n:
        s = d[n % 36] + s
        n //= 36
    return s

def version():
    root = "/usr/share/zoneinfo"
    for f in ("tzdata.zi", "+VERSION"):
        p = os.path.join(root, f)
        if os.path.exists(p):
            with open(p) as fh:
                l = fh.readline().strip()
            return l.replace("# version ", "") if f == "tzdata.zi" else l
    return "unknown"

def state(zi, ts):
    dt = (EPOCH + timedelta(seconds=ts)).astimezone(zi)
    return (int(dt.utcoffset().total_seconds()), dt.tzname())

def table(name):
    zi = zoneinfo.ZoneInfo(name)
    s0 = state(zi, START)
    states = [s0]
    trans = []
    prev, prev_ts = s0, START
    ts = START + STEP
    while ts <= END:
        s = state(zi, ts)
        if s != prev:
            lo, hi = prev_ts, ts           # state(lo)==prev, state(hi)!=prev
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if state(zi, mid) == prev:
                    lo = mid
                else:
                    hi = mid
            # a second change inside the step is resolved by the next sample
            sh = state(zi, hi)
            if sh not in states:
                states.append(sh)
            trans.append((hi, states.index(sh)))
            prev, prev_ts = sh, hi
            ts = hi + STEP
            continue
        prev_ts = ts
        ts += STEP
    st = ";".join("%d,%s" % (o, a) for o, a in states)
    last = START
    tk = []
    for t, i in trans:
        tk.append("%s.%s" % (b36(t - last), b36(i)))
        last = t
    return st + "|" + " ".join(tk)

def main():
    names = sorted(n for n in zoneinfo.available_timezones()
                   if n not in ("Factory", "localtime") and not n.startswith("posix"))
    tables, index, assign = [], {}, []
    for n in names:
        t = table(n)
        if t not in index:
            index[t] = len(tables)
            tables.append(t)
        assign.append((n, index[t]))
    out = []
    out.append("/-")
    out.append("L4Factoidal.XPath4.TzData: GENERATED FILE, do not edit.")
    out.append("")
    out.append("IANA time zone database version %s, from /usr/share/zoneinfo." % version())
    out.append("Generator: python3 tools/xpath4/gen-tzdata.py > formal/lean4/L4Factoidal/XPath4/TzData.lean")
    out.append("")
    out.append("`tzZoneIndex` has one line `Zone/Name=k` per zone and link; `tzTables[k]` is")
    out.append("`states|transitions`. `states` is `;`-separated `offsetSeconds,abbreviation`;")
    out.append("state 0 applies before the first transition. `transitions` is a space-separated")
    out.append("list of `D.S`: D is the number of seconds, base 36, since the previous")
    out.append("transition (the first: since 1900-01-01T00:00:00Z), and S is the state index, base 36,")
    out.append("that applies from that instant on. Transitions cover 1900 to 2100; the last state")
    out.append("applies after the last transition. A zone whose rules continue past 2100 keeps the state")
    out.append("in force at the end of 2099.")
    out.append("-/")
    out.append("namespace L4Factoidal.XPath4")
    out.append("")
    out.append("def tzDataVersion : String := \"%s\"" % version())
    out.append("")
    out.append("/-- Seconds since the Unix epoch of 1900-01-01T00:00:00Z (negative). -/")
    out.append("def tzBase : Int := %d" % START)
    out.append("")
    out.append("def tzZoneIndex : String :=")
    out.append('  "' + "\\n".join("%s=%d" % a for a in assign) + '"')
    out.append("")
    out.append("def tzTables : Array String := #[")
    out.append(",\n".join('  "%s"' % t for t in tables))
    out.append("]")
    out.append("")
    out.append("end L4Factoidal.XPath4")
    sys.stdout.write("\n".join(out) + "\n")

main()
