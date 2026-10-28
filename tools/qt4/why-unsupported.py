#!/usr/bin/env python3
"""Count, per qt4tests dependency, the test cases that it makes
`unsupported` in the l4qt4 runner, for XPath 4.0 and XQuery 4.0 mode.

    python3 tools/qt4/why-unsupported.py [ROOT] [--features a,b,...]

ROOT is the vendored qt4tests (default third_party/testing/qt4tests).
Only test cases whose `spec` dependency admits the mode are counted (an
XQuery-only case is scored in XQuery mode).  The rules copy `depOk` and
`featureSupportedIn` of formal/lean4/Harness/Qt4Run.lean; pass
`--features` to name the features the runner supports, if they differ.
A case with more than one failing dependency is counted under each one
(column "all") and under the first one in document order (column
"first").  The script reads the XML files only; it runs no test.
"""
import sys, os, collections
import xml.etree.ElementTree as ET

NS = "{http://www.w3.org/2010/09/qt-fots-catalog}"
args = [a for a in sys.argv[1:]]
feats = {"higherOrderFunctions", "serialization", "simple-uca-fallback",
         "advanced-uca-fallback", "binary", "expath-file", "schemaImport",
         "schemaValidation", "typedData", "non_unicode_codepoint_collation",
         "arbitraryPrecisionDecimal", "dtd-validation-option", "xinclude-option"}
xp_only = {"namespace-axis", "xpath-1.0-compatibility"}
settings = {"dtd-validation-option", "xinclude-option"}  # may also be absent (configureFor)
if "--features" in args:
    i = args.index("--features"); feats = set(args[i + 1].split(",")); del args[i:i + 2]
root = args[0] if args else "third_party/testing/qt4tests"

def spec_ok(v, xq):
    for t in v.split():
        if t.startswith("XQ" if xq else "XP"):
            rest = t[2:]; plus = rest.endswith("+")
            try: k = int(rest[:-1] if plus else rest)
            except ValueError: continue
            if k == 40 or (plus and k <= 40): return True
    return False

def dep_ok(d, xq):
    ty, v = d.get("type"), d.get("value", "")
    sat = d.get("satisfied", "true") != "false"
    if ty == "feature":
        has = lambda f: f in feats or (not xq and f in xp_only)
        a = all(has(f) for f in v.split())
        return a if sat else (not a or all(f in settings for f in v.split()))
    if ty == "xml-version":
        has = any(x == "1.1" or (x.startswith("1.0") and x != "1.0:4-") for x in v.split())
        return has if sat else not has
    if ty == "xsd-version": return (v == "1.1") if sat else (v != "1.1")
    if ty == "language": return (v == "en") if sat else (v != "en")
    if ty == "default-language": return True if sat else v != "en"
    if ty == "unicode-normalization-form":
        ok = v in ("NFC", "NFD", "NFKC", "NFKD", "FULLY-NORMALIZED"); return ok if sat else not ok
    if ty == "limits":
        ok = v in ("big_integer", "year_lt_0"); return ok if sat else not ok
    return not sat

def label(d):
    s = "" if d.get("satisfied", "true") != "false" else "!"
    return f"{s}{d.get('type')}={d.get('value')}"

cat = ET.parse(os.path.join(root, "catalog.xml")).getroot()
env_bad = {}
def env_reason(e):
    for c in e:
        tag = c.tag.replace(NS, "")
        if tag in ("collection", "function-library"): return "env:" + tag
    return None
for e in cat.findall(NS + "environment"):
    r = env_reason(e)
    if r: env_bad[e.get("name")] = r

out = {}
for mode, xq in (("xpath", False), ("xquery", True)):
    first = collections.Counter(); allc = collections.Counter(); applicable = 0
    for ts in cat.findall(NS + "test-set"):
        f = os.path.join(root, ts.get("file"))
        if not os.path.exists(f): continue
        s = ET.parse(f).getroot()
        sdeps = s.findall(NS + "dependency")
        local = {e.get("name"): env_reason(e) for e in s.findall(NS + "environment") if e.get("name")}
        for tc in s.findall(NS + "test-case"):
            deps = tc.findall(NS + "dependency")
            specs = [d for d in deps if d.get("type") == "spec"] or [d for d in sdeps if d.get("type") == "spec"]
            if specs and not any(spec_ok(d.get("value", ""), xq) for d in specs): continue
            applicable += 1
            bad = [label(d) for d in sdeps + deps if d.get("type") != "spec" and not dep_ok(d, xq)]
            env = tc.find(NS + "environment")
            if env is not None:
                r = env.get("ref")
                why = (local[r] if r in local else env_bad.get(r)) if r else env_reason(env)
                if why: bad.append(why)
            if bad:
                first[bad[0]] += 1
                for b in set(bad): allc[b] += 1
    out[mode] = (applicable, first, allc)

keys = sorted(set(out["xpath"][2]) | set(out["xquery"][2]),
              key=lambda k: -(out["xpath"][2][k] + out["xquery"][2][k]))
print(f"applicable cases: XPath {out['xpath'][0]}, XQuery {out['xquery'][0]}")
print(f"{'dependency':45} {'XP all':>7} {'XP first':>8} {'XQ all':>7} {'XQ first':>8}")
for k in keys:
    print(f"{k:45} {out['xpath'][2][k]:7} {out['xpath'][1][k]:8} {out['xquery'][2][k]:7} {out['xquery'][1][k]:8}")
print(f"{'total (first)':45} {'':7} {sum(out['xpath'][1].values()):8} {'':7} {sum(out['xquery'][1].values()):8}")
