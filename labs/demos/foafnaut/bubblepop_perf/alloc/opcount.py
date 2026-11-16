#!/usr/bin/env python3
"""Allocations, bytes and reference-count operations of one JavaScript operation: the opcost.py loop bodies
run on a counting build at N and 5N; the slope per iteration, less the empty loop's.
  opcount.py OPCOST_DIR COUNT_BINARY OUT.json     (OPCOST_DIR: the directory of opcost.py, one up from here)"""
import importlib.util, json, os, subprocess, sys, tempfile, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leancount
src = open(os.path.join(sys.argv[1], 'opcost.py')).read(); src = src[src.index('OPS = {'):src.index('BIG = re.compile')]
class oc: pass
ns = {}; exec(src, ns); oc.OPS = ns['OPS']; oc.CLOSURE_OPS = ns['CLOSURE_OPS']; oc.TEMPLATE = ns['TEMPLATE']; oc.INNER = ns['INNER']
def _script(tmp, op, n):
    path = os.path.join(tmp, '%s-%d.js' % (op, n))
    open(path, 'w').write(oc.TEMPLATE % (n, oc.INNER if op in oc.CLOSURE_OPS else '', oc.OPS[op])); return path
oc.script = _script
binary = sys.argv[2]; N = 20000; tmp = tempfile.mkdtemp()
def counts(op, n):
    p = oc.script(tmp, op, n); out = os.path.join(tmp, 'c.tsv')
    r = subprocess.run([binary, 'run', p], env=dict(os.environ, LEANPROF_OUT=out), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if r.returncode != 0: return None
    return leancount.load(out)
def slope(op):
    a = counts(op, N); c = counts(op, 5 * N)
    if not a or not c: return None
    d = {k: (c[0][k] - a[0].get(k, 0)) / (4.0 * N) for k in c[0]}; b = {k: (c[1][k] - a[1].get(k, 0)) / (4.0 * N) for k in c[1]}
    s = leancount.summary(d, b); sh = collections.Counter()
    for k, v in d.items():
        if k[1] in leancount.ALLOC and v > 0.01: sh['%s@%s' % (leancount.shape_name(k), leancount.short(k[0]))] += v
    return {'allocs': s['allocs'], 'bytes': s['alloc_bytes'], 'rc': s['rc'], 'copy_bytes': s['copy_bytes'], 'shapes': dict(sh)}
res = {}
for op in oc.OPS:
    res[op] = slope(op)
be = res['base_empty']; bc = res['base_closure']
print('%-16s %7s %7s %7s %7s  %s' % ('op', 'allocs', 'bytes', 'rc', 'copyB', 'what is allocated (per iteration)'))
for op, r in res.items():
    if r is None: print('%-16s failed' % op); continue
    b = bc if op in oc.CLOSURE_OPS and op != 'base_closure' else be
    if op in ('base_empty', 'base_closure'): b = {'allocs': 0, 'bytes': 0, 'rc': 0, 'copy_bytes': 0, 'shapes': {}}
    sh = {k: v - b['shapes'].get(k, 0) for k, v in r['shapes'].items()}
    desc = ', '.join('%.0f %s' % (v, k) for k, v in sorted(sh.items(), key=lambda x: -x[1]) if v > 0.4)
    r['net'] = {'allocs': r['allocs'] - b['allocs'], 'bytes': r['bytes'] - b['bytes'], 'rc': r['rc'] - b['rc'], 'copy_bytes': r['copy_bytes'] - b['copy_bytes'], 'what': desc}
    print('%-16s %7.1f %7.0f %7.1f %7.0f  %s' % (op, r['net']['allocs'], r['net']['bytes'], r['net']['rc'], r['net']['copy_bytes'], desc[:230]))
json.dump(res, open(sys.argv[3], 'w'), indent=1)
