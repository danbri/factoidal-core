#!/usr/bin/env python3
"""Read the TSV files of a counting build (leanprof.h): allocations, reference-count operations and
copied bytes, by kind, by constructor shape and by C function.
  leancount.py RUN.tsv [--base BASE.tsv] [--top N] [--scale K]   (counts of RUN less BASE, divided by K)"""
import collections, csv, re, sys
SHAPES = {(3,0,8):'Value.num', (2,0,1):'Value.bool', (4,1,0):'Value.str', (5,1,0):'Value.obj', (6,1,0):'Value.sym',
  (7,1,0):'Value.big', (0,4,1):'Obj', (0,6,0):'Env', (0,1,3):'PropV.data', (1,2,2):'PropV.acc', (0,5,1):'Ctx',
  (0,8,16):'HeapOf', (0,3,0):'PropMap or 3-tuple', (0,2,0):'pair / EStateM.Result.ok', (1,2,0):'List.cons / Result.error',
  (1,1,0):'Option.some / Kind.array', (0,1,2):'Binding', (2,6,0):'Kind.closure', (3,0,1):'ctor(3,0,1)'}
ALLOC = ('ctor','closure','box-float','box-uint64','array-new','array-grow','array-copy','string-new','string-grow','string-copy','floatarray-grow','floatarray-copy')
COPY = ('array-grow','array-copy','string-grow','string-copy','floatarray-grow','floatarray-copy')
def load(p):
    d = collections.Counter(); b = collections.Counter()
    for r in csv.reader(open(p), delimiter='\t'):
        k = (r[0], r[1], int(r[2]), int(r[3]), int(r[4])); d[k] += int(r[5]); b[k] += int(r[6])
    return d, b
def diff(run, base=None, scale=1.0):
    d, b = load(run)
    if base:
        d0, b0 = load(base)
        for k in d0: d[k] -= d0[k]; b[k] -= b0[k]
    return {k: v / scale for k, v in d.items()}, {k: v / scale for k, v in b.items()}
def short(fn): return re.sub(r'___redArg|___lam__\d+|_spec__\d+|___at_.*', '', re.sub(r'^(lp_l4factoidal_)?(L4Factoidal_)?', '', fn))
def summary(d, b):
    s = collections.Counter()
    for k, v in d.items():
        kind = k[1]
        if kind in ALLOC: s['allocs'] += v; s['alloc_bytes'] += b[k]
        if kind in COPY: s['copies'] += v; s['copy_bytes'] += b[k]
        if kind.startswith('rc-'): s['rc'] += v
    return s
def shape_name(k):
    if k[1] == 'ctor': return SHAPES.get(k[2:], 'ctor%s' % (k[2:],))
    return k[1]
if __name__ == '__main__':
    a = sys.argv[1:]; base = None; top = 25; scale = 1.0
    if '--base' in a: base = a[a.index('--base') + 1]
    if '--top' in a: top = int(a[a.index('--top') + 1])
    if '--scale' in a: scale = float(a[a.index('--scale') + 1])
    d, b = diff(a[0], base, scale); s = summary(d, b)
    print('allocations %.0f  bytes %.0f  rc ops %.0f  copies %.0f  copied bytes %.0f' % (s['allocs'], s['alloc_bytes'], s['rc'], s['copies'], s['copy_bytes']))
    bs = collections.Counter(); bb = collections.Counter()
    for k, v in d.items():
        if k[1] in ALLOC: bs[shape_name(k)] += v; bb[shape_name(k)] += b[k]
    print('-- allocations by shape (count, % of allocations, bytes)')
    for n, v in bs.most_common(top): print('  %12.0f %5.1f%% %12.0f  %s' % (v, 100 * v / max(s['allocs'], 1), bb[n], n))
    bf = collections.Counter(); bfb = collections.Counter(); rf = collections.Counter()
    for k, v in d.items():
        if k[1] in ALLOC: bf[short(k[0])] += v; bfb[short(k[0])] += b[k]
        if k[1].startswith('rc-'): rf[short(k[0])] += v
    print('-- allocations by function')
    for n, v in bf.most_common(top): print('  %12.0f %5.1f%% %12.0f  %s' % (v, 100 * v / max(s['allocs'], 1), bfb[n], n))
    print('-- rc ops by function')
    for n, v in rf.most_common(top): print('  %12.0f %5.1f%%  %s' % (v, 100 * v / max(s['rc'], 1), n))
    print('-- top sites (function, shape)')
    fs = collections.Counter()
    for k, v in d.items():
        if k[1] in ALLOC: fs[(short(k[0]), shape_name(k))] += v
    for (f, n), v in fs.most_common(top): print('  %12.0f %5.1f%%  %-40s %s' % (v, 100 * v / max(s['allocs'], 1), f, n))
