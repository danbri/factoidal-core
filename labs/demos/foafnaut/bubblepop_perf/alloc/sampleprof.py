#!/usr/bin/env python3
"""Where a macOS sample(1) profile spends its time on memory management.

Each self sample of the call tree is put in a class by its leaf symbol (alloc, free, tls: a thread-local lookup
reached from an allocation, rc: the slow paths of reference counting, copy, engine: a function of the Lean
program, runtime, other) and charged to the nearest enclosing engine function.

  sampleprof.py FILE [--top N] [--under REGEX] [--symbols DYLIB] [--mem-owners]
    --under REGEX     count only samples below a frame that matches (e.g. 'L4Factoidal_JS_|Hosts_LeanJS': script turns)
    --symbols DYLIB   name '???' frames of libweb-render.dylib from its symbol table (sample(1) leaves them
                      unnamed when the process ended before the sampling did)
    --mem-owners      one list: alloc + free + tls + rc + copy samples by enclosing engine function

Take a profile with:  sample PID SECONDS 1 -mayDie -file FILE   (1 ms interval).
Waiting threads (kevent, __ulock_wait and the like) are left out. Inlined fast paths of the allocator count as
engine time, so the memory-management share is a lower bound."""
import re, sys, collections
path = sys.argv[1]; top = 25
if '--top' in sys.argv: top = int(sys.argv[sys.argv.index('--top')+1])
under = re.compile(sys.argv[sys.argv.index('--under')+1]) if '--under' in sys.argv else None
line_re = re.compile(r'^([ +!:|]*)(\d+)\s+(.+?)\s+\(in ([^)]+)\)')
def klass(sym):
    s = sym
    if re.search(r'__ulock_wait|kevent|__psynch_cvwait|mach_msg|__semwait|__workq_kernreturn|start_wqthread|__select|__read_nocancel|poll$', s): return 'idle'
    if '_tlv_get_addr' in s or 'tlv_' in s: return 'tls'
    if 'heartbeat' in s: return 'heartbeat'
    if re.search(r'mi_|_mi_|malloc|calloc|realloc|lean_alloc|alloc_small|alloc_object|mi_heap', s) and 'free' not in s: return 'alloc'
    if re.search(r'free|lean_del|del_core|dealloc', s): return 'free'
    if re.search(r'lean_dec_ref|lean_inc_ref|dec_ref_cold|inc_ref_cold|lean_mark_', s): return 'rc'
    if re.search(r'memmove|memcpy|bcopy|copy_expand|lean_copy|array_copy|ensure_exclusive', s): return 'copy'
    if re.search(r'memset|bzero', s): return 'zero'
    if re.search(r'mpz|__gmp|lean_nat_big|lean_int_big', s): return 'bignum'
    if re.search(r'^l_|^L4|^lp_|^_?initialize_|^l4', s): return 'engine'
    if re.search(r'lean_', s): return 'runtime'
    return 'other'
import bisect, subprocess
symtab = None
if '--symbols' in sys.argv:
    out = subprocess.run(['nm', '-n', sys.argv[sys.argv.index('--symbols')+1]], capture_output=True, text=True).stdout
    symtab = sorted((int(p[0], 16), p[2].lstrip('_') if p[2].startswith('_l') else p[2][1:] if p[2].startswith('_') else p[2]) for p in (l.split() for l in out.splitlines()) if len(p) == 3 and p[1] in 'tT')
    addrs = [a for a, _ in symtab]
off_re = re.compile(r'load address 0x[0-9a-f]+ \+ 0x([0-9a-f]+)')
def resolve(ln, sym, img):
    if sym != '???': return sym
    if img == 'libdyld.dylib': return 'tlv_unsymbolicated'
    if symtab and img == 'libweb-render.dylib':
        m = off_re.search(ln)
        if m:
            i = bisect.bisect_right(addrs, int(m.group(1), 16)) - 1
            if i >= 0: return symtab[i][1]
    return sym
rows = []; in_tree = False
for ln in open(path, errors='replace'):
    if ln.startswith('Call graph:'): in_tree = True; continue
    if in_tree and (ln.startswith('Total number in stack') or ln.startswith('Sort by top of stack')): break
    if not in_tree: continue
    m = line_re.match(ln)
    if not m: continue
    rows.append((len(m.group(1)), int(m.group(2)), resolve(ln, m.group(3), m.group(4))))
tot = collections.Counter(); by = collections.defaultdict(collections.Counter); selfeng = collections.Counter()
stack = []
for i, (d, n, sym) in enumerate(rows):
    while stack and stack[-1][0] >= d: stack.pop()
    kids = 0; j = i + 1
    while j < len(rows) and rows[j][0] > d:
        if rows[j][0] == d + 2 or (rows[j][0] > d and all(rows[k][0] > rows[j][0] - 1 or k == j for k in range(i+1, j+1)) and rows[j][0] == min(r[0] for r in rows[i+1:j+1])): pass
        j += 1
    # direct children: rows in (i, j) with minimal depth
    if j > i + 1:
        md = min(r[0] for r in rows[i+1:j])
        kids = sum(r[1] for r in rows[i+1:j] if r[0] == md)
    selfn = n - kids
    stack.append((d, sym))
    if selfn <= 0: continue
    if under and not any(under.search(x) for _, x in stack): continue
    k = klass(sym)
    owner = next((s for _, s in reversed(stack) if klass(s) == 'engine'), '(none)')
    tot[k] += selfn
    if k == 'engine': selfeng[sym] += selfn
    if k in ('other','runtime'): by['_'+k][sym] += selfn
    else: by[k][owner] += selfn
tot.pop('idle', None)
N = sum(tot.values())
if '--mem-owners' in sys.argv:
    agg = collections.Counter()
    for k in ('alloc', 'free', 'tls', 'rc', 'copy'):
        for o, v in by[k].items(): agg[o] += v
    print('samples', N, ' memory-management samples', sum(agg.values()))
    for o, v in agg.most_common(top): print('  %6d %5.1f%%  %s' % (v, 100.0 * v / N, re.sub(r'^(lp_l4factoidal_)?(L4Factoidal_)?', '', o)[:100]))
    sys.exit(0)
print('samples', N)
for k, v in tot.most_common(): print('  %-8s %7d  %5.1f%%' % (k, v, 100.0 * v / N))
short = lambda s: re.sub(r'^l_L4Factoidal_', '', s)[:90]
for k in ('alloc', 'free', 'rc', 'copy', 'tls'):
    print('--', k, 'by enclosing engine function')
    for s, v in by[k].most_common(top): print('  %6d %5.1f%%  %s' % (v, 100.0 * v / N, short(s)))
for k in ('_other','_runtime'):
    print('--', k, 'leaf symbols')
    for s_, v in by[k].most_common(top): print('  %6d %5.1f%%  %s' % (v, 100.0 * v / N, s_[:90]))
print('-- engine self')
for s, v in selfeng.most_common(top): print('  %6d %5.1f%%  %s' % (v, 100.0 * v / N, short(s)))
