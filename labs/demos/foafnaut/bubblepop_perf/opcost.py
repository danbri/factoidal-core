#!/usr/bin/env python3
"""The cost of one JavaScript operation, for each engine named.

Each operation is the body of the loop

    function f(n) { var s = 1, k = 3, a = [...], o = {...}, t = '...'; for (var i = 0; i < n; i++) { BODY } return s; }

`f` makes no function of its own: `g0`, `g1`, `gf` and the method of `o` are top-level functions.
The register machine of BubblePopJS (`JS/Compile.lean`) compiles only a function whose variables
no closure can hold, so a helper function declared inside `f` would put every operation on the
tree-walking evaluator. The three operations that need a closure in `f` (`closure_new`,
`arrow_new`, `call_local`) use a second form of `f` with an inner function, and their cost is
less the empty loop of that form (`base_closure`).

The script runs at N and at 5N iterations. The cost of an operation is the slope of the CPU time
between the two sizes, less the slope of the empty loop (`base_empty`), in nanoseconds. A slope
removes the engine's start and the cost of parsing. CPU time, not wall time: the machine is
often busy. Rounds interleave the engines; the least time of each (engine, operation, size) counts.

  opcost.py [--n N] [--runs R] [--only a,b,...] [--json FILE] NAME=CMD [NAME=CMD ...]
      e.g.  bubblepop='formal/lean4/.lake/build/bin/leanjs run'  qjs=/path/qjs  v8-jitless='node --jitless'
      Each CMD gets the script path as its last argument. Ratios are against the last engine named.

  opcost.py --callgrind [--n N] [--only a,b,...] NAME=CMD
      One engine under `valgrind --tool=callgrind` (exact, slow; default N 20000): for each
      operation the instructions, the heap allocations (`mi_malloc_small` calls of the Lean
      runtime) and the calls into the big number runtime, each for one iteration and less the
      empty loop. A call into the big number runtime on a hot path is a defect to look at: see
      docs/designissues/2026-11-09-foafnaut-perf-exploration.md, "Integers through GMP".

Exit status: 0; 2 for a usage error; 3 when an engine fails on a script.
"""
import collections, json, os, re, resource, shlex, subprocess, sys, tempfile

# name -> the loop body
OPS = {
    'base_empty': '',
    'const_assign': 's = 1;',
    'local_read': 's = k;',
    'add': 's = s + k;',
    'sub': 's = s - k;',
    'mul': 's = s * 1;',
    'div': 's = s / 1;',
    'mod': 's = i % 7;',
    'band': 's = i & 255;',
    'bor': 's = i | 1;',
    'bxor': 's = i ^ 5;',
    'shl': 's = i << 1;',
    'sar': 's = i >> 1;',
    'shr': 's = i >>> 1;',
    'bnot': 's = ~i;',
    'neg': 's = -i;',
    'not': 's = !i;',
    'lt': 's = i < k;',
    'le': 's = i <= k;',
    'eq': 's = i == k;',
    'ne': 's = i != k;',
    'seq': 's = i === k;',
    'sne': 's = i !== k;',
    'typeof': 's = typeof i;',
    'cond': 's = i ? 1 : 2;',
    'and': 's = i && k;',
    'inc_post': 's++;',
    'inc_pre': '++s;',
    'add_assign': 's += k;',
    'if_stmt': 'if (i < 0) s = 2;',
    'block_let': '{ let q = i; s = q; }',
    'try_noop': 'try { s = i; } catch (e) { }',
    'arr_read_const': 's = a[3];',
    'arr_read': 's = a[i & 7];',
    'arr_write': 'a[3] = i;',
    'arr_len': 's = a.length;',
    'prop_read': 's = o.x;',
    'prop_write': 'o.x = i;',
    'prop_read_proto': 's = o.toString;',
    'str_len': 's = t.length;',
    'str_index': 's = t[3];',
    'str_charCodeAt': 's = t.charCodeAt(3);',
    'str_concat_num': "s = 'k' + i;",
    'num_to_str': 's = String(i);',
    'math_floor': 's = Math.floor(i);',
    'call0': 's = g0();',
    'call1': 's = g1(i);',
    'call_method': 's = o.m(i);',
    'base_closure': '',
    'call_local': 's = h1(i);',
    'new_obj': 's = {};',
    'new_obj2': 's = { x: i, y: k };',
    'new_arr': 's = [];',
    'new_arr3': 's = [i, k, 1];',
    'closure_new': 's = function () { return i; };',
    'arrow_new': 's = () => i;',
    'global_read': 's = G;',
    'global_write': 'G = i;',
    'global_fn': 's = gf(i);',
    'global_math': 's = Math;',
    'undefined_read': 's = undefined;',
}

# operations whose `f` holds an inner function (the evaluator runs them on every engine stage)
CLOSURE_OPS = ('base_closure', 'call_local', 'closure_new', 'arrow_new')

TEMPLATE = """if (typeof print === 'undefined') globalThis.print = function () { console.log.apply(console, arguments); };
var N = %d;
var G = 1; function gf(x) { return x; }
function g0() { return 1; } function g1(x) { return x; } function om(x) { return x; }
function f(n) { var s = 1, k = 3, a = [1,2,3,4,5,6,7,8], o = { x: 1, m: om }, t = 'abcdefgh';%s
  for (var i = 0; i < n; i++) { %s } return s; }
var r = f(N); print(typeof r);
"""
INNER = """
  function h1(x) { return x; }"""

BIG = re.compile(r'^(lean_cstr_to_nat|l_Float_ofScientific|lean_int_big_\w+|lean_nat_big_\w+|lean_big_\w+|'
                 r'lean_float_of_nat|l_Float_ofInt|lean_alloc_mpz)$')


def script(tmp, op, n):
    path = os.path.join(tmp, '%s-%d.js' % (op, n))
    with open(path, 'w') as f:
        f.write(TEMPLATE % (n, INNER if op in CLOSURE_OPS else '', OPS[op]))
    return path


def run_cpu(cmd, path):
    """CPU milliseconds (user and system) of one run, or None and the error text."""
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run(cmd + [path], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    if p.returncode != 0:
        return None, p.stderr.decode(errors='replace')[:200]
    return ((r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)) * 1000.0, ''


def short(name):
    return re.sub(r"'\d+$", '', re.sub(r'^lp_l4factoidal_(L4Factoidal_)?', '', name))[:48]


def load_callgrind(path):
    """Total instructions, calls per callee, and calls per (caller, callee) of a callgrind file."""
    names = {}
    total = 0
    calls = collections.Counter()
    edges = collections.Counter()
    cur = callee = pending = None

    def name_of(tok):
        m = re.match(r'\((\d+)\)(?: (.*))?$', tok)
        if not m:
            return tok
        if m.group(2) is not None:
            names[m.group(1)] = m.group(2)
        return names.get(m.group(1), m.group(1))

    for line in open(path, errors='replace'):
        line = line.rstrip('\n')
        if line.startswith('fn='):
            cur = name_of(line[3:])
        elif line.startswith('cfn='):
            callee = name_of(line[4:])
        elif line.startswith('calls='):
            pending = int(line[6:].split()[0])
        elif line and (line[0].isdigit() or line[0] in '+-*'):
            parts = line.split()
            if len(parts) < 2:
                continue
            try:
                ir = int(parts[1])
            except ValueError:
                continue
            if pending is not None:
                calls[callee] += pending
                edges[(cur, callee)] += pending
                pending = None
            else:
                total += ir
    return total, calls, edges


def callgrind(engine, names, n, tmp):
    ename, cmd = engine
    if subprocess.run(['sh', '-c', 'command -v valgrind'], stdout=subprocess.DEVNULL).returncode != 0:
        print('valgrind is not installed', file=sys.stderr)
        return 2
    prof = {}
    for op in ['base_empty', 'base_closure'] + [x for x in names if x not in ('base_empty', 'base_closure')]:
        out = os.path.join(tmp, 'cg.%s.out' % op)
        p = subprocess.run(['valgrind', '--tool=callgrind', '--callgrind-out-file=' + out] + cmd + [script(tmp, op, n)],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if p.returncode != 0 or not os.path.exists(out):
            print('FAIL %s %s: %s' % (ename, op, p.stderr.decode(errors='replace')[-200:]), file=sys.stderr)
            return 3
        prof[op] = load_callgrind(out)
    print('%s, callgrind, N = %d: for one iteration, less the empty loop' % (ename, n))
    print('the empty loop itself: %.0f instructions (with the start of the engine spread over N)'
          % (prof['base_empty'][0] / n))
    print('%-16s %12s %8s   %s' % ('operation', 'instructions', 'allocs', 'calls into the big number runtime (caller -> callee x calls)'))
    rows = []
    for op in names:
        if op in ('base_empty', 'base_closure'):
            continue
        bt, bc, be = prof['base_closure' if op in CLOSURE_OPS else 'base_empty']
        t, c, e = prof[op]
        big = sorted((((e[k] - be[k]) / n, k) for k in e if BIG.match(k[1])), reverse=True)
        big = ['%s -> %s x%.2f' % (short(k[0]), k[1], v) for v, k in big if v > 0.05]
        rows.append(((t - bt) / n, op, (c['mi_malloc_small'] - bc['mi_malloc_small']) / n, big))
    for ins, op, allocs, big in sorted(rows, reverse=True):
        print('%-16s %12.0f %8.1f   %s' % (op, ins, allocs, '; '.join(big) or '-'))
    return 0


def main():
    args = sys.argv[1:]
    n = None
    runs = 3
    only = None
    json_out = None
    cg = False
    engines = []
    while args:
        a = args.pop(0)
        if a == '--n':
            n = int(args.pop(0))
        elif a == '--runs':
            runs = int(args.pop(0))
        elif a == '--only':
            only = args.pop(0).split(',')
        elif a == '--json':
            json_out = args.pop(0)
        elif a == '--callgrind':
            cg = True
        elif '=' in a and not a.startswith('-'):
            name, cmd = a.split('=', 1)
            engines.append((name, shlex.split(cmd)))
        else:
            print(__doc__)
            return 2
    if not engines or (cg and len(engines) != 1):
        print(__doc__)
        return 2
    names = [x for x in OPS if only is None or x in only or x in ('base_empty', 'base_closure')]
    unknown = [x for x in (only or []) if x not in OPS]
    if unknown:
        print('unknown operation: ' + ', '.join(unknown), file=sys.stderr)
        return 2
    with tempfile.TemporaryDirectory() as tmp:
        if cg:
            return callgrind(engines[0], names, n or 20000, tmp)
        n = n or 200000
        sizes = (n, 5 * n)
        best = {}
        for _ in range(runs):
            for ename, cmd in engines:
                for op in names:
                    for size in sizes:
                        t, err = run_cpu(cmd, script(tmp, op, size))
                        if t is None:
                            print('FAIL %s %s: %s' % (ename, op, err), file=sys.stderr)
                            return 3
                        key = (ename, op, size)
                        if key not in best or t < best[key]:
                            best[key] = t
    slope = {(e, op): (best[(e, op, sizes[1])] - best[(e, op, sizes[0])]) * 1e6 / (sizes[1] - sizes[0])
             for e, _ in engines for op in names}
    def base_of(op):
        return 'base_closure' if op in CLOSURE_OPS else 'base_empty'
    cost = {(e, op): slope[(e, op)] - (slope[(e, base_of(op))] if op != base_of(op) else 0)
            for e, _ in engines for op in names}
    first = engines[0][0]
    ref = engines[-1][0]
    print('ns for one operation, less the empty loop (base_empty and base_closure are the loops); N = %d and %d, '
          'least CPU time of %d runs' % (sizes[0], sizes[1], runs))
    head = '%-16s ' % 'operation' + ' '.join('%12s' % e for e, _ in engines)
    if len(engines) > 1:
        head += '  %9s' % ('%s/%s' % (first[:4], ref[:4]))
    print(head)
    for op in sorted(names, key=lambda x: -cost[(first, x)]):
        line = '%-16s ' % op + ' '.join('%12.0f' % cost[(e, op)] for e, _ in engines)
        if len(engines) > 1:
            r = cost[(ref, op)]
            line += '  %9s' % ('%.0f' % (cost[(first, op)] / r) if r >= 1 else '-')
        print(line)
    if json_out:
        with open(json_out, 'w') as f:
            json.dump({'n': sizes, 'runs': runs, 'ns': {e: {op: round(cost[(e, op)], 1) for op in names} for e, _ in engines}}, f, indent=1)
    return 0


sys.exit(main())
