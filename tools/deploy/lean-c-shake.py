#!/usr/bin/env python3
"""lean-c-shake.py: function-level reachability over the C that Lean emits, and a post-pass.

Reads the generated C of a link set. Writes a report. With --out it writes a changed copy of
each file whose module initialiser changes:
  --mode prune  removes eager initialisers of constants that no root reaches
  --mode lazy   also turns each remaining eager constant into a once cell (lean_obj_once),
                the mechanism Lean 4.33 already uses for closed terms
Roots: --root SYM, --root-file F (every C token of a file), --nm-undefined F (symbols a
runtime object needs). Results and limits: docs/20261106-deployable-modules.md
"""
import argparse, json, os, re, subprocess, sys, hashlib, collections

STR = re.compile(r'"(?:[^"\\]|\\.)*"')
TOK = re.compile(r'[A-Za-z_][A-Za-z0-9_]*')
FN_DEF = re.compile(r'^(?:LEAN_EXPORT |static |extern )*[A-Za-z_][\w ]*[ *]+\*?([A-Za-z_]\w*)\(.*\)\s*\{\s*$')
VAR_DEF = re.compile(r'^(static |LEAN_EXPORT )?(const )?([A-Za-z_]\w*\*?(?: \*)?) ?\*?([A-Za-z_]\w*)(?: = (.*))?;\s*$')
INIT_NAME = re.compile(r'^(runtime_|meta_)?initialize_\w+$')
EAGER = re.compile(r'^(\w+) = (_init_\w+)\(\);$')
IOINIT = re.compile(r'^res = (\w+)\(\);$')
CHAIN = re.compile(r'^res = ((?:runtime_|meta_)?initialize_\w+)\(builtin\);$')
ONCE = {'lean_object*': 'obj', 'uint8_t': 'uint8', 'uint16_t': 'uint16', 'uint32_t': 'uint32',
        'uint64_t': 'uint64', 'size_t': 'usize', 'double': 'float', 'float': 'float32'}

class File: pass

def parse(path):
    f = File(); f.path = path; f.lines = open(path, errors='replace').read().split('\n')
    f.items = []      # (name, static, kind, deps_tokens, first, last)
    f.inits = {}      # init fn -> (first,last)
    i, n = 0, len(f.lines)
    while i < n:
        line = f.lines[i]
        if line.startswith('#') or line.startswith('//') or not line:
            i += 1; continue
        m = FN_DEF.match(line)
        if m:
            j = i + 1; depth = 1
            while True:
                t = f.lines[j]
                if '{' in t or '}' in t:
                    t = STR.sub('', t); depth += t.count('{') - t.count('}')
                    if depth == 0: break
                j += 1
            name = m.group(1)
            toks = set(TOK.findall(STR.sub('""', '\n'.join(f.lines[i + 1:j]))))
            toks.update(TOK.findall(line[line.index('('):]))
            f.items.append((name, line.startswith('static'), 'f', toks, i, j))
            i = j + 1; continue
        if line.endswith(';') and '(' not in line.split(' = ')[0]:
            m = VAR_DEF.match(line)
            if m:
                toks = set(TOK.findall(m.group(5) or ''))
                f.items.append((m.group(4), m.group(1) == 'static ', 'v', toks, i, i))
        i += 1
    return f

def build(files):
    nodes = {}; glob = {}
    for f in files:
        f.local = {}
        for (name, static, kind, toks, a, b) in f.items:
            key = (f.path, name) if static else name
            if kind == 'v' and key in nodes and nodes[key]['kind'] == 'f': continue
            nd = nodes.get(key)
            if nd is None or nd['kind'] == 'v' and (kind == 'f' or (toks and not nd['toks'])):
                nodes[key] = {'kind': kind, 'toks': toks, 'file': f, 'name': name, 'first': a, 'last': b, 'init': None}
            if static: f.local[name] = key
            else: glob.setdefault(name, key)
    return nodes, glob

def init_statements(f, name_item):
    (_, _, _, _, a, b) = name_item
    return f.lines[a + 1:b]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--files', required=True, help='file with one C path per line')
    ap.add_argument('--root', action='append', default=[])
    ap.add_argument('--root-file', action='append', default=[])
    ap.add_argument('--nm-undefined', action='append', default=[])
    ap.add_argument('--keep-io-init', action='store_true', default=True)
    ap.add_argument('--mode', choices=['report', 'prune', 'lazy'], default='report')
    ap.add_argument('--out')
    ap.add_argument('--json')
    a = ap.parse_args()
    paths = [l.strip() for l in open(a.files) if l.strip()]
    files = [parse(p) for p in paths]
    nodes, glob = build(files)
    # initialisers
    eager = []; ioinit = []; chain = collections.defaultdict(list); initfns = {}
    for f in files:
        for it in f.items:
            if it[2] == 'f' and INIT_NAME.match(it[0]):
                initfns[it[0]] = (f, it)
                body = init_statements(f, it)
                for k, s in enumerate(body):
                    m = EAGER.match(s)
                    if m: eager.append((f, it[0], m.group(1), m.group(2)))
                    m = IOINIT.match(s)
                    if m:
                        g = body[k + 2 + 0] if False else None
                        ioinit.append((f, it[0], m.group(1)))
                    m = CHAIN.match(s)
                    if m: chain[it[0]].append(m.group(1))
                    r = re.match(r'^return (initialize_\w+)\(builtin\);$', s)
                    if r: chain[it[0]].append(r.group(1))
    def res(f, t):
        k = f.local.get(t)
        if k is not None: return k
        return glob.get(t)
    for (f, fn, g, ini) in eager:
        k = res(f, g)
        if k in nodes: nodes[k]['init'] = res(f, ini)
    # roots
    roots = set()
    for r in a.root:
        if r in glob: roots.add(glob[r])
        else: print('root not found', r, file=sys.stderr)
    for rf in a.root_file:
        for t in set(TOK.findall(open(rf, errors='replace').read())):
            if t in glob and not INIT_NAME.match(t): roots.add(glob[t])
    for nf in a.nm_undefined:
        for t in open(nf).read().split():
            if t in glob and not INIT_NAME.match(t): roots.add(glob[t])
    if a.keep_io_init:
        for (f, fn, ini) in ioinit:
            k = res(f, ini)
            if k: roots.add(k)
    # reach; initialiser functions are not traversed: a constant pulls its own initialiser
    seen = set(); stack = list(roots)
    while stack:
        k = stack.pop()
        if k in seen or k not in nodes: continue
        seen.add(k); nd = nodes[k]
        if nd['init']: stack.append(nd['init'])
        for t in nd['toks']:
            r = res(nd['file'], t)
            if r is not None and r not in seen and not INIT_NAME.match(t): stack.append(r)
    fnodes = [k for k, v in nodes.items() if v['kind'] == 'f' and not INIT_NAME.match(v['name'])]
    live_eager = [(f, fn, g, ini) for (f, fn, g, ini) in eager if res(f, g) in seen]
    rep = {'files': len(files), 'nodes': len(nodes), 'functions': len(fnodes),
           'live_functions': sum(1 for k in fnodes if k in seen),
           'eager': len(eager), 'live_eager': len(live_eager), 'io_init': [x[2] for x in ioinit], 'roots': len(roots)}
    print(json.dumps(rep))
    if a.json:
        json.dump({'live': sorted(nodes[k]['name'] for k in seen), 'dead_eager': [e[2] for e in eager if res(e[0], e[2]) not in seen]}, open(a.json, 'w'))
    if a.mode == 'report': return
    # which init functions still do work
    keep_stmt = {(id(f), fn, g) for (f, fn, g, ini) in live_eager} if a.mode == 'prune' else set()
    ioset = {fn for (f, fn, i) in ioinit}
    has_work = {fn for (f, fn, g) in [(x[0], x[1], x[2]) for x in live_eager]} if a.mode == 'prune' else set()
    has_work |= ioset
    # Lazy mode: a constant used at file scope cannot become a call; keep it eager.
    lazy = {}
    if a.mode == 'lazy':
        for (f, fn, g, ini) in live_eager:
            k = res(f, g); nd = nodes[k]
            line = f.lines[nd['first']]
            m = VAR_DEF.match(line)
            ty = (m.group(3) + ('*' if '*' in line.split(g)[0] and '*' not in m.group(3) else '')).replace(' ', '')
            if ty not in ONCE:
                print('eager left, type', ty, g, file=sys.stderr); keep_stmt.add((id(f), fn, g)); has_work.add(fn); continue
            lazy[k] = (f, fn, g, ini, ty)
        rep['lazy'] = len(lazy)
    changed = {fn: True for fn in has_work}
    live_init = set()
    def needs(fn, stack=()):
        if fn in live_init: return True
        if fn not in chain and fn not in has_work: return False
        r = fn in has_work
        return r
    # fixed point over the chain
    memo = {}
    def need(fn):
        if fn in memo: return memo[fn]
        memo[fn] = False
        r = fn in has_work
        for c in chain.get(fn, []):
            if need(c): r = True
        memo[fn] = r; return r
    os.makedirs(a.out, exist_ok=True)
    lazy_by_token = {}
    for k, (f, fn, g, ini, ty) in lazy.items():
        lazy_by_token.setdefault(g, []).append((k, f, ini, ty))
    outlist = []
    nlazy_uses = 0
    for f in files:
        lines = list(f.lines)
        init_items = [it for it in f.items if it[2] == 'f' and INIT_NAME.match(it[0])]
        for it in init_items:
            fn = it[0]; a0, b0 = it[4], it[5]
            body = lines[a0 + 1:b0]; new = []; i = 0
            while i < len(body):
                s = body[i]
                m = EAGER.match(s)
                if m:
                    g = m.group(1)
                    if (id(f), fn, g) in keep_stmt: new.append(s)
                    else:
                        if i + 1 < len(body) and body[i + 1] == f'lean_mark_persistent({g});': i += 1
                    i += 1; continue
                m = CHAIN.match(s)
                if m and not need(m.group(1)):
                    i += 3; continue
                r = re.match(r'^return (initialize_\w+)\(builtin\);$', s)
                if r and not need(r.group(1)):
                    new.append('return lean_io_result_mk_ok(lean_box(0));'); i += 1; continue
                new.append(s); i += 1
            lines[a0 + 1:b0] = body + [] if False else new + [''] * (len(body) - len(new))
        # Lazy rewrite of uses inside function bodies.
        if lazy:
            used = set(); protos = []; defs = []
            for it in f.items:
                if it[2] != 'f' or INIT_NAME.match(it[0]): continue
                hit = [t for t in it[3] if t in lazy_by_token and res(f, t) in lazy]
                if not hit: continue
                pat = re.compile(r'(?<![A-Za-z0-9_&])(' + '|'.join(map(re.escape, hit)) + r')(?![A-Za-z0-9_])')
                for j in range(it[4] + 1, it[5]):
                    new, c = pat.subn(lambda m: m.group(1) + '__once()', lines[j])
                    if c: lines[j] = new; nlazy_uses += c; used.update(hit)
            for t in used:
                k = res(f, t); (_, _, g, ini, ty) = lazy[k]
                if f is lazy[k][0]: continue
                protos.append(f'{ty} {g}__once(void);')
            mine = [v for v in lazy.values() if v[0] is f]
            for (_, _, g, ini, ty) in mine:
                protos.append(f'{"LEAN_EXPORT " if True else ""}{ty} {g}__once(void);')
                defs.append(f'static lean_once_cell_t {g}__cell = LEAN_ONCE_CELL_INITIALIZER;')
                defs.append(f'LEAN_EXPORT {ty} {g}__once(void) {{ return lean_{ONCE[ty]}_once(&{g}, &{g}__cell, {ini}); }}')
            if protos:
                at = next(i for i, l in enumerate(lines) if l.startswith('extern "C" {')) + 2
                lines[at:at] = protos
            if defs:
                at = max(i for i, l in enumerate(lines) if l == '#ifdef __cplusplus')
                lines[at:at] = defs
        text = '\n'.join(lines)
        o = os.path.join(a.out, f.path.replace('/', '_').lstrip('_')[-120:])
        if text != '\n'.join(f.lines):
            open(o, 'w').write(text); outlist.append((f.path, o))
        else:
            outlist.append((f.path, f.path))
    json.dump(outlist, open(os.path.join(a.out, 'files.json'), 'w'))
    print(json.dumps({'changed': sum(1 for p, o in outlist if p != o), 'lazy': len(lazy), 'lazy_uses': nlazy_uses}))

main()
