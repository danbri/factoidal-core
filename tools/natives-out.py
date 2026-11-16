#!/usr/bin/env python3
"""Move the three large built-in dispatchers (callNative, extraNative, moreNative) of
JS/Interp.lean out of the evaluator's mutual block (one-off refactor; kept as the record of how).

They become plain (non-recursive) definitions in namespace `Natives`, taking `core : CoreFn H`, a
dispatcher for the functions of the block they call (`CoreOp`, one constructor per function,
`CoreOp.Res` its result type). Inside the block, `coreRun n` is that dispatcher at fuel `n`, and
`callNative`, `extraNative`, `moreNative` stay as one-line wrappers. A call `f n a b` in a native
becomes `core.f a b` (`CoreFn.f`, reducible), so the bodies keep their text.

usage: natives-out.py Interp.lean
"""
import re
import sys

path = sys.argv[1]
src = open(path).read().split('\n')
# rawElems (no fuel, in the block's text) is used by a built-in: put it before the block
_r = next(i for i, l in enumerate(src) if l.startswith('def rawElems '))
_raw = src[_r - 1:_r + 7]
assert _raw[0].startswith('/--') and _raw[-1] == '', _raw
del src[_r - 1:_r + 7]
_m = next(i for i, l in enumerate(src) if l == 'mutual' and i > 1600)
src[_m:_m] = _raw
NAT = ['callNative', 'extraNative', 'moreNative']
# moved with them, no wrapper left in the block: only built-ins call it (with a callback)
MOVED = NAT + ['iterEach']
lo = next(i for i, l in enumerate(src) if l == 'mutual' and i > 1600)
hi = next(i for i in range(lo + 1, len(src)) if src[i] == 'end')


def split_top(s):
    out, d, cur, i = [], 0, '', 0
    while i < len(s):
        c = s[i]
        if c in '([{':
            d += 1
        if c in ')]}':
            d -= 1
        if d == 0 and s.startswith(' → ', i):
            out.append(cur)
            cur = ''
            i += 3
            continue
        cur += c
        i += 1
    out.append(cur)
    return out


sigs = {}
for i in range(lo, hi):
    m = re.match(r'^def (\w+) : (Nat → .*)$', src[i])
    if m:
        parts = split_top(m.group(2))
        if parts[-1].startswith('M '):
            sigs[m.group(1)] = (parts[1:-1], parts[-1][2:].strip())

# the three definitions: from the doc comment before `def` to the line after `termination_by`
spans = {}
for f in MOVED:
    s = next(i for i in range(lo, hi) if src[i].startswith(f'def {f} '))
    d = s
    while d > 0 and not src[d - 1].startswith('/--') and src[d - 1].strip() != '':
        d -= 1
    if src[d - 1].startswith('/--'):
        d -= 1
    e = next(i for i in range(s + 1, hi) if src[i].startswith('termination_by'))
    spans[f] = (d, s, e)

names = set(sigs)
used = set()
bodies = {}
for f in MOVED:
    d, s, e = spans[f]
    doc = src[d:s]
    head = src[s]
    assert src[s + 1].strip().startswith('| 0,'), (f, src[s + 1])
    arm = src[s + 2]
    m = re.match(r'^  \| n \+ 1, (.*) => (do)?\s*$', arm)
    assert m, (f, arm)
    pats = m.group(1)
    body = src[s + 3:e]
    text = '\n'.join(body)
    # a loop bounded by the fuel (`for _ in [0:n]`) ends early at a small fuel with a result that
    # is not out of fuel: bound it by the steps alone, as the iterator loops elsewhere are
    text = text.replace('for _ in [0:n] do', 'for _ in [0:1000000000] do')

    def sub(mm):
        g = mm.group(1)
        used.add(g)
        if g in MOVED and g != 'callNative':
            return f'Natives.{g} core'
        return f'core.{g}'
    text = re.sub(r'(?<![\w.\'])(' + '|'.join(sorted(names, key=len, reverse=True)) + r') n(?![\w\'])', sub, text)
    left = re.findall(r'(?<![\w.\'])n(?![\w\'])', re.sub(r'"[^"]*"', '', re.sub(r'--.*', '', text)))
    assert not left, (f, 'n left', len(left))
    args, res = sigs[f]
    binders = ' '.join(f'({p} : {t})' for p, t in zip(pats.split(', '), args))
    bodies[f] = (doc, f'def {f} (core : CoreFn H) {binders} : M {res} := do', text)

used.discard('extraNative')
used.discard('moreNative')
used.discard('iterEach')
ops = sorted(used, key=lambda x: list(sigs).index(x))

core = []
w = core.append
w('/-! ## The built-in dispatchers, outside the evaluator\'s mutual block\n')
w('`callNative`, `extraNative` and `moreNative` (about 4,000 lines) call back into the evaluator')
w('through one dispatcher, `CoreFn`: a request (`CoreOp`, one constructor per function of the block')
w('they use) and its answer (`CoreOp.Res`). Out of the block they are plain definitions, so Lean')
w('makes no structural-recursion equation lemmas for them (those of the block took minutes and')
w('gigabytes), and a property of the block is proved for them once, from the same property of the')
w('dispatcher (`JS/FuelMono.lean`). Inside the block, `coreRun n` answers requests at fuel `n`. -/\n')
w('/-- A call from a built-in into the evaluator. -/')
w('inductive CoreOp (H : Type) where')
for o in ops:
    a, r = sigs[o]
    w(f'  | {o}' + ''.join(f' (a{j} : {t})' for j, t in enumerate(a)))
w('')
w('/-- The type of the answer to a request. -/')
w('def CoreOp.Res : CoreOp H → Type')
for o in ops:
    a, r = sigs[o]
    w(f'  | .{o}' + ' _' * len(a) + f' => {r}')
w('')
w('/-- Requests answered in the monad: the evaluator, at some fuel, as built-ins see it. -/')
w('abbrev CoreFn (H : Type) := (op : CoreOp H) → JSM H op.Res\n')
for o in ops:
    a, r = sigs[o]
    bs = ' '.join(f'(a{j} : {t})' for j, t in enumerate(a))
    ap = ' '.join(f'a{j}' for j in range(len(a)))
    w(f'@[reducible] def CoreFn.{o} (c : CoreFn H) {bs} : JSM H {r} := c (.{o} {ap})')
w('\nnamespace Natives\n')
for f in ['iterEach', 'moreNative', 'extraNative', 'callNative']:
    doc, head, text = bodies[f]
    core += doc
    w(head)
    w(text)
    w('')
w('end Natives\n')

dispatch = ['/-- The evaluator at fuel `n`, as the built-ins call it (`CoreFn`). -/',
            'def coreRun : Nat → (op : CoreOp H) → M op.Res',
            '  | 0, _ => throw (.halt "fuel")',
            '  | n + 1, op =>',
            '    match op with']
for o in ops:
    a, r = sigs[o]
    ap = ' '.join(f'a{j}' for j in range(len(a)))
    dispatch.append(f'    | .{o}' + ''.join(f' a{j}' for j in range(len(a))) + f' => {o} n {ap}')
dispatch.append('termination_by structural n _ => n\n')

wrappers = {}
for f in NAT:
    d, s, e = spans[f]
    args, res = sigs[f]
    ps = ' '.join(f'a{j}' for j in range(len(args)))
    wrappers[f] = src[d:s] + [src[s], src[s + 1], f'  | n + 1, {", ".join(f"a{j}" for j in range(len(args)))} => Natives.{f} (coreRun n) {ps}',
                               src[e]]
    if f == 'callNative':
        wrappers[f] = dispatch + wrappers[f]

out = []
i = 0
order = sorted(NAT, key=lambda f: spans[f][0])
while i < len(src):
    if i == lo:
        out += core
    hit = [f for f in MOVED if spans[f][0] == i]
    if hit:
        f = hit[0]
        out += wrappers.get(f, [])
        i = spans[f][2] + 1
        continue
    out.append(src[i])
    i += 1
open(path, 'w').write('\n'.join(out))
print('ops', len(ops), 'lines moved', sum(spans[f][2] - spans[f][1] for f in MOVED))
