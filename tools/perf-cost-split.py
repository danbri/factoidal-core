#!/usr/bin/env python3
"""tools/perf-cost-split.py -- CPU time per warm run of an SBM11 query, split
into cost classes, at two thread counts (or two binaries).

Record: docs/designissues/2026-10-12-parallel-block-scans.md, stage 1h
(https://github.com/danbri/factoidal/issues/961).

Input: `perf script -F comm,tid,ip,sym,dso` output of profiles taken with
`perf record -e cpu-clock -F HZ --call-graph dwarf,8192`. Give two profiles
per side: one of `--repeat N` and one of `--repeat 1` of the same command.
The `--repeat 1` profile (open, first run, exit) is subtracted, so the
figures are CPU milliseconds per warm run, summed over all threads.

Usage:
  perf-cost-split.py [--hz 1999] A_N.txt A_1.txt B_N.txt B_1.txt WARM_RUNS
      [--detail CLASS] [--top K]

WARM_RUNS is N - 1. With --detail CLASS the symbols (or, for the runtime and
allocator classes, the leaf and its first Lean caller) of one class are
listed by the difference in samples, B minus A.

Classes (a sample goes to the first that matches, in this order):
  spin (pool polling)    a frame of WorkerPool.Cell.poll or Cell.take?
  page faults, zeroing   a page-fault frame, or the leaf clear_page*
  atomic RC / MT refs    the leaf is lean_inc_ref_cold, lean_dec_ref_cold,
                         lean_st_ref_get/take/set/swap or lean_mark_mt.
                         lean_dec_ref_cold also frees single-threaded
                         objects whose count reaches zero, so this class is
                         an upper bound for atomic operations.
  allocator              the leaf is mimalloc (mi_*, _mi_*, a C++ name with
                         mi_ near its start), lean_alloc*, lean_free* or lean_del*
  kernel: wake/sleep     kernel leaf under futex, schedule or a task switch
  kernel: read/open      any other kernel leaf (pread, open, copies)
  compute (Lean code)    everything else
This VM has no hardware counters (`perf stat -e cache-misses` is "not
supported"), so cache misses are not a class: more samples in the same
compute symbol at the same work are the only sign of them.
"""
import collections
import re
import sys

RC = {'lean_inc_ref_cold', 'lean_dec_ref_cold', 'lean_st_ref_get', 'lean_st_ref_take',
      'lean_st_ref_set', 'lean_st_ref_swap', 'lean_mark_mt', 'lean_inc_ref_n_cold'}
FAULT = {'asm_exc_page_fault', 'exc_page_fault', 'handle_mm_fault', 'do_huge_pmd_anonymous_page'}
FRAME = re.compile(r'\s*[0-9a-f]+\s+(.*?)(?:\+0x[0-9a-f]+)?\s+\((.*)\)\s*$')


def classify(frames):
    syms = [f[0] for f in frames]
    if any('WorkerPool_Cell_poll' in s or 'WorkerPool_Cell_take' in s for s in syms):
        return 'spin (pool polling)'
    leaf, dso = frames[0]
    if leaf.startswith('clear_page') or any(s in FAULT for s in syms):
        return 'page faults, zeroing'
    if leaf in RC:
        return 'atomic RC / MT refs'
    if leaf.startswith(('mi_', '_mi_', 'lean_alloc', 'lean_free', 'lean::lean_del', 'lean_del')) \
            or 'mi_' in leaf[:12]:
        return 'allocator'
    if 'kernel' in dso:
        if leaf.startswith(('finish_task_switch', '_raw_spin_unlock_irqrestore')) or \
                any(s.startswith(('futex_', '__x64_sys_futex', 'schedule', 'try_to_wake')) for s in syms):
            return 'kernel: wake/sleep'
        return 'kernel: read/open'
    return 'compute (Lean code)'


def samples(path):
    """Yield the frames (leaf first) of each sample."""
    frames, open_ = [], False
    with open(path, errors='replace') as fh:
        for line in fh:
            if not line.strip():
                if open_ and frames:
                    yield frames
                frames, open_ = [], False
            elif not line.startswith((' ', '\t')):
                frames, open_ = [], True
            else:
                m = FRAME.match(line)
                if m:
                    frames.append((m.group(1), m.group(2)))
    if open_ and frames:
        yield frames


def count(path, detail):
    by_class, by_key, n = collections.Counter(), collections.Counter(), 0
    for fr in samples(path):
        n += 1
        c = classify(fr)
        by_class[c] += 1
        if detail and c == detail:
            if c.startswith('compute'):
                key = fr[0][0]
            else:
                caller = next((f[0] for f in fr if f[0].startswith('lp_')), '?')
                key = f'{fr[0][0][:30]} <- {caller}'
            by_key[key[:150]] += 1
    if n == 0:
        sys.exit(f'{path}: no samples (is it `perf script` output?)')
    return by_class, by_key, n


def main():
    args = sys.argv[1:]
    hz, detail, top = 1999, None, 15
    for flag in ('--hz', '--detail', '--top'):
        if flag in args:
            i = args.index(flag)
            val = args[i + 1]
            del args[i:i + 2]
            if flag == '--hz':
                hz = int(val)
            elif flag == '--detail':
                detail = val
            else:
                top = int(val)
    if len(args) != 5:
        sys.exit(__doc__)
    a_n, a_1, b_n, b_1, runs = args[0], args[1], args[2], args[3], int(args[4])
    if runs < 1:
        sys.exit('WARM_RUNS must be at least 1')
    sides = []
    for full, one in ((a_n, a_1), (b_n, b_1)):
        cf, kf, nf = count(full, detail)
        c1, k1, n1 = count(one, detail)
        sides.append(({k: cf[k] - c1[k] for k in set(cf) | set(c1)},
                      {k: kf[k] - k1[k] for k in set(kf) | set(k1)}, nf - n1))
    ms = lambda x: x / hz * 1000 / runs
    (ca, ka, na), (cb, kb, nb) = sides
    print('class | A ms CPU per warm run | B ms CPU per warm run | B - A')
    print('--- | ---: | ---: | ---:')
    for k in sorted(set(ca) | set(cb), key=lambda k: -(cb.get(k, 0) - ca.get(k, 0))):
        print(f'{k} | {ms(ca.get(k, 0)):.3f} | {ms(cb.get(k, 0)):.3f} | {ms(cb.get(k, 0)) - ms(ca.get(k, 0)):+.3f}')
    print(f'total | {ms(na):.3f} | {ms(nb):.3f} | {ms(nb) - ms(na):+.3f}')
    if detail:
        print(f'\n{detail}: samples A, B, B - A (warm runs only)')
        for k in sorted(set(ka) | set(kb), key=lambda k: -(kb.get(k, 0) - ka.get(k, 0)))[:top]:
            print(f'{ka.get(k, 0):6d} {kb.get(k, 0):6d} {kb.get(k, 0) - ka.get(k, 0):+6d} {k}')


if __name__ == '__main__':
    main()
