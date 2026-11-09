#!/usr/bin/env python3
"""Make Lean's big Nat and Int literals persistent in C that is compiled for wasm32.

Why (docs/designissues/2026-11-08-lean-js-engine.md, section 17): Lean 4.33's compiler
treats a Nat literal that is a scalar on the 64-bit machine that compiles it (below 2^63)
as needing no reference counting. It emits the literal as `lean_unsigned_to_nat(Nu)` or
`lean_cstr_to_nat("N")` and then passes that one value to as many owners as the program
has, with no `lean_inc`. On wasm32 a Nat of 2^31 or more is a heap object (an mpz), so
the first owner that is done with it frees it and the others keep a dangling pointer.
Measured in the Foafnaut Wasm engine (2026-11-09): `JS.callMethod` gave one literal
2^40 (the evaluator's fuel) to `getV` and to `callV`, and `WebScripts.startLean` put the
literal 4,000,000,000 (`Page.Limits.fuel`) into a closure and into the `Limits` record;
the frees that followed broke mimalloc's free lists ("memory access out of bounds" in
`mi_malloc_small`, "remainder by zero", dlmalloc aborts). The same holds for an `Int`
made from such a literal (`lean_nat_to_int`): small on 64-bit up to 2^31 - 1, a heap
object on wasm32 above 2^30 - 1.

The fix is the representation the compiler already assumes: each such literal becomes
one persistent object per call site (reference count 0, so every `lean_inc` and
`lean_dec` leaves it alone and nothing frees it), made on first use. On a 64-bit target
the literal is a scalar and the macro returns it unchanged.

  wasm32-nat-literals.py --rewrite IN.c OUT.c   rewrite one file (exit 0; prints the count)
  wasm32-nat-literals.py --batch OUTDIR NAME=IN.c...
                                                for each input, the file to compile: IN.c when it
                                                has no site, else OUTDIR/NAME.c, rewritten
  wasm32-nat-literals.py --count FILE_OR_DIR... the sites a wasm32 build rewrites
  wasm32-nat-literals.py --self-test
"""
import re
import sys
from pathlib import Path

NAT_LIMIT = 2 ** 31          # LEAN_MAX_SMALL_NAT + 1 on wasm32
INT_LIMIT = 2 ** 30          # LEAN_MAX_SMALL_INT + 1 on wasm32

NAT = re.compile(r'(?P<var>v_\w+) = (?:lean_cstr_to_nat\("(?P<s>\d+)"\)|lean_unsigned_to_nat\((?P<u>\d+)u\));')
TOINT = re.compile(r'(?P<var>v_\w+) = lean_nat_to_int\((?P<arg>v_\w+)\);')

PRELUDE = r'''
/* tools/wasm32-nat-literals.py: big Nat and Int literals are persistent on wasm32. */
#ifndef L4_PERSISTENT_LITERAL
#define L4_PERSISTENT_LITERAL(MAKE) ({ static lean_object * l4_lit_; \
  if (l4_lit_ == 0) { lean_object * l4_v_ = (MAKE); if (!lean_is_scalar(l4_v_)) lean_mark_persistent(l4_v_); l4_lit_ = l4_v_; } \
  l4_lit_; })
#endif
'''


def literal_value(m):
    return int(m.group('s') or m.group('u'))


def rewrite(text):
    """The text with every big literal made persistent, and the number of sites."""
    big = {}
    count = 0

    def nat(m):
        nonlocal count
        v = literal_value(m)
        if v < NAT_LIMIT:
            return m.group(0)
        big[m.group('var')] = v
        count += 1
        make = m.group(0).split(' = ', 1)[1].rstrip(';')
        return f"{m.group('var')} = L4_PERSISTENT_LITERAL({make});"

    small = {m.group('var'): literal_value(m) for m in NAT.finditer(text)}
    text = NAT.sub(nat, text)

    def toint(m):
        nonlocal count
        v = big.get(m.group('arg'), small.get(m.group('arg')))
        if v is None or v < INT_LIMIT:
            return m.group(0)
        count += 1
        return f"{m.group('var')} = L4_PERSISTENT_LITERAL(lean_nat_to_int({m.group('arg')}));"

    text = TOINT.sub(toint, text)
    if count:
        at = text.find('#include <lean/lean.h>')
        if at < 0:
            raise SystemExit('wasm32-nat-literals: no #include <lean/lean.h> to put the macro after')
        end = text.index('\n', at) + 1
        text = text[:end] + PRELUDE + text[end:]
    return text, count


def self_test():
    src = ('#include <lean/lean.h>\n'
           'lean_object* f(lean_object* a){\n'
           'v_x_1_ = lean_unsigned_to_nat(4000000000u);\n'
           'v_x_2_ = lean_cstr_to_nat("1099511627776");\n'
           'v_x_3_ = lean_unsigned_to_nat(7u);\n'
           'v_x_4_ = lean_unsigned_to_nat(2147483647u);\n'
           'v_x_5_ = lean_nat_to_int(v_x_4_);\n'
           'v_x_6_ = lean_nat_to_int(v_x_3_);\n'
           '}\n')
    out, n = rewrite(src)
    assert n == 3, n
    assert 'L4_PERSISTENT_LITERAL(lean_unsigned_to_nat(4000000000u))' in out
    assert 'L4_PERSISTENT_LITERAL(lean_cstr_to_nat("1099511627776"))' in out
    assert 'v_x_3_ = lean_unsigned_to_nat(7u);' in out
    assert 'v_x_4_ = lean_unsigned_to_nat(2147483647u);' in out       # a scalar on wasm32
    assert 'v_x_5_ = L4_PERSISTENT_LITERAL(lean_nat_to_int(v_x_4_));' in out  # not a small Int there
    assert 'v_x_6_ = lean_nat_to_int(v_x_3_);' in out
    assert out.index('#define L4_PERSISTENT_LITERAL') > out.index('#include <lean/lean.h>')
    assert rewrite(out)[1] == 0  # idempotent
    unchanged, n0 = rewrite('#include <lean/lean.h>\nv_a_1_ = lean_unsigned_to_nat(3u);\n')
    assert n0 == 0 and 'L4_PERSISTENT_LITERAL' not in unchanged
    print('wasm32-nat-literals: self-test ok')


def main(argv):
    if argv[:1] == ['--self-test']:
        self_test()
        return 0
    if argv[:1] == ['--rewrite'] and len(argv) == 3:
        text, n = rewrite(Path(argv[1]).read_text())
        Path(argv[2]).write_text(text)
        print(n)
        return 0
    if argv[:1] == ['--batch'] and len(argv) > 1:
        out = Path(argv[1]); out.mkdir(parents=True, exist_ok=True)
        total = 0
        for item in argv[2:]:
            name, src = item.split('=', 1)
            text, n = rewrite(Path(src).read_text(errors='replace'))
            if n:
                dst = out / (name + '.c')
                if not dst.exists() or dst.read_text() != text:
                    dst.write_text(text)
                print(dst)
                total += n
            else:
                print(src)
        print(f'wasm32-nat-literals: {total} literal sites made persistent', file=sys.stderr)
        return 0
    if argv[:1] == ['--count'] and len(argv) > 1:
        total = 0
        for arg in argv[1:]:
            p = Path(arg)
            for f in sorted(p.rglob('*.c')) if p.is_dir() else [p]:
                n = rewrite(f.read_text(errors='replace'))[1]
                if n:
                    print(f'{n:5d} {f}')
                total += n
        print(f'wasm32-nat-literals: {total} literal sites')
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
