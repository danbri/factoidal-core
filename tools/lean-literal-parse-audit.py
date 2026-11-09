#!/usr/bin/env python3
"""List the functions whose generated C reads a big Nat literal from decimal text at every call.

Lean 4.33.1 emits `lean_cstr_to_nat("N")` for a `Nat` literal N of 2^32 or more. That call makes a
GMP number from the text, at every evaluation: about 40 ns on x86_64 (2026-11-09, record
docs/designissues/2026-11-09-foafnaut-perf-exploration.md). When the literal is part of a closed
term that the compiler moved into an `_init_` function, it is made once and costs nothing later.
When it stays in the body of a function, every call of that function pays for it. A `Float`
literal whose digits make a number of 2^32 or more (`4294967295.0` is 42949672950 and an exponent)
is such a literal too, followed by a call of `Float.ofScientific`.

This tool reads the C that `lake build` wrote (`.lake/build/ir`) and prints each site that is
not in an `_init_` function: file, function, literal. It reads no Lean source and runs nothing.

Upstream: https://github.com/leanprover/lean4/issues/16007. The repair for a hot site today: put
the constant in a definition of its own (`@[noinline] def twoPow53F : Float := 9007199254740992.0`,
made once when the module starts), or test a bound below 2^32 first.

  lean-literal-parse-audit.py [DIR_OR_FILE ...]      default: formal/lean4/.lake/build/ir
  lean-literal-parse-audit.py --count [DIR ...]      one line: sites, functions, files
  lean-literal-parse-audit.py --under PREFIX ...     only files whose path has PREFIX (e.g. L4Factoidal/JS/)
  lean-literal-parse-audit.py --conversions [DIR ...]
      the calls of `Float.ofNat` and `Float.ofInt` instead (C symbols `lean_float_of_nat`,
      `l_Float_ofInt`). In Lean 4.33.1 each such call reads 2^53 from text inside Lean core
      (`Float.ofScientific`), 40 to 45 ns. In a module that imports
      `L4Factoidal.Prim.FloatOfNat`, a call that the source writes as `Float.ofNat`,
      `Float.ofInt` or `n.toFloat`, and a `Float` literal with no decimal point, are the fast
      twins (its `csimp` theorems). So for a module with the import the count is 0, or the
      line names a route that the theorems do not reach: read the C and add a theorem. For a
      module without the import, the list is what the import would change.

  In `--float-literals` and `--conversions` the functions of the twins themselves are not
  listed: each calls its core function in its slow branch, by design.
  lean-literal-parse-audit.py --float-literals [DIR ...]
      the `Float` literals with a decimal point that the compiler left in the body of a
      function: the calls of `Float.ofScientific` (C symbol `l_Float_ofScientific`, printed as
      `core`) and of its twin `Prim.ofScientificFast` (printed as `twin`; a module that imports
      `L4Factoidal.Prim.FloatOfNat` calls the twin). A `core` call reads 2^53 from text (the
      first test of `Float.ofScientific`, about 40 ns). A literal with an exponent above 22, or
      with a mantissa of 2^53 or more, takes the slow case, in core and in the twin: big number
      arithmetic at every call (`1e300` in `WebPaint.cullCurve` was 85% of a frame until commit
      57fe3531d, 2026-11-09). The line says `slow case` for those, `fast case` for the others,
      and `?` for an argument that is not a literal in the same function. A `twin` call in the
      fast case costs a few machine operations and needs no repair. `lean_cstr_to_nat` does not
      appear for `1e300`, so the default mode does not list it.

Exit status: 0; 2 when a path does not exist or holds no C file (an empty walk is an error, not
a clean result). The tool lists; it is not a gate.

What it cannot see: a literal that the C compiler folds or that Lean's compiler writes in
another form after a toolchain change. `python3 tools/test_lean_literal_parse_audit.py` compiles
a small Lean file with the pinned toolchain and checks that the tool finds the known sites
(a positive control). Run it after a toolchain change.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT = ROOT / 'formal' / 'lean4' / '.lake' / 'build' / 'ir'
FUNC = re.compile(r'^(?:static |LEAN_EXPORT )?[\w\* ]+?\b(\w+)\(.*\)\s*\{\s*$')
LIT = re.compile(r'lean_cstr_to_nat\("(\d+)"\)')
CONV = re.compile(r'= (lean_float_of_nat|l_Float_ofInt)\(')
SCI = re.compile(r'= (l_Float_ofScientific|lp_l4factoidal_L4Factoidal_Prim_ofScientificFast)\((\w+), (\w+), (\w+)\)')
# The twins of `L4Factoidal/Prim/FloatOfNat.lean`: each calls its core function in its slow branch.
TWIN_FUNCTIONS = ('lp_l4factoidal_L4Factoidal_Prim_natToFloat', 'lp_l4factoidal_L4Factoidal_Prim_intToFloat',
                  'lp_l4factoidal_L4Factoidal_Prim_ofScientificFast')
SET_NAT = re.compile(r'^\s*(\w+) = lean_unsigned_to_nat\((\d+)u\);')
SET_BIG = re.compile(r'^\s*(\w+) = lean_cstr_to_nat\("(\d+)"\);')
SET_BOOL = re.compile(r'^\s*(\w+) = ([01]);')


def sites(path):
    """(function, literal, line number, True when a Float.ofScientific call follows) for each site."""
    out = []
    fn = None
    lines = path.read_text(errors='replace').split('\n')
    for i, line in enumerate(lines):
        if line and not line[0].isspace():
            m = FUNC.match(line)
            if m:
                fn = m.group(1)
        m = LIT.search(line)
        if m and fn and not fn.startswith('_init_'):
            is_float = any('Float_ofScientific' in x for x in lines[i + 1:i + 3])
            out.append((fn, m.group(1), i + 1, is_float))
    return out


def conversions(path):
    """(function, 'Float.ofNat' or 'Float.ofInt', line number) for each call outside `_init_` code."""
    out = []
    fn = None
    for i, line in enumerate(path.read_text(errors='replace').split('\n')):
        if line and not line[0].isspace():
            m = FUNC.match(line)
            if m:
                fn = m.group(1)
        m = CONV.search(line)
        if m and fn and not fn.startswith('_init_') and not is_twin(fn):
            out.append((fn, 'Float.ofNat' if m.group(1) == 'lean_float_of_nat' else 'Float.ofInt', i + 1))
    return out


def is_twin(fn):
    """True for a twin of `Prim/FloatOfNat.lean` and its boxed or reduced copies."""
    return any(fn == t or fn.startswith(t + '___') for t in TWIN_FUNCTIONS)


def float_literals(path):
    """(function, mantissa, sign, exponent, line number, 'core' or 'twin') for each call of
    `Float.ofScientific` or of its twin outside `_init_` code and outside the twins. An argument
    is an int when the same function sets it from a literal, else None."""
    out = []
    fn = None
    known = {}
    for i, line in enumerate(path.read_text(errors='replace').split('\n')):
        if line and not line[0].isspace():
            m = FUNC.match(line)
            if m:
                fn = m.group(1)
                known = {}
        for pattern in (SET_NAT, SET_BIG, SET_BOOL):
            m = pattern.match(line)
            if m:
                known[m.group(1)] = int(m.group(2))
        m = SCI.search(line)
        if m and fn and not fn.startswith('_init_') and not is_twin(fn):
            callee = 'core' if m.group(1) == 'l_Float_ofScientific' else 'twin'
            out.append((fn, known.get(m.group(2)), known.get(m.group(3)), known.get(m.group(4)), i + 1, callee))
    return out


def literal_text(mantissa, sign, exponent):
    """The literal as `MeE` or `Me-E`, with `?` for a part that is not known; and its case."""
    if mantissa is None or exponent is None:
        case = '?'
    elif mantissa < 2 ** 53 and exponent <= 22:
        case = 'fast case'
    else:
        case = 'slow case'
    text = '%se%s%s' % ('?' if mantissa is None else mantissa,
                        '?' if sign is None else ('-' if sign else ''),
                        '?' if exponent is None else exponent)
    return text, case


def short(fn):
    return re.sub(r'^lp_\w+?_(?=L4Factoidal_|[A-Z])', '', re.sub(r'^l_', '', fn))


def main(argv=None):
    args = list(sys.argv[1:] if argv is None else argv)
    count = '--count' in args
    under = None
    if '--under' in args:
        under = args[args.index('--under') + 1]
        del args[args.index('--under'):args.index('--under') + 2]
    paths = [Path(a) for a in args if not a.startswith('--')] or [DEFAULT]
    files = []
    for p in paths:
        if p.is_dir():
            files += sorted(p.rglob('*.c'))
        elif p.is_file():
            files.append(p)
        else:
            print('no such path: %s (run `lake build` in formal/lean4 first)' % p, file=sys.stderr)
            return 2
    if under:
        files = [f for f in files if under in str(f)]
    if not files:
        print('no C file found', file=sys.stderr)
        return 2
    if '--conversions' in args:
        per_file = {}
        total = 0
        for f in files:
            found = conversions(f)
            if found:
                per_file[str(f)] = found
                total += len(found)
        base = str(DEFAULT) + '/'
        if not count:
            for f, found in sorted(per_file.items(), key=lambda kv: -len(kv[1])):
                fns = sorted({short(fn) for fn, _, _ in found})
                print('%5d  %s  (%s%s)' % (len(found), f.replace(base, ''), ', '.join(fns[:3]), ', ...' if len(fns) > 3 else ''))
        print('%d calls of Float.ofNat or Float.ofInt outside init code, in %d files (%d C files read)'
              % (total, len(per_file), len(files)))
        return 0
    if '--float-literals' in args:
        base = str(DEFAULT) + '/'
        total = slow = core = 0
        with_calls = set()
        for f in files:
            for fn, mantissa, sign, exponent, line, callee in float_literals(f):
                text, case = literal_text(mantissa, sign, exponent)
                total += 1
                slow += case == 'slow case'
                core += callee == 'core'
                with_calls.add(str(f))
                if not count:
                    print('%s:%d  %s  %s  %s  %s' % (str(f).replace(base, ''), line, short(fn), text, case, callee))
        print('%d Float literals converted outside init code: %d core, %d twin; %d slow case; in %d files '
              '(%d C files read)' % (total, core, total - core, slow, len(with_calls), len(files)))
        return 0
    rows = []
    for f in files:
        for fn, lit, line, is_float in sites(f):
            rows.append((str(f), short(fn), lit, line, is_float))
    if count:
        print('%d sites in %d functions of %d files (%d C files read)'
              % (len(rows), len({(r[0], r[1]) for r in rows}), len({r[0] for r in rows}), len(files)))
        return 0
    base = str(DEFAULT) + '/'
    for f, fn, lit, line, is_float in rows:
        print('%s:%d  %s  %s%s' % (f.replace(base, ''), line, fn, lit, '  (Float literal)' if is_float else ''))
    print('%d sites in %d functions of %d files (%d C files read)'
          % (len(rows), len({(r[0], r[1]) for r in rows}), len({r[0] for r in rows}), len(files)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
