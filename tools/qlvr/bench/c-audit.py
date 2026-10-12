#!/usr/bin/env python3
"""tools/qlvr/bench/c-audit.py — count the Lean runtime operations in the C
that Lean generated for one function
(https://github.com/danbri/factoidal/issues/797; record:
docs/designissues/2026-10-12-lean-to-c-performance.md).

    python3 tools/qlvr/bench/c-audit.py FILE.c NAME [NAME...]

NAME is matched against the C function name (a substring, e.g.
`QlvrKernel_filterAS`; `___boxed` wrappers are skipped). For each function
the script prints the number of call sites of each category in its body.
A loop compiled as `goto _start` has one iteration per pass through the
body, so for a loop with one path the counts are per iteration; with
branches they are an upper bound, and the record says which path is hot.

Categories:
  nat      lean_nat_* and lean_unsigned_to_nat / lean_usize_to_nat (Nat
           arithmetic and tests: an inline fast path for small numbers and a
           call into the runtime (GMP) for big ones)
  rc       lean_inc*, lean_dec* (reference count updates; on a scalar a test)
  box      lean_box*, lean_unbox* (boxing to / from an object pointer)
  alloc    lean_alloc_*, lean_mk_*, lean_copy_*, ctor allocation
  arrget   lean_array_get*, lean_array_fget*, lean_byte_array_get/fget
           (index given as a boxed Nat)
  uget     lean_byte_array_uget, lean_array_uget (unboxed index)
  push     lean_byte_array_push, lean_array_push, lean_float_array_push
           (out of line in lean.h 4.33)
  call     calls to other generated Lean functions (lp_*)
"""
import re
import sys

CATS = [
    ("nat", re.compile(r"\blean_(nat_\w+|unsigned_to_nat|usize_to_nat|uint64_to_nat|uint64_of_nat|usize_of_nat)\(")),
    ("rc", re.compile(r"\blean_(inc|dec)(_ref|_n)?\(")),
    ("box", re.compile(r"\blean_(box|unbox)(_\w+)?\(")),
    ("alloc", re.compile(r"\blean_(alloc_\w+|mk_\w+|copy_\w+)\(")),
    ("arrget", re.compile(r"\blean_(array_get\w*|array_fget\w*|byte_array_get|byte_array_fget)\(")),
    ("uget", re.compile(r"\blean_(byte_array_uget|array_uget|float_array_uget)\(")),
    ("push", re.compile(r"\blean_(byte_array_push|array_push|float_array_push)\(")),
    ("call", re.compile(r"\blp_\w+\(")),
]


def bodies(text, needle):
    head = re.compile(r"^(LEAN_EXPORT |static )?[\w\*]+[ \*]+((?:lp|l)_\w+)\(([^)]*)\)\{$", re.M)
    for m in head.finditer(text):
        name = m.group(2)
        if needle not in name or name.endswith("___boxed"):
            continue
        depth, i = 1, m.end()
        while depth and i < len(text):
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
            i += 1
        yield name, text[m.end():i]


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    text = open(sys.argv[1]).read()
    found = False
    for needle in sys.argv[2:]:
        for name, body in bodies(text, needle):
            found = True
            counts = {c: len(r.findall(body)) for c, r in CATS}
            lines = body.count("\n")
            print(f"{name}: {lines} lines; " + ", ".join(f"{c} {n}" for c, n in counts.items()))
    if not found:
        print("c-audit: no function matched", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
