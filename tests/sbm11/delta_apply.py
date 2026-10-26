#!/usr/bin/env python3
"""tests/sbm11/delta_apply.py — the oracle of the SBM11 delta tests (stage 5,
https://github.com/danbri/factoidal/issues/791).

  delta_apply.py BASE.nq OPS.txt OUTDIR [--final-only]

OPS.txt holds batches of operations, one per line:

  batch                       start a new batch (one SPARQL Update request)
  + S P O [G] .               INSERT DATA of one quad (N-Quads terms)
  - S P O [G] .               DELETE DATA of one quad
  clear <G> | clear DEFAULT   CLEAR GRAPH <G> | CLEAR DEFAULT
  drop <G>                    DROP GRAPH <G>
  # ...                       a comment

For each batch K this writes OUTDIR/batch-K.ru (the SPARQL Update text that
`l4sbm11 update` sends) and, unless --final-only, OUTDIR/after-K.nq: the quads
of BASE with batches 1..K applied, one at a time, to a Python set of quads
(SPARQL 1.1 Update sections 3.1.1, 3.1.2, 3.2.2, 3.2.4). OUTDIR/final.nq is
the state after the last batch. This is a separate implementation from the
Lean overlay (`Storage/Sbm11/Overlay.lean`), over the N-Quads text of the
terms: BASE and OPS must use one spelling per term (`l4sbm11 canon` output
for BASE, and the same spelling in OPS). Prints the batch count.
"""
import os
import re
import sys

TERM = re.compile(r'<[^>]*>|_:[A-Za-z0-9_.-]+|"(?:[^"\\]|\\.)*"(?:@[A-Za-z0-9-]+|\^\^<[^>]*>)?')


def parse_quad(text):
    terms = []
    pos = 0
    text = text.strip()
    while True:
        while pos < len(text) and text[pos] in ' \t':
            pos += 1
        if pos < len(text) and text[pos] == '.':
            break
        m = TERM.match(text, pos)
        if not m:
            raise SystemExit(f"cannot read a term at {pos}: {text!r}")
        terms.append(m.group(0))
        pos = m.end()
    if len(terms) == 3:
        return (terms[0], terms[1], terms[2], None)
    if len(terms) == 4:
        return tuple(terms)
    raise SystemExit(f"not a quad: {text!r}")


def quad_line(q):
    s, p, o, g = q
    return f"{s} {p} {o} {g} ." if g else f"{s} {p} {o} ."


def triple_block(qs):
    out = []
    for g in sorted({q[3] for q in qs}, key=lambda x: x or ""):
        body = " ".join(f"{q[0]} {q[1]} {q[2]} ." for q in qs if q[3] == g)
        out.append(f"GRAPH {g} {{ {body} }}" if g else body)
    return " ".join(out)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    final_only = "--final-only" in sys.argv
    base_path, ops_path, outdir = args
    os.makedirs(outdir, exist_ok=True)
    state = set()
    with open(base_path, encoding="utf-8") as f:
        for line in f:
            if line.strip() and not line.startswith("#"):
                state.add(parse_quad(line))
    batches = []
    for line in open(ops_path, encoding="utf-8"):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line == "batch":
            batches.append([])
            continue
        if line.startswith("+ "):
            batches[-1].append(("add", parse_quad(line[2:])))
        elif line.startswith("- "):
            batches[-1].append(("remove", parse_quad(line[2:])))
        elif line.startswith("clear ") or line.startswith("drop "):
            kind, g = line.split(None, 1)
            batches[-1].append((kind, None if g == "DEFAULT" else g))
        else:
            raise SystemExit(f"unknown operation: {line!r}")
    for k, ops in enumerate(batches, 1):
        # the update text: consecutive operations of one kind in one request part
        parts = []
        i = 0
        while i < len(ops):
            kind = ops[i][0]
            if kind in ("add", "remove"):
                j = i
                while j < len(ops) and ops[j][0] == kind:
                    j += 1
                qs = [q for _, q in ops[i:j]]
                parts.append(("INSERT DATA" if kind == "add" else "DELETE DATA") + " { " + triple_block(qs) + " }")
                i = j
            else:
                g = ops[i][1]
                if kind == "clear":
                    parts.append(f"CLEAR GRAPH {g}" if g else "CLEAR DEFAULT")
                else:
                    parts.append(f"DROP GRAPH {g}")
                i += 1
        with open(os.path.join(outdir, f"batch-{k}.ru"), "w", encoding="utf-8") as f:
            f.write(" ;\n".join(parts) + "\n")
        # the effect, one operation at a time, on the set of quads
        for kind, x in ops:
            if kind == "add":
                state.add(x)
            elif kind == "remove":
                state.discard(x)
            else:
                state = {q for q in state if q[3] != x}
        if not final_only or k == len(batches):
            name = "final.nq" if final_only else f"after-{k}.nq"
            with open(os.path.join(outdir, name), "w", encoding="utf-8") as f:
                for q in sorted(state, key=lambda q: (q[3] or "", q[0], q[1], q[2])):
                    f.write(quad_line(q) + "\n")
    if not final_only and batches:
        with open(os.path.join(outdir, "final.nq"), "w", encoding="utf-8") as f:
            for q in sorted(state, key=lambda q: (q[3] or "", q[0], q[1], q[2])):
                f.write(quad_line(q) + "\n")
    print(len(batches))


if __name__ == "__main__":
    main()
