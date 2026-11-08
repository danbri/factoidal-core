#!/usr/bin/env python3
"""Port the SpecTec-generated WebAssembly 3.0 Lean file to this repository's Lean.

Input:  third_party/spectec-lean4/generated/Wasm-f3268fa9.lean, the output of the SpecTec Lean 4
        backend (https://github.com/Wasm-DSL/spectec, branch lean4-wip, commit 16b70bde, with
        the patches in tools/wasmvm/spectec-patches/) for our pinned WebAssembly spec
        (third_party/wasm-spec, WebAssembly/spec f3268fa9). The command is in
        third_party/spectec-lean4/generated/README.md. Until 2026-11-07 the input was the
        branch's own output, third_party/spectec-lean4/spectec/test-lean4/Wasm.lean, which is
        kept for reference.
Output: formal/lean4/L4Factoidal/WasmVM/Spec/Wasm30.lean (namespace L4Factoidal.WasmVM.Spec).

The output is GENERATED (Iron Rule 2). Do not edit it by hand: change a rule here and
rerun. `--check` regenerates in memory and fails if the committed file differs; the test
tools/wasmvm/test_port_spec.py runs it.

Every rule below has a NAME, the REASON it is needed, and the exact number of places it
must change. A rule that changes a different number of places stops the port, so a new
input cannot pass through a rule silently. The rules and their reasons are also listed in
docs/designissues/2026-11-07-wasmvm-spec-layer.md.
"""

import argparse
import hashlib
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import port_builtins  # noqa: E402  (rule builtin-definitions, kept in its own file)

ROOT = pathlib.Path(__file__).resolve().parents[2]
DEFAULT_INPUT = ROOT / "third_party/spectec-lean4/generated/Wasm-f3268fa9.lean"
OUTPUT = ROOT / "formal/lean4/L4Factoidal/WasmVM/Spec/Wasm30.lean"
INPUT_SHA256 = "a2c2c44637c104d3d9e7799bd7ca412cbbb443dc2e87db7b1bf8209f06d0f7f8"
NAMESPACE = "L4Factoidal.WasmVM.Spec"

RULES = []  # (name, reason, count) in the order applied; filled by `rule`


class PortError(Exception):
    pass


def rule(name, reason):
    def wrap(fn):
        def run(text):
            new, count = fn(text)
            RULES.append((name, reason, count))
            return new
        run.rule_name = name
        return run
    return wrap


def expect(name, got, want):
    if got != want:
        raise PortError(f"rule {name}: changed {got} places, expected {want}")


def subn_exact(pattern, repl, text, want, name, flags=0):
    new, n = re.subn(pattern, repl, text, flags=flags)
    expect(name, n, want)
    return new, n


# ---------------------------------------------------------------------------
# Rules

def record_update(text):
    pat = re.compile(r"\((\w+|\(\w+ \w+\)) <\| ([A-Z_, ]+?) := ")
    out, i, n = [], 0, 0
    while True:
        m = pat.search(text, i)
        if not m:
            break
        # find the matching ' |>)' at depth 0 of parentheses after ':='
        j, depth = m.end(), 0
        while True:
            c = text[j]
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            elif depth == 0 and text.startswith(" |>)", j):
                break
            j += 1
        path = m.group(2).replace(", ", ".")
        out.append(text[i:m.start()])
        inner, k = record_update(text[m.end():j])
        out.append("{ %s with %s := %s }" % (m.group(1), path, inner))
        i, n = j + 4, n + 1 + k
    out.append(text[i:])
    return "".join(out), n


@rule("record-update",
      "The backend prints record update as `(r <| F := v |>)` (Rocq syntax) and a "
      "nested path as `F, G`. Lean 4 writes `{ r with F := v }` and `F.G`.")
def r_record_update(text):
    text, n = record_update(text)
    expect("record-update", n, 24)
    return text, n


# Functions the backend prints with `match` arms that do not cover every value of the
# argument type. SpecTec functions are partial: the missing cases are values outside
# the function's domain (for example `signif 16`, or `free_addrtype` applied to a
# number type that is not an address type, because the subtype addrtype <: numtype
# became the supertype). Lean 4 rejects a non-exhaustive `def`. Each gets a last arm
# `| _, ... => default`; nothing in the spec applies them outside their domain.
PARTIAL_DEFS = [
    "opt_", "signif", "expon", "free_externidx", "IN", "FN", "JN", "zsize",
    "as_deftype", "free_addrtype", "const", "default_", "fun_sx", "fun_testop_",
    "fun_relop_", "packfield_", "unpackfield_",
]


@rule("partial-def-default-arm",
      "SpecTec functions may be partial; Lean 4 needs exhaustive matches. A final arm "
      "returning `default` is added to each listed function. That arm is reached only "
      "for arguments outside the function's domain in the official spec.")
def r_partial_defs(text):
    n = 0
    for name in PARTIAL_DEFS:
        m = re.search(r"^def %s : ∀ (.*?) , .*\n" % re.escape(name), text, re.M)
        if not m:
            raise PortError(f"partial def {name} not found")
        arity = len(re.findall(r"\((?:\w+|_) :", m.group(1)))
        # the end of the equations: the first blank line after the header
        end = text.index("\n\n", m.end())
        arm = "\n  | %s =>\n    default" % ", ".join(["_"] * arity)
        text = text[:end] + arm + text[end:]
        n += 1
    return text, n


@rule("wrap-namespace",
      "Put everything in namespace %s inside a `noncomputable section` (so a derived "
      "instance that depends on a noncomputable one is not compiled either), make every "
      "generated `def`, `opaque` and `instance` noncomputable (this layer is for proofs and should emit no code), and make the "
      "preamble's `Append (Option a)` instance scoped so it does not leak to other "
      "modules." % NAMESPACE)
def r_wrap(text):
    n = 0
    text, k = subn_exact(r"^instance : Append \(Option a\) where",
                         "scoped instance : Append (Option a) where", text, 1,
                         "wrap-namespace", flags=re.M)
    n += k
    text, k = re.subn(r"^def ", "noncomputable def ", text, flags=re.M)
    n += k
    text, k = re.subn(r"^opaque ", "noncomputable opaque ", text, flags=re.M)
    n += k
    text, k = re.subn(r"^instance ", "noncomputable instance ", text, flags=re.M)
    n += k
    header = (
        "/-\n"
        "GENERATED FILE. Do not edit. Made by tools/wasmvm/port-spec.py from\n"
        "third_party/spectec-lean4/generated/Wasm-f3268fa9.lean\n(sha256 %s),\n"
        "the SpecTec Lean 4 backend's output for the WebAssembly 3.0 specification.\n"
        "Rules applied: see the script and docs/designissues/2026-11-07-wasmvm-spec-layer.md.\n"
        "-/\n\n"
        "namespace %s\n\nnoncomputable section\n\n" % (INPUT_SHA256, NAMESPACE))
    return (header + text.rstrip("\n") + "\n\nend -- noncomputable section\n\nend %s\n"
            % NAMESPACE), n


@rule("mod-operator",
      "The backend prints natural-number remainder as `a mod b`; Lean 4 writes `a % b`.")
def r_mod(text):
    return subn_exact(r" mod ", " % ", text, 14, "mod-operator")


@rule("relaxed-choice-getD",
      "`fun_relaxed2`/`fun_relaxed4` pick element i of a list of a type variable with "
      "`l[i]!`, which needs `Inhabited`, which a type variable lacks. `l.getD i X_1` is "
      "the same where i is in range, and the relaxed index always is (relaxed2 < 2, "
      "relaxed4 < 4).")
def r_relaxed(text):
    return subn_exact(r"\[(X_1, [^\]]*)\]\[(\(proj_relaxed[24]_0 i\)|0)\]!",
                      r"[\1].getD \2 X_1", text, 4, "relaxed-choice-getD")


@rule("field-prefix-application",
      "The backend prints four field reads as `(F r)`; in Lean 4 a structure field is "
      "read as `r.F` (`F r` would need the structure's namespace open).")
def r_field_prefix(text):
    return subn_exact(r"\((STRUCTS|ARRAYS|EXNS|GLOBALS) (\w+|\([^()]*\))\)",
                      r"(\2.\1)", text, 4, "field-prefix-application")


PREAMBLE_PRIMITIVES = """
/- PORT (rule preamble-primitives): SpecTec sequence primitives the backend calls but
   does not define. Their meaning is SpecTec's: `s[i] = .. f` updates element i with f;
   `s[i : j] = bs` replaces the j elements from i with bs; map over three sequences. -/
def list_update_func (l : List α) (i : Nat) (f : α → α) : List α := l.modify i f
def list_slice_update (l : List α) (i j : Nat) (bs : List α) : List α :=
  l.take i ++ bs ++ l.drop (i + j)
def list_map3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | a :: as, b :: bs, c :: cs => f a b c :: list_map3 f as bs cs
  | _, _, _ => []
"""


@rule("preamble-primitives",
      "The backend calls `list_update_func`, `list_slice_update` and `list_map3` (SpecTec "
      "sequence update, slice update, and three-way map) but its preamble does not "
      "define them. They are added to the preamble, after `setminus_`.")
def r_preamble(text):
    anchor = "/- Generated Code -/"
    if text.count(anchor) != 1:
        raise PortError("preamble anchor not found")
    return text.replace(anchor, PREAMBLE_PRIMITIVES.lstrip("\n") + anchor), 1


# Types whose derived `BEq` is recursive: the eight mutually recursive type syntax
# types, `list` (nested `List X`) and `instr` (blocks hold instruction lists).
RECURSIVE_BEQ_TYPES = ["typeuse", "heaptype", "valtype", "storagetype", "fieldtype",
                       "comptype", "subtype", "rectype", "list", "instr"]


def block_end(text, start):
    """Offset just after the declaration starting at `start`: after the enclosing
    `mutual ... end` block if there is one, else after its `deriving` line."""
    before = text[:start]
    if before.rfind("\nmutual\n") > before.rfind("\nend\n"):
        return re.compile(r"^end\n", re.M).search(text, start).end()
    return re.compile(r"^deriving .*\n", re.M).search(text, start).end()


@rule("classical-beq-for-recursive-types",
      "`deriving BEq` on a recursive type compiles to recursive C (a stack-depth "
      "recursion that tools/lean-tail-recursion-audit.py gates), although this layer is "
      "never run. For the listed types the derived `BEq` is replaced by the "
      "noncomputable instance `a == b := decide (a = b)` (classical). SpecTec's `==` "
      "means equality, so this is the same relation, and `a == b = true <-> a = b` holds "
      "by `decide_eq_true_iff` with no LawfulBEq proof needed.")
def r_classical_beq(text):
    n = 0
    for ty in RECURSIVE_BEQ_TYPES:
        m = re.search(r"^inductive %s\b((?:\s*\([^()]*\))*) : Type\b.*where\n" % ty, text, re.M)
        if not m:
            raise PortError(f"type {ty} not found")
        d = re.compile(r"^deriving Inhabited, BEq\n", re.M).search(text, m.end())
        nxt = re.compile(r"^(inductive|structure|def|abbrev|end)\b", re.M).search(text, m.end())
        if not d or (nxt and nxt.start() < d.start()):
            raise PortError(f"type {ty}: `deriving Inhabited, BEq` not found")
        text = text[:d.start()] + "deriving Inhabited\n" + text[d.end():]
        params = m.group(1).strip()
        if params:
            names = re.findall(r"\((\w+) :", params)
            head = "{%s} : BEq (%s %s)" % (" ".join(names), ty, " ".join(names))
        else:
            head = ": BEq %s" % ty
        inst = ("\n/- PORT (rule classical-beq-for-recursive-types) -/\n"
                "noncomputable instance %s := ⟨fun a b => @decide (a = b) "
                "(Classical.propDecidable _)⟩\n" % head)
        at = block_end(text, m.start())
        text = text[:at] + inst + text[at:]
        n += 1
    return text, n


@rule("strip-trailing-whitespace",
      "The backend leaves spaces at line ends (after `forall ...,` and in the preamble); "
      "`git diff --check` reports them. Removing them changes no token.")
def r_strip_ws(text):
    return subn_exact(r"[ \t]+$", "", text, 1260, "strip-trailing-whitespace", flags=re.M)


@rule("builtin-definitions", port_builtins.REASON)
def r_builtins(text):
    # After wrap-namespace: the import must come before the header and namespace.
    text, n = port_builtins.apply(text, PortError)
    expect("builtin-definitions", n, len(port_builtins.DEFS) + 1)
    return text, n


PIPELINE = [r_preamble, r_classical_beq, r_field_prefix, r_record_update, r_partial_defs, r_mod, r_relaxed, r_strip_ws, r_wrap, r_builtins]


def port(src):
    RULES.clear()
    text = src
    for step in PIPELINE:
        text = step(text)
    return text


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--input", type=pathlib.Path, default=DEFAULT_INPUT)
    ap.add_argument("--output", type=pathlib.Path, default=OUTPUT)
    ap.add_argument("--check", action="store_true",
                    help="fail if the output file differs from a fresh port")
    ap.add_argument("--rules", action="store_true", help="print the rules applied")
    args = ap.parse_args()
    raw = args.input.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != INPUT_SHA256:
        print(f"input sha256 {digest} is not the pinned {INPUT_SHA256}", file=sys.stderr)
        return 2
    try:
        out = port(raw.decode("utf-8"))
    except PortError as e:
        print(f"port-spec: {e}", file=sys.stderr)
        return 1
    if args.rules:
        for name, reason, count in RULES:
            print(f"{name} ({count}): {reason}")
    if args.check:
        if not args.output.exists() or args.output.read_text("utf-8") != out:
            print(f"{args.output} is not the port of {args.input}; rerun port-spec.py",
                  file=sys.stderr)
            return 1
        return 0
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(out, "utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
