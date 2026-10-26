#!/usr/bin/env python3
"""Self-test for tools/lean-tail-recursion-audit.py (issue 750).

Each fixture is a small Lean source and the C that Lean 4.33 emits for it (cut
down to the lines the audit reads).  The test runs the audit's `--gate` on the
fixture tree and checks the exit code and the class of each declaration.

    python3 tools/test_lean_tail_recursion_audit.py            # this tool
    python3 tools/test_lean_tail_recursion_audit.py --tool OLD # another copy

With `--tool` pointing at the audit of core 4b5892b0
(`git show 4b5892b0:tools/lean-tail-recursion-audit.py > /tmp/old.py`), the
fixtures marked `defect` below FAIL: each one is a miss of that version that
https://github.com/danbri/factoidal/issues/750 records.  The others pass on
both versions.  The `___redArg wrapper` fixture fails on the audit before
5d94d3de (`git show 5d94d3de^:tools/lean-tail-recursion-audit.py`), the miss
https://github.com/danbri/factoidal/issues/746 repaired.  Measured
2026-10-10: this tool 12 pass, 0 fail (out of 12); 4b5892b0 4 pass, 8 fail
(out of 12); 5d94d3de^ 3 pass, 9 fail (out of 12).  Exit 0 only when every
fixture passes. The temporary repository includes the real companion
compiler-replacement gate and a positive control for it; production gate
composition is exercised rather than stubbed out.
"""

import argparse, contextlib, importlib.util, io, json, os, shutil, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_TOOL = os.path.join(HERE, "lean-tail-recursion-audit.py")

P = "lp_l4factoidal_"


def cfun(name, body, tail=False):
    """One emitted C function: the header line ends with `{`, braces nest."""
    out = ["LEAN_EXPORT lean_object* %s(lean_object* x_1){" % name, "_start:", "{"]
    out += body
    if tail:
        out.append("goto _start;")
    out += ["}", "}"]
    return "\n".join(out) + "\n"


def call(callee, var="x_2"):
    return "lean_object* %s = %s(x_1);" % (var, callee)


RET = "return x_2;"

# name, defect-of-4b5892b0?, lean source, C source, allow list, check(exit, rows)
FIXTURES = []


def fixture(name, defect, lean, c, allow, check, output_contains=None):
    FIXTURES.append((name, defect, lean, c, allow, check, output_contains))


def cls(rows, decl):
    return sorted(set(r["class"] for r in rows if r["decl"] == decl))


# 1. A direct non-tail self-call over a List: the base case of the tool.
fixture(
    "direct self-call", False,
    "namespace T\ndef walk (xs : List Nat) : Nat :=\n  match xs with\n  | [] => 0\n  | _ :: r => walk r + 1\nend T\n",
    cfun(P + "T_walk", [call(P + "T_walk"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_walk") == ["length"])

# 2. A tail self-call is a loop: no row, gate passes.
fixture(
    "tail self-call is a loop", False,
    "namespace T\ndef loop (xs : List Nat) (acc : Nat) : Nat := acc\nend T\n",
    cfun(P + "T_loop", ["x_1 = x_1;"], tail=True),
    "",
    lambda ex, rows: ex == 0 and cls(rows, "T_loop") == [])

# 3. A mutual pair with no self-call: recursion only through the cycle.
fixture(
    "mutual pair", True,
    "namespace T\nmutual\ndef isEven (xs : List Nat) : Bool := true\n"
    "def isOdd (xs : List Nat) : Bool := false\nend\nend T\n",
    cfun(P + "T_isEven", [call(P + "T_isOdd"), RET]) +
    cfun(P + "T_isOdd", [call(P + "T_isEven"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_isEven") == ["length"] and cls(rows, "T_isOdd") == ["length"])

# 4. The reduced-arity copy carries the self-call; it maps to the definition.
fixture(
    "___redArg wrapper", False,
    "namespace T\ndef count (xs : List Nat) (k : Nat) : Nat := 0\nend T\n",
    cfun(P + "T_count___redArg", [call(P + "T_count___redArg"), RET]) +
    cfun(P + "T_count", [call(P + "T_count___redArg"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_count") == ["length"])

# 5. Two constants with the same short name; only A.insertBy is replaced.
fixture(
    "csimp namesake", True,
    "namespace A\ndef insertBy (xs : List Nat) : List Nat := xs\n"
    "def insertByTR (xs : List Nat) : List Nat := xs\n"
    "@[csimp] theorem insertBy_eq : @insertBy = @insertByTR := rfl\nend A\n"
    "namespace B\ndef insertBy (xs : List Nat) : List Nat := xs\nend B\n",
    cfun(P + "A_insertBy", [call(P + "A_insertBy"), RET]) +
    cfun(P + "B_insertBy", [call(P + "B_insertBy"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "A_insertBy") == ["replaced"] and cls(rows, "B_insertBy") == ["length"])

# 6. A doc-comment line that starts with "namespace" (Syntax/Turtle.lean:447,
#    the cause for readCollectionRest).
fixture(
    "namespace word in a doc comment", True,
    "namespace T\n/-- The directive's\nnamespace token, which must be a prefix. -/\n"
    "def readPrefix (cs : List Char) : Nat := 0\n"
    "def readRest (cs : List Char) : Nat := 0\nend T\n",
    cfun(P + "T_readRest", [call(P + "T_readRest"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_readRest") == ["length"])

# 7. An abbrev of Array Char plus a Nat fuel (XML/Parser.lean, the cause for
#    scanRefs): the input is the array, not the fuel.
fixture(
    "length alias with fuel", True,
    "namespace T\nabbrev Chars := Array Char\n"
    "def scan (s : Chars) (start : Nat) : Nat → Bool\n  | 0 => false\n  | f + 1 => scan s (start + 1) f\nend T\n",
    cfun(P + "T_scan", [call(P + "T_scan"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_scan") == ["length"])

# 8. `end X` of a section must not close the enclosing namespace.
fixture(
    "section end", True,
    "namespace T\nsection Helpers\ndef a (xs : List Nat) : Nat := 0\nend Helpers\n"
    "def b (xs : List Nat) : Nat := 0\nend T\n",
    cfun(P + "T_b", [call(P + "T_b"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_b") == ["length"])

# 9. A symbol with no Lean declaration is `unknown`, and `unknown` is gated.
fixture(
    "unknown is gated", True,
    "namespace T\ndef other (n : Nat) : Nat := n\nend T\n",
    cfun(P + "Mystery_f", [call(P + "Mystery_f"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "Mystery_f") == ["unknown"])

# 10. Recursion through a closure body `___lam__0` that calls back.
fixture(
    "closure body cycle", True,
    "namespace T\ndef walkTree (xs : List Nat) : Nat := 0\nend T\n",
    cfun(P + "T_walkTree", ["lean_object* c = lean_alloc_closure((void*)(" + P + "T_walkTree___lam__0), 1, 0);",
                            call("lean_apply_1"), RET]) +
    cfun(P + "T_walkTree___lam__0", [call(P + "T_walkTree"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_walkTree") == ["length"])

# 11. An allow-list line covers a declaration: gate passes.
fixture(
    "allow list line", False,
    "namespace T\ndef walk (xs : List Nat) : Nat := 0\nend T\n",
    cfun(P + "T_walk", [call(P + "T_walk"), RET]),
    "T_walk  # (c) fixture\n",
    lambda ex, rows: ex == 0)

# 12. A `where` helper with its own signature, in a file with a `where` in column 0.
fixture(
    "where helper", True,
    "namespace T\ndef outer (n : Nat) : Nat :=\n  scanList [] n\nwhere\n"
    "  scanList (acc : List Nat) (n : Nat) : Nat := n\nend T\n",
    cfun(P + "T_outer_scanList", [call(P + "T_outer_scanList"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_outer_scanList") == ["length"])

# A replaced specification passes the recursion stage, but its stale caller
# must still fail the real companion gate. This catches bypassing that gate.
fixture(
    "chained csimp gate rejects caller", False,
    "namespace T\ndef spec (xs : List Nat) : Nat := 0\n"
    "def fast (xs : List Nat) : Nat := 0\n"
    "@[csimp] theorem spec_eq : @spec = @fast := rfl\n"
    "def stale (xs : List Nat) : Nat := spec xs\nend T\n",
    cfun(P + "T_spec", [call(P + "T_spec"), RET]) +
    cfun(P + "T_fast", ["return x_1;"]) +
    cfun(P + "T_stale", [call(P + "T_spec"), RET]),
    "",
    lambda ex, rows: ex == 1 and cls(rows, "T_spec") == ["replaced"],
    "GATE FAIL: tools/lean-csimp-reach.py --gate exited 1")


def load(tool):
    spec = importlib.util.spec_from_file_location("tailrec_audit_under_test", tool)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run_fixture(tool, lean, c, allow):
    tmp = tempfile.mkdtemp(prefix="tailrec-fixture-")
    try:
        lean_dir = os.path.join(tmp, "formal", "lean4")
        ir_dir = os.path.join(lean_dir, ".lake", "build", "ir")
        os.makedirs(os.path.join(lean_dir, "L4Factoidal"))
        os.makedirs(os.path.join(ir_dir, "L4Factoidal"))
        tools_dir = os.path.join(tmp, "tools")
        os.makedirs(tools_dir)
        shutil.copyfile(os.path.join(HERE, "lean-csimp-reach.py"),
                        os.path.join(tools_dir, "lean-csimp-reach.py"))
        # The companion refuses an empty theorem/caller inventory. Supply a
        # complete, unrelated positive control, not a fake successful tool.
        with open(os.path.join(lean_dir, "lakefile.lean"), "w") as fh:
            fh.write("package l4factoidal\n")
        with open(os.path.join(lean_dir, "L4Factoidal", "ReachControl.lean"), "w") as fh:
            fh.write("namespace ReachControl\ndef spec (xs : List Nat) : List Nat := xs\n"
                     "def fast (xs : List Nat) : List Nat := xs\n"
                     "@[csimp] theorem spec_eq : @spec = @fast := rfl\n"
                     "def caller (xs : List Nat) : List Nat := spec xs\nend ReachControl\n")
        with open(os.path.join(ir_dir, "L4Factoidal", "ReachControl.c"), "w") as fh:
            fh.write(cfun(P + "ReachControl_spec", ["return x_1;"]) +
                     cfun(P + "ReachControl_fast", ["return x_1;"]) +
                     cfun(P + "ReachControl_caller", [call(P + "ReachControl_fast"), RET]))
        with open(os.path.join(lean_dir, "L4Factoidal", "Fixture.lean"), "w") as fh:
            fh.write(lean)
        with open(os.path.join(ir_dir, "L4Factoidal", "Fixture.c"), "w") as fh:
            fh.write(c)
        allow_path = os.path.join(tmp, "allow.txt")
        with open(allow_path, "w") as fh:
            fh.write(allow)
        json_path = os.path.join(tmp, "out.json")
        mod = load(tool)
        mod.REPO, mod.IR_DIR, mod.LEAN_DIR = tmp, ir_dir, lean_dir
        argv = ["lean-tail-recursion-audit.py", "--gate", "--allow", allow_path, "--json", json_path]
        saved = sys.argv
        sys.argv = argv
        buf = io.StringIO()
        try:
            with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
                ex = mod.main()
        except Exception as e:  # a crash is a failure, with its message
            return None, [], "%s: %s" % (type(e).__name__, e)
        finally:
            sys.argv = saved
        rows = []
        if os.path.exists(json_path):
            with open(json_path) as fh:
                rows = json.load(fh).get("rows", [])
        return ex, rows, buf.getvalue()
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tool", default=DEFAULT_TOOL, help="the audit script to test")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()
    npass = nfail = 0
    for name, defect, lean, c, allow, check, output_contains in FIXTURES:
        ex, rows, out = run_fixture(args.tool, lean, c, allow)
        ok = ex is not None and check(ex, rows) and (output_contains is None or output_contains in out)
        npass += ok
        nfail += not ok
        got = "exit %s; %s" % (ex, ", ".join("%s=%s" % (r["decl"], r["class"]) for r in rows) or "no rows")
        print("%-4s %-34s %-7s %s" % ("PASS" if ok else "FAIL", name,
                                      "defect" if defect else "", got))
        if args.verbose and not ok:
            print(out)
    print("%d pass, %d fail (out of %d)" % (npass, nfail, npass + nfail))
    return 0 if nfail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
