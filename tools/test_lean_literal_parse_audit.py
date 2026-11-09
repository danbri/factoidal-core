#!/usr/bin/env python3
"""Self-test of tools/lean-literal-parse-audit.py.

    python3 tools/test_lean_literal_parse_audit.py                  # synthetic cases and the compiler control
    python3 tools/test_lean_literal_parse_audit.py --synthetic-only # no Lean toolchain needed

Synthetic cases give the tool C text of the shape that Lean 4.33.1 writes and check each mode.

The compiler control compiles a small Lean file with the pinned toolchain (`lean -c`, run from
`formal/lean4`) and checks that the tool finds the sites that file is known to have. It is the
check that the tool can still see what it looks for. When it fails after a toolchain change, read
the generated C: either the compiler writes these literals in another form (change the tool), or
it no longer reads them from text (then `L4Factoidal/Prim/FloatOfNat.lean` and the named constants
of `JS/Number.lean` are no longer needed; see docs/designissues/2026-11-09-foafnaut-perf-exploration.md).

Exit status: 0 all cases pass; 1 a case fails; 2 no case fails and the compiler control was NOT
RUN because `lean` is not on PATH (never 0 in that state, except with --synthetic-only).
"""
import contextlib
import importlib.util
import io
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
TOOL = os.path.join(HERE, "lean-literal-parse-audit.py")
LEAN_DIR = os.path.join(REPO, "formal", "lean4")

spec = importlib.util.spec_from_file_location("lean_literal_parse_audit", TOOL)
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)

RESULTS = []   # (kind, name, detail); kind: pass, fail, notrun


class NotRun(Exception):
    """A case that needs a tool that is not there (the exit code is 2, never 0)."""


def case(name):
    def deco(fn):
        try:
            fn()
        except NotRun as e:
            RESULTS.append(("notrun", name, str(e)))
        except Exception as e:  # noqa: BLE001 -- a failure of any kind fails the case
            RESULTS.append(("fail", name, "%s: %s" % (type(e).__name__, e)))
        else:
            RESULTS.append(("pass", name, ""))
        return fn
    return deco


def run(args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        rc = tool.main(args)
    return rc, out.getvalue(), err.getvalue()


# C text in the shape of Lean 4.33.1 output (for a `Float` literal: the exponent, the sign, the
# mantissa, then the call): one function with a `Nat` literal in its body, one `_init_` function
# with a `Nat` literal, one `Float` literal with a mantissa above 2^32, the two conversions, and
# `Float.ofScientific` calls of each case.
SYNTHETIC_C = """#include <lean/lean.h>
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_of_nat(lean_object*);
double l_Float_ofInt(lean_object*);
static lean_object* _init_lp_l4factoidal_A_big(void){
_start:
{
lean_object* v___x_1_;
v___x_1_ = lean_cstr_to_nat("9007199254740993");
return v___x_1_;
}
}
LEAN_EXPORT uint8_t lp_l4factoidal_A_inBody(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_;
v___x_2_ = lean_cstr_to_nat("9007199254740992");
v___x_3_ = lean_nat_dec_lt(v_n_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT double lp_l4factoidal_A_floatLit(double v_x_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; double v___x_5_;
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_3_ = 1;
v___x_2_ = lean_cstr_to_nat("42949672950");
v___x_5_ = l_Float_ofScientific(v___x_2_, v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT double lp_l4factoidal_A_slowLit(double v_x_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; double v___x_5_;
v___x_4_ = lean_unsigned_to_nat(300u);
v___x_3_ = 0;
v___x_2_ = lean_unsigned_to_nat(1u);
v___x_5_ = l_Float_ofScientific(v___x_2_, v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT double lp_l4factoidal_A_unknownLit(lean_object* v_m_1_, uint8_t v_s_2_, lean_object* v_e_3_){
_start:
{
double v___x_5_;
v___x_5_ = l_Float_ofScientific(v_m_1_, v_s_2_, v_e_3_);
return v___x_5_;
}
}
static double _init_lp_l4factoidal_A_half(void){
_start:
{
lean_object* v___x_1_; uint8_t v___x_2_; lean_object* v___x_3_; double v___x_4_;
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_2_ = 1;
v___x_1_ = lean_unsigned_to_nat(5u);
v___x_4_ = l_Float_ofScientific(v___x_1_, v___x_2_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT double lp_l4factoidal_A_conv(lean_object* v_n_1_, lean_object* v_i_2_){
_start:
{
double v___x_3_; double v___x_4_;
v___x_3_ = lean_float_of_nat(v_n_1_);
v___x_4_ = l_Float_ofInt(v_i_2_);
return v___x_3_ + v___x_4_;
}
}
"""


class Tree:
    def __init__(self, files):
        self.dir = tempfile.mkdtemp(prefix="literalaudit-")
        for rel, text in files.items():
            path = os.path.join(self.dir, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                fh.write(text)

    def close(self):
        shutil.rmtree(self.dir, ignore_errors=True)


@case("default mode: a literal in a function body is listed, the same literal in an _init_ function is not")
def _():
    t = Tree({"A.c": SYNTHETIC_C})
    try:
        rc, out, err = run([t.dir])
        assert rc == 0, (rc, err)
        lines = out.strip().split("\n")
        assert len(lines) == 3, out
        assert "A_inBody  9007199254740992" in lines[0] and "(Float literal)" not in lines[0], lines[0]
        assert "A_floatLit  42949672950  (Float literal)" in lines[1], lines[1]
        assert lines[2] == "2 sites in 2 functions of 1 files (1 C files read)", lines[2]
        assert "A_big" not in out and "9007199254740993" not in out, out
    finally:
        t.close()


@case("--count prints one line; --under keeps only the files whose path has the prefix")
def _():
    t = Tree({"X/A.c": SYNTHETIC_C, "Y/B.c": SYNTHETIC_C})
    try:
        rc, out, err = run(["--count", t.dir])
        assert rc == 0 and out.strip() == "4 sites in 4 functions of 2 files (2 C files read)", out
        rc, out, err = run(["--count", "--under", "X/", t.dir])
        assert rc == 0 and out.strip() == "2 sites in 2 functions of 1 files (1 C files read)", out
    finally:
        t.close()


@case("--conversions: Float.ofNat and Float.ofInt calls outside init code")
def _():
    t = Tree({"A.c": SYNTHETIC_C})
    try:
        rc, out, err = run(["--conversions", t.dir])
        assert rc == 0, (rc, err)
        assert "2 calls of Float.ofNat or Float.ofInt outside init code, in 1 files (1 C files read)" in out, out
        assert "A_conv" in out, out
    finally:
        t.close()


@case("--float-literals: fast case, slow case and unknown arguments; an _init_ function is not listed")
def _():
    t = Tree({"A.c": SYNTHETIC_C})
    try:
        rc, out, err = run(["--float-literals", t.dir])
        assert rc == 0, (rc, err)
        lines = out.strip().split("\n")
        assert len(lines) == 4, out
        assert "A_floatLit  42949672950e-1  fast case" in lines[0], lines[0]
        assert "A_slowLit  1e300  slow case" in lines[1], lines[1]
        assert "A_unknownLit  ?e??  ?" in lines[2], lines[2]
        assert lines[3] == ("3 calls of Float.ofScientific outside init code (1 slow case), in 1 files "
                            "(1 C files read)"), lines[3]
        assert "A_half" not in out, out
    finally:
        t.close()


@case("the case of a literal: the bounds of the fast case of Float.ofScientific in Lean 4.33.1")
def _():
    assert tool.literal_text(2 ** 53 - 1, 0, 22) == ("%de22" % (2 ** 53 - 1), "fast case")
    assert tool.literal_text(2 ** 53, 0, 0)[1] == "slow case"
    assert tool.literal_text(1, 1, 23) == ("1e-23", "slow case")
    assert tool.literal_text(None, 1, 2) == ("?e-2", "?")
    assert tool.literal_text(7, None, None) == ("7e??", "?")


@case("a path that does not exist, and a directory with no C file, give exit status 2")
def _():
    rc, out, err = run([os.path.join(tempfile.gettempdir(), "no-such-dir-literal-audit")])
    assert rc == 2 and "no such path" in err, (rc, err)
    t = Tree({"readme.txt": "no C here\n"})
    try:
        rc, out, err = run([t.dir])
        assert rc == 2 and "no C file found" in err, (rc, err)
        rc, out, err = run(["--under", "Nothing/", t.dir])
        assert rc == 2, (rc, err)
    finally:
        t.close()


CONTROL_LEAN = """def inBody (n : Nat) : Bool := n < 9007199254740992
def big : Nat := 9007199254740993
def conv (n : Nat) (i : Int) : Float := Float.ofNat n + Float.ofInt i
def small (n : Nat) : Bool := n < 4294967295
"""


@case("compiler control: the pinned Lean writes the known sites in the form the tool reads")
def _():
    env = dict(os.environ)
    env["PATH"] = os.path.join(os.path.expanduser("~"), ".elan", "bin") + os.pathsep + env.get("PATH", "")
    lean = shutil.which("lean", path=env["PATH"])
    if lean is None:
        raise NotRun("`lean` is not on PATH (install elan and the toolchain of formal/lean4/lean-toolchain)")
    tmp = tempfile.mkdtemp(prefix="literalaudit-lean-")
    try:
        src = os.path.join(tmp, "LiteralControl.lean")
        with open(src, "w") as fh:
            fh.write(CONTROL_LEAN)
        cfile = os.path.join(tmp, "LiteralControl.c")
        p = subprocess.run([lean, "-R", tmp, "-c", cfile, src], cwd=LEAN_DIR, env=env, capture_output=True,
                           text=True, timeout=300)
        assert p.returncode == 0 and os.path.exists(cfile), "lean failed: %s %s" % (p.stdout, p.stderr)
        rc, out, err = run([cfile])
        assert rc == 0, (rc, err)
        assert "inBody  9007199254740992" in out, (
            "the literal 2^53 in `inBody` was not found. Read %s: the compiler writes it in another form, or no "
            "longer reads it from text.\n%s" % (cfile, out))
        assert "1 sites in 1 functions of 1 files" in out, out      # `big` is init code; `small` is below 2^32
        rc, out, err = run(["--conversions", cfile])
        assert rc == 0 and "2 calls of Float.ofNat or Float.ofInt outside init code" in out, out
    except AssertionError:
        kept = os.path.join(tempfile.gettempdir(), "literalaudit-lean-failed")
        shutil.rmtree(kept, ignore_errors=True)
        shutil.copytree(tmp, kept)
        raise
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main():
    synthetic_only = "--synthetic-only" in sys.argv[1:]
    results = [r for r in RESULTS if not (synthetic_only and r[1].startswith("compiler control"))]
    for kind, name, detail in results:
        if kind == "fail":
            print("FAIL  %s\n      %s" % (name, detail))
        elif kind == "notrun":
            print("NOT RUN: %s -- %s" % (name, detail))
    passed = sum(1 for r in results if r[0] == "pass")
    failed = sum(1 for r in results if r[0] == "fail")
    not_run = sum(1 for r in results if r[0] == "notrun")
    print("%d pass, %d fail, %d not run (out of %d)%s" % (
        passed, failed, not_run, len(results),
        "; compiler control not requested" if synthetic_only else ""))
    if failed:
        return 1
    return 2 if not_run else 0


if __name__ == "__main__":
    sys.exit(main())
