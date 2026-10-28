#!/usr/bin/env python3
"""Self-test for tools/lean-csimp-reach.py (https://github.com/danbri/factoidal/issues/871).

    python3 tools/test_lean_csimp_reach.py                  # synthetic cases and the real build
    python3 tools/test_lean_csimp_reach.py --synthetic-only # no Lean build needed
    python3 tools/test_lean_csimp_reach.py --tool PATH      # another copy of the tool (a mutant, an old version)
    python3 tools/test_lean_csimp_reach.py --mutants        # break the tool 17 ways; each must fail a case

Two groups.

SYNTHETIC cases build a small Lean tree and the C that Lean 4.33 emits for it (cut
down to the lines the tool reads: function headers ending in `{`, calls, closure
references, file-scope static closures, prototypes) and run the tool on it.  Each
case checks the exit code and the findings.  They pin the rules in the header of the
tool: what is a reference, what is the owner of a function, the exclusion rules, the
exit codes, and the Lean name mangling against symbols that the compiler emitted.

REAL BUILD cases run the tool on formal/lean4/.lake/build/ir.  The first of them is
the case of the issue: `L4Factoidal.CsimpReachFixture` (a known-bad example kept on
purpose) has callers that a `@[csimp]` replacement does not reach, and the tool must
report exactly those and not the caller that it does reach.  Until the tool existed
this case was an expected failure that named the issue (`xfail`: a failure counted
apart, and a pass failed the run); it is a plain assertion now.  Without a build the
real cases are NOT RUN and the exit code is 2; `--synthetic-only` says so on purpose.
The real cases also require `Harness.Qlvr` (the namespace is `QlvrTool`),
which is outside the library and l4wasm import closures. Build its Lean
artifacts with `lake build L4Factoidal l4wasm +Harness.Qlvr +Harness.CryptoProbe` from formal/lean4.

Exit code: 0 all run cases pass, 1 a case failed, 2 the real build was not found.
"""

import contextlib, importlib.util, io, json, os, shutil, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
TOOL = os.path.join(HERE, "lean-csimp-reach.py")
if "--tool" in sys.argv[1:]:        # test another copy of the tool, as the audit's self-test does
    TOOL = os.path.abspath(sys.argv[sys.argv.index("--tool") + 1])
IR = os.path.join(REPO, "formal", "lean4", ".lake", "build", "ir")
FIX = "L4Factoidal.CsimpReachFixture"

spec = importlib.util.spec_from_file_location("lean_csimp_reach", TOOL)
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


# ------------------------------------------------------------------ builders

P = "lp_l4factoidal_"


def cfun(name, body=(), static=False):
    """One emitted C function: the header ends in `{`, braces nest, as Lean emits them."""
    head = "LEAN_EXPORT lean_object* %s(lean_object* x_1){" % name
    if static:
        head = "static lean_object* %s(){" % name
    return "\n".join([head, "_start:", "{"] + list(body) + ["}", "}"]) + "\n"


def call(sym, var="x_2"):
    return "lean_object* %s = %s(x_1);" % (var, sym)


def closure(sym, var="x_3"):
    return "lean_object* %s = lean_alloc_closure((void*)(%s), 1, 0);" % (var, sym)


def proto(sym):
    return "LEAN_EXPORT lean_object* %s(lean_object*);\n" % sym


def static_closure(name, sym):
    return ("static const lean_closure_object %s = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) "
            "+ sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)%s, .m_arity = 1, .m_num_fixed = 0, "
            ".m_objs = {} };\n" % (name, sym))


def sym(*comps):
    return tool.mangle_name(list(comps), P)


class Tree:
    """A temporary Lean tree and C tree."""

    def __init__(self, lean, c, allow=None, lakefile=True):
        self.dir = tempfile.mkdtemp(prefix="csimpreach-")
        self.lean_dir = os.path.join(self.dir, "lean")
        self.ir_dir = os.path.join(self.dir, "ir")
        os.makedirs(self.lean_dir)
        os.makedirs(self.ir_dir)
        if lakefile:
            with open(os.path.join(self.lean_dir, "lakefile.lean"), "w") as fh:
                fh.write("package l4factoidal\n")
        for rel, text in lean.items():
            path = os.path.join(self.lean_dir, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                fh.write(text)
        for rel, text in c.items():
            path = os.path.join(self.ir_dir, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                fh.write(text)
        self.allow = os.path.join(self.dir, "allow.txt")
        with open(self.allow, "w") as fh:
            fh.write(allow or "")

    def run(self, *extra):
        out = os.path.join(self.dir, "out.json")
        buf, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(err):
            rc = tool.main(["--ir-dir", self.ir_dir, "--lean-dir", self.lean_dir, "--allow", self.allow,
                            "--json", out] + list(extra))
        res = json.load(open(out)) if os.path.exists(out) else None
        return rc, res, buf.getvalue(), err.getvalue()

    def close(self):
        shutil.rmtree(self.dir, ignore_errors=True)


with_tree = Tree


def pairs(res, status="new"):
    return sorted((f["left"], f["caller"]) for f in res["findings"] if f["status"] == status)


BASE_LEAN = """namespace A
def f (xs : List Nat) : Nat := 0
def g (xs : List Nat) : Nat := 0
@[csimp] theorem f_eq : @f = @g := rfl
def uses (xs : List Nat) : Nat := f xs
def keeps (xs : List Nat) : Nat := f xs
end A
"""


def base_c(extra=""):
    return {"A.c": (cfun(sym("A", "f"), [call(sym("A", "f"))]) +        # f calls itself
                    cfun(sym("A", "g"), [call(sym("A", "g"))]) +        # g calls itself
                    cfun(sym("A", "uses"), [call(sym("A", "g"))]) +     # a caller the replacement reached
                    extra)}


# ---------------------------------------------------------------- mangling


@case("mangling: the names that the compiler emitted")
def _():
    known = [
        (["L4Factoidal", "RDF", "isIri"], "lp_l4factoidal_L4Factoidal_RDF_isIri"),
        # a subscript: U+2083 is _u2083; `_at_` ends in `_`, so the next component gets `_00`; `spec_0` has `__`
        (["WellFounded", "opaqueFix₃", "_at_", "String", "Slice", "contains", "_at_", "L4Factoidal", "RDF",
          "isIriFast", "spec_0", "spec_0", "_redArg"],
         "lp_l4factoidal_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00L4Factoidal_RDF_"
         "isIriFast_spec__0_spec__0___redArg"),
        # a private name: `_private`, the module, the number 0, then the full name
        (["_private", "L4Factoidal", "RDF", "Core", 0, "L4Factoidal", "RDF", "instHashableTerm", "hash",
          "match_1", "splitter", "_redArg"],
         "lp_l4factoidal___private_L4Factoidal_RDF_Core_0__L4Factoidal_RDF_instHashableTerm_hash_match__1_splitter"
         "___redArg"),
        # `'` is _x27, `!` is _x21, `?` is _x3f
        (["L4Factoidal", "Tests", "iri!", "_auto_1"], "lp_l4factoidal_L4Factoidal_Tests_iri_x21___auto__1"),
        (["Std", "Legacy", "Range", "forIn'", "loop"], "lp_l4factoidal_Std_Legacy_Range_forIn_x27_loop"),
        (["L4Factoidal", "Storage", "appendPlan?"], "lp_l4factoidal_L4Factoidal_Storage_appendPlan_x3f"),
        # a component that starts with a digit or reads as an escape gets `_00`
        (["A", "x41"], "lp_l4factoidal_A_00x41"),
        (["A", "2b"], "lp_l4factoidal_A_002b"),
        (["A", "u2083"], "lp_l4factoidal_A_00u2083"),
        # a numeric component is `_n_`, and a component after it follows `__`
        (["A", 3, "b"], "lp_l4factoidal_A_3__b"),
        # a name that ends in `_` makes the next component need `_00`
        (["A", "x_", "y"], "lp_l4factoidal_A_x___00y"),
        (["A", "b", "_boxed"], "lp_l4factoidal_A_b___boxed"),
    ]
    for comps, want in known:
        got = tool.mangle_name(comps, "lp_l4factoidal_")
        assert got == want, "%r: %s != %s" % (comps, got, want)
        assert tool.demangle(got[len("lp_l4factoidal_"):]) == comps, "demangle %s -> %r" % (got, comps)
    assert tool.package_prefix("l4factoidal") == "lp_l4factoidal_"
    assert tool.package_prefix("a_b") == "lp_a__b_"


@case("mangling: a character above 0xffff, and the round trip of many names")
def _():
    comps = ["A", "x\U0001d7d8y"]
    s = tool.mangle_name(comps, "")
    assert s == "A_x_U0001d7d8y", s
    assert tool.demangle(s) == comps
    for comps in (["a"], ["_"], ["__"], ["_a"], ["a_"], ["0"], ["00"], ["a", "0"], ["a", "_0"], ["a", 0],
                  ["a", 0, "b"], ["a", 12, "_b"], ["_private", "M", 0, "x"], ["x", "_at_", "y", "spec_3"],
                  ["α", "β"], ["a", "u"], ["a", "U12345678"], ["a", "x"], ["a", "xzz"]):
        s = tool.mangle_name(comps, "")
        assert tool.demangle(s) == comps, "%r -> %s -> %r" % (comps, s, tool.demangle(s))


@case("chain_of: the owner of a function")
def _():
    d = lambda *c: tool.chain_of(list(c))   # noqa: E731
    assert d("A", "f") == (("A", "f"), ("A", "f"), False)
    assert d("A", "f", "_redArg", "_boxed")[:2] == (("A", "f"), ("A", "f"))
    assert d("A", "f", "_lam_3", "_boxed")[:2] == (("A", "f"), ("A", "f"))
    assert d("A", "f", "_closed_1")[:2] == (("A", "f"), ("A", "f"))
    assert d("A", "f", "_closed_1", "value")[:2] == (("A", "f"), ("A", "f"))
    assert d("A", "f", "_boxed_const_1")[:2] == (("A", "f"), ("A", "f"))
    # List.foldl specialised at the site of A.user: the owner is A.user
    assert d("List", "foldl", "_at_", "A", "user", "spec_0") == (("List", "foldl"), ("A", "user"), True)
    # nested specialisation: the owner is the last declaration of the chain
    assert d("X", "_at_", "Y", "_at_", "A", "user", "spec_0", "spec_0", "_redArg")[:2] == (("X",), ("A", "user"))
    # a private name inside a chain
    assert d("_private", "Init", "Data", 0, "Std", "loop", "_at_", "A", "user", "spec_1")[:2] == \
        (("Std", "loop"), ("A", "user"))
    # `spec_1` is not stripped from a name without a chain
    assert d("A", "spec_1") == (("A", "spec_1"), ("A", "spec_1"), False)
    assert tool.decl_of_symbol("_init_" + sym("A", "c", "_closed_1"), P)[1] == ("A", "c")
    assert tool.decl_of_symbol("l_List_foldl___at___00A_user_spec__0", P)[:2] == (("List", "foldl"), ("A", "user"))
    assert tool.decl_of_symbol("main", P) is None


# --------------------------------------------------------- what is a finding


@case("a caller of f is a finding; a caller of g, and f itself, are not")
def _():
    t = with_tree({"A.lean": BASE_LEAN}, base_c(cfun(sym("A", "keeps"), [call(sym("A", "f"))])))
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 1, (rc, out, err)
        assert pairs(res) == [("A.f", "A.keeps")], pairs(res)
        assert res["stats"]["theorems"] == 1 and res["stats"]["left_sides"] == 1
        assert res["stats"]["replacement_uses"] == 1
        assert res["theorems"][0]["replacement_callers"] == ["A.uses"], res["theorems"]
        assert "GATE FAIL" in out
    finally:
        t.close()


@case("without --gate the exit code is 0 whatever is found")
def _():
    t = with_tree({"A.lean": BASE_LEAN}, base_c(cfun(sym("A", "keeps"), [call(sym("A", "f"))])))
    try:
        rc, res, out, err = t.run()
        assert rc == 0 and pairs(res) == [("A.f", "A.keeps")], (rc, out)
    finally:
        t.close()


@case("no caller of f: the gate passes")
def _():
    t = with_tree({"A.lean": BASE_LEAN}, base_c())
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0 and pairs(res) == [], (rc, out, err)
        assert "GATE PASS" in out
    finally:
        t.close()


@case("a closure of f, a call of f's reduced-arity copy and of its boxed wrapper are references")
def _():
    c = base_c(cfun(sym("A", "viaClosure"), [closure(sym("A", "f", "_boxed"))]) +
               cfun(sym("A", "viaRedArg"), [call(sym("A", "f", "_redArg"))]) +
               cfun(sym("A", "viaBoxed"), [call(sym("A", "f", "_boxed"))]) +
               cfun(sym("A", "viaLam", "_lam_0"), [call(sym("A", "f"))]))
    t = with_tree({"A.lean": BASE_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert pairs(res) == [("A.f", "A.viaBoxed"), ("A.f", "A.viaClosure"), ("A.f", "A.viaLam"),
                              ("A.f", "A.viaRedArg")], pairs(res)
        kinds = {f["caller"]: {e["kind"] for e in f["evidence"]} for f in res["findings"]}
        assert kinds["A.viaClosure"] == {"closure"} and kinds["A.viaRedArg"] == {"call"}, kinds
    finally:
        t.close()


@case("a static closure at file scope is a reference held by the constant (the shape of an instance)")
def _():
    c = base_c(proto(sym("A", "f")) + static_closure(sym("A", "inst", "_closed_0") + "_value", sym("A", "f", "_boxed")))
    t = with_tree({"A.lean": BASE_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert pairs(res) == [("A.f", "A.inst")], pairs(res)
        assert res["findings"][0]["evidence"][0]["kind"] == "static-closure"
    finally:
        t.close()


@case("a prototype is not a reference")
def _():
    t = with_tree({"A.lean": BASE_LEAN}, base_c(proto(sym("A", "f")) + proto(sym("A", "f", "_boxed"))))
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0 and pairs(res) == [], pairs(res)
    finally:
        t.close()


@case("a specialised copy of f, made for a caller, is a reference by that caller")
def _():
    copy = sym("A", "f") + "___at___00A_user_spec__0"
    c = base_c(cfun(copy, [call(copy)]))
    t = with_tree({"A.lean": BASE_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert pairs(res) == [("A.f", "A.user")], pairs(res)
        assert res["findings"][0]["evidence"][0]["kind"] == "specialised-copy"
    finally:
        t.close()


@case("own family: f's lambdas, closed terms, helpers and the specialisations made inside f are not findings")
def _():
    c = base_c(cfun(sym("A", "f", "_lam_0"), [call(sym("A", "f"))]) +
               cfun(sym("A", "f", "_redArg"), [call(sym("A", "f"))]) +
               cfun("_init_" + sym("A", "f", "_closed_1"), [call(sym("A", "f"))], static=True) +
               cfun(sym("A", "f", "go"), [call(sym("A", "f"))]) +
               cfun("l_List_foldl___at___00A_f_spec__0", [call(sym("A", "f"))]))
    t = with_tree({"A.lean": BASE_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0 and res["findings"] == [], pairs(res)
    finally:
        t.close()


@case("the same short name in another namespace is another function")
def _():
    lean = BASE_LEAN + "namespace B\ndef f (xs : List Nat) : Nat := 0\ndef user (xs : List Nat) : Nat := f xs\nend B\n"
    c = base_c(cfun(sym("B", "f"), [call(sym("B", "f"))]) + cfun(sym("B", "user"), [call(sym("B", "f"))]))
    t = with_tree({"A.lean": lean}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0 and res["findings"] == [], pairs(res)
    finally:
        t.close()


@case("a private left side: the symbol carries the module, and a caller of it is found")
def _():
    lean = ("namespace P\nprivate def u (xs : List Nat) : Nat := 0\nprivate def uTR (xs : List Nat) : Nat := 0\n"
            "@[csimp] private theorem u_eq : @u = @uTR := rfl\nend P\n")
    priv = lambda *c: tool.mangle_name(["_private", "P", 0] + list(c), P)   # noqa: E731
    c = {"P.c": cfun(priv("P", "u"), []) + cfun(priv("P", "uTR"), []) +
         cfun(sym("P", "viaTR"), [call(priv("P", "uTR"))]) + cfun(sym("P", "keeps"), [call(priv("P", "u"))])}
    t = with_tree({"P.lean": lean}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert pairs(res) == [("P.u", "P.keeps")], pairs(res)
    finally:
        t.close()


# ------------------------------------------------------ specification liveness


SPEC_LEAN = """namespace S
def a (xs : List Nat) : Nat := 0
def aTR (xs : List Nat) : Nat := 0
def b (xs : List Nat) : Nat := 0
def bTR (xs : List Nat) : Nat := 0
@[csimp] theorem a_eq : @a = @aTR := rfl
@[csimp] theorem b_eq : @b = @bTR := rfl
end S
"""


def spec_c(extra):
    return {"S.c": (cfun(sym("S", "a"), []) + cfun(sym("S", "aTR"), []) + cfun(sym("S", "b"), []) +
                    cfun(sym("S", "bTR"), []) + cfun(sym("S", "user"), [call(sym("S", "aTR"))]) + extra)}


@case("a reference held by a specification that nothing reaches is suppressed")
def _():
    t = with_tree({"S.lean": SPEC_LEAN}, spec_c(cfun(sym("S", "a"), [call(sym("S", "b"))])))
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0, out
        assert [(f["left"], f["caller"], f["status"]) for f in res["findings"]] == [("S.b", "S.a", "spec-internal")], \
            res["findings"]
    finally:
        t.close()


@case("a specification that a live caller reaches makes the references in its body findings again")
def _():
    c = spec_c(cfun(sym("S", "a"), [call(sym("S", "b"))]) + cfun(sym("S", "live"), [call(sym("S", "a"))]))
    t = with_tree({"S.lean": SPEC_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 1
        assert pairs(res) == [("S.a", "S.live"), ("S.b", "S.a")], pairs(res)
    finally:
        t.close()


@case("an allowed reference does not make its specification live")
def _():
    c = spec_c(cfun(sym("S", "a"), [call(sym("S", "b"))]) + cfun(sym("S", "live"), [call(sym("S", "a"))]))
    t = with_tree({"S.lean": SPEC_LEAN}, c, allow="S.a S.live  # the call is on the leaf, where a does not recurse\n")
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0, out
        st = {(f["left"], f["caller"]): f["status"] for f in res["findings"]}
        assert st == {("S.a", "S.live"): "allowed", ("S.b", "S.a"): "spec-internal"}, st
        assert res["stale_allow"] == []
    finally:
        t.close()


# ------------------------------------------------------------------ allow list


@case("allow list: a line with a reason passes the gate; a line that matches nothing is reported stale")
def _():
    c = base_c(cfun(sym("A", "keeps"), [call(sym("A", "f"))]))
    allow = "A.f A.keeps  # read 2026-10-15: on a leaf\nA.f A.gone  # no longer exists\nA.* A.kee*s # pattern\n"
    t = with_tree({"A.lean": BASE_LEAN}, c, allow=allow)
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0, out
        assert [f["status"] for f in res["findings"]] == ["allowed"]
        assert [(s["left"], s["caller"]) for s in res["stale_allow"]] == [("A.f", "A.gone"), ("A.*", "A.kee*s")], \
            res["stale_allow"]
        assert "match no finding" in out
    finally:
        t.close()


@case("allow list: a line with no reason, or with three fields, fails the gate")
def _():
    c = base_c(cfun(sym("A", "keeps"), [call(sym("A", "f"))]))
    for allow in ("A.f A.keeps\n", "A.f A.keeps extra # reason\n", "A.f # reason\n"):
        t = with_tree({"A.lean": BASE_LEAN}, c, allow=allow)
        try:
            rc, res, out, err = t.run("--gate")
            assert rc == 1 and res["allow_errors"], (allow, rc, out)
        finally:
            t.close()


@case("allow list: `*` matches any text and nothing else matches a prefix")
def _():
    A = tool.Allow
    assert A._match("A.f", "A.f") and not A._match("A.f", "A.fx") and not A._match("A.f", "xA.f")
    assert A._match("A.*", "A.f.go") and A._match("*", "anything") and A._match("A.*Loop", "A.readLoop")
    assert not A._match("A.*Loop", "A.readLoops")
    assert A._match("A.appendPlan?", "A.appendPlan?") and not A._match("A.appendPlan?", "A.appendPlanX")


# ---------------------------------------------------------------- the reasons


@case("reasons: before the theorem, after it, and a module that does not import it")
def _():
    lean_a = """namespace A
def f (xs : List Nat) : Nat := 0
def g (xs : List Nat) : Nat := 0
def early (xs : List Nat) : Nat := f xs
@[csimp] theorem f_eq : @f = @g := rfl
def late (xs : List Nat) : Nat := f xs
def uses (xs : List Nat) : Nat := f xs
end A
"""
    lean_b = "import A\nnamespace B\ndef viaImport (xs : List Nat) : Nat := A.f xs\nend B\n"
    lean_c = "namespace C\ndef noImport (xs : List Nat) : Nat := A.f xs\nend C\n"
    c = {"A.c": (cfun(sym("A", "f"), []) + cfun(sym("A", "g"), []) + cfun(sym("A", "early"), [call(sym("A", "f"))]) +
                 cfun(sym("A", "late"), [call(sym("A", "f"))]) + cfun(sym("A", "uses"), [call(sym("A", "g"))])),
         "B.c": cfun(sym("B", "viaImport"), [call(sym("A", "f"))]),
         "C.c": cfun(sym("C", "noImport"), [call(sym("A", "f"))])}
    t = with_tree({"A.lean": lean_a, "B.lean": lean_b, "C.lean": lean_c}, c)
    try:
        rc, res, out, err = t.run("--gate")
        why = {f["caller"]: f["reason"] for f in res["findings"]}
        assert why == {"A.early": "before-theorem", "A.late": "after-theorem", "B.viaImport": "after-theorem",
                       "C.noImport": "not-imported"}, why
    finally:
        t.close()


@case("reasons: a module that imports the theorem's module through another module is not 'not-imported'")
def _():
    lean_a = BASE_LEAN
    lean_b = "import A\nnamespace B\ndef x := 1\nend B\n"
    lean_c = "import B\nnamespace C\ndef viaChain (xs : List Nat) : Nat := A.f xs\nend C\n"
    c = base_c() | {"C.c": cfun(sym("C", "viaChain"), [call(sym("A", "f"))])}
    t = with_tree({"A.lean": lean_a, "B.lean": lean_b, "C.lean": lean_c}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert [(f["caller"], f["reason"]) for f in res["findings"]] == [("C.viaChain", "after-theorem")], res["findings"]
    finally:
        t.close()


# ---------------------------------------------------------- reading the source


@case("the source reader: attribute forms, statements, namespaces, opens, comments")
def _():
    lean = """/- a block comment with @[csimp] theorem fake : @x = @y := rfl -/
-- a line comment @[csimp] theorem fake2 : @x = @y := rfl
namespace N.M
open Other in
def a := 1
section Inner
open Q
@[csimp]
theorem one : @N.M.a = @N.M.b := rfl
end Inner
@[inline, csimp] protected theorem two : N.M.a = N.M.b := rfl
@[csimp] theorem Foo.three.{u} : @a.{u} = @b.{u} := rfl
@[csimp] theorem four (n : Nat) : @a = @b := rfl
@[csimp] def five : Nat := 0
attribute [csimp] one
end N.M
"""
    sc = tool.LeanScan()
    tool.scan_file(sc, "T", "T.lean", lean.splitlines(keepends=True))
    th = sc.theorems
    names = [(t["thm"], t["lhs"], t["rhs"], bool(t["error"])) for t in th]
    assert names[0] == ("one", "N.M.a", "N.M.b", False), names
    assert names[1] == ("two", "N.M.a", "N.M.b", False), names
    assert names[2] == ("Foo.three", "a", "b", False), names
    assert names[3] == ("four", "a", "b", False), names     # binders before the colon do not matter
    assert th[4]["error"] and "not followed by `theorem`" in th[4]["error"], names
    assert th[5]["error"] and "attribute [csimp]" in th[5]["error"], names
    assert len(th) == 6, len(th)     # nothing is read from the two comments
    assert th[0]["ns"] == ["N", "M"] and th[0]["opens"] == ["Q"], (th[0]["ns"], th[0]["opens"])
    assert th[1]["opens"] == [], th[1]["opens"]       # the `open Q` ended with its section
    # an `open ... in` is not in force afterwards
    assert "Other" not in th[0]["opens"]


@case("name resolution: the namespace chain, the dotted prefix of the theorem, opens, _root_")
def _():
    th = dict(module="M", ns=["A", "B"], thm="C.t", opens=["O"])
    c = [".".join(x) for x in tool.candidates(th, "f")]
    assert c == ["A.B.C.f", "A.B.f", "A.f", "f", "A.B.C.O.f", "A.B.O.f", "A.O.f", "O.f"], c
    assert [".".join(x) for x in tool.candidates(th, "_root_.X.f")] == ["X.f"]
    assert [".".join(x) for x in tool.candidates(th, "Term.joinKey")][0] == "A.B.C.Term.joinKey"


# ------------------------------------------------------------------ exit codes


@case("exit 2: no @[csimp] theorem, no emitted C, no use of any replacement; exit 1: an unresolved theorem")
def _():
    t = with_tree({"A.lean": "namespace A\ndef f := 1\nend A\n"}, base_c())
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 2 and "no @[csimp] theorem" in err, (rc, err)
    finally:
        t.close()
    t = with_tree({"A.lean": BASE_LEAN}, {})
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 2 and "no .c file" in err, (rc, err)
    finally:
        t.close()
    # the replacement is never called: a scanner that sees nothing must not report a zero
    t = with_tree({"A.lean": BASE_LEAN}, {"A.c": cfun(sym("A", "f"), []) + cfun(sym("A", "g"), [])})
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 2 and "no use of any @[csimp] replacement" in err, (rc, err)
    finally:
        t.close()
    # the left side has no C symbol: the theorem is listed, and the gate fails
    c = {"A.c": cfun(sym("A", "g"), []) + cfun(sym("A", "uses"), [call(sym("A", "g"))])}
    t = with_tree({"A.lean": BASE_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 1 and len(res["problems"]) == 1 and "A.f" not in str(res["findings"]), (rc, res["problems"])
        assert "NOT RESOLVED" in out
    finally:
        t.close()


@case("a theorem in a module with no emitted C file is listed as not built; it does not fail the gate")
def _():
    other = "namespace B\ndef p := 1\ndef q := 1\n@[csimp] theorem p_eq : @p = @q := rfl\nend B\n"
    t = with_tree({"A.lean": BASE_LEAN, "B.lean": other}, base_c())
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0 and res["problems"] == [], (rc, res["problems"], err)
        assert [x["theorem"] for x in res["not_built"]] == ["p_eq"], res["not_built"]
        assert "NOT BUILT B.lean" in out, out
    finally:
        t.close()


@case("an unreadable statement and the `attribute [csimp]` form fail the gate; they are not skipped")
def _():
    lean = BASE_LEAN + "namespace A\n@[csimp] theorem bad : f 1 = g 1 := rfl\nattribute [csimp] f_eq\nend A\n"
    t = with_tree({"A.lean": lean}, base_c())
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 1 and len(res["problems"]) == 2, (rc, res["problems"])
    finally:
        t.close()


@case("a C file whose module has no Lean source is ignored and counted")
def _():
    c = base_c() | {"Gone.c": cfun(sym("Gone", "x"), [call(sym("A", "f"))])}
    t = with_tree({"A.lean": BASE_LEAN}, c)
    try:
        rc, res, out, err = t.run("--gate")
        assert rc == 0 and res["stats"]["stale_cfiles"] == 1, (rc, res["stats"])
    finally:
        t.close()


@case("a left side with two theorems is one target, and both are listed")
def _():
    lean_a = BASE_LEAN
    lean_b = ("import A\nnamespace B\ndef h (xs : List Nat) : Nat := 0\nopen A in\n@[csimp] theorem f_eq2 : @A.f = @h := rfl\n"
              "end B\n")
    c = base_c() | {"B.c": cfun(sym("B", "h"), []) + cfun(sym("B", "uses"), [call(sym("B", "h"))])}
    t = with_tree({"A.lean": lean_a, "B.lean": lean_b}, c)
    try:
        rc, res, out, err = t.run()
        assert res["stats"]["theorems"] == 2 and res["stats"]["left_sides"] == 1, res["stats"]
        assert "left side with two theorems" in out
    finally:
        t.close()


# ---------------------------------------------------------------- real build

REQUIRED_REAL_MODULES = ("L4Factoidal.CsimpReachFixture", "Harness.Qlvr", "Harness.CryptoProbe")


def missing_real_artifacts(ir_dir):
    return [module for module in REQUIRED_REAL_MODULES
            if not os.path.isfile(os.path.join(ir_dir, *module.split(".")) + ".c")]


@case("real-build prerequisites: a partial library build does not provide the Qlvr harness")
def _():
    with tempfile.TemporaryDirectory() as tmp:
        assert missing_real_artifacts(tmp) == list(REQUIRED_REAL_MODULES)
        for index, module in enumerate(REQUIRED_REAL_MODULES):
            path = os.path.join(tmp, *module.split(".")) + ".c"
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as fh:
                fh.write("// prerequisite presence control\n")
            assert missing_real_artifacts(tmp) == list(REQUIRED_REAL_MODULES[index + 1:])
        assert missing_real_artifacts(tmp) == []


def real_cases():
    @case("real build: the tool reports the callers of the fixture's specification that the replacement did not reach")
    def _():
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, "reach.json")
            buf = io.StringIO()
            with contextlib.redirect_stdout(buf):
                rc = tool.main(["--json", out])
            assert rc == 0, "the tool failed on the real build (exit %d):\n%s" % (rc, buf.getvalue()[-3000:])
            res = json.load(open(out))
        found = {(f["left"], f["caller"]): f for f in res["findings"] if f["status"] != "spec-internal"}
        spec_name = FIX + ".weightSpec"
        for caller, reason in (("callBefore", "before-theorem"), ("callViaInstance", "after-theorem"),
                               ("callViaInline", "after-theorem"), ("weightInline", "before-theorem"),
                               ("instWeighList", "before-theorem")):
            f = found.get((spec_name, FIX + "." + caller))
            assert f is not None, ("no finding for %s: the tool lost the case, or the compiler now replaces it "
                                   "(read the header of CsimpReachFixture.lean before changing this case)" % caller)
            assert f["reason"] == reason, (caller, f["reason"])
        assert (spec_name, FIX + ".callDirect") not in found, "callDirect was reached by the replacement"
        assert all(f["left"] != FIX + ".weightFast" for f in res["findings"])
        row = [t for t in res["theorems"] if t["left"] == spec_name]
        assert len(row) == 1 and FIX + ".callDirect" in row[0]["replacement_callers"], row

    @case("real build: every @[csimp] theorem of the source is resolved, and the positive control sees uses")
    def _():
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, "reach.json")
            with contextlib.redirect_stdout(io.StringIO()):
                tool.main(["--json", out])
            res = json.load(open(out))
        assert res["problems"] == [], res["problems"]
        assert res["stats"]["theorems"] >= 100 and res["stats"]["replacement_uses"] > 100, res["stats"]

    @case("real build: the #guard lines of the fixture emit no function")
    def _():
        path = os.path.join(IR, "L4Factoidal", "CsimpReachFixture.c")
        defs, _dup = tool.scan_definitions([(path, "L4Factoidal/CsimpReachFixture.c", FIX)])
        expect = {"weightSpec", "weightInline", "callBefore", "weightLoop", "weightFast", "callDirect",
                  "callViaInstance", "callViaInline", "instWeighList"}
        owners = set()
        for name in defs:
            if name.startswith("initialize_"):
                continue
            d = tool.decl_of_symbol(name, "lp_l4factoidal_")
            assert d is not None, name
            owner = d[1]
            assert owner[:2] == ("L4Factoidal", "CsimpReachFixture") and owner[2] in expect, (name, owner)
            owners.add(owner[2])
        assert owners == expect, owners ^ expect

    @case("real build: the callers repaired for the issue stay repaired")
    def _():
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, "reach.json")
            with contextlib.redirect_stdout(io.StringIO()):
                tool.main(["--json", out])
            res = json.load(open(out))
        rows = {t["left"]: t for t in res["theorems"]}
        # JSON-LD framing: the twin of the `where` helper never reached its only caller; matchingSubjects has its own twin
        assert "L4Factoidal.JSONLD.matchingSubjects" in rows, "the csimp theorem for matchingSubjects is gone"
        assert any(c.endswith("frameRec") for c in rows["L4Factoidal.JSONLD.matchingSubjects"]["replacement_callers"])
        helper = [f for f in res["findings"] if f["left"] == "L4Factoidal.JSONLD.matchingSubjects.matchingSubjectsGo"]
        assert all(f["status"] == "spec-internal" for f in helper), helper
        # qlvr: the side index imports the module of the cmpBytes twin
        users = rows["L4Factoidal.Qlvr.cmpBytes"]["replacement_callers"]
        for caller in ("L4Factoidal.Qlvr.Side.sortChunk", "L4Factoidal.Qlvr.Side.sideLookupM", "QlvrTool.runSideIndex"):
            assert caller in users, "%s calls cmpBytes again" % caller
        left = {f["caller"] for f in res["findings"] if f["left"] == "L4Factoidal.Qlvr.cmpBytes" and f["status"] != "spec-internal"}
        assert left == {"L4Factoidal.Qlvr.cmpBytesFast"}, left
        # XML: the specification parseChildren had a second entry (the RDF/XML reader's parseChildrenFold) that
        # no theorem covered; it has its own theorem now, and the pair of specifications is held by no live code
        assert "L4Factoidal.XML.parseChildren" in rows, "the csimp theorem for parseChildren is gone"
        assert "L4Factoidal.Syntax.RdfXml.parseChildrenFold" in rows["L4Factoidal.XML.parseChildren"]["replacement_callers"], \
            "parseChildrenFold calls parseChildren again"
        ring = [f for f in res["findings"] if f["left"] in ("L4Factoidal.XML.parseChildren", "L4Factoidal.XML.parseElement")]
        assert ring and all(f["status"] == "spec-internal" for f in ring), ring

    @case("real build: Lean's own @[csimp] table and the source reader list the same theorems (--cross-check)")
    def _():
        if shutil.which("lake") is None:
            raise NotRun("`lake` is not on PATH")
        with contextlib.redirect_stderr(io.StringIO()) as err:
            got = tool.cross_check(tool.scan_lean_tree(os.path.join(REPO, "formal", "lean4")), IR,
                                   os.path.join(REPO, "formal", "lean4"))
        if got is None:
            raise NotRun("`lake env lean` could not import the built modules: " + err.getvalue()[-300:])
        only_src, only_lean, n_lean, skipped = got
        assert not only_src and not only_lean, (only_src, only_lean)
        assert n_lean >= 100, n_lean

    @case("real build: the gate passes on the tree")
    def _():
        with contextlib.redirect_stdout(io.StringIO()):
            rc = tool.main(["--gate"])
        assert rc == 0, "gate failed (exit %d)" % rc


# ------------------------------------------------------------------ mutants
# Each entry replaces one piece of the tool by a break and expects the synthetic cases to fail.  A pattern
# that no longer occurs in the tool is reported, so that this table is edited with the tool.

MUTANTS = {
    "static closures are not read": (
        '                    elif s.startswith("static const lean_closure_object "):\n                        m = CLOSURE_DEF.match(s)\n                        if m:\n                            for t in tok.finditer(s):',
        '                    elif False:\n                        m = CLOSURE_DEF.match(s)\n                        if m:\n                            for t in tok.finditer(s):'),
    "no own-family exclusion": (
        '    return owner_cfile == decl_cfile and (\n        owner == comps or (len(owner) > len(comps) and owner[:len(comps)] == comps))',
        '    return False'),
    "helpers of f are findings": (
        'owner == comps or (len(owner) > len(comps) and owner[:len(comps)] == comps))',
        'owner == comps)'),
    "boxed wrappers are not references": (
        '        mangle_name(base + ["_boxed"], prefix): "boxed",\n', ''),
    "reduced-arity copies are not references": (
        '        mangle_name(base + ["_redArg"], prefix): "redArg",\n        mangle_name(base + ["_redArg", "_boxed"], prefix): "redArg-boxed",\n', ''),
    "mangling: `_` stays `_`": (
        '        elif c == "_":\n            out.append("__")', '        elif c == "_":\n            out.append("_")'),
    "mangling: no `_00`": (
        '                need = (isinstance(prev, str) and prev.endswith("_")) or _check_disambiguation(m)', '                need = False'),
    "specialised copies are not read": (
        '        while lo < len(names) and names[lo].startswith(stem):', '        while False:'),
    "no suppression by specification": (
        '        if f["spec"] is not None and sym_of[f["spec"]] not in live:\n            f["status"] = "spec-internal"',
        '        if False:\n            f["status"] = "spec-internal"'),
    "an allowed finding makes a specification live": (
        '            if holder_live and f["allowed_by"] is None and f["left_sym"] not in live:',
        '            if holder_live and f["left_sym"] not in live:'),
    "no positive control": (
        '    if targets and right_total == 0:', '    if False:'),
    "private names are not resolved": (
        '        if private_symbol(th["module"], comps, prefix) in defined:\n            return comps, th["module"]', ''),
    "the reason is always `after-theorem`": (
        '    if caller_mod in thm_mods:\n        thm_line', '    if False:\n        thm_line'),
    "an allow line needs no reason": (
        '                    elif not reason:\n                        self.errors.append("%s:%d: no reason after `#`" % (os.path.basename(path), n))\n                    else:',
        '                    else:'),
    "the attribute command is ignored": (
        '        if ma and any(a.strip() == "csimp" for a in ma.group(1).split(",")):', '        if False:'),
    "comments are not blanked": (
        '        code.append("".join(out))\n    return code', '        code.append(raw.rstrip("\\n"))\n    return code'),
    "C files of deleted modules are read": (
        '            if module in modules:\n                found.append((path, rel, module))',
        '            if True:\n                found.append((path, rel, module))'),
}


def run_mutants():
    import subprocess
    src = open(TOOL).read()
    survived = []
    with tempfile.TemporaryDirectory() as tmp:
        for name, (old, new) in MUTANTS.items():
            if old not in src:
                print("PATTERN MISSING  %s" % name)
                survived.append(name)
                continue
            path = os.path.join(tmp, "mutant.py")
            with open(path, "w") as fh:
                fh.write(src.replace(old, new, 1))
            p = subprocess.run([sys.executable, os.path.abspath(__file__), "--synthetic-only", "--tool", path],
                               capture_output=True, text=True, timeout=600)
            line = [l for l in p.stdout.splitlines() if " pass, " in l]
            killed = p.returncode == 1 and bool(line)     # a mutant that does not even run is not a kill
            print("%s  %s  %s" % ("killed  " if killed else "SURVIVED", name, line[-1] if line else p.stderr[-200:]))
            if not killed:
                survived.append(name)
    print("%d mutants, %d killed, %d survived or missing" % (len(MUTANTS), len(MUTANTS) - len(survived), len(survived)))
    return 1 if survived else 0


def main():
    if "--mutants" in sys.argv[1:]:
        return run_mutants()
    synthetic_only = "--synthetic-only" in sys.argv[1:]
    not_run = False
    if synthetic_only:
        pass
    elif missing := missing_real_artifacts(IR):
        not_run = True
        print("NOT RUN: missing emitted C for %s at %s -- run "
              "`lake build L4Factoidal l4wasm +Harness.Qlvr +Harness.CryptoProbe` in formal/lean4, "
              "or pass --synthetic-only" % (", ".join(missing), IR))
    else:
        real_cases()
    bad = sum(1 for r in RESULTS if r[0] == "fail")
    ok = sum(1 for r in RESULTS if r[0] == "pass")
    skipped = [r for r in RESULTS if r[0] == "notrun"]
    for kind, name, detail in RESULTS:
        if kind == "fail":
            print("FAIL %s: %s" % (name, detail))
        elif kind == "notrun":
            print("NOT RUN %s: %s" % (name, detail))
    print("%d pass, %d fail, %d not run (out of %d)%s" % (
        ok, bad, len(skipped), len(RESULTS),
        "; real-build cases NOT RUN" if not_run else ("; real-build cases not requested" if synthetic_only else "")))
    if bad:
        return 1
    return 2 if (not_run or skipped) else 0


if __name__ == "__main__":
    sys.exit(main())
