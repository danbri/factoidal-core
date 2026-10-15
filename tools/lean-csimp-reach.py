#!/usr/bin/env python3
"""Check that every `@[csimp]` replacement reaches the compiled code that should use it.

https://github.com/danbri/factoidal/issues/871.  Record: docs/designissues/2026-10-15-csimp-reach.md.

WHAT GOES WRONG
===============
A theorem `@[csimp] theorem f_eq : @f = @g` makes the code generator emit `g`
wherever the source says `f`.  Lean makes the replacement while it turns the VALUE
of the declaration being compiled into its intermediate form
(`Lean/Compiler/LCNF/ToLCNF.lean`, `CSimp.replaceConstant`), and only in declarations
compiled after the theorem is in the environment.  Later passes inline the stored
body of another declaration into the caller, and that body was compiled before the
theorem.  So a caller keeps calling `f` in the emitted C when
  * it is compiled before the theorem (earlier in the module, or in a module that
    does not import the theorem's module);
  * it is in the same `mutual` block as `f`, or `f` is a `where` helper of it (the
    helper is part of the caller's declaration, so no theorem can come between
    them: `JSONLD.matchingSubjects`, found by this tool);
  * it reaches `f` through a definition compiled before the theorem that the
    compiler inlines: an instance (the case of 2026-10-15, `Hashable Term`, where
    `lake build` passed and the C of `FastGraph` still called the recursive hash:
    skills/lean4-proof-patterns/SKILL.md, section 9d), an `@[inline]` or
    `@[macro_inline]` definition, a function that is specialised.
`tools/lean-tail-recursion-audit.py` cannot see this: it marks the left side of every
`@[csimp]` theorem `replaced` from the THEOREM and never looks at the callers.  This
tool looks at the callers.

METHOD (read-only; the Lean source for the theorems, the emitted C for the callers)
===================================================================================
 1. Find every `@[csimp]` theorem under formal/lean4 (`@[csimp]` or `@[.., csimp, ..]`
    before `theorem`, on the same line or the line above; the statement `@f = @g` or
    `f = g`, with an optional universe list).  The list is derived from the tree on
    every run.  An empty list is exit 2.  A theorem whose statement this tool cannot
    read, and the `attribute [csimp]` command form, fail the gate: they are listed,
    never skipped.
 2. Resolve the names `f` and `g` against the namespace chain, the declaration's own
    dotted prefix and the `open` namespaces in force, in the order Lean tries them,
    and map each to its C symbol with Lean's own mangling
    (`Lean/Compiler/NameMangling.lean`, Lean 4.33): `_` is `__`; any other character
    that is not an ASCII letter or digit is `_xHH`, `_uHHHH` or `_UHHHHHHHH` by its
    code point; a component that could be read as an escape or a number gets `_00`;
    a numeric component is `_n_`; a private name starts `_private.<Module>.0.`; the
    package prefix is `lp_<package>_`.  A name counts as resolved only if its symbol
    is DEFINED in some emitted C file.  A mangling error therefore shows as an
    unresolved theorem, for every theorem, and cannot pass as "no callers".
 3. Read every `.c` under formal/lean4/.lake/build/ir whose module has a Lean source
    file (a C file of a deleted module is ignored and counted).  A reference to `f`
    is any occurrence of the symbol of `f`, or of its `___boxed`, `___redArg` or
    `___redArg___boxed` form, inside a function body or in a file-scope
    `static const lean_closure_object` (the closure that an instance with one field
    is compiled to).  A specialised copy of `f` (`f___at___00<caller>_spec__N`) is a
    reference by `<caller>`.  The bodies of `initialize_*` functions are not read: they
    only assign the module's own constants.
 4. Name the declaration that holds each reference (the OWNER): demangle the symbol,
    drop `_boxed`, `_redArg`, `_lam_N`, `_closed_N`, `_closed_N` + `_value`,
    `_boxed_const_N` and `spec_N`, and take the declaration after the last `_at_` (the
    declaration the code was specialised for).  Every owner that is not excluded below
    is a FINDING: (f, owner).
 5. Say why, from the import graph of the Lean sources and the line of the owner's
    declaration: `not-imported` (the owner's module does not import the module of the
    theorem), `before-theorem` (same module, declared above the theorem),
    `after-theorem` (compiled after the theorem and still calls `f`: the call came in
    through an inlined or specialised definition), `same-module` (order unknown).
    What to do: `not-imported`, import the module of the theorem with a comment that
    says why (if that makes a cycle, give the owner a twin after the theorem, as
    `matchingSubjectsFast` does); `before-theorem`, give the owner a twin declared
    after the theorem, or move the theorem above the owner; `after-theorem`, install
    the fast form where it is reached (an `instance (priority := high)`, as for
    `Hashable Term`), or state the inlined definition with `g`.  A finding that is
    right to leave goes on the allow list with its reason.

EXCLUSION RULES (each with its reason; a reference is NOT a finding when ...)
-----------------------------------------------------------------------------
  own family      the owner is `f`, or a `where`/`let rec` helper of `f` (`f.go`: its
                  name starts with `f.`), in the C file of `f`.  Reason: these are the
                  body of `f`; `f` calling itself is not a caller.  This covers the
                  boxed and reduced-arity forms, the lambda-lifted pieces, the closed
                  terms and every specialisation made inside `f`.
  Lean theorems   (the equation lemmas, `f_eq`, specification lemmas)  Reason: a
                  theorem is erased before the code generator, so no C function holds
                  one.  No rule is needed and none is applied.
  #eval, #guard   Reason: their code runs in the interpreter and is not emitted into
                  the module's C.  Checked on `L4Factoidal.CsimpReachFixture`, which
                  has four `#guard` lines that call the specification: the
                  self-test asserts that the module's C holds no function for them.
                  A `private def` that only the `#guard` lines call IS emitted; it
                  is a finding, and goes on the allow list with the reason `guard`.
  specification   the owner is itself the left side of a `@[csimp]` theorem (or a
                  helper of one), and is not LIVE.  Reason: the code generator never
                  calls it, so its body runs only if something reaches it.  A
                  specification is LIVE when a finding against it is held by live
                  code and is not on the allow list; a live specification makes the
                  references in its own body findings again.  The rule is decided by
                  the theorems, not by the spelling of a name.  A name pattern
                  (`*Spec`, `*Sem`) would hide `labelStepSem`, which the loop of
                  `ggpLabeledBnodes` calls at run time (anti-pattern 31).
  allow list      `tools/lean-csimp-reach-allow.txt`: one line `f owner # reason` for
                  a finding that was read and judged harmless or left on purpose.
                  The reason is required.  `*` in either name matches any text.  A
                  line that matches no finding is reported as stale.

EXIT CODES
==========
  0  no finding outside the allow list (without `--gate`, 0 whatever is found)
  1  `--gate` and: a finding not on the allow list, a theorem whose statement or names
     could not be resolved, an allow line with no reason, or (`--cross-check`) a
     theorem that the source reader and Lean's own table do not both list
  2  nothing to check: no `@[csimp]` theorem, no emitted C, no use of any replacement
     in the C (the positive control: the scanner or the symbol mapping is wrong, and
     a zero would mean nothing), or `--cross-check` could not run

USAGE
=====
    cd formal/lean4 && lake build           # first: the tool reads the emitted C
    python3 tools/lean-csimp-reach.py --gate
    python3 tools/lean-csimp-reach.py --json /tmp/reach.json --verbose
    python3 tools/lean-csimp-reach.py --cross-check   # needs `lake` on PATH; see LIMITS
    python3 tools/test_lean_csimp_reach.py            # the self-test

LIMITS (state these with any result; anti-pattern 28)
=====================================================
  * A call whose BODY was inlined leaves no symbol.  If the compiler inlined the body
    of `f` itself into a caller (a small or `@[inline]` `f`), the C holds the code of
    `f` and no reference to it, and this tool reports nothing.  The tool sees a path
    that keeps a CALL of `f`.  It does not see a path that copied the body.
  * The tool reads the emitted C of the last `lake build`.  A module that was not
    built, or a stale build, is not audited; a left side with no C symbol is an
    unresolved theorem and fails the gate.
  * References are found by symbol name.  A function reached only through `lean_apply`
    of a closure built in another module is seen where the closure is built, not where
    it is applied.
  * Name resolution reproduces Lean's order by looking for a defined symbol; it does
    not elaborate.  A theorem that depends on `export`, a notation or a macro for the
    name of `f` is unresolved, and says so.
  * Only `formal/lean4` is read.  A `@[csimp]` theorem of the Lean core library
    (`List.map` and the like) is not audited.  A repair by an instance of higher
    priority (`instHashableTermLoop`) is not a `@[csimp]` theorem and is not audited.
  * `--cross-check` compares the theorems found in the source with Lean's own table (the
    environment extension `Lean.Compiler.CSimp.ext`) after importing every built
    module of the package, so a theorem registered by a macro or by a form this tool
    does not read is reported.  A module that defines the root-level `main` cannot be
    imported with another one; such a module is imported alone when the source scan
    found a theorem in it, and is otherwise not covered by the cross-check.
  * Two theorems with the same left side (`isIri_eq_isIriFast` in `RDF/Core.lean` and
    in `Syntax/NTriples.lean`) are one target here; Lean keeps the last one it imports.
    The tool lists both and judges `not-imported` against the modules of both.
  * A finding names the first reason that applies.  The reason points to where to
    look; it does not prove the cause.
  * The tool judges which function the C calls.  It does not judge whether the
    replacement is faster.
  * A specification that compiled code calls and that has no `@[csimp]` theorem of its
    own is not reported (`XML.parseChildren` until 2026-10-15).  When a finding names
    such a function as the owner, grep the tree for its other callers.

WHAT THIS TOOL MISSED, AND WHY (keep this list; each entry cost a defect)
=========================================================================
  * 2026-10-15 (https://github.com/danbri/factoidal/issues/867): a `@[csimp]` theorem
    for the derived `Hashable Term` passed `lake build` and the tail-recursion audit
    while `FastGraph` still called the recursive hash.  The audit reads the theorem,
    not the callers.  `L4Factoidal.CsimpReachFixture` is the same mechanism in the
    smallest form, and `tools/test_lean_csimp_reach.py` asserts that this tool
    reports it.
  * 2026-10-15 (this tool, first run on the tree): the theorem for the `where` helper
    `JSONLD.matchingSubjects.matchingSubjectsGo` (issue 746) had never reached its only
    caller, `matchingSubjects`, which is the declaration the helper belongs to.  The
    audit counted the helper as `replaced`.  Repaired by a twin of `matchingSubjects`.
    Two modules of the qlvr side index called `cmpBytes` without importing the module
    of its twin (issue 804).  The tool's list of findings is in the record.
  * 2026-10-15 (reading the tool's own findings): the finding "`XML.parseElement` is still
    called by `XML.parseChildren`" led to a second caller of `parseChildren`:
    `Syntax/RdfXml.lean`, `parseChildrenFold`.  `parseChildren` is the specification of
    `parseChildrenW`, but it had no `@[csimp]` theorem of its own: the theorem for
    `parseElement` reaches the document element only.  This tool lists the callers of the
    left sides of theorems, so it could not report that caller, and an allow-list line of
    the tail-recursion audit said "specification only" for `parseChildren`.  A chain of
    markup entities under `rdf:RDF` used one native frame for each level (6,000 levels
    overflowed 512 KB).  Repaired by `parseChildren_eq_parseChildrenFromStart`.
"""

import argparse
import bisect
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_DIR = os.path.join(REPO, "formal", "lean4")
IR_DIR = os.path.join(LEAN_DIR, ".lake", "build", "ir")
ALLOW_FILE = os.path.join(REPO, "tools", "lean-csimp-reach-allow.txt")
DEFAULT_PACKAGE = "l4factoidal"

# ------------------------------------------------------------------ mangling
# Lean 4.33 `Lean.Name.mangle` (src/lean/Lean/Compiler/NameMangling.lean).  The
# self-test checks every rule below against symbols that the compiler emitted.


def mangle_string(s):
    out = []
    for c in s:
        o = ord(c)
        if c.isascii() and (c.isalpha() or c.isdigit()):
            out.append(c)
        elif c == "_":
            out.append("__")
        elif o < 0x100:
            out.append("_x%02x" % o)
        elif o < 0x10000:
            out.append("_u%04x" % o)
        else:
            out.append("_U%08x" % o)
    return "".join(out)


def _hex_run(m, i, k):
    seg = m[i:i + k]
    return len(seg) == k and all(ch in "0123456789abcdef" for ch in seg)


def _check_disambiguation(m):
    """True if the mangled text `m`, placed after a separator, could be read as
    an escape (`x41`, `u2083`), as a number, or is empty."""
    i = 0
    while i < len(m) and m[i] == "_":
        i += 1
    if i >= len(m):
        return True
    b = m[i]
    if b == "x":
        return _hex_run(m, i + 1, 2)
    if b == "u":
        return _hex_run(m, i + 1, 4)
    if b == "U":
        return _hex_run(m, i + 1, 8)
    return "0" <= b <= "9"


def mangle_name(comps, prefix=""):
    """`comps` is a list of components: a str, or an int for a numeric component."""
    res = ""
    prev = None
    for idx, c in enumerate(comps):
        if isinstance(c, int):
            res = ("%d_" % c) if idx == 0 else res + "_" + str(c) + "_"
        else:
            m = mangle_string(c)
            if idx == 0:
                res = ("00" + m) if _check_disambiguation(m) else m
            else:
                need = (isinstance(prev, str) and prev.endswith("_")) or _check_disambiguation(m)
                res = res + ("_00" if need else "_") + m
        prev = c
    return prefix + res


def _hex_value(s, p, k):
    if _hex_run(s, p, k):
        return int(s[p:p + k], 16), p + k
    return None


def demangle(s):
    """The inverse of `mangle_name(comps, "")` (Lean.Name.demangle)."""
    res = []
    n = len(s)

    def name_start(p):
        if p >= n:
            return
        ch = s[p]
        p += 1
        if "0" <= ch <= "9":
            if ch == "0" and p < n and s[p] == "0":
                demangle_aux(p + 1, "", 0)
            else:
                decode_num(p, ord(ch) - 48)
        elif ch == "_":
            demangle_aux(p, "", 1)
        else:
            demangle_aux(p, ch, 0)

    def decode_num(p, num):
        while p < n and "0" <= s[p] <= "9":
            num = num * 10 + ord(s[p]) - 48
            p += 1
        res.append(num)
        if p < n:
            name_start(p + 2)

    def demangle_aux(p0, acc, ucount):
        while True:
            if p0 >= n:
                res.append(acc + "_" * (ucount // 2))
                return
            ch = s[p0]
            p = p0 + 1
            if ch == "_":
                ucount += 1
                p0 = p
                continue
            if ucount % 2 == 0:
                acc = acc + "_" * (ucount // 2) + ch
                ucount = 0
                p0 = p
                continue
            if "0" <= ch <= "9":
                res.append(acc + "_" * (ucount // 2))
                if ch == "0" and p < n and s[p] == "0":
                    acc, ucount, p0 = "", 0, p + 1
                    continue
                decode_num(p, ord(ch) - 48)
                return
            for esc, width in (("x", 2), ("u", 4), ("U", 8)):
                if ch == esc:
                    h = _hex_value(s, p, width)
                    if h:
                        acc = acc + "_" * (ucount // 2) + chr(h[0])
                        ucount, p0 = 0, h[1]
                        break
            else:
                res.append(acc)
                acc = "_" * (ucount // 2) + ch
                ucount, p0 = 0, p
                continue
            continue

    name_start(0)
    return res


def package_prefix(package):
    return "lp_%s_" % mangle_string(package)


def public_symbol(comps, prefix):
    return mangle_name(list(comps), prefix)


def private_symbol(module, comps, prefix):
    return mangle_name(["_private"] + module.split(".") + [0] + list(comps), prefix)


def symbol_variants(comps, prefix, private_module=None):
    """The symbols that stand for the declaration in emitted C: the function, its
    boxed wrapper, its reduced-arity copy and the boxed wrapper of that."""
    base = (["_private"] + private_module.split(".") + [0] + list(comps)) if private_module else list(comps)
    return {
        mangle_name(base, prefix): "plain",
        mangle_name(base + ["_boxed"], prefix): "boxed",
        mangle_name(base + ["_redArg"], prefix): "redArg",
        mangle_name(base + ["_redArg", "_boxed"], prefix): "redArg-boxed",
    }


# Components that the compiler appends to the name of a declaration.
ARTIFACT = re.compile(r"^(?:_boxed|_redArg|_lam_\d+|_elam_\d+|_closed_\d+|_boxed_const_\d+)$")
SPEC_COMP = re.compile(r"^spec_\d+$")


def _strip_private(part):
    if part and part[0] == "_private":
        for i, x in enumerate(part):
            if isinstance(x, int):
                return part[i + 1:]
    return part


CLOSED_COMP = re.compile(r"^_closed_\d+$")


def _strip_tail(part, allow_spec):
    """Drop the components that the compiler appends.  The C emitter adds `_value` to
    the symbol of a static closure (`X___closed__0_value`), which reads back as the
    two components `_closed_0` and `value`."""
    part = list(part)
    while part:
        last = part[-1]
        if isinstance(last, str) and (ARTIFACT.match(last) or (allow_spec and SPEC_COMP.match(last))):
            part.pop()
        elif last == "value" and len(part) >= 2 and isinstance(part[-2], str) and CLOSED_COMP.match(part[-2]):
            del part[-2:]
        else:
            break
    return part


def chain_of(comps):
    """(head, owner) of a demangled symbol.  `head` is the declaration whose body
    the function is; `owner` is the declaration the code was made for: the last
    declaration of an `_at_` chain, or the head when there is no chain."""
    parts = [[]]
    for c in _strip_tail(comps, False):
        if c == "_at_":
            parts.append([])
        else:
            parts[-1].append(c)
    out = []
    for i, p in enumerate(parts):
        p = _strip_private(p)
        p = _strip_tail(p, len(parts) > 1 and i == len(parts) - 1)
        out.append(tuple(p))
    return out[0], out[-1], len(parts) > 1


def decl_of_symbol(sym, prefix):
    """(head, owner, is_specialised) for an emitted symbol, or None if the symbol
    is not a mangled Lean name of this package or of the core library."""
    s = sym
    if s.startswith("_init_"):
        s = s[len("_init_"):]
    if s.startswith(prefix):
        body = s[len(prefix):]
    elif s.startswith("l_"):
        body = s[2:]
    else:
        return None
    return chain_of(demangle(body))


def dotted(comps):
    return ".".join(str(c) for c in comps)


# ------------------------------------------------------------- Lean sources

CHAR_LIT = re.compile(r"'(?:\\(?:[\\'\"ntr0]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\})|[^\\'\n])'")
IDENT_CH = re.compile(r"[A-Za-z0-9_'!?\u00c0-\uffff]")


def blank_comments(lines):
    """Lean source with comments and string/char literals blanked out, columns
    kept.  Block comments nest.  (The same reader as lean-tail-recursion-audit.py.)"""
    code = []
    depth = 0
    in_str = False
    for raw in lines:
        line = raw.rstrip("\n")
        out = []
        i = 0
        n = len(line)
        while i < n:
            c = line[i]
            if depth > 0:
                if line.startswith("/-", i):
                    depth += 1
                    out.append("  ")
                    i += 2
                elif line.startswith("-/", i):
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    out.append(" ")
                    i += 1
                continue
            if in_str:
                if c == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                    continue
                if c == '"':
                    in_str = False
                    out.append('"')
                else:
                    out.append(" ")
                i += 1
                continue
            if line.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if line.startswith("--", i):
                out.append(" " * (n - i))
                break
            if c == '"':
                in_str = True
                out.append('"')
                i += 1
                continue
            if c == "'":
                prev = line[i - 1] if i > 0 else " "
                if not IDENT_CH.match(prev):
                    m = CHAR_LIT.match(line, i)
                    if m:
                        out.append("'" + " " * (m.end() - i - 2) + "'")
                        i = m.end()
                        continue
            out.append(c)
            i += 1
        code.append("".join(out))
    return code


NAME_RE = r"[A-Za-z_][A-Za-z0-9_'!?.\u00c0-\uffff]*"
NAMESPACE = re.compile(r"^namespace\s+(%s)" % NAME_RE)
SECTION = re.compile(r"^(?:noncomputable\s+)?section(?:\s+(%s))?\s*$" % NAME_RE)
MUTUAL = re.compile(r"^mutual\s*$")
END = re.compile(r"^end(?:\s+(%s))?\s*$" % NAME_RE)
# whitespace between the names is required, so a name has one split and a failed match is not exponential
OPEN = re.compile(r"^\s*open\s+(%s(?:\s+%s)*)\s*$" % (NAME_RE, NAME_RE))
OPEN_IN = re.compile(r"^\s*open\s+(?:%s\s+)+in\b" % NAME_RE)
ATTR = re.compile(r"@\[([^\]]*)\]")
ATTRIBUTE_CMD = re.compile(r"^\s*(?:local\s+|scoped\s+)?attribute\s*\[([^\]]*)\]")
THEOREM = re.compile(r"(?:(?:private|protected|nonrec)\s+)*(theorem|lemma)\s+(%s)" % NAME_RE)
EQ_STATEMENT = re.compile(r"^@?(%s)\s*=\s*@?(%s)$" % (NAME_RE, NAME_RE))
UNIVERSES = re.compile(r"\.\{[^}]*\}")
DECL_NAME = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:def|abbrev|theorem|lemma|opaque|instance|structure|inductive|class|axiom)\s+(?:\([^)]*\)\s*)?(%s)" % NAME_RE)
IMPORT = re.compile(r"^(?:(?:public|meta|private)\s+)*import\s+(?:all\s+)?([A-Za-z_][\w.]*)")


def _after_top_colon(rest):
    depth = 0
    for k, ch in enumerate(rest):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0 and not rest.startswith(":=", k):
            return rest[k + 1:].strip()
    return None


def _unparen(text):
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        ok = True
        for k, ch in enumerate(text):
            depth += ch == "("
            depth -= ch == ")"
            if depth == 0 and k < len(text) - 1:
                ok = False
                break
        if not ok:
            break
        text = text[1:-1].strip()
    return text


class LeanScan:
    """What the Lean sources say: the modules, their imports, the declaration
    lines, and the `@[csimp]` theorems."""

    def __init__(self):
        self.modules = {}      # module -> relative path
        self.imports = {}      # module -> [module]
        self.decl_line = {}    # module -> {full dotted name -> line}
        self.theorems = []     # dicts, see scan_file
        self.defines_main = set()   # modules that define the root-level `main` (two of them cannot be imported together)


def scan_lean_tree(lean_dir):
    sc = LeanScan()
    for root, dirs, files in os.walk(lean_dir):
        dirs[:] = sorted(d for d in dirs if d not in (".lake", ".git", "node_modules"))
        for f in sorted(files):
            if not f.endswith(".lean") or f == "lakefile.lean":
                continue
            path = os.path.join(root, f)
            rel = os.path.relpath(path, lean_dir)
            module = rel[:-5].replace(os.sep, ".")
            with open(path, "r", errors="replace") as fh:
                lines = fh.readlines()
            sc.modules[module] = rel
            scan_file(sc, module, rel, lines)
    return sc


def scan_file(sc, module, rel, lines):
    code = blank_comments(lines)
    imports = []
    decls = {}
    scopes = []     # [kind, name, opens]; kind: ns, sec, mutual
    base_opens = []

    def ns_parts():
        out = []
        for kind, name, _ in scopes:
            if kind == "ns":
                out.extend(name.split("."))
        return out

    def opens_now():
        out = list(base_opens)
        for _, _, o in scopes:
            out.extend(o)
        return out

    n = len(code)
    for i in range(n):
        line = code[i]
        if not line.strip():
            continue
        col0 = not line[0].isspace()
        if col0:
            mi = IMPORT.match(line)
            if mi:
                imports.append(mi.group(1))
                continue
            m = NAMESPACE.match(line)
            if m:
                scopes.append(["ns", m.group(1), []])
                continue
            m = SECTION.match(line)
            if m:
                scopes.append(["sec", m.group(1), []])
                continue
            if MUTUAL.match(line):
                scopes.append(["mutual", None, []])
                continue
            m = END.match(line)
            if m:
                name = m.group(1)
                if name is None:
                    if scopes and scopes[-1][0] in ("mutual", "sec") and \
                            (scopes[-1][0] == "mutual" or scopes[-1][1] is None):
                        scopes.pop()
                else:
                    want = len(name.split("."))
                    got = 0
                    while scopes and got < want:
                        kind, nm, _ = scopes.pop()
                        if kind != "mutual":
                            got += len((nm or "").split("."))
                continue
            md = DECL_NAME.match(line)
            if md:
                short = md.group(1)
                full = short[len("_root_."):] if short.startswith("_root_.") else dotted(ns_parts() + [short])
                decls.setdefault(full, i + 1)
                if full == "main":
                    sc.defines_main.add(module)
        mo = OPEN.match(line)
        if mo and not OPEN_IN.match(line):
            target = scopes[-1][2] if scopes else base_opens
            target.extend(mo.group(1).split())
        ma = ATTRIBUTE_CMD.match(line)
        if ma and any(a.strip() == "csimp" for a in ma.group(1).split(",")):
            sc.theorems.append(dict(module=module, file=rel, line=i + 1, thm=None, ns=ns_parts(),
                                    opens=opens_now(), lhs=None, rhs=None,
                                    error="the `attribute [csimp]` command form is not read; write `@[csimp]` before the theorem"))
        for am in ATTR.finditer(line):
            if not any(a.strip() == "csimp" for a in am.group(1).split(",")):
                continue
            buf = line[am.end():]
            j = i
            while ":=" not in buf and j + 1 < n and j < i + 12:
                j += 1
                buf += " " + code[j]
            head = UNIVERSES.sub("", " ".join(buf.split(":=")[0].split()))
            th = dict(module=module, file=rel, line=i + 1, thm=None, ns=ns_parts(), opens=opens_now(),
                      lhs=None, rhs=None, error=None)
            mt = THEOREM.match(head)
            if not mt:
                th["error"] = "`@[csimp]` is not followed by `theorem`: " + head[:80]
            else:
                th["thm"] = mt.group(2)
                stmt = _after_top_colon(head[mt.end():].strip())
                me = EQ_STATEMENT.match(_unparen(stmt)) if stmt is not None else None
                if not me:
                    th["error"] = "statement is not `@f = @g`: " + (stmt or head)[:100]
                else:
                    th["lhs"], th["rhs"] = me.group(1), me.group(2)
            sc.theorems.append(th)
    sc.imports[module] = imports
    sc.decl_line[module] = decls


def import_closure(sc, module, cache):
    """All modules that `module` imports, directly or not."""
    if module in cache:
        return cache[module]
    seen = set()
    stack = list(sc.imports.get(module, ()))
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(sc.imports.get(m, ()))
    cache[module] = seen
    return seen


# ------------------------------------------------------------------ emitted C

DEF_LINE = re.compile(r"^(?:LEAN_EXPORT\s+|static\s+)*[A-Za-z_][A-Za-z0-9_ \*]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
CLOSURE_DEF = re.compile(r"^static const lean_closure_object ([A-Za-z_][A-Za-z0-9_]*) =")
CONST_DEF = re.compile(r"^LEAN_EXPORT\s+(?:const\s+)?[A-Za-z_][A-Za-z0-9_ \*]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*(?:;|=)")
CONTROL = {"if", "else", "while", "for", "switch", "return", "sizeof", "do"}
STRLIT = re.compile(r'"(?:\\.|[^"\\])*"')


def list_c_files(ir_dir, modules):
    """[(path, relative path, module)] for the C files whose module has a Lean
    source, and the number of C files ignored because it has none."""
    found = []
    stale = 0
    for root, _dirs, files in os.walk(ir_dir):
        for f in sorted(files):
            if not f.endswith(".c"):
                continue
            path = os.path.join(root, f)
            rel = os.path.relpath(path, ir_dir)
            module = rel[:-2].replace(os.sep, ".")
            if module in modules:
                found.append((path, rel, module))
            else:
                stale += 1
    found.sort(key=lambda t: t[1])
    return found, stale


def scan_definitions(cfiles):
    """name -> relative path of the first C file that defines it, for functions
    and static closure constants; the number of names defined twice."""
    defs = {}
    dup = 0
    for path, rel, _module in cfiles:
        cur = None
        depth = 0
        with open(path, "r", errors="replace") as fh:
            for line in fh:
                if cur is None:
                    if not line or line[0].isspace() or line[0] in "/#":
                        continue
                    s = line.rstrip("\n")
                    if s.endswith("{"):
                        m = DEF_LINE.match(s)
                        if m and m.group(1) not in CONTROL:
                            name = m.group(1)
                            if name in defs:
                                dup += 1
                            else:
                                defs[name] = rel
                            cur = name
                            depth = s.count("{") - s.count("}")
                    elif s.startswith("static const lean_closure_object "):
                        m = CLOSURE_DEF.match(s)
                        if m:
                            defs.setdefault(m.group(1), rel)
                    elif s.startswith("LEAN_EXPORT "):
                        m = CONST_DEF.match(s)
                        if m:
                            defs.setdefault(m.group(1), rel)
                    continue
                s = STRLIT.sub('""', line) if '"' in line else line
                depth += s.count("{") - s.count("}")
                if depth <= 0:
                    cur = None
    return defs, dup


def scan_references(cfiles, prefix, wanted):
    """references[symbol] = {(relative path, referencing definition, kind)} for
    each symbol in `wanted`.  kind: call, closure, value or static-closure."""
    tok = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(prefix) + r"[A-Za-z0-9_]+")
    refs = defaultdict(set)
    for path, rel, _module in cfiles:
        cur = None
        depth = 0
        skip = False
        with open(path, "r", errors="replace") as fh:
            for line in fh:
                if cur is None:
                    if not line or line[0].isspace() or line[0] in "/#":
                        continue
                    s = line.rstrip("\n")
                    if s.endswith("{"):
                        m = DEF_LINE.match(s)
                        if m and m.group(1) not in CONTROL:
                            cur = m.group(1)
                            skip = cur.startswith("initialize_")
                            depth = s.count("{") - s.count("}")
                    elif s.startswith("static const lean_closure_object "):
                        m = CLOSURE_DEF.match(s)
                        if m:
                            for t in tok.finditer(s):
                                sym = t.group(0)
                                if sym in wanted and sym != m.group(1):
                                    refs[sym].add((rel, m.group(1), "static-closure"))
                    continue
                s = STRLIT.sub('""', line) if '"' in line else line
                depth += s.count("{") - s.count("}")
                if not skip and prefix in s:
                    for t in tok.finditer(s):
                        sym = t.group(0)
                        if sym in wanted:
                            if "(void*)" in s[max(0, t.start() - 9):t.start()]:
                                kind = "closure"
                            elif s[t.end():t.end() + 1] == "(":
                                kind = "call"
                            else:
                                kind = "value"
                            refs[sym].add((rel, cur, kind))
                if depth <= 0:
                    cur = None
                    skip = False
    return refs


# --------------------------------------------------------------- resolution


def candidates(th, ident):
    """Names (component lists) that `ident` may denote, in the order Lean tries
    them: the namespace chain from the innermost outwards (the prefix of the
    declaration's own dotted name counts as a namespace), the root, `open`s."""
    ident = ident.strip()
    idc = ident.split(".")
    if idc[0] == "_root_":
        return [idc[1:]]
    chain = list(th["ns"]) + (th["thm"].split(".")[:-1] if th["thm"] else [])
    out = []
    for k in range(len(chain), 0, -1):
        out.append(chain[:k] + idc)
    out.append(idc)
    for o in th["opens"]:
        for k in range(len(chain), -1, -1):
            out.append(chain[:k] + o.split(".") + idc)
    return out


def resolve(th, ident, defined, prefix):
    """(components, private module or None) of the first candidate whose symbol is defined."""
    for comps in candidates(th, ident):
        if public_symbol(comps, prefix) in defined:
            return comps, None
        if private_symbol(th["module"], comps, prefix) in defined:
            return comps, th["module"]
    return None, None


# ---------------------------------------------------------------- allow list


class Allow:
    def __init__(self, path):
        self.entries = []   # [left pattern, owner pattern, reason, line, used]
        self.errors = []
        if path and os.path.exists(path):
            with open(path, "r") as fh:
                for n, line in enumerate(fh, 1):
                    body, _, comment = line.partition("#")
                    body = body.strip()
                    if not body:
                        continue
                    parts = body.split()
                    reason = comment.strip()
                    if len(parts) != 2:
                        self.errors.append("%s:%d: expected `left owner # reason`" % (os.path.basename(path), n))
                    elif not reason:
                        self.errors.append("%s:%d: no reason after `#`" % (os.path.basename(path), n))
                    else:
                        self.entries.append([parts[0], parts[1], reason, n, False])

    @staticmethod
    def _match(pat, name):
        if pat == name:
            return True
        if "*" in pat:
            return re.fullmatch(".*".join(re.escape(p) for p in pat.split("*")), name) is not None
        return False

    def find(self, left, owner):
        """The first entry that matches, or None.  Marking an entry as used is the caller's job."""
        for e in self.entries:
            if self._match(e[0], left) and self._match(e[1], owner):
                return e
        return None


# ------------------------------------------------------------------ analysis


class Target:
    """One left side `f`, with every theorem that replaces it."""

    def __init__(self, comps, private_module, sym, cfile):
        self.comps = tuple(comps)
        self.private_module = private_module
        self.sym = sym
        self.cfile = cfile
        self.theorems = []   # (theorem dict, replacement components, replacement symbol, replacement private module)
        self.name = dotted(comps)


def own_family(owner, comps, owner_cfile, decl_cfile):
    """True if the declaration `owner` is `comps` or a helper of it (`comps.go`)
    and its C function is in the C file of `comps`."""
    return owner_cfile == decl_cfile and (
        owner == comps or (len(owner) > len(comps) and owner[:len(comps)] == comps))


def resolve_theorems(sc, defs, prefix):
    """(targets by left symbol, [(theorem, why)] for the theorems that could not be resolved)."""
    defined = set(defs)
    # a nullary constant is initialised by `_init_<symbol>`
    defined.update(n[len("_init_"):] for n in defs if n.startswith("_init_"))
    problems = []
    targets = {}
    for th in sc.theorems:
        if th["error"]:
            problems.append((th, th["error"]))
            continue
        lc, lp = resolve(th, th["lhs"], defined, prefix)
        rc, rp = resolve(th, th["rhs"], defined, prefix)
        if lc is None:
            problems.append((th, "left side `%s` has no emitted C symbol (the module is not built, it is not a "
                                 "compiled definition, or its name is one this tool cannot resolve)" % th["lhs"]))
            continue
        if rc is None:
            problems.append((th, "replacement `%s` has no emitted C symbol" % th["rhs"]))
            continue
        lsym = private_symbol(lp, lc, prefix) if lp else public_symbol(lc, prefix)
        t = targets.get(lsym)
        if t is None:
            t = targets[lsym] = Target(lc, lp, lsym, defs.get(lsym) or defs.get("_init_" + lsym) or "")
        rsym = private_symbol(rp, rc, prefix) if rp else public_symbol(rc, prefix)
        t.theorems.append((th, tuple(rc), rsym, rp))
    return targets, problems


def collect(cfiles, defs, prefix, targets):
    """(raw findings, uses of the replacements).
    raw[(left symbol, owner)] = [evidence]; uses[left symbol] = {owner of a caller of a replacement}.
    A symbol may be the left side of one theorem and the replacement of another, so it has a list of roles."""
    wanted = defaultdict(list)
    for t in targets.values():
        for sym in symbol_variants(t.comps, prefix, t.private_module):
            wanted[sym].append(("left", t, t.comps, t.cfile))
        for th, rc, rsym, rp in t.theorems:
            rfile = defs.get(rsym) or defs.get("_init_" + rsym) or ""
            for sym in symbol_variants(rc, prefix, rp):
                wanted[sym].append(("right", t, rc, rfile))
    refs = scan_references(cfiles, prefix, set(wanted))

    raw = {}
    uses = defaultdict(set)
    for sym, held in refs.items():
        for side, t, comps, decl_cfile in wanted[sym]:
            for rel, holder, kind in held:
                d = decl_of_symbol(holder, prefix)
                owner = d[1] if d else (holder,)
                if own_family(owner, comps, rel, decl_cfile):
                    continue
                if side == "right":
                    uses[t.sym].add(dotted(owner))
                else:
                    ev = dict(holder=holder, cfile=rel, kind=kind)
                    if ev not in raw.setdefault((t.sym, owner), []):
                        raw[(t.sym, owner)].append(ev)

    # the specialised copies of each left side: `f___at___00<caller>_spec__N`
    names = sorted(defs)
    for t in targets.values():
        base = (["_private"] + t.private_module.split(".") + [0] + list(t.comps)) if t.private_module else list(t.comps)
        stem = mangle_name(base + ["_at_"], prefix)
        lo = bisect.bisect_left(names, stem)
        while lo < len(names) and names[lo].startswith(stem):
            name = names[lo]
            lo += 1
            d = decl_of_symbol(name, prefix)
            if d is None or d[0] != t.comps or own_family(d[1], t.comps, defs[name], t.cfile):
                continue
            raw.setdefault((t.sym, d[1]), []).append(dict(holder=name, cfile=defs[name], kind="specialised-copy"))
    return raw, uses


def spec_of(owner, spec_comps):
    """The left side of a theorem that `owner` is, or is a helper of; or None."""
    for sp in spec_comps:
        if owner == sp or (len(owner) > len(sp) and owner[:len(sp)] == sp):
            return sp
    return None


def run(ir_dir, lean_dir, allow_path, package=None):
    """The whole check.  Returns a dict, or the exit code 2 with a message on stderr."""
    if not os.path.isdir(ir_dir):
        sys.stderr.write("no emitted C at %s -- run `lake build` in formal/lean4 first\n" % ir_dir)
        return 2
    package = package or package_name(lean_dir)
    prefix = package_prefix(package)
    sc = scan_lean_tree(lean_dir)
    if not sc.modules:
        sys.stderr.write("no Lean sources under %s -- refusing to report\n" % lean_dir)
        return 2
    if not sc.theorems:
        sys.stderr.write("no @[csimp] theorem found under %s -- refusing to report a zero\n" % lean_dir)
        return 2
    cfiles, stale = list_c_files(ir_dir, sc.modules)
    if not cfiles:
        sys.stderr.write("no .c file under %s has a Lean source -- refusing to report a zero\n" % ir_dir)
        return 2
    defs, dup = scan_definitions(cfiles)
    targets, problems = resolve_theorems(sc, defs, prefix)
    raw, uses = collect(cfiles, defs, prefix, targets)
    right_total = sum(len(v) for v in uses.values())
    if targets and right_total == 0:
        sys.stderr.write("the scan sees no use of any @[csimp] replacement in %d C files: the scanner or the "
                         "symbol mapping is wrong -- refusing to report a zero\n" % len(cfiles))
        return 2

    sym_of = {t.comps: t.sym for t in targets.values()}
    allow = Allow(allow_path)
    closure_cache = {}
    findings = []
    for (lsym, owner), ev in sorted(raw.items(), key=lambda kv: (targets[kv[0][0]].name, dotted(kv[0][1]))):
        t = targets[lsym]
        f = dict(left=t.name, caller=dotted(owner), left_sym=lsym, owner_comps=owner,
                 evidence=sorted(ev, key=lambda e: (e["cfile"], e["holder"])),
                 spec=spec_of(owner, list(sym_of)), allow=None, status=None)
        f["reason"], f["why"] = explain(sc, t, f, closure_cache)
        f["allowed_by"] = allow.find(f["left"], f["caller"])
        findings.append(f)

    # A specification is LIVE when a finding against it is held by live code and is not allowed.  Code that is
    # held by a specification that nothing reaches never runs, so its findings are suppressed.
    live = set()
    changed = True
    while changed:
        changed = False
        for f in findings:
            holder_live = f["spec"] is None or sym_of[f["spec"]] in live
            if holder_live and f["allowed_by"] is None and f["left_sym"] not in live:
                live.add(f["left_sym"])
                changed = True
    for f in findings:
        if f["spec"] is not None and sym_of[f["spec"]] not in live:
            f["status"] = "spec-internal"
        elif f["allowed_by"] is not None:
            f["status"] = "allowed"
            f["allow"] = f["allowed_by"][2]
            f["allowed_by"][4] = True
        else:
            f["status"] = "new"

    theorem_rows = []
    for t in targets.values():
        for th, rc, rsym, rp in t.theorems:
            theorem_rows.append(dict(file=th["file"], line=th["line"], theorem=th["thm"], left=t.name,
                                     replacement=dotted(rc), module=th["module"],
                                     replacement_callers=sorted(uses.get(t.sym, ()))))
    return dict(
        package=package, prefix=prefix, theorems=theorem_rows, problems=problems, findings=findings,
        allow=allow, targets=targets, stats=dict(
            cfiles=len(cfiles), stale_cfiles=stale, definitions=len(defs), duplicate_definitions=dup,
            lean_modules=len(sc.modules), theorems=len(sc.theorems), left_sides=len(targets),
            replacement_uses=right_total))


def explain(sc, target, finding, closure_cache):
    """(reason code, sentence) for a finding."""
    cfile = finding["evidence"][0]["cfile"]
    caller_mod = cfile[:-2].replace(os.sep, ".")
    thm_mods = {th["module"] for th, _rc, _rs, _rp in target.theorems}
    kinds = {e["kind"] for e in finding["evidence"]}
    copy = " (a specialised copy of the left side was made for it)" if "specialised-copy" in kinds else ""
    if caller_mod in thm_mods:
        thm_line = min(th["line"] for th, _a, _b, _c in target.theorems if th["module"] == caller_mod)
        line = decl_position(sc, caller_mod, finding["owner_comps"])
        if line is None:
            return "same-module", "same module as the @[csimp] theorem, order unknown" + copy
        if line < thm_line:
            return "before-theorem", ("declared at line %d, above the @[csimp] theorem at line %d: the replacement "
                                      "applies only to code compiled after it" % (line, thm_line)) + copy
        return "after-theorem", ("declared at line %d, below the @[csimp] theorem at line %d, and still calls the "
                                 "left side: the call came in through an inlined or specialised definition compiled "
                                 "before the theorem" % (line, thm_line)) + copy
    imported = import_closure(sc, caller_mod, closure_cache)
    if not (imported & thm_mods):
        return "not-imported", ("module %s does not import %s, so the replacement is not in force there"
                                % (caller_mod, " or ".join(sorted(thm_mods)))) + copy
    return "after-theorem", ("module %s imports the theorem's module and still calls the left side: the call came "
                             "in through an inlined or specialised definition compiled before the theorem"
                             % caller_mod) + copy


def decl_position(sc, module, owner):
    """Line of the declaration of `owner` (or of the longest prefix of it that is declared)."""
    decls = sc.decl_line.get(module, {})
    comps = list(owner)
    while comps:
        line = decls.get(dotted(comps))
        if line is not None:
            return line
        comps.pop()
    return None


def package_name(lean_dir):
    path = os.path.join(lean_dir, "lakefile.lean")
    if os.path.exists(path):
        with open(path, "r", errors="replace") as fh:
            for line in fh:
                m = re.match(r"^package\s+(\S+)", line)
                if m:
                    return m.group(1).strip("«»")
    return DEFAULT_PACKAGE


# --------------------------------------------------------------- cross-check

DUMP_TEMPLATE = """import Lean
%(imports)s
open Lean Compiler

#eval show CoreM Unit from do
  let env <- getEnv
  let s := CSimp.ext.getState env
  for n in s.thmNames.toList do
    let mod := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!).toString
      | none => "<current>"
    IO.println s!"CSIMP\\t{mod}\\t{n}"
"""


def _lean_dump(modules, lean_dir):
    """The (module, theorem name) pairs of Lean's `@[csimp]` table after importing `modules`, or None."""
    text = DUMP_TEMPLATE % dict(imports="\n".join("import " + m for m in modules))
    with tempfile.TemporaryDirectory() as tmp:
        script = os.path.join(tmp, "CsimpDump.lean")
        with open(script, "w") as fh:
            fh.write(text)
        try:
            p = subprocess.run(["lake", "env", "lean", script], cwd=lean_dir, capture_output=True, text=True,
                               timeout=1800)
        except (OSError, subprocess.TimeoutExpired) as e:
            sys.stderr.write("cross-check: could not run `lake env lean`: %s\n" % e)
            return None
    rows = [l.split("\t") for l in p.stdout.splitlines() if l.startswith("CSIMP\t")]
    if p.returncode != 0 or not rows:
        sys.stderr.write("cross-check: `lake env lean` failed (exit %d)\n%s\n"
                         % (p.returncode, (p.stdout + p.stderr)[-2000:]))
        return None
    return {(mod, thm) for _tag, mod, thm in rows}


def cross_check(sc, ir_dir, lean_dir):
    """Compare the theorems found in the source with Lean's own table.

    Every built module is imported in one Lean process, except the modules that define the
    root-level `main` (a second `main` in one environment is an error): those are imported one
    at a time, and only when the source scan found a theorem in them.  Returns (only in the
    source, only in Lean, theorems in Lean for this package, modules not imported) or None."""
    built = sorted(m for m in sc.modules if os.path.exists(os.path.join(ir_dir, *m.split(".")) + ".c"))
    batches = [[m for m in built if m not in sc.defines_main]]
    holders = {th["module"] for th in sc.theorems}
    skipped = []
    for m in built:
        if m in sc.defines_main:
            if m in holders:
                batches.append([m])
            else:
                skipped.append(m)
    seen = set()
    for batch in batches:
        got = _lean_dump(batch, lean_dir)
        if got is None:
            return None
        seen |= got
    roots = {m.split(".")[0] for m in sc.modules}
    imported = {m for b in batches for m in b}
    lean_side = {(mod, thm.split(".")[-1]) for mod, thm in seen if mod.split(".")[0] in roots}
    src_side = {(th["module"], th["thm"].split(".")[-1]) for th in sc.theorems if th["thm"]}
    return (sorted(x for x in src_side - lean_side if x[0] in imported),
            sorted(lean_side - src_side), len(lean_side), skipped)


# ------------------------------------------------------------------- output


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--gate", action="store_true",
                    help="exit 1 on a finding outside the allow list, an unresolved theorem or an allow line with no reason")
    ap.add_argument("--json", metavar="PATH", help="write the full result as JSON")
    ap.add_argument("--allow", default=ALLOW_FILE)
    ap.add_argument("--ir-dir", default=IR_DIR)
    ap.add_argument("--lean-dir", default=LEAN_DIR)
    ap.add_argument("--package", default=None, help="Lake package name (default: read from lakefile.lean)")
    ap.add_argument("--verbose", action="store_true", help="list every theorem and every suppressed finding")
    ap.add_argument("--cross-check", action="store_true",
                    help="compare the theorems found in the source with Lean's own table (needs `lake`)")
    args = ap.parse_args(argv)

    res = run(args.ir_dir, args.lean_dir, args.allow, args.package)
    if isinstance(res, int):
        return res
    findings, st = res["findings"], res["stats"]
    allow = res["allow"]
    new = [f for f in findings if f["status"] == "new"]
    allowed = [f for f in findings if f["status"] == "allowed"]
    internal = [f for f in findings if f["status"] == "spec-internal"]
    stale = [e for e in allow.entries if not e[4]]
    first_line = {}
    for t in res["theorems"]:
        first_line.setdefault(t["left"], t)

    print("Lean @[csimp] reach check")
    print("=========================")
    print("C files scanned: %d (ignored, no Lean source: %d)   definitions: %d   Lean modules: %d"
          % (st["cfiles"], st["stale_cfiles"], st["definitions"], st["lean_modules"]))
    print("@[csimp] theorems found: %d   distinct left sides: %d   not resolved: %d"
          % (st["theorems"], st["left_sides"], len(res["problems"])))
    print("Calls of a replacement found in the emitted C (the positive control): %d" % st["replacement_uses"])
    shared = [n for n in {t["left"] for t in res["theorems"]}
              if sum(1 for t in res["theorems"] if t["left"] == n) > 1]
    for n in sorted(shared):
        print("  left side with two theorems: %s (%s)" % (n, ", ".join(
            "%s:%d" % (t["file"], t["line"]) for t in res["theorems"] if t["left"] == n)))
    for th, why in res["problems"]:
        print("  NOT RESOLVED %s:%d %s: %s" % (th["file"], th["line"], th["thm"] or "?", why))
    print("Findings (a left side that compiled code still reaches): %d" % len(findings))
    print("  new: %d   allowed: %d   suppressed, held by a specification nothing reaches: %d"
          % (len(new), len(allowed), len(internal)))
    reasons = defaultdict(int)
    for f in new + allowed:
        reasons[f["reason"]] += 1
    if reasons:
        print("  by reason: " + ", ".join("%s %d" % (k, v) for k, v in sorted(reasons.items())))
    print("Allow list: %d lines, %d match no finding, %d malformed"
          % (len(allow.entries), len(stale), len(allow.errors)))
    print()

    def show(f, label):
        ev = f["evidence"][0]
        th = first_line.get(f["left"])
        print("%s %s" % (label, f["left"]))
        print("    still reached by %s   [%s: %s, %s%s]" % (
            f["caller"], ev["cfile"], ev["holder"][:90], ev["kind"],
            (" +%d more" % (len(f["evidence"]) - 1)) if len(f["evidence"]) > 1 else ""))
        if th:
            print("    theorem %s:%d  %s -> %s" % (th["file"], th["line"], th["theorem"], th["replacement"]))
        print("    %s: %s" % (f["reason"], f["why"]))
        if f["allow"]:
            print("    allowed: %s" % f["allow"])
        elif label == "NEW":
            print("    to leave it on purpose, add to %s:  %s %s   # <reason>"
                  % (os.path.relpath(args.allow, REPO), f["left"], f["caller"]))

    for f in new:
        show(f, "NEW")
    if args.verbose:
        for f in allowed:
            show(f, "allowed")
        for f in internal:
            show(f, "spec-internal")
        print()
        print("Theorems")
        print("--------")
        for t in res["theorems"]:
            print("  %s:%d  %s -> %s   (replacement called by %d)" % (
                t["file"], t["line"], t["left"], t["replacement"], len(t["replacement_callers"])))
    if stale:
        print()
        print("Stale allow lines (no finding matches; remove them):")
        for e in stale:
            print("  %s %s   # line %d" % (e[0], e[1], e[3]))
    for e in allow.errors:
        print("ALLOW LIST: " + e)

    if args.json:
        slim = dict(
            package=res["package"], stats=st, theorems=res["theorems"],
            problems=[dict(file=th["file"], line=th["line"], theorem=th["thm"], why=why) for th, why in res["problems"]],
            findings=[{k: v for k, v in f.items() if k not in ("owner_comps", "spec", "allowed_by")} for f in findings],
            stale_allow=[dict(left=e[0], caller=e[1], line=e[3]) for e in stale],
            allow_errors=allow.errors)
        with open(args.json, "w") as fh:
            json.dump(slim, fh, indent=1)
        print("wrote %s" % args.json)

    if args.cross_check:
        print()
        out = cross_check(scan_lean_tree(args.lean_dir), args.ir_dir, args.lean_dir)
        if out is None:
            print("Cross-check with Lean's own table: NOT RUN")
            return 2
        only_src, only_lean, n_lean, skipped = out
        print("Cross-check with Lean's own table (Lean.Compiler.CSimp.ext): %d theorems of this package in the "
              "table, %d found in the source; %d modules that define `main` and hold no theorem were not imported"
              % (n_lean, st["theorems"], len(skipped)))
        for m, t in only_src:
            print("  only in the source: %s %s" % (m, t))
        for m, t in only_lean:
            print("  only in Lean's table (the tool does not read it): %s %s" % (m, t))
        if only_src or only_lean:
            if args.gate:
                return 1

    if args.gate:
        print()
        if new or res["problems"] or allow.errors:
            print("GATE FAIL: %d finding(s) not on the allow list, %d theorem(s) not resolved, %d bad allow line(s)"
                  % (len(new), len(res["problems"]), len(allow.errors)))
            print("Repair a finding as skills/lean4-proof-patterns/SKILL.md section 9e says, or add it to the allow "
                  "list with a reason.")
            return 1
        print("GATE PASS: every left side that compiled code still reaches is on %s with a reason"
              % os.path.relpath(args.allow, REPO))
    return 0


if __name__ == "__main__":
    sys.exit(main())
