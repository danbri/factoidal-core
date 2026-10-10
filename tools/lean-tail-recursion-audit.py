#!/usr/bin/env python3
"""Audit the Lean library for recursion that is not compiled to a loop.

METHOD (read-only, over compiled output, never over source shape)
================================================================
Lean 4 compiles a *direct tail* self-call into a jump: the emitted C function
opens with a `_start:` label and the tail call becomes `goto _start;`.  Any
call that survives as a real C call consumes a C stack frame.  This tool reads
`formal/lean4/.lake/build/ir/**/*.c` and builds, for each C file (one Lean
module), the call graph over the functions that file defines: an edge for
every real call and for every closure the function allocates.  A function is
RECURSIVE when it lies on a cycle of that graph: a surviving self-call, a
closure of itself, or a strongly connected component of two or more
functions (mutual recursion, recursion through a `___redArg` copy, a
`___lam__N` closure body, or a `_spec` specialisation of a combinator that
calls back).  A `___boxed` wrapper is merged into the function it wraps.
Each recursive function is mapped back to its Lean declaration and classified
by what bounds the recursion depth.

Classes
-------
  length    depth is proportional to the length of an input the caller
            controls (a List, String, ByteArray, Array, token stream, or an
            `abbrev` of one, such as `abbrev Chars := Array Char`)
  depth     depth is the nesting depth of an input tree (JSON, XML,
            an expression or algebra term; a recursive `inductive`)
  counter   depth is a Nat argument -- a fuel or a count.  A count READ FROM
            THE INPUT (a wire-format entry count, a fuel of `s.size + 1`)
            is an input-length recursion wearing a Nat.
  bounded   recursion over a fixed structure, or over nothing the caller
            grows; or a core library function whose depth this tool knows
            (a hash-map bucket chain, a balanced-tree walk) -- see CORE_BOUNDS
  replaced  the left side of a `@[csimp]` theorem (or a `where` / `let rec`
            helper of one): the code generator emits the right side instead
  unknown   the Lean declaration could not be located or read

`--gate` checks the classes length, depth, counter and unknown: every
recursive declaration of those classes must have a line in
`tools/lean-tail-recursion-allow.txt`.  Only `bounded` and `replaced` pass
without a line.

LIMITS OF THE METHOD (state these with any result)
--------------------------------------------------
  * Inlining and specialisation.  Lean specialises core combinators at our
    call sites (`..._at_..._spec__N`).  Those appear as separate functions:
    one whose head is our own function is attributed to that function; one
    whose head is a core function is attributed to the first of our
    declarations in its `_at_` chain and classified by CORE_BOUNDS.  A
    combinator that is NOT specialised (it stays in Lean's own
    `libleanshared`) is invisible here, except that a closure our function
    allocates is an edge, so a cycle through such a combinator and back is
    still seen.
  * A mutual cycle is counted as recursion even when every call in it is in
    tail position.  A C compiler may turn such a sibling call into a jump on
    one target and not on another (wasm without the tail-call extension), so
    the tool does not assume it.
  * `List.foldr`, `List.map`, `List.flatMap` etc. carry `@[csimp]`
    tail-recursive replacements in Lean core, so a call to one of those is
    NOT by itself evidence of stack growth.  A call to a combinator without
    such a replacement is invisible to this tool unless it is specialised
    into our C files.
  * Class assignment reads the Lean source signature textually (comments and
    string literals removed).  It ranks suspects; it does not prove a bound.
  * The scan sees only what was compiled.  A module absent from
    `.lake/build/ir` is not audited -- run `lake build` first.
  * The scan reads every `.c` under `.lake/build/ir`, including those of
    modules that no longer exist when the `.lake` directory is restored from
    a cache: a stale file is audited as if it were built.  Delete the `.c`
    files that have no `.lean` source first (the CI step does).

WHAT THIS TOOL MISSED, AND WHY (keep this list; each entry cost a defect)
-------------------------------------------------------------------------
  * Until 2026-10-10 a symbol that ends in `___redArg` (the compiler's
    reduced-arity copy of a definition) was not mapped back to its Lean
    declaration: it landed in class `unknown`, which the gate did not check,
    and 24 input-proportional recursions were outside the gate
    (https://github.com/danbri/factoidal/issues/746).
  * Until 2026-10-10 (https://github.com/danbri/factoidal/issues/750) the
    gate passed on core 4b5892b0 while two length-proportional recursions
    overflowed the 512 KB stack canary:
    - `L4Factoidal.XML.scanRefs` (XML/Parser.lean:1173, issue 673) compiles
      to `lp_l4factoidal_L4Factoidal_XML_scanRefs` with two surviving
      self-calls.  The tool found it and mapped it, but put it in class
      `counter`: its input is `s : Chars`, and `Chars` is
      `abbrev Chars := Array Char`; the classifier matched only the literal
      words `List`, `Array`, `String`, so it saw only the Nat fuel.  The
      gate checked `length` and `depth` only, so `counter` (32 symbols) was
      not gated.  Now: length aliases are resolved, and `counter` is gated.
    - `L4Factoidal.Syntax.readCollectionRest` (Syntax/Turtle.lean:1310,
      issue 678) compiles to `lp_l4factoidal_L4Factoidal_Syntax_readCollectionRest`
      with one surviving self-call, and is one of a seven-function strongly
      connected component (readObject, readCollection, ...).  The Lean
      indexer matched `namespace` at the start of ANY line, and the doc
      comment of `readPnameNs` has a line that starts "namespace token,
      which must be ..." (Syntax/Turtle.lean:447).  Every declaration after
      that line was indexed as `L4Factoidal.Syntax.token.*`, the lookup
      failed, and the symbol landed in `unknown`, which was not gated.  The
      mutual cycle was printed but cycles were never gated either.  Now: the
      indexer skips comments and string literals, `unknown` is gated, and
      every member of a cycle is a gated row.
    Other defects found in the same audit of the audit: `section X` ...
    `end X` popped a namespace; the closure-body suffix of Lean 4.33 is
    `___lam__N`, but the tool stripped `_lambda_N`, which this compiler
    never emits; a nested `_at_..._spec` name produced an owner that is not
    a declaration; a recursive `inductive` was detected only when its
    constructors used `->`, not `→`, so most tree types were missed;
    `where` helpers and `let rec` were not indexed; derived instances
    (`instReprX`, `instDecidableEqX`) were not mapped.
  * Until the same date a `@[csimp]` theorem marked its left-hand side
    `replaced` by the LAST component of the name only, so a csimp for
    `XSLT.insertBy` also marked `XML.Canonical.insertBy` replaced, and one
    for `OWL.OwlXml.readAnnotations` marked `Syntax.readAnnotations` (a
    Turtle parser function) replaced.  Now the theorem's names are resolved
    against the namespace it is written in, and the mark is by fully
    qualified name.  `tools/test_lean_tail_recursion_audit.py` holds a
    fixture for each defect in this list.
"""

import argparse, fnmatch, json, os, re, sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IR_DIR = os.path.join(REPO, "formal", "lean4", ".lake", "build", "ir")
LEAN_DIR = os.path.join(REPO, "formal", "lean4")

PKG_PREFIXES = ("lp_l4factoidal_", "l_")
OUR_PREFIX = "lp_l4factoidal_"

GATED = ("length", "depth", "counter", "unknown")

# ---------------------------------------------------------------- C scanning

FUNC_DEF = re.compile(r"^(?:LEAN_EXPORT\s+|static\s+)*[A-Za-z_][A-Za-z0-9_ \*]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
IDENT_CALL = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")
CLOSURE_REF = re.compile(r"\(void\*\)\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)")
CONTROL = {"if", "else", "while", "for", "switch", "return", "sizeof", "do"}


STRLIT = re.compile(r'"(?:\\\\.|[^"\\\\])*"' + r"|'(?:\\\\.|[^'\\\\])*'")


def scan_c_file(path):
    """Return (defs, calls, closures) for one emitted C file.

    Function bodies are delimited by BRACE DEPTH, not by a `}` in column 0:
    Lean emits every nested block's braces in column 0 too, and a
    column-0 terminator silently truncates each body at its first inner
    block.  That bug made the first run of this tool report 24 recursions
    where there are hundreds.
    """
    defs, calls, closures = {}, defaultdict(set), defaultdict(set)
    cur = None
    depth = 0
    body = []
    with open(path, "r", errors="replace") as fh:
        lines = fh.readlines()

    def finish(name, body):
        d = defs[name]
        for b in body:
            if "goto _start;" in b:
                d["tail"] += 1
            for cm in IDENT_CALL.finditer(b):
                callee = cm.group(1)
                if callee in CONTROL:
                    continue
                calls[name].add(callee)
                if callee == name:
                    d["self"] += 1
            for cl in CLOSURE_REF.finditer(b):
                closures[name].add(cl.group(1))
                if cl.group(1) == name or cl.group(1) == name + "___boxed":
                    d["selfclosure"] += 1

    for i, raw in enumerate(lines):
        line = raw.rstrip("\n")
        stripped = STRLIT.sub('""', line)
        if cur is None:
            if not line or line[0].isspace() or line.startswith("//") or line.startswith("#"):
                continue
            if not line.endswith("{"):
                continue
            m = FUNC_DEF.match(line)
            if not m:
                continue
            name = m.group(1)
            if name in CONTROL:
                continue
            cur = name
            defs[name] = {"line": i + 1, "self": 0, "selfclosure": 0, "tail": 0}
            body = []
            depth = stripped.count("{") - stripped.count("}")
            continue
        depth += stripped.count("{") - stripped.count("}")
        body.append(line)
        if depth <= 0:
            finish(cur, body)
            cur = None
            body = []
    if cur is not None:
        finish(cur, body)
    return defs, calls, closures


# ------------------------------------------------------------- demangling

ESC = re.compile(r"_x([0-9a-f]{2})")
# compiler decorations at the END of a symbol, stripped repeatedly:
# `f___redArg___lam__0___boxed` -> `f`
TRAILER = re.compile(r"(?:___boxed|___redArg|___lam__\d+|___closed__\d+(?:_value)?|_spec__\d+|___elambda__\d+|_lambda_\d+)$")
PRIVATE = re.compile(r"^_+private_[A-Za-z0-9_]*?_0_+")
AT_SPLIT = re.compile(r"___at___(?:00)?")


def mangle(lean_name):
    out = []
    for ch in lean_name:
        if ch == ".":
            out.append("_")
        elif ch.isalnum() or ch == "_":
            out.append(ch)
        else:
            out.append("_x%02x" % ord(ch))
    return "".join(out)


def decode(s):
    return ESC.sub(lambda m: chr(int(m.group(1), 16)), s)


def strip_trailers(s):
    while True:
        t = TRAILER.sub("", s)
        if t == s:
            return s
        s = t


def strip_prefix(sym):
    for p in PKG_PREFIXES:
        if sym.startswith(p):
            return sym[len(p):]
    return sym


def strip_wrappers(sym):
    """Drop the compiler's decorations, keep the user-visible core."""
    return strip_trailers(strip_prefix(sym))


def depriv(s):
    return PRIVATE.sub("", s)


def spec_chain(sym):
    """[head, ctx1, ctx2, ...] for `head___at___00ctx1___at___00ctx2_spec__N`.

    `head` is the function whose body this is; each ctx is the declaration at
    whose call site the previous one was specialised (innermost first).
    """
    s = strip_wrappers(sym)
    parts = AT_SPLIT.split(s)
    return [depriv(strip_trailers(p)) for p in parts if p]


def owner_of(sym):
    """Compatibility helper: the first declaration of a symbol's chain."""
    chain = spec_chain(sym)
    return chain[0] if chain else strip_wrappers(sym)


def readable(sym):
    return decode(owner_of(sym))


# ------------------------------------------------------------ Lean indexing

CHAR_LIT = re.compile(r"'(?:\\(?:[\\'\"ntr0]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\})|[^\\'\n])'")
IDENT_CH = re.compile(r"[A-Za-z0-9_'!?À-￿]")


class CodeLines:
    """Lean source with comments and string/char literals blanked out.

    Column positions are preserved (blanked characters become spaces), so
    indentation tests still work.  Block comments nest, as in Lean.
    """

    def __init__(self, lines):
        self.code = []
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
            self.code.append("".join(out))


DECL = re.compile(
    r"^(\s*)(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|partial|noncomputable|unsafe|nonrec)\s+)*"
    r"(def|abbrev|opaque)\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
OTHER_TOP = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(theorem|lemma|instance|example|axiom|class|deriving|#[a-z_]+|set_option|open|attribute|variable|universe|macro|syntax|elab|notation|initialization|builtin_initialize)\b")
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
SECTION = re.compile(r"^(?:noncomputable\s+)?section(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
MUTUAL = re.compile(r"^mutual\s*$")
END = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
INDUCTIVE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|unsafe)\s+)*(inductive|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
WHERE_END = re.compile(r"\bwhere\s*$")
WHERE_HELPER = re.compile(
    r"^(\s+)(?:@\[[^\]]*\]\s*)*(?:(?:private|partial|unsafe|noncomputable)\s+)*([A-Za-z_][A-Za-z0-9_'!?]*)")
LET_REC = re.compile(r"\blet\s+rec\s+([A-Za-z_][A-Za-z0-9_'!?]*)")
ABBREV_TYPE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected)\s+)*(?:abbrev|def)\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*(?::\s*Type[^:=]*)?:=\s*(.+)$")
CSIMP_ATTR = re.compile(r"@\[\s*csimp\s*\]")
CSIMP_EQ = re.compile(r"@([A-Za-z_][A-Za-z0-9_'!?.]*)\s*=\s*@([A-Za-z_][A-Za-z0-9_'!?.]*)")
NOT_HELPER = {"termination_by", "decreasing_by", "deriving", "where", "with", "match", "fun",
              "if", "then", "else", "let", "have", "show", "do", "by", "at", "from", "for",
              "return", "pure"}

LENGTH_WORDS = ["List", "Array", "ByteArray", "String", "Substring", "Subarray", "FloatArray"]


def _sig(code, i, start_col=0, max_lines=12):
    """The signature text from line i (from column start_col) up to `:=` or `where`."""
    buf = [code[i][start_col:]]
    for j in range(i + 1, min(i + max_lines, len(code))):
        if ":=" in buf[-1] or "|" in buf[-1].lstrip()[:1]:
            break
        buf.append(code[j])
    s = " ".join(buf)
    s = s.split(":=")[0]
    s = re.split(r"\bwhere\b", s)[0]
    return " ".join(s.split())


def index_lean(lean_dir=None, repo=None):
    """mangled-name -> dict(lean, file, line, sig, partial, owner).

    Also returns the recursive datatypes, the `@[csimp]` replacements keyed by
    the MANGLED FULL name of the left side, the names of length aliases
    (`abbrev Chars := Array Char`), and the csimp theorems it could not
    resolve.  A definition named by the LEFT of a csimp theorem is a
    SPECIFICATION: it stays in the tree for the proofs to be about, the code
    generator emits the right-hand constant instead, and its surviving
    self-call is on no shipping path.  Reporting it as a live stack risk is a
    false positive -- and one that would keep the gate red after a repair,
    which is how a gate gets switched off.
    """
    lean_dir = lean_dir or LEAN_DIR
    repo = repo or REPO
    idx = {}
    tree_types = set()
    pending_csimp = []          # (ns, lhs, rhs, file, line)
    aliases = {}                # short and full alias name -> type text
    inductives = []             # (file, mutual_id or None, short, full, body)
    for root, dirs, files in os.walk(lean_dir):
        dirs[:] = sorted(d for d in dirs if d not in (".lake", ".git", "node_modules"))
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(root, f)
            rel = os.path.relpath(path, repo)
            with open(path, "r", errors="replace") as fh:
                lines = fh.readlines()
            code = CodeLines(lines).code
            scopes = []         # ("ns", "A.B") | ("sec", name) | ("mutual", id)
            mutual_seq = [0]
            opens = []          # namespaces named by `open` (file-wide approximation)

            def ns_parts():
                out = []
                for kind, name in scopes:
                    if kind == "ns":
                        out.extend(name.split("."))
                return out

            def cur_mutual():
                for kind, name in reversed(scopes):
                    if kind == "mutual":
                        return name
                return None

            owner = None            # full name of the current def (for where / let rec)
            where_mode = False
            helper_indent = None
            i = 0
            n = len(code)
            while i < n:
                line = code[i]
                if not line.strip():
                    i += 1
                    continue
                col0 = not line[0].isspace()
                if col0:
                    m = NAMESPACE.match(line)
                    if m:
                        scopes.append(("ns", m.group(1)))
                        owner, where_mode = None, False
                        i += 1
                        continue
                    m = SECTION.match(line)
                    if m:
                        scopes.append(("sec", m.group(1)))
                        owner, where_mode = None, False
                        i += 1
                        continue
                    if MUTUAL.match(line):
                        mutual_seq[0] += 1
                        scopes.append(("mutual", "%s#%d" % (rel, mutual_seq[0])))
                        owner, where_mode = None, False
                        i += 1
                        continue
                    m = END.match(line)
                    if m:
                        name = m.group(1)
                        if name is None:
                            if scopes and scopes[-1][0] in ("mutual", "sec") and \
                               (scopes[-1][0] == "mutual" or scopes[-1][1] is None):
                                scopes.pop()
                        else:
                            # `end A.B` closes scopes whose names join to A.B
                            want = name.split(".")
                            got = []
                            while scopes and len(got) < len(want):
                                kind, nm = scopes.pop()
                                if kind == "mutual":
                                    continue
                                got = (nm or "").split(".") + got
                        owner, where_mode = None, False
                        i += 1
                        continue
                mo = re.match(r"^\s*open\s+([A-Za-z_][A-Za-z0-9_'. ]*?)\s*(?:\bin\b.*)?$", line)
                if mo:
                    opens.extend(o for o in mo.group(1).split() if o not in ("scoped", "in"))
                for cm in CSIMP_ATTR.finditer(line):
                    window = " ".join(code[i:i + 6])
                    mm = CSIMP_EQ.search(window)
                    if mm:
                        pending_csimp.append((ns_parts(), mm.group(1), mm.group(2), rel, i + 1, list(opens)))
                    else:
                        pending_csimp.append((ns_parts(), None, None, rel, i + 1, list(opens)))
                mi = INDUCTIVE.match(line) if col0 else None
                if mi:
                    short = mi.group(2)
                    full = ".".join(ns_parts() + [short])
                    body = [line]
                    j = i + 1
                    while j < n and (not code[j].strip() or code[j][0].isspace()
                                     or code[j].startswith("|")):
                        body.append(code[j])
                        j += 1
                    inductives.append((rel, cur_mutual(), short, full, " ".join(body)))
                    owner, where_mode = None, False
                    i += 1
                    continue
                md = DECL.match(line)
                if md and (col0 or not where_mode or len(md.group(1)) < (helper_indent or 1 << 30)):
                    short = md.group(3)
                    if short.startswith("_root_."):
                        full = short[len("_root_."):]
                    else:
                        full = ".".join(ns_parts() + [short])
                    sig = _sig(code, i, md.end(3))
                    idx[mangle(full)] = {
                        "lean": full, "file": rel, "line": i + 1, "sig": sig,
                        "partial": bool(re.search(r"\bpartial\b", line[:md.start(2)])),
                        "owner": None,
                    }
                    ma = ABBREV_TYPE.match(line.strip())
                    if ma and (md.group(2) == "abbrev" or re.search(r":\s*Type\b", line)):
                        # a type alias: record its head type constructor
                        head = re.match(r"\s*\(?\s*([A-Za-z_][A-Za-z0-9_.]*)", ma.group(2))
                        if head:
                            aliases[short.split(".")[-1]] = head.group(1)
                            aliases[full] = head.group(1)
                    owner = full
                    where_mode = bool(WHERE_END.search(_sig_tail(code, i)))
                    helper_indent = None
                    for mm in LET_REC.finditer(line):
                        _add_helper(idx, owner, mm.group(1), code, i, mm.end(1), rel)
                    i += 1
                    continue
                if col0:
                    if owner is not None and re.match(r"^where\b", line):
                        # `where` in column 0 after the body: helpers follow
                        where_mode = True
                        helper_indent = None
                        i += 1
                        continue
                    if OTHER_TOP.match(line):
                        owner, where_mode = None, False
                    elif not line.startswith(("termination_by", "decreasing_by", "|")):
                        # a column-0 line that is not part of the current definition
                        if where_mode:
                            where_mode = False
                    i += 1
                    continue
                # indented line inside the current definition
                if owner is not None:
                    for mm in LET_REC.finditer(line):
                        _add_helper(idx, owner, mm.group(1), code, i, mm.end(1), rel)
                    if not where_mode and WHERE_END.search(line):
                        where_mode = True
                        helper_indent = None
                        i += 1
                        continue
                    if where_mode:
                        ind = len(line) - len(line.lstrip())
                        if helper_indent is None:
                            helper_indent = ind
                        if ind == helper_indent:
                            mh = WHERE_HELPER.match(line)
                            if mh and mh.group(2) not in NOT_HELPER and not line.lstrip().startswith("|"):
                                _add_helper(idx, owner, mh.group(2), code, i, mh.end(2), rel)
                        elif ind < helper_indent:
                            where_mode = False
                i += 1

    # recursive datatypes: an inductive or structure that mentions itself,
    # or another inductive of the same `mutual` block, in its body
    by_mutual = defaultdict(set)
    for rel, mut, short, full, body in inductives:
        if mut:
            by_mutual[mut].add(short)
    for rel, mut, short, full, body in inductives:
        rest = body.split("\n", 1)[0]
        head_end = re.search(r"\b%s\b" % re.escape(short), body)
        after = body[head_end.end():] if head_end else body
        names = {short} | (by_mutual[mut] if mut else set())
        if any(re.search(r"\b%s\b" % re.escape(nm), after) for nm in names):
            tree_types.add(short)
            tree_types.add(full)

    # length aliases, closed under alias-of-alias
    length_names = set(LENGTH_WORDS)
    changed = True
    while changed:
        changed = False
        for name, rhs in aliases.items():
            if name in length_names:
                continue
            if rhs in length_names or rhs.split(".")[-1] in length_names:
                length_names.add(name)
                changed = True

    # resolve csimp names against the namespace the theorem is written in
    replaced = {}
    unresolved = []
    for ns, lhs, rhs, rel, ln, opened in pending_csimp:
        if lhs is None:
            unresolved.append((rel, ln, "no `@lhs = @rhs` equation found"))
            continue
        full_l = _resolve(idx, ns, lhs, opened)
        full_r = _resolve(idx, ns, rhs, opened) or rhs
        if full_l is None:
            unresolved.append((rel, ln, "left side %s not found" % lhs))
            continue
        replaced[mangle(full_l)] = full_r
    return idx, tree_types, replaced, length_names, unresolved


def _sig_tail(code, i, max_lines=12):
    """The code text from the declaration line to the line holding `:=`."""
    buf = []
    for j in range(i, min(i + max_lines, len(code))):
        buf.append(code[j])
        if ":=" in code[j]:
            break
    return buf[-1] if buf else ""


def _add_helper(idx, owner, name, code, i, col, rel):
    full = owner + "." + name
    key = mangle(full)
    if key in idx:
        return
    idx[key] = {"lean": full, "file": rel, "line": i + 1, "sig": _sig(code, i, col),
                "partial": False, "owner": owner}


def _resolve(idx, ns, name, opened=()):
    """The full name `name` denotes when written inside namespace `ns`.

    The enclosing namespaces are tried innermost first, then the namespaces
    named by `open` (each relative to the enclosing namespaces too).
    """
    if name.startswith("_root_."):
        name = name[len("_root_."):]
    for k in range(len(ns), -1, -1):
        cand = ".".join(ns[:k] + [name])
        if mangle(cand) in idx:
            return cand
    for o in opened:
        for k in range(len(ns), -1, -1):
            cand = ".".join(ns[:k] + o.split(".") + [name])
            if mangle(cand) in idx:
                return cand
    return None


# ----------------------------------------------------------- classification

COUNTER_SIG = re.compile(r"\bNat\b")
RAW_INPUT = re.compile(r"ByteArray|List UInt8|Array UInt8|\bString\b|Substring|List Char|List Token|List Lexeme|\bChars\b")
PARSEY = re.compile(r"decode|parse|read|scan|expand|lex|token|deserial", re.I)

# Core-library functions that Lean specialises into our C files.  The head of
# a `X___at___00Ours_spec__N` symbol is X; when X is one of these, the depth
# is X's, not that of our declaration's signature.
CORE_BOUNDS = [
    (r"^Std_DHashMap_Internal_AssocList_", "bounded",
     "Std.HashMap bucket chain (AssocList): the map doubles its buckets at 75% load, "
     "so the expected chain length is O(1)"),
    (r"^Std_DTreeMap_Internal_Impl_", "bounded",
     "Std.TreeMap walk: depth is the height of a balanced tree, O(log n)"),
    (r"^Array_qsort_sort", "length",
     "Array.qsort partition recursion: expected depth O(log n), worst case n"),
    (r"^List_", "length",
     "core List function specialised at this call site keeps a non-tail recursion over the list"),
    (r"^Array_", "length",
     "core Array function specialised at this call site keeps a non-tail recursion"),
]

DERIVED = re.compile(r"^(.*?)_?inst(Repr|DecidableEq|BEq|Hashable|Ord|ToJson|FromJson|ToString|Inhabited)([A-Za-z0-9]+?)(?:_([A-Za-z0-9]+))?(?:__\d+)?$")


def risk(entry, cls, decl, selfcalls):
    """Rank suspects.  Highest = recursion whose depth a document author sets.

    This is an ORDERING, not a proof.  It has no way to know whether a
    function is reachable from an entry point that sees untrusted input.
    """
    if cls not in ("length", "depth", "counter"):
        return 0
    r = 1
    sig = entry["sig"] if entry else ""
    if RAW_INPUT.search(sig):
        r += 3
    if PARSEY.search(decl):
        r += 2
    if cls == "depth":
        r += 1
    r += min(selfcalls, 3)
    return r


def classify(entry, tree_types, length_names=None):
    if entry is None:
        return "unknown", ""
    length_names = length_names or set(LENGTH_WORDS)
    sig = entry["sig"]
    short = entry["lean"].split(".")[-1]
    # the argument list and result only: drop the declaration's own name
    args = re.sub(r"^\s*%s\b" % re.escape(short), " ", sig, count=1)
    words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", args))
    words |= {w.split(".")[-1] for w in words}
    tree_hit = sorted(t for t in tree_types if "." not in t and t in words)
    len_hit = sorted(w for w in length_names if w in words)
    has_nat = COUNTER_SIG.search(args) is not None
    if len_hit:
        note = "list/array/string argument (%s)" % ", ".join(len_hit[:3])
        if has_nat:
            note += "; Nat step count as well"
        return "length", note
    if tree_hit:
        return "depth", "recursive datatype: " + ", ".join(tree_hit[:3])
    if has_nat:
        return "counter", "Nat step argument -- input-length if the count is read from the input"
    return "bounded", ""


# ------------------------------------------------------------------- areas

AREAS = [
    ("XMPP", r"/XMPP/"),
    ("SPARQL", r"/SPARQL/"),
    ("RDF parsers/serializers", r"/RDF/|/Syntax/"),
    ("Shardborough (storage)", r"/Storage/|/Cottas/|/HDT/"),
    ("JSON-LD", r"/JSONLD/"),
    ("XML", r"/XML/"),
    ("XSD", r"/XSD/"),
    ("OWL", r"/OWL/|/RDFS/"),
    ("SHACL/ShEx", r"/SHACL/|/ShEx/"),
    ("XPath/XSLT", r"/XPath/|/XSLT/"),
    ("CSVW", r"/CSVW/"),
]


def area_of(path):
    for name, pat in AREAS:
        if re.search(pat, "/" + path.replace(os.sep, "/")):
            return name
    return "everything else"


# -------------------------------------------------------------------- graph


def sccs(graph, nodes):
    """Tarjan, iterative.  Returns the components of two or more nodes."""
    index = {}
    low = {}
    onstack = {}
    stack = []
    result = []
    counter = [0]
    for root in sorted(nodes):
        if root in index:
            continue
        work = [(root, iter(sorted(graph.get(root, ()))))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        onstack[root] = True
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in nodes:
                    continue
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    onstack[w] = True
                    work.append((w, iter(sorted(graph.get(w, ())))))
                    advanced = True
                    break
                elif onstack.get(w):
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    onstack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                if len(comp) > 1:
                    result.append(comp)
    return result


def module_recursion(defs, calls, closures):
    """Recursive functions of ONE C file.

    Returns (recursive, comps): `recursive` maps each recursive function to
    "self" (a surviving self-call or self-closure), "cycle" (member of a
    strongly connected component of two or more functions) or "self+cycle";
    `comps` is the list of components (each a sorted list).  `___boxed`
    wrappers are merged into the function they wrap.
    """
    def canon(n):
        if n.endswith("___boxed") and n[: -len("___boxed")] in defs:
            return n[: -len("___boxed")]
        return n

    nodes = set(canon(n) for n in defs if n.startswith(OUR_PREFIX))
    graph = defaultdict(set)
    for n in defs:
        cn = canon(n)
        if cn not in nodes:
            continue
        for c in set(calls.get(n, ())) | set(closures.get(n, ())):
            if c in defs:
                cc = canon(c)
                if cc in nodes and not (n.endswith("___boxed") and cc == cn):
                    graph[cn].add(cc)
    recursive = {}
    for n in nodes:
        if n in graph[n]:
            recursive[n] = "self"
    comps = [sorted(c) for c in sccs(graph, nodes)]
    for comp in comps:
        for m in comp:
            recursive[m] = "self+cycle" if m in recursive else "cycle"
    return recursive, comps


# -------------------------------------------------------------------- main


def build_lookup(lean_idx):
    def lookup_core(core):
        if core in lean_idx:
            return lean_idx[core]
        # `where`-bound helpers that the indexer did not see compile to
        # Owner_go / Owner_loop
        for suffix in ("_go", "_loop", "_aux", "_step"):
            if core.endswith(suffix) and core[: -len(suffix)] in lean_idx:
                return lean_idx[core[: -len(suffix)]]
        return None
    return lookup_core


def resolve_symbol(sym, lookup_core, tree_types, length_names):
    """(decl, entry, class, note, via) for one C symbol."""
    chain = spec_chain(sym)
    head = chain[0] if chain else strip_wrappers(sym)
    entry = lookup_core(head)
    if entry is not None:
        cls, note = classify(entry, tree_types, length_names)
        return decode(head), entry, cls, note, ""
    # a derived instance method: `NS_instReprT_repr__4`, `NS_instDecidableEqT_decEq`.
    # It is on a cycle only when T is recursive, so the depth is T's nesting.
    md = DERIVED.match(head)
    if md:
        return decode(head), None, "depth", \
            "derived %s instance; recursion follows the nesting of %s values" % (md.group(2), md.group(3)), ""
    # a core function specialised at one of our call sites
    for ctx in chain[1:]:
        ce = lookup_core(ctx)
        if ce is None:
            mdc = DERIVED.match(ctx)
            if mdc:
                return decode(ctx), None, "depth", \
                    "derived %s instance; recursion follows the nesting of %s values (through %s)" % (
                        mdc.group(2), mdc.group(3), decode(head)), decode(head)
            continue
        for pat, cls, note in CORE_BOUNDS:
            if re.search(pat, head):
                return decode(ctx), ce, cls, note, decode(head)
        return decode(ctx), ce, "unknown", "core function specialised here; depth not known to this tool", decode(head)
    decl = decode(chain[-1] if len(chain) > 1 else head)
    return decl, None, "unknown", "", decode(head) if len(chain) > 1 else ""


def run_audit(ir_dir=None, lean_dir=None, repo=None):
    """Scan the IR and the Lean source.  Returns a dict, or an int exit code."""
    ir_dir = ir_dir or IR_DIR
    lean_dir = lean_dir or LEAN_DIR
    repo = repo or REPO
    if not os.path.isdir(ir_dir):
        sys.stderr.write("no compiled IR at %s -- run `lake build` in formal/lean4 first\n" % ir_dir)
        return 2
    cfiles = []
    for root, _dirs, files in os.walk(ir_dir):
        for f in files:
            if f.endswith(".c"):
                cfiles.append(os.path.join(root, f))
    cfiles.sort()
    if not cfiles:
        sys.stderr.write("no .c files under %s -- refusing to report a zero\n" % ir_dir)
        return 2

    lean_idx, tree_types, csimp_replaced, length_names, csimp_unresolved = index_lean(lean_dir, repo)
    if not lean_idx:
        sys.stderr.write("no Lean declarations found under %s -- refusing to report\n" % lean_dir)
        return 2
    lookup_core = build_lookup(lean_idx)

    rows = []
    cycle_rows = []
    nfuncs = 0
    for path in cfiles:
        defs, calls, closures = scan_c_file(path)
        nfuncs += len(defs)
        rel = os.path.relpath(path, ir_dir)
        recursive, comps = module_recursion(defs, calls, closures)
        comp_of = {}
        for comp in comps:
            for m in comp:
                comp_of[m] = comp
        for sym in sorted(recursive):
            d = defs[sym]
            boxed = defs.get(sym + "___boxed", {"self": 0, "selfclosure": 0})
            decl, entry, cls, note, via = resolve_symbol(sym, lookup_core, tree_types, length_names)
            if entry is not None:
                lean_name = entry["lean"]
                own = entry.get("owner")
                if mangle(lean_name) in csimp_replaced:
                    cls = "replaced"
                    note = "specification; the code generator emits %s (@[csimp])" % csimp_replaced[mangle(lean_name)]
                elif own and mangle(own) in csimp_replaced:
                    cls = "replaced"
                    note = "helper of %s, a specification the code generator replaces by %s (@[csimp])" % (
                        own, csimp_replaced[mangle(own)])
            leanfile = entry["file"] if entry else ""
            comp = comp_of.get(sym, [])
            selfn = d["self"] + d["selfclosure"] + boxed["selfclosure"]
            rows.append({
                "risk": risk(entry, cls, decl, max(selfn, 1)),
                "symbol": sym,
                "decl": decl,
                "lean": entry["lean"] if entry else "",
                "file": leanfile,
                "line": entry["line"] if entry else 0,
                "class": cls,
                "note": note,
                "via": via,
                "selfcalls": d["self"],
                "selfclosure": d["selfclosure"] + boxed["selfclosure"],
                "tailjumps": d["tail"],
                "cfile": rel,
                "area": area_of(leanfile or rel),
                "partial": bool(entry and entry["partial"]),
                "kind": recursive[sym],
                "cycle_size": len(comp),
                "cycle": [readable(m) for m in comp[:8]],
            })
        for comp in comps:
            members = [r for r in rows if r["symbol"] in set(comp) and r["cfile"] == rel]
            classes = set(r["class"] for r in members)
            worst = next((c for c in ("length", "depth", "counter", "unknown", "bounded", "replaced")
                          if c in classes), "unknown")
            first = next((r for r in members if r["class"] == worst), members[0] if members else None)
            cycle_rows.append({
                "members": [readable(m) for m in comp],
                "size": len(comp),
                "class": worst,
                "note": first["note"] if first else "",
                "file": first["file"] if first else "",
                "area": first["area"] if first else area_of(rel),
                "cfile": rel,
            })
    return {
        "rows": rows, "cycles": cycle_rows, "cfiles": len(cfiles), "functions": nfuncs,
        "decls": len(lean_idx), "csimp": len(csimp_replaced), "csimp_unresolved": csimp_unresolved,
        "length_aliases": sorted(set(length_names) - set(LENGTH_WORDS)),
    }


def allowed(decl, allow):
    """Is `decl` on the allow list?  A line with `*` is an fnmatch pattern."""
    if decl in allow:
        return True
    return any("*" in pat and fnmatch.fnmatchcase(decl, pat) for pat in allow)


def read_allow(path):
    """decl -> comment (the text after `#`, possibly empty)."""
    allow = {}
    if os.path.exists(path):
        with open(path) as fh:
            for line in fh:
                body, _, comment = line.partition("#")
                body = body.strip()
                if body:
                    allow[body] = comment.strip()
    return allow


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", metavar="PATH", help="write the full table as JSON")
    ap.add_argument("--gate", action="store_true",
                    help="exit 1 if a recursive declaration of class length, depth, counter "
                         "or unknown is not in tools/lean-tail-recursion-allow.txt")
    ap.add_argument("--allow", default=None)
    ap.add_argument("--ir-dir", default=None, help="compiled IR directory (default: formal/lean4/.lake/build/ir)")
    ap.add_argument("--lean-dir", default=None, help="Lean source directory (default: formal/lean4)")
    ap.add_argument("--write-allow", action="store_true",
                    help="rewrite the allow file from this run (records the baseline)")
    ap.add_argument("--fstar", action="store_true",
                    help="scan formal/fstar/ocaml-output/*.ml for non-tail self-calls instead")
    ap.add_argument("--top", type=int, default=40, help="rows to print per class")
    args = ap.parse_args(argv)
    allow_path = args.allow or os.path.join(REPO, "tools", "lean-tail-recursion-allow.txt")

    if args.fstar:
        return fstar_mode(args)

    res = run_audit(args.ir_dir, args.lean_dir, REPO if not args.lean_dir else os.path.dirname(os.path.dirname(os.path.abspath(args.lean_dir))))
    if isinstance(res, int):
        return res
    rows, cycle_rows = res["rows"], res["cycles"]

    # ---------------------------------------------------------------- report
    print("Lean tail-recursion audit")
    print("=========================")
    print("C files scanned: %d   functions defined: %d   Lean declarations indexed: %d"
          % (res["cfiles"], res["functions"], res["decls"]))
    print("@[csimp] replacements resolved by full name: %d   not resolved: %d"
          % (res["csimp"], len(res["csimp_unresolved"])))
    for rel, ln, why in res["csimp_unresolved"]:
        print("  csimp not resolved: %s:%d (%s)" % (rel, ln, why))
    if res["length_aliases"]:
        short = sorted(set(x for x in res["length_aliases"] if "." not in x))
        print("Type aliases read as list/array/string types: %d (%s, ...; full list in --json)"
              % (len(short), ", ".join(short[:8])))
    nself = sum(1 for r in rows if "self" in r["kind"])
    ncyc = sum(1 for r in rows if r["kind"] == "cycle")
    print("Recursive functions whose recursion is NOT a `goto _start` loop: %d"
          % len(rows))
    print("  with a surviving self-call or self-closure: %d   only through a cycle: %d" % (nself, ncyc))
    print("Mutual-recursion cycles (strongly connected components, per module): %d" % len(cycle_rows))
    print()

    per_class = defaultdict(int)
    decls_per_class = defaultdict(set)
    for r in rows:
        per_class[r["class"]] += 1
        decls_per_class[r["class"]].add(r["decl"])
    print("By class (C functions / distinct declarations)")
    print("----------------------------------------------")
    for c in ("length", "depth", "counter", "bounded", "replaced", "unknown"):
        print("  %-9s %5d %5d%s" % (c, per_class.get(c, 0), len(decls_per_class.get(c, ())),
                                    "   gated" if c in GATED else ""))
    print()

    per_area = defaultdict(lambda: defaultdict(int))
    for r in rows:
        per_area[r["area"]][r["class"]] += 1
    print("By area (length / depth / counter / bounded / replaced / unknown)")
    print("----------------------------------------------------------------")
    names = [n for n, _ in AREAS] + ["everything else"]
    for a in names:
        d = per_area.get(a)
        if not d:
            continue
        print("  %-26s %4d %4d %4d %4d %4d %4d" % (
            a, d.get("length", 0), d.get("depth", 0), d.get("counter", 0),
            d.get("bounded", 0), d.get("replaced", 0), d.get("unknown", 0)))
    print()

    ranked = sorted(rows, key=lambda r: (-r["risk"], r["area"], r["decl"]))
    print("Input-proportional recursions (class length and depth), ranked by risk")
    print("----------------------------------------------------------------------")
    print("%-4s %-48s %-8s %-24s %s" % ("risk", "declaration", "class", "area", "lean file:line"))
    shown = 0
    for r in ranked:
        if r["class"] not in ("length", "depth"):
            continue
        shown += 1
        if shown > args.top:
            break
        print("%-4d %-48s %-8s %-24s %s:%d" % (
            r["risk"], r["decl"][:48], r["class"], r["area"][:24], r["file"] or "?", r["line"]))
    remaining = sum(1 for r in ranked if r["class"] in ("length", "depth")) - min(shown, args.top)
    if remaining > 0:
        print("  ... %d more (use --json for the full table)" % remaining)
    print()

    if cycle_rows:
        print("Mutual-recursion cycles (largest 20)")
        print("------------------------------------")
        for c in sorted(cycle_rows, key=lambda c: (-c["size"], c["members"][0]))[:20]:
            print("  size %-3d %-8s %s" % (c["size"], c["class"], ", ".join(c["members"][:4])))
        print()

    print("Method limits: see the docstring at the top of this file.")

    if args.json:
        with open(args.json, "w") as fh:
            json.dump(res, fh, indent=1)
        print("wrote %s" % args.json)

    if args.write_allow:
        with open(allow_path, "w") as fh:
            fh.write("# Baseline for `tools/lean-tail-recursion-audit.py --gate`.\n")
            for r in sorted(set(r["decl"] for r in rows if r["class"] in GATED)):
                fh.write(r + "\n")
        print("wrote %s" % os.path.relpath(allow_path, REPO))

    if args.gate:
        allow = read_allow(allow_path)
        offenders = {}
        for r in rows:
            if r["class"] in GATED and not allowed(r["decl"], allow):
                offenders.setdefault(r["decl"], r)
        gated_decls = set(r["decl"] for r in rows if r["class"] in GATED)
        unused = sorted(d for d in allow if d not in gated_decls and not (
            "*" in d and any(fnmatch.fnmatchcase(g, d) for g in gated_decls)))
        pending = sum(1 for d, c in allow.items() if "PENDING" in c)
        untriaged = sum(1 for d, c in allow.items() if "UNTRIAGED" in c)
        print()
        print("Allow list: %d lines, %d marked (a) PENDING, %d marked UNTRIAGED, %d match no gated row"
              % (len(allow), pending, untriaged, len(unused)))
        if offenders:
            print()
            print("GATE FAIL: %d recursive declaration(s) of class %s not in %s"
                  % (len(offenders), "/".join(GATED), os.path.relpath(allow_path, REPO)))
            for decl in sorted(offenders):
                r = offenders[decl]
                print("  %s  (%s, %s)  %s:%d%s" % (decl, r["class"], r["kind"], r["file"] or r["cfile"],
                                                  r["line"], ("  via " + r["via"]) if r["via"] else ""))
            return 1
        print()
        print("GATE PASS: every recursive declaration of class %s is listed in %s"
              % ("/".join(GATED), os.path.relpath(allow_path, REPO)))
    return 0


# ------------------------------------------------------------- F* / OCaml

ML_LET = re.compile(r"^(?:let|and)\s+rec\s+([A-Za-z_][A-Za-z0-9_']*)")
ML_TOP = re.compile(r"^(?:let|and|type|module|open|exception|external|val)\b")


def fstar_mode(args):
    ml_dir = os.path.join(REPO, "formal", "fstar", "ocaml-output")
    if not os.path.isdir(ml_dir):
        sys.stderr.write("no %s\n" % ml_dir)
        return 2
    files = sorted(f for f in os.listdir(ml_dir) if f.endswith(".ml"))
    if not files:
        sys.stderr.write("no .ml under %s -- refusing to report a zero\n" % ml_dir)
        return 2
    found = []
    for f in files:
        path = os.path.join(ml_dir, f)
        with open(path, "r", errors="replace") as fh:
            lines = fh.readlines()
        cur = None
        start = 0
        body = []
        for i, line in enumerate(lines + ["let __eof = ()\n"]):
            m = ML_LET.match(line)
            if m or (ML_TOP.match(line) and cur):
                if cur:
                    text = "".join(body)
                    calls = len(re.findall(r"\b%s\b" % re.escape(cur), text))
                    if calls:
                        found.append((f, start + 1, cur, calls))
                cur = m.group(1) if m else None
                start = i
                body = []
                continue
            if cur:
                body.append(line)
    print("F* extracted-OCaml self-recursion scan (source shape, not compiled form)")
    print("=======================================================================")
    print("files: %d   recursive functions with a self-call: %d" % (len(files), len(found)))
    print()
    print("This mode is COARSER than the Lean mode: OCaml is not compiled to a")
    print("readable IR here, so it cannot tell a tail call from a stacked one.")
    print("It ranks `let rec` definitions by self-call count as suspects only.")
    print()
    for f, ln, name, n in sorted(found, key=lambda t: -t[3])[:args.top]:
        print("  %-40s %-28s %s:%d" % (name[:40], "%d self-call(s)" % n, f, ln))
    return 0


if __name__ == "__main__":
    sys.exit(main())
