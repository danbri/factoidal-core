#!/usr/bin/env python3
"""Inventory of the top-level F* lemmas under formal/fstar, with a relevance
rule (https://github.com/danbri/factoidal/issues/757, steps 1 and 2).

    python3 tools/fstar-theorem-inventory.py                 # TSV to stdout
    python3 tools/fstar-theorem-inventory.py --out PATH      # TSV to PATH
    python3 tools/fstar-theorem-inventory.py --stats         # counts to stderr
    python3 tools/fstar-theorem-inventory.py --root DIR      # another tree

The tree is walked on every run (anti-pattern 30). An empty walk, or a walk
that finds no lemma, exits 2.

WHAT IS READ
------------
Every *.fst and *.fsti file below the root, recursively.

Comments are removed first, with the F* lexer's own rules
(FStarC_Parser_LexFStar.ml, F* 2025): `(*` opens a block comment and block
comments NEST, `*)` closes one level, there is no string handling inside a
block comment; `//` (and so `///`) comments out the rest of the line; a
string literal is `"` ... `"` with backslash escapes; a character literal is
`'c'` or `'\\e'` when the `'` does not continue an identifier. A lemma inside
a comment is therefore not found (CLAUDE.md, "F* Syntax Traps", 1).

A TOP-LEVEL DECLARATION starts at a line whose column 0 holds one of the
declaration keywords (let, val, and, assume, type, noeq, unopteq, open,
module, include, friend, instance, class, effect, new_effect, sub_effect,
layered_effect, exception, #push-options, #pop-options, #set-options,
#reset-options, #restart-solver, %splice) or a qualifier (private, unfold,
irreducible, noextract, inline_for_extraction, abstract, opaque_to_smt) or an
attribute `[@`. A line holding only qualifiers or attributes joins the next
declaration. Every other line continues the declaration above it. Measured
2026-10-10: the column-0 lines that are not in this set are `}`, `;`, `=`,
`]`, `)`, `[` (a list literal) and one continuation line, all continuations.
Local `let ... : Lemma ... in` definitions inside a proof are indented and
are not top-level declarations.

RECOGNISED LEMMA FORMS
----------------------
A declaration is a lemma when its keyword is one of

    val NAME ... : ... Lemma ...          (statement; the proof is a later
                                           `let NAME ... =` with no type)
    assume val NAME ... : ... Lemma ...   (an axiom; kind "assume val")
    let NAME ... : ... Lemma ... = ...
    let rec NAME ... : ... Lemma ... = ...
    and NAME ... : ... Lemma ... = ...    (mutual recursion)

and its RESULT computation type starts with the word `Lemma`. The result
type is the text after the first depth-0 `:` of the signature, cut at the
last depth-0 `->`. A `Lemma` that is only the type of a binder, for example
`(f : x:t -> Lemma (p x))`, does not make the declaration a lemma. The
signature of a `let` ends at the first depth-0 `=` that is not part of an
operator; the signature of a `val` is the whole declaration. Depth counts
(), [] and {} (and so (| |), [| |], {| |}).

The form `let NAME = e <: Lemma ...` (an ascription on the body) was looked
for and does not occur in the tree (2026-10-10); it is not recognised.
Declarations whose result is `Pure unit ...`, `Ghost unit ...`,
`GTot unit` or `squash ...` state a property too but are NOT lemmas here;
`--stats` prints how many of them there are.

When a module has both `val NAME` (in the .fsti or the .fst) and `let NAME`
with a `Lemma` type, one row is kept: the `.fsti` val, then the `.fst` val,
then the let.

COLUMNS (TSV, one header line)
------------------------------
module, name, kind, location (path:line from the repository root),
relevance (RELEVANT or HELPER), reasons, refs_local (declarations of the
same module that reference the lemma), refs_external (Module.name of
declarations in other modules that reference it), statement_sha256,
statement.

The STATEMENT is the declaration without its qualifiers and keyword: the
name, the binders and the type (for a let, up to the definitional `=`),
with every run of white space replaced by one space. statement_sha256 is
the SHA-256 of the UTF-8 statement text. A white-space change does not
change the hash; any other change does.

REFERENCES are found by a WORD MATCH: declaration D references lemma L
(module M, name n) when the comment-free text of D contains n as a whole
F* identifier (letters, digits, _ and '), D is not L itself or its own
val/let partner, and D's module is M or names M somewhere in its text
(`open M`, `module X = M`, `M.n`, `friend M`, `include M`), directly or
through `include`. This over-approximates: a local binder or a same-named
definition in a visible module counts as a reference. It never
under-approximates an explicit use. A use through an SMT pattern is not
visible to it; see PAT below.

RELEVANCE RULE (also in docs/theorem-registry.md, "F* theorem classification")
-------------------------------------------------------------
Applied to the STATEMENT and the reference sets only. The lemma's own name
is never read; a name resemblance never decides relevance (anti-pattern 31).
A lemma is RELEVANT, with these reason codes, when any of them holds:

  EXT     it is referenced from a declaration of another module.
  SPEC    the statement uses a definition (not a lemma) of a specification
          module: a module with a name component `Spec`, derived from the
          tree on each run, or one listed in SPEC_EXTRA.
  SEM     the statement names a semantics: it uses a definition of a module
          listed in SEMANTICS_MODULES (the interpretation, model and
          entailment definitions), or an identifier with a segment in
          SEM_WORDS (interp, interpretation, entails, entailment, model,
          satisfies, holds, denot, ...).
  W3C     the statement uses a definition of a module listed in
          W3C_FUNCTION_MODULES (RDFC-1.0 canonicalization, the SPARQL
          algebra and its operators, graph isomorphism, JSON-LD, CSVW,
          SHACL, ShEx, XPath, XSD).
  PROP    the statement uses an identifier with a segment in PROP_WORDS
          (sound, complete, refines, licensed, equiv, fixpoint, terminates,
          roundtrip, ...): it states soundness, completeness, refinement,
          equivalence of a fast form with a reference form, or termination.
  RT      the statement uses both a parsing identifier (segment in
          PARSE_WORDS) and a printing identifier (segment in PRINT_WORDS):
          a round trip.
  ASSUMED it is an `assume val`: an axiom the F* proofs rest on.
  TOP     no declaration references it and it has no SMT pattern: a result
          stated for its own sake, or an unused lemma. The rule cannot tell
          which, so it is RELEVANT.
  PAT     it has an SMT pattern and so can be used where no word match sees
          it. The rule cannot decide, so it is RELEVANT.
  MULTI   it is referenced by more than one declaration, all in its own
          module: it is not used "inside one proof only". The rule cannot
          decide, so it is RELEVANT.

It is a HELPER (NOT RELEVANT, code LOCAL1) only when it is referenced by
exactly one declaration, of its own module, has no SMT pattern, is not
assumed, and none of EXT, SPEC, SEM, W3C, PROP, RT holds. Where the rule
cannot decide, the row is RELEVANT: it errs towards classifying.

Each content code prints the identifier that triggered it, e.g.
`SEM:rdfs_entails`, so a reader can check the decision.
"""

import argparse, hashlib, os, re, sys
from collections import defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_ROOT = os.path.join(REPO, "formal", "fstar")

# ---------------------------------------------------------------------------
# Rule tables. Every module named here must exist in the walked tree, or the
# tool exits 2 (counting-coverage rule 4: a list must report its own gaps).
# They are checked only when the walk is the real tree (--root not given).
# ---------------------------------------------------------------------------
SPEC_EXTRA = [
    "RDF.Entailment.Simple.Boundary",   # the simple-entailment interpolation condition
]
SEMANTICS_MODULES = [
    "OWL.Semantics",                     # interp, denot_*, satisfies, entails_under
    "RDF.Entailment.Simple.ModelTheory",
    "RDF.Entailment.RDFS.ModelTheory",
    "RDF.Semantics.HypothesisWitness",
]
W3C_FUNCTION_MODULES = [
    "RDF.Canonical",                     # RDFC-1.0
    "RDF.GraphIsomorphism",              # RDF 1.1 Concepts graph isomorphism
    "SPARQL11.Algebra",                  # SPARQL 1.1 algebra and its operators
    "JSONLD.Expand", "JSONLD.Compact", "JSONLD.Flatten", "JSONLD.FromRdf",
    "JSONLD.Frame",
    "CSVW.Conversion",
    "SHACL.Validation",
    "ShEx.Validation",
    "XPath.Eval",
    "XSD.Datatypes", "XSD.Facets",
]
SEM_WORDS = {
    "interp", "interpretation", "interpretations", "entails", "entailment",
    "entailed", "model", "models", "satisfies", "satisfy", "satisfiable",
    "satisfaction", "holds", "denot", "denotation", "iext", "icext",
}
PROP_WORDS = {
    "sound", "soundness", "complete", "completeness", "refines",
    "refinement", "licensed", "licenses", "license", "equiv", "equivalent",
    "equivalence", "fixpoint", "terminates", "termination", "roundtrip",
    "correct", "correctness", "isomorphic",
}
PARSE_WORDS = {"parse", "parser", "parsed", "decode", "decoder", "deserialize",
               "deserialise", "unescape", "lex", "tokenize", "scan"}
PRINT_WORDS = {"serialize", "serialise", "serializer", "serialised",
               "serialized", "encode", "encoder", "print", "printer",
               "render", "escape", "emit"}

DECL_KW = {"let", "val", "and", "assume", "type", "noeq", "unopteq", "open",
           "module", "include", "friend", "instance", "class", "effect",
           "new_effect", "sub_effect", "layered_effect", "exception",
           "#push-options", "#pop-options", "#set-options", "#reset-options",
           "#restart-solver", "%splice"}
QUALIFIERS = {"private", "unfold", "irreducible", "noextract",
              "inline_for_extraction", "abstract", "opaque_to_smt", "total",
              "reifiable", "reflectable"}

IDCH = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'")
OPCH = set("!$%&*+-.<>=?^|~:@#\\/")
CHAR_RE = re.compile(r"'(\\(x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\\n])'B?")
IDENT_RE = re.compile(r"(?<![\w'])([A-Za-z_][\w']*)")
MODNAME_RE = re.compile(r"(?<![\w'.])([A-Z][\w']*(?:\.[A-Z][\w']*)*)")


def strip_comments(src):
    """Return src with comments blanked and string/char literal contents
    blanked, keeping every newline (so line numbers are unchanged)."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("(*", i):
                depth += 1; out.append("  "); i += 2; continue
            if src.startswith("*)", i):
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if c == "\n" else " "); i += 1; continue
        if src.startswith("(*", i):
            depth = 1; out.append("  "); i += 2; continue
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if c == '"':
            out.append('"'); i += 1
            while i < n and src[i] != '"':
                if src[i] == "\\" and i + 1 < n:
                    out.append(" "); out.append("\n" if src[i + 1] == "\n" else " ")
                    i += 2; continue
                out.append("\n" if src[i] == "\n" else " "); i += 1
            out.append('"'); i += 1; continue
        if c == "'" and (i == 0 or src[i - 1] not in IDCH):
            m = CHAR_RE.match(src, i)
            if m:
                out.append("'" + " " * (m.end() - i - 2) + "'"); i = m.end(); continue
        out.append(c); i += 1
    return "".join(out)


def first_token(line):
    m = re.match(r"\s*(\[@@?|[^\s(\[]+)", line)
    return m.group(1) if m else ""


def skip_attr(text, i):
    """text[i:] starts with `[@`; return the index after the matching `]`."""
    d = 0
    while i < len(text):
        if text[i] == "[": d += 1
        elif text[i] == "]":
            d -= 1
            if d == 0: return i + 1
        i += 1
    return i


def is_qualifier_line(line):
    s = line.strip()
    i = 0
    while i < len(s):
        if s[i].isspace(): i += 1; continue
        if s.startswith("[@", i): i = skip_attr(s, i); continue
        m = re.match(r"[A-Za-z_]+", s[i:])
        if m and m.group(0) in QUALIFIERS: i += m.end(); continue
        return False
    return bool(s)


def split_decls(stripped):
    """Yield (start_line_1based, text) for each top-level declaration."""
    lines = stripped.split("\n")
    starts = []
    pending = None
    for k, line in enumerate(lines):
        if not line or line[0].isspace():
            continue
        tok = first_token(line)
        if tok.startswith("[@") or tok in QUALIFIERS:
            if is_qualifier_line(line):
                if pending is None: pending = k
                continue
            starts.append(pending if pending is not None else k); pending = None
            continue
        if tok in DECL_KW:
            starts.append(pending if pending is not None else k); pending = None
    out = []
    for j, s in enumerate(starts):
        e = starts[j + 1] if j + 1 < len(starts) else len(lines)
        out.append((s + 1, "\n".join(lines[s:e])))
    return out


def depth0_positions(text, pred):
    """Indices i where depth is 0 and pred(text, i) holds."""
    d = 0
    res = []
    for i, c in enumerate(text):
        if c in "([{": d += 1; continue
        if c in ")]}": d -= 1; continue
        if d == 0 and pred(text, i): res.append(i)
    return res


def _standalone(text, i, ch):
    if text[i] != ch: return False
    a = text[i - 1] if i > 0 else " "
    b = text[i + 1] if i + 1 < len(text) else " "
    return a not in OPCH and b not in OPCH


def is_eq(text, i): return _standalone(text, i, "=")
def is_colon(text, i): return _standalone(text, i, ":")


def is_arrow(text, i):
    if not text.startswith("->", i): return False
    a = text[i - 1] if i > 0 else " "
    b = text[i + 2] if i + 2 < len(text) else " "
    return a not in OPCH and b not in OPCH


DECL_HEAD_RE = re.compile(r"\s*(assume\s+val|val|let\s+rec|let|and)\s+")
NAME_RE = re.compile(r"([a-z_][\w']*)")


def parse_decl(text):
    """Return a dict for a let/val/and/assume val declaration, or None."""
    i = 0
    while True:
        m = re.match(r"\s*", text[i:]); i += m.end()
        if text.startswith("[@", i): i = skip_attr(text, i); continue
        m = re.match(r"[A-Za-z_]+", text[i:])
        if m and m.group(0) in QUALIFIERS: i += m.end(); continue
        break
    m = DECL_HEAD_RE.match(text, i)
    if not m: return None
    kw = re.sub(r"\s+", " ", m.group(1))
    j = m.end()
    nm = NAME_RE.match(text, j)
    if not nm: return None
    name = nm.group(1)
    if name in ("rec", "_"): return None
    base = nm.end()
    rest = text[base:]
    if kw in ("val", "assume val"):
        sig = rest
    else:
        eqs = depth0_positions(rest, is_eq)
        sig = rest[:eqs[0]] if eqs else rest
    colons = depth0_positions(sig, is_colon)
    result, result_at = None, None
    if colons:
        ty_at = colons[0] + 1
        ty = sig[ty_at:]
        arrows = depth0_positions(ty, is_arrow)
        r_at = ty_at + (arrows[-1] + 2 if arrows else 0)
        raw = sig[r_at:]
        result = raw.strip()
        result_at = base + r_at + (len(raw) - len(raw.lstrip()))
    stmt = re.sub(r"\s+", " ", name + sig).strip()
    return {"kw": kw, "name": name, "result": result, "statement": stmt,
            "smtpat": bool(re.search(r"\bSMTPat(Or)?\b", sig)),
            "sig_span": (base, base + len(sig)), "result_at": result_at}


def ident_segments(ident):
    base = ident.split(".")[-1]
    parts = []
    for p in re.split(r"[_']+", base):
        parts += re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|[0-9]+", p)
    return [p.lower() for p in parts if p]


def module_of(path, stripped):
    m = re.search(r"^module\s+([A-Z][\w'.]*)\s*$", stripped, re.M)
    if m: return m.group(1)
    base = os.path.basename(path)
    return base[: -5] if base.endswith(".fsti") else base[: -4]


def family_of(module):
    """F* module family for the counts of issue 757 step 4 (e)."""
    if (module.startswith("Parser.") or module.startswith("SPARQL11.Parser")
            or module in ("RDF.NTriples.RoundTrip", "RDF.Turtle.Serialize")
            or module.startswith("RDF.NQuads.")):
        return "parsers"
    if module.startswith("RDF.Entailment.RDFS") or module.startswith("RDFS."):
        return "RDFS"
    if module.startswith("RDF."): return "RDF"
    if module.startswith(("OWL.", "OWL2.", "Tableau")) or module == "Tableau":
        return "OWL"
    if module.startswith(("SPARQL.", "SPARQL11.")): return "SPARQL"
    return "other"


def walk(root):
    files = []
    for dp, dn, fn in os.walk(root):
        dn.sort()
        for f in sorted(fn):
            if f.endswith((".fst", ".fsti")):
                files.append(os.path.join(dp, f))
    return files


def build(root, check_tables):
    files = walk(root)
    if not files:
        sys.exit("fstar-theorem-inventory: no .fst/.fsti file under %s" % root)
    decls = []           # every top-level declaration
    mod_text = defaultdict(list)
    stats = defaultdict(int)
    word = re.compile(r"(?<![\w'])Lemma(?![\w'])")
    for path in files:
        raw = open(path, encoding="utf-8", errors="replace").read()
        stripped = strip_comments(raw)
        mod = module_of(path, stripped)
        mod_text[mod].append(stripped)
        stats["files"] += 1
        # Where each line that `grep -c Lemma` counts comes from (see the
        # classification doc): comment or string only, a longer identifier
        # only (`MemLemmas`), the result type of a top-level lemma, a binder
        # or non-result position of a top-level signature, or the body of a
        # declaration (a local lemma inside a proof).
        raw_lines, code_lines = raw.split("\n"), stripped.split("\n")
        cat = {}
        for k, l in enumerate(raw_lines):
            if "Lemma" not in l: continue
            stats["grep_lines"] += 1
            if not word.search(code_lines[k]):
                cat[k] = ("comment_or_string_only" if "Lemma" not in code_lines[k]
                          else "longer_identifier_only")
        for line_no, text in split_decls(stripped):
            p = parse_decl(text)
            decls.append({"module": mod, "path": path, "line": line_no,
                          "text": text, "parsed": p,
                          "fsti": path.endswith(".fsti")})
            for m in word.finditer(text):
                k = line_no - 1 + text.count("\n", 0, m.start())
                if p and p["result_at"] == m.start():
                    c = "top_level_result"
                elif p and p["sig_span"][0] <= m.start() < p["sig_span"][1]:
                    c = "top_level_signature_other"
                else:
                    c = "declaration_body"
                order = ["top_level_result", "top_level_signature_other", "declaration_body"]
                if k not in cat or (cat[k] in order and order.index(c) < order.index(cat[k])):
                    cat[k] = c
        for c in cat.values(): stats["grep_lines_" + c] += 1
    modules = set(mod_text)
    rel = lambda p: os.path.relpath(p, REPO) if p.startswith(REPO) else p

    if check_tables:
        bad = [m for m in SPEC_EXTRA + SEMANTICS_MODULES + W3C_FUNCTION_MODULES
               if m not in modules]
        if bad:
            sys.exit("fstar-theorem-inventory: rule tables name modules that do "
                     "not exist: %s" % ", ".join(bad))

    # Module visibility: M sees N when M names N, closed under `include`.
    mentions, includes = {}, defaultdict(set)
    for mod, texts in mod_text.items():
        s = set()
        for t in texts:
            for m in MODNAME_RE.finditer(t):
                parts = m.group(1).split(".")
                for k in range(1, len(parts) + 1):
                    cand = ".".join(parts[:k])
                    if cand in modules: s.add(cand)
            for m in re.finditer(r"^include\s+([A-Z][\w'.]*)", t, re.M):
                includes[mod].add(m.group(1))
        s.add(mod)
        mentions[mod] = s
    visible = {}
    for mod in modules:
        seen = set(mentions[mod]); stack = list(seen)
        while stack:
            x = stack.pop()
            for y in includes.get(x, ()):
                if y not in seen: seen.add(y); stack.append(y)
        visible[mod] = seen

    # Definitions (non-lemma) per module, for SPEC / SEM / W3C resolution.
    spec_modules = {m for m in modules if "Spec" in m.split(".")} | set(SPEC_EXTRA)
    defined_in = defaultdict(set)    # identifier -> modules that define it (non-lemma)
    for d in decls:
        p = d["parsed"]
        if p is not None:
            if not re.match(r"Lemma\b", p["result"] or ""):
                defined_in[p["name"]].add(d["module"])
        else:
            m = re.match(r"\s*(?:noeq\s+|unopteq\s+)?type\s+([a-z_][\w']*)", d["text"])
            if m:
                defined_in[m.group(1)].add(d["module"])
                for c in re.finditer(r"\|\s*([A-Z][\w']*)", d["text"]):
                    defined_in[c.group(1)].add(d["module"])

    # Lemmas.
    lemma_rank = lambda d: (0 if d["fsti"] and d["parsed"]["kw"] == "val" else
                            1 if d["parsed"]["kw"] in ("val", "assume val") else 2)
    by_key = {}
    for d in decls:
        p = d["parsed"]
        if p is None or p["result"] is None: continue
        if re.match(r"Lemma\b", p["result"]):
            key = (d["module"], p["name"])
            if key not in by_key or lemma_rank(d) < lemma_rank(by_key[key]):
                by_key[key] = d
            stats["lemma_decls_" + p["kw"].replace(" ", "_")] += 1
        elif re.match(r"(Pure|Ghost)\s+unit\b|GTot\s+unit\b|squash\b", p["result"]):
            stats["not_recognised_pure_ghost_squash"] += 1
    if not by_key:
        sys.exit("fstar-theorem-inventory: found no lemma under %s" % root)

    # Reference index: identifier -> declarations whose text contains it.
    token_index = defaultdict(list)
    for idx, d in enumerate(decls):
        for tok in set(IDENT_RE.findall(d["text"])):
            token_index[tok].append(idx)

    rows = []
    for (mod, name), d in sorted(by_key.items()):
        p = d["parsed"]
        refs_local, refs_ext = set(), set()
        for idx in token_index.get(name, ()):
            e = decls[idx]
            ename = e["parsed"]["name"] if e["parsed"] else None
            if e["module"] == mod and ename == name: continue
            if mod not in visible.get(e["module"], ()): continue
            label = ename if ename else "%s:%d" % (os.path.basename(e["path"]), e["line"])
            if e["module"] == mod: refs_local.add(label)
            else: refs_ext.add("%s.%s" % (e["module"], label))
        stmt_body = p["statement"][len(name):]
        idents = set(IDENT_RE.findall(stmt_body)) - {name}
        reasons = []
        if refs_ext: reasons.append("EXT")
        vis = visible.get(mod, {mod})

        def resolve(ids, mods):
            hits = sorted(i for i in ids
                          if any(m in mods and m in vis for m in defined_in.get(i.split(".")[-1], ())))
            return hits
        h = resolve(idents, spec_modules)
        if h: reasons.append("SPEC:" + h[0])
        h = resolve(idents, set(SEMANTICS_MODULES))
        hw = sorted(i for i in idents if set(ident_segments(i)) & SEM_WORDS)
        if h or hw: reasons.append("SEM:" + (h or hw)[0])
        h = resolve(idents, set(W3C_FUNCTION_MODULES))
        if h: reasons.append("W3C:" + h[0])
        hp = sorted(i for i in idents if set(ident_segments(i)) & PROP_WORDS)
        rt = sorted(i for i in idents if "round" in ident_segments(i)
                    and "trip" in ident_segments(i))
        if hp or rt: reasons.append("PROP:" + (hp or rt)[0])
        hpa = sorted(i for i in idents if set(ident_segments(i)) & PARSE_WORDS)
        hpr = sorted(i for i in idents if set(ident_segments(i)) & PRINT_WORDS)
        if hpa and hpr: reasons.append("RT:%s+%s" % (hpa[0], hpr[0]))
        if p["kw"] == "assume val": reasons.append("ASSUMED")
        nrefs = len(refs_local) + len(refs_ext)
        if nrefs == 0 and not p["smtpat"]: reasons.append("TOP")
        if p["smtpat"]: reasons.append("PAT")
        if not refs_ext and len(refs_local) > 1: reasons.append("MULTI")
        relevance = "RELEVANT" if reasons else "HELPER"
        if not reasons: reasons = ["LOCAL1"]
        stmt = p["statement"]
        rows.append({
            "module": mod, "name": name, "kind": p["kw"],
            "location": "%s:%d" % (rel(d["path"]), d["line"]),
            "relevance": relevance, "reasons": ",".join(reasons),
            "refs_local": " ".join(sorted(refs_local)),
            "refs_external": " ".join(sorted(refs_ext)),
            "statement_sha256": hashlib.sha256(stmt.encode("utf-8")).hexdigest(),
            "statement": stmt, "family": family_of(mod),
        })
    stats["lemmas_unique"] = len(rows)
    stats["lemma_files"] = len({r["location"].rsplit(":", 1)[0] for r in rows})
    stats["relevant"] = sum(1 for r in rows if r["relevance"] == "RELEVANT")
    stats["helper"] = len(rows) - stats["relevant"]
    for r in rows:
        for c in r["reasons"].split(","):
            stats["reason_" + c.split(":")[0]] += 1
    return rows, stats


COLUMNS = ["module", "name", "kind", "location", "family", "relevance",
           "reasons", "refs_local", "refs_external", "statement_sha256",
           "statement"]


def write_tsv(rows, fh):
    fh.write("\t".join(COLUMNS) + "\n")
    for r in rows:
        fh.write("\t".join(r[c].replace("\t", " ") for c in COLUMNS) + "\n")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--root", default=None,
                    help="F* tree to walk (default formal/fstar of this repository)")
    ap.add_argument("--out", default=None, help="write the TSV here instead of stdout")
    ap.add_argument("--stats", action="store_true", help="print counts to stderr")
    a = ap.parse_args(argv)
    root = a.root or DEFAULT_ROOT
    rows, stats = build(root, check_tables=a.root is None)
    if a.out:
        with open(a.out, "w", encoding="utf-8") as fh: write_tsv(rows, fh)
    else:
        write_tsv(rows, sys.stdout)
    if a.stats:
        for k in sorted(stats): sys.stderr.write("%s\t%d\n" % (k, stats[k]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
