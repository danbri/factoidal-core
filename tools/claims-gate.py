#!/usr/bin/env python3
"""The CLAIMS gate (https://github.com/danbri/factoidal-core/issues/1178, P1, and
https://github.com/danbri/factoidal-core/issues/1179, P2).

`foundation/claims.toml` lists the public claims of Factoidal: at most a few
dozen theorems that a release note, hub page or README may call "proved". The
owner reviews that file; nobody is asked to review the proofs. Reason and
source: docs/designissues/2026-11-27-formal-verification-post-review.md.

Static checks (no Lean build; inputs derived from the tree on every run,
anti-pattern 30). Exit 1 when any of these fails:

  * an entry lacks a required field, has an unknown status, or repeats an id;
  * the number of entries is more than `max-entries`;
  * the named file does not exist, or holds no `theorem` whose fully
    qualified name (namespaces resolved) is the `theorem` field;
  * the theorem is `private` (its name is not stable);
  * the module is reached by no build root of lakefile.lean, so no build
    checks it (anti-pattern 35, tools/lean-unbuilt-modules.py);
  * P2, statement freeze: the SHA-256 of the theorem's statement (the text from
    the name to the top-level `:=`, comments removed, white space collapsed) is
    not `statement_sha256`; or the SHA-256 of a definition listed in
    `spec_defs` (its whole source text, comments removed) is not the recorded
    one. A change of a statement or of a specification definition therefore
    needs an edit of the register entry in the same commit, where a reviewer
    sees it. Proofs are free to change.
  * a name in `stages` is not a stage (or area) of docs/dataflow-inventory.md.
    `stages` says which dataflow stages the claim is about; it is how a release
    counts the entry points a claim covers (tools/assurance-manifest.py). It is
    an explicit decision, never a name match (anti-pattern 31).
  * P3, hypothesis witness: an entry with `witness` names a theorem that does
    not exist in the named file, or whose proof does not apply the claim's
    theorem. A witness instantiates the claim at concrete arguments and proves
    every hypothesis there, so Lean (in CI) checks that the hypotheses can
    hold at the same time. A claim whose hypotheses are contradictory has no
    witness. An entry with assumptions has a `witness` or a `witness_none`
    reason; the number of `witness_none` entries is `max-unwitnessed` exactly
    (a ratchet that only goes down).

Modes:
  python3 -I tools/claims-gate.py               check, exit 0 or 1
  python3 -I tools/claims-gate.py --show ID     print the statement and hashes
  python3 -I tools/claims-gate.py --rehash      print the hashes to record
  python3 -I tools/claims-gate.py --record ID|--all
      write the current hashes into the register (after review)
  python3 -I tools/claims-gate.py --modules     print the claim modules (to build)
  python3 -I tools/claims-gate.py --axioms-lean FILE
      write a Lean file with `#print axioms` for each claim, for CI to run with
      `lake env lean FILE` after `lake build L4Factoidal`
  python3 -I tools/claims-gate.py --check-axioms LOG
      read the output of that run; exit 1 if any claim depends on an axiom
      other than propext, Classical.choice and Quot.sound (for example
      sorryAx or Lean.ofReduceBool from native_decide), or is missing
"""
import hashlib
import os
import re
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "formal", "lean4")
REGISTER = os.path.join(ROOT, "foundation", "claims.toml")
STATUSES = {"proposed", "reviewed"}
REQUIRED = ["id", "theorem", "file", "about", "says", "does_not_say",
            "assumptions", "status", "statement_sha256"]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

DECL = re.compile(
    r"^(?P<mods>(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*)"
    r"(?P<kw>theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque|axiom)\b\s*(?P<name>[^\s:({\[⦃]*)",
    re.M)


def strip_comments(src):
    """Remove `--` line comments and nested `/- ... -/` block comments. String
    literals are kept as they are (a `--` inside a string is rare in
    statements; the hash is over the result either way, so it is stable)."""
    out, i, depth, n = [], 0, 0, len(src)
    in_str = False
    while i < n:
        c = src[i]
        if depth == 0 and not in_str and c == '"':
            in_str = True
            out.append(c); i += 1; continue
        if in_str:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(src[i + 1]); i += 2; continue
            if c == '"':
                in_str = False
            i += 1; continue
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if c == "\n":
                out.append("\n")
            i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(c); i += 1
    return "".join(out)


def namespaces_at(lines):
    """Namespace stack before each line: `namespace X`, `section [X]`,
    `mutual`, `end [X]`."""
    stack, result = [], []
    for line in lines:
        result.append(list(stack))
        m = re.match(r"^\s*(namespace|section|mutual|end)\b\s*([\w.]*)", line)
        if not m:
            continue
        kw, name = m.group(1), m.group(2)
        if kw == "namespace":
            stack.append(("ns", name))
        elif kw in ("section", "mutual"):
            stack.append(("sec", name if kw == "section" else ""))
        elif stack:
            stack.pop()
    return result


def full_name(ns_stack, short):
    if short.startswith("_root_."):
        return short[len("_root_."):]
    parts = [n for kind, n in ns_stack if kind == "ns" and n]
    return ".".join(parts + [short]) if parts else short


def declarations(path):
    """Map full name -> (keyword, modifiers, text of the declaration) for every
    declaration in the file. The text runs to the next column-0 declaration or
    namespace/section/end line."""
    src = strip_comments(open(path, encoding="utf-8").read())
    lines = src.split("\n")
    stacks = namespaces_at(lines)
    starts = []
    for idx, line in enumerate(lines):
        m = DECL.match(line)
        if m:
            starts.append((idx, m))
    boundary = re.compile(r"^(?:@\[|private |protected |noncomputable |partial |unsafe |theorem |lemma |def |abbrev |instance |structure |inductive |class |example |opaque |axiom |mutual\b|macro|syntax |notation|infix|prefix|postfix|elab |deriving |namespace |section |end\b|open |variable |universe |set_option |attribute |#)")
    out = {}
    for k, (idx, m) in enumerate(starts):
        j = idx + 1
        while j < len(lines) and not boundary.match(lines[j]):
            j += 1
        text = "\n".join(lines[idx:j])
        name = m.group("name") or f"<example@{idx + 1}>"
        out.setdefault(full_name(stacks[idx], name), []).append((m.group("kw"), m.group("mods"), text, idx + 1))
    return out


def statement_of(text):
    """The text from the theorem keyword to the first `:=` (or ` | ` match
    arm, or `where`) at bracket depth 0, white space collapsed."""
    depth = 0
    pending = 0  # `let x ... :=` and `have h ... :=` inside the statement
    i = 0
    while i < len(text):
        c = text[i]
        if c in "([{⦃⟨":
            depth += 1
        elif c in ")]}⦄⟩":
            depth -= 1
        elif depth == 0 and re.match(r"(?<![\w.])(let|have)\s", text[i:i + 5]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_.'")):
            pending += 1
        elif depth == 0 and text.startswith(":=", i):
            if pending:
                pending -= 1
                i += 2
                continue
            return " ".join(text[:i].split())
        elif depth == 0 and text[i] == "\n" and re.match(r"\s*\|", text[i + 1:]):
            return " ".join(text[:i].split())
        i += 1
    return " ".join(text.split())


def sha(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def module_of(file_rel):
    p = os.path.relpath(os.path.join(ROOT, file_rel), LEAN)
    return p[:-len(".lean")].replace(os.sep, ".")


def lake_roots():
    """The build roots of lakefile.lean, read as tools/lean-unbuilt-modules.py
    reads them (library roots, globs, lean_exe roots)."""
    text = open(os.path.join(LEAN, "lakefile.lean"), encoding="utf-8").read()
    roots = {"L4Factoidal"}
    roots.update(re.findall(r"root\s*:=\s*`([\w.]+)", text))
    for block in re.findall(r"(?:roots|globs)\s*:=\s*#\[(.*?)\]", text, re.S):
        roots.update(re.findall(r"`([\w.]+)", block))
    return roots


def closure():
    seen, todo = set(), sorted(lake_roots())
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = os.path.join(LEAN, *mod.split(".")) + ".lean"
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as f:
            for line in f:
                if line.startswith("import "):
                    todo.extend(line[len("import "):].split())
    if len(seen) < 10:
        sys.exit("claims-gate: import walk reached fewer than 10 modules; refusing an empty walk")
    return seen


def inventory_stages():
    """The `stage` and `area` cells of docs/dataflow-inventory.md."""
    names = set()
    path = os.path.join(ROOT, "docs", "dataflow-inventory.md")
    if not os.path.exists(path):
        return names
    for line in open(path, encoding="utf-8"):
        if line.startswith("| ") and not line.startswith(("| area", "|---")):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cells) > 2:
                names.add(cells[2].strip("`"))
                names.add(cells[0])
    return names


def load():
    with open(REGISTER, "rb") as f:
        data = tomllib.load(f)
    return data.get("meta", {}), data.get("claim", [])


def find(claim, cache):
    path = os.path.join(ROOT, claim["file"])
    if not os.path.exists(path):
        return None, f"file {claim['file']} does not exist"
    if path not in cache:
        cache[path] = declarations(path)
    decls = cache[path]
    hits = [d for d in decls.get(claim["theorem"], []) if d[0] in ("theorem", "lemma")]
    if not hits:
        return None, f"no theorem {claim['theorem']} in {claim['file']}"
    if len(hits) > 1:
        return None, f"{len(hits)} theorems named {claim['theorem']} in {claim['file']}"
    return hits[0], None


def spec_hash(name, file_rel, cache):
    path = os.path.join(ROOT, file_rel)
    if not os.path.exists(path):
        return None, f"spec file {file_rel} does not exist"
    if path not in cache:
        cache[path] = declarations(path)
    hits = cache[path].get(name, [])
    if len(hits) != 1:
        return None, f"spec definition {name}: {len(hits)} declarations in {file_rel}"
    return sha(" ".join(hits[0][2].split())), None


def hashes(claim, cache):
    hit, err = find(claim, cache)
    if err:
        return None, None, [err]
    errs, specs = [], {}
    for spec in claim.get("spec_defs", []):
        name, _, file_rel = spec["name"], None, spec.get("file", claim["file"])
        h, e = spec_hash(name, file_rel, cache)
        if e:
            errs.append(e)
        specs[name] = h
    return sha(statement_of(hit[2])), specs, errs


def check():
    meta, claims = load()
    errors = []
    maxn = meta.get("max-entries")
    if not isinstance(maxn, int):
        errors.append("[meta] max-entries is missing")
    elif len(claims) > maxn:
        errors.append(f"{len(claims)} entries, more than max-entries {maxn}")
    if not claims:
        errors.append("the register has no entries")
    reach = closure()
    stages = inventory_stages()
    cache, ids = {}, set()
    for c in claims:
        cid = c.get("id", "<no id>")
        for field in REQUIRED:
            if field not in c or c[field] in ("", []):
                if field == "assumptions" and c.get(field) == []:
                    continue
                errors.append(f"{cid}: field {field} is missing or empty")
        if cid in ids:
            errors.append(f"{cid}: id repeated")
        ids.add(cid)
        if c.get("status") not in STATUSES:
            errors.append(f"{cid}: status {c.get('status')!r} is not one of {sorted(STATUSES)}")
        if c.get("status") == "reviewed" and not c.get("reviewed"):
            errors.append(f"{cid}: status reviewed needs a `reviewed` field (who, date, words)")
        for st in c.get("stages", []):
            if st not in stages:
                errors.append(f"{cid}: stage {st!r} is not a stage of docs/dataflow-inventory.md")
        if "theorem" not in c or "file" not in c:
            continue
        hit, err = find(c, cache)
        if err:
            errors.append(f"{cid}: {err}")
            continue
        if "private" in hit[1]:
            errors.append(f"{cid}: {c['theorem']} is private")
        mod = module_of(c["file"])
        if mod not in reach:
            errors.append(f"{cid}: module {mod} is reached by no build root of lakefile.lean, so no build checks it")
        st, specs, errs = hashes(c, cache)
        errors.extend(f"{cid}: {e}" for e in errs)
        if st and st != c.get("statement_sha256"):
            errors.append(f"{cid}: statement of {c['theorem']} changed (sha256 {st}); review it and update statement_sha256 in the same commit")
        for spec in c.get("spec_defs", []):
            got = specs.get(spec["name"])
            if got and got != spec.get("sha256"):
                errors.append(f"{cid}: specification definition {spec['name']} changed (sha256 {got}); review it and update its sha256 in the same commit")
        w = c.get("witness")
        if c.get("assumptions") and not w and not c.get("witness_none"):
            errors.append(f"{cid}: has assumptions but no `witness` and no `witness_none` reason (P3)")
        if w and c.get("witness_none"):
            errors.append(f"{cid}: has both `witness` and `witness_none`")
        if w:
            path = os.path.join(ROOT, w.get("file", c["file"]))
            if not os.path.exists(path):
                errors.append(f"{cid}: witness file {w.get('file')} does not exist")
            else:
                if path not in cache:
                    cache[path] = declarations(path)
                wh = [d for d in cache[path].get(w["name"], []) if d[0] in ("theorem", "def")]
                short = c["theorem"].rsplit(".", 1)[-1]
                if not wh:
                    errors.append(f"{cid}: witness theorem {w['name']} not found in {w.get('file', c['file'])}")
                elif not re.search(r"(?<![\w.'])(?:[\w.]*\.)?" + re.escape(short) + r"(?![\w'])", wh[0][2].split(":=", 1)[-1]):
                    errors.append(f"{cid}: witness {w['name']} does not apply {c['theorem']} (its body must instantiate the claim, so Lean checks that the hypotheses hold together)")
                elif module_of(os.path.relpath(path, ROOT)) not in reach:
                    errors.append(f"{cid}: witness module is reached by no build root")
    unwitnessed = sum(1 for c in claims if c.get("witness_none"))
    maxu = meta.get("max-unwitnessed")
    if unwitnessed and maxu is None:
        errors.append("[meta] max-unwitnessed is missing")
    elif maxu is not None and unwitnessed > maxu:
        errors.append(f"{unwitnessed} entries without a witness, more than max-unwitnessed {maxu}")
    elif maxu is not None and unwitnessed < maxu:
        errors.append(f"{unwitnessed} entries without a witness, fewer than max-unwitnessed {maxu} (lower it: it only goes down)")
    for e in errors:
        print("claims-gate: FAIL " + e)
    reviewed = sum(1 for c in claims if c.get("status") == "reviewed")
    witnessed = sum(1 for c in claims if c.get("witness"))
    print(f"claims-gate: {len(claims)} claims ({reviewed} reviewed, {len(claims) - reviewed} proposed), "
          f"{witnessed} with a hypothesis witness, {unwitnessed} with assumptions and no witness, {len(errors)} errors")
    return 1 if errors else 0


def show(cid):
    _, claims = load()
    cache = {}
    for c in claims:
        if c["id"] == cid or cid == "--all":
            hit, err = find(c, cache)
            if err:
                print(c["id"], err); continue
            print(f"== {c['id']}  ({c['theorem']}, {c['file']}:{hit[3]})")
            print(statement_of(hit[2]))
            st, specs, errs = hashes(c, cache)
            print("statement_sha256 =", st)
            for k, v in specs.items():
                print(f"spec {k} sha256 = {v}")
            for e in errs:
                print("error:", e)


def axioms_lean(out):
    _, claims = load()
    mods = sorted({module_of(c["file"]) for c in claims})
    with open(out, "w", encoding="utf-8") as f:
        f.write("-- Generated by tools/claims-gate.py --axioms-lean. Do not edit.\n")
        for m in mods:
            f.write(f"import {m}\n")
        for c in claims:
            f.write(f"\n#eval IO.println \"claim {c['id']}\"\n#print axioms {c['theorem']}\n")
    return 0


def check_axioms(log):
    _, claims = load()
    text = open(log, encoding="utf-8").read()
    blocks = re.split(r"^claim (\S+)\s*$", text, flags=re.M)
    seen = {}
    for k in range(1, len(blocks), 2):
        seen[blocks[k]] = blocks[k + 1]
    errors = []
    for c in claims:
        body = seen.get(c["id"])
        if body is None:
            errors.append(f"{c['id']}: no #print axioms output")
            continue
        if "does not depend on any axioms" in body:
            continue
        m = re.search(r"depends on axioms:\s*\[(.*?)\]", body, re.S)
        if not m:
            errors.append(f"{c['id']}: cannot read the axioms output: {body.strip()[:200]}")
            continue
        used = {a.strip() for a in m.group(1).split(",") if a.strip()}
        extra = used - STANDARD_AXIOMS
        if extra:
            errors.append(f"{c['id']}: {c['theorem']} depends on {sorted(extra)}")
    for e in errors:
        print("claims-gate axioms: FAIL " + e)
    print(f"claims-gate axioms: {len(claims)} claims, {len(errors)} errors")
    return 1 if errors else 0


def record(target):
    """Write the current hashes into foundation/claims.toml for one entry, or
    for all with --all. Use it after reviewing a statement change; the diff of
    the register then shows the change to a reviewer."""
    _, claims = load()
    text = open(REGISTER, encoding="utf-8").read()
    parts = text.split("[[claim]]")
    cache, done = {}, 0
    for k in range(1, len(parts)):
        m = re.search(r'^id = "([^"]+)"', parts[k], re.M)
        c = next((c for c in claims if m and c["id"] == m.group(1)), None)
        if not c or (target != "--all" and c["id"] != target):
            continue
        st, specs, errs = hashes(c, cache)
        if errs or not st:
            print(f"{c['id']}: not recorded: {errs}")
            continue
        block = re.sub(r'^statement_sha256 = "[^"]*"', f'statement_sha256 = "{st}"', parts[k], flags=re.M)
        for name, h in specs.items():
            block = re.sub(r'(\{ name = "' + re.escape(name) + r'",[^}]*sha256 = ")[^"]*(")', lambda mm: mm.group(1) + h + mm.group(2), block)
        parts[k] = block
        done += 1
    open(REGISTER, "w", encoding="utf-8").write("[[claim]]".join(parts))
    print(f"recorded hashes for {done} entries")
    return 0


def main(argv):
    if not argv:
        return check()
    if argv[0] == "--record":
        return record(argv[1] if len(argv) > 1 else "--all")
    if argv[0] == "--show":
        show(argv[1] if len(argv) > 1 else "--all"); return 0
    if argv[0] == "--rehash":
        show("--all"); return 0
    if argv[0] == "--modules":
        _, claims = load()
        print(" ".join(sorted({module_of(c["file"]) for c in claims})))
        return 0
    if argv[0] == "--axioms-lean":
        return axioms_lean(argv[1])
    if argv[0] == "--check-axioms":
        return check_axioms(argv[1])
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
