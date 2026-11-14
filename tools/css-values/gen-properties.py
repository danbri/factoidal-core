#!/usr/bin/env python3
"""Generate the CSS property table data for the built-in engine.

Inputs (paths relative to the repository root):
  third_party/mdn-data/css/properties.json   upstream mdn-data, unmodified (CC0-1.0)
  third_party/mdn-data/css/syntaxes.json     upstream mdn-data, unmodified (CC0-1.0)
  third_party/mdn-data/README.md             carries the "Version: x.y.z" line
  tools/css-values/supplement.json           hand-written additions and corrections

Output:
  formal/lean4/L4Factoidal/Rendering/CssValues/Data.lean

supplement.json takes precedence over mdn-data. Its keys:
  "properties": {name: {"syntax", "inherited", "initial", "longhands"}}
      Each field given replaces the mdn-data field; a name mdn-data lacks needs at least "syntax".
      "longhands" is the list of longhands of a shorthand, in canonical order ([] for a longhand).
      A vendor-prefixed mdn-data property is kept only when it is named here (an empty object
      is enough) or in "aliases".
  "aliases": {alias name: target name}
      The alias gets a row of its own with the target's grammar, inherited flag, initial value and
      longhands (legacy -webkit- names and the like).
  "syntaxes": {non-terminal name without angle brackets: grammar}
  "remove": [property names to drop]

Grammars are written in the CSS Value Definition Syntax exactly as the CSS specifications write it.

The non-terminals in NATIVE are implemented by the engine itself, so they are never emitted and a
reference to one is never reported. Every other non-terminal reachable from a kept property grammar
must be defined; undefined references make the run fail, and definitions nothing reaches are left
out of the output. Both are reported on stderr.

Usage:
  gen-properties.py           write Data.lean
  gen-properties.py --check   exit 1 when Data.lean differs from what would be generated
  gen-properties.py --quiet   do not list unused definitions
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
MDN = os.path.join(ROOT, "third_party", "mdn-data")
SUPPLEMENT = os.path.join(HERE, "supplement.json")
OUT = os.path.join(ROOT, "formal", "lean4", "L4Factoidal", "Rendering", "CssValues", "Data.lean")

# Non-terminals the engine implements natively. Never emitted, never reported as undefined.
NATIVE = set("""
number integer length percentage length-percentage angle angle-percentage time time-percentage
frequency frequency-percentage resolution flex dimension string url ident custom-ident dashed-ident
hex-color color zero declaration-value any-value
calc() min() max() clamp() round() mod() rem() sin() cos() tan() asin() acos() atan() atan2()
pow() sqrt() hypot() log() exp() abs() sign() calc-size() progress() random()
sibling-count() sibling-index()
calc-sum calc-product calc-value calc-keyword calc-constant calc-size-basis rounding-strategy
random-value-sharing
rgb() rgba() hsl() hsla() hwb() lab() lch() oklab() oklch() color() color-mix() light-dark()
contrast-color() device-cmyk() alpha() color-interpolate()
named-color system-color deprecated-system-color absolute-color-function absolute-color-base
color-base color-function color-interpolation-method colorspace-params predefined-rgb-params
predefined-rgb predefined-polar-params predefined-polar predefined-rectangular-params
predefined-rectangular xyz-params xyz xyz-space custom-params color-space rectangular-color-space
polar-color-space custom-color-space hue-interpolation-method hue alpha-value modern-rgb-syntax
modern-rgba-syntax legacy-rgb-syntax legacy-rgba-syntax modern-hsl-syntax modern-hsla-syntax
legacy-hsl-syntax legacy-hsla-syntax modern-device-cmyk-syntax legacy-device-cmyk-syntax
cmyk-component color-stripe
""".split())

PROP_REF = re.compile(r"<'([^']+)'>")
TYPE_REF = re.compile(r"<([A-Za-z-][A-Za-z0-9-]*(?:\(\))?)(?:\s*\[[^\]]*\])?>")
PROSE_KEY = re.compile(r"^[a-z]+(?:[A-Z][A-Za-z]*)+$")


def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def mdn_version():
    with open(os.path.join(MDN, "README.md"), encoding="utf-8") as f:
        m = re.search(r"Version:\s*`?([0-9][0-9A-Za-z.+-]*)`?", f.read())
    if not m:
        sys.exit("gen-properties: no 'Version:' line in third_party/mdn-data/README.md")
    return m.group(1)


def lean_string(s):
    if "\n" in s or "\r" in s or "\t" in s:
        s = " ".join(s.split())
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def byte_order(name):
    return name.encode("utf-8")


def build(quiet=False):
    errors = []
    warnings = []
    mdn_props = load(os.path.join(MDN, "css", "properties.json"))
    mdn_syn = load(os.path.join(MDN, "css", "syntaxes.json"))
    sup = load(SUPPLEMENT)
    sup_props = sup.get("properties", {})
    aliases = sup.get("aliases", {})
    remove = set(sup.get("remove", []))

    # --- properties -------------------------------------------------------------------------
    props = {}
    for name, entry in mdn_props.items():
        if name == "--*" or name in remove:
            continue
        if name.startswith("-") and name not in sup_props:
            continue
        initial = entry.get("initial", "")
        shorthand = isinstance(initial, list) or isinstance(entry.get("computed"), list)
        props[name] = {
            "syntax": entry["syntax"],
            "inherited": bool(entry.get("inherited", False)),
            "initial": "" if isinstance(initial, list) else initial,
            "longhands": None if shorthand else [],
        }
    for name in remove:
        if name not in mdn_props:
            warnings.append("remove: %s is not in mdn-data" % name)
    for name, over in sup_props.items():
        if name in remove:
            errors.append("%s is both removed and defined in the supplement" % name)
            continue
        row = props.get(name)
        if row is None:
            if "syntax" not in over:
                errors.append("supplement property %s is not in mdn-data and has no syntax" % name)
                continue
            row = {"syntax": "", "inherited": False, "initial": "", "longhands": []}
            props[name] = row
        for key in over:
            if key not in ("syntax", "inherited", "initial", "longhands"):
                errors.append("supplement property %s: unknown key %s" % (name, key))
        row.update({k: v for k, v in over.items() if k in row})
    for alias, target in aliases.items():
        if target not in props:
            errors.append("alias %s: target %s is not in the table" % (alias, target))
            continue
        if alias in sup_props:
            errors.append("%s is both an alias and a supplement property" % alias)
        props[alias] = dict(props[target])

    for name, row in sorted(props.items()):
        if row["longhands"] is None:
            errors.append("shorthand %s: mdn-data marks it as a shorthand; give its longhands "
                          "(or []) in the supplement" % name)
            row["longhands"] = []
        if PROSE_KEY.match(row["initial"]):
            errors.append("%s: initial value %r is an mdn-data prose key; give a concrete value "
                          "in the supplement" % (name, row["initial"]))
        if row["longhands"] and name in row["longhands"]:
            errors.append("%s lists itself as a longhand" % name)
        for longhand in row["longhands"]:
            if longhand not in props:
                errors.append("%s: longhand %s is not in the table" % (name, longhand))
        if "'/'" in row["syntax"] or "','" in row["syntax"]:
            errors.append("%s: grammar quotes a literal; write / and , bare" % name)

    # --- non-terminals ----------------------------------------------------------------------
    syntaxes = {name: entry["syntax"] for name, entry in mdn_syn.items()}
    syntaxes.update(sup.get("syntaxes", {}))
    for name in list(syntaxes):
        if name in NATIVE:
            del syntaxes[name]

    undefined = {}
    reached = set()
    todo = []

    def scan(owner, grammar):
        for ref in PROP_REF.findall(grammar):
            if ref not in props:
                undefined.setdefault("<'%s'>" % ref, set()).add(owner)
        for ref in TYPE_REF.findall(grammar):
            if ref in NATIVE or ref in reached:
                continue
            if ref not in syntaxes:
                undefined.setdefault("<%s>" % ref, set()).add(owner)
                continue
            reached.add(ref)
            todo.append(ref)

    for name, row in props.items():
        scan(name, row["syntax"])
    while todo:
        ref = todo.pop()
        scan("<%s>" % ref, syntaxes[ref])

    for ref in sorted(undefined):
        errors.append("undefined reference %s (used by %s)" % (ref, ", ".join(sorted(undefined[ref])[:6])))
    unused = sorted(set(syntaxes) - reached, key=byte_order)
    if unused and not quiet:
        warnings.append("unused definitions left out (%d): %s" % (len(unused), " ".join(unused)))

    # --- output -----------------------------------------------------------------------------
    version = mdn_version()
    lines = [
        "/-",
        "GENERATED by tools/css-values/gen-properties.py from third_party/mdn-data/css/{properties,syntaxes}.json",
        "(mdn-data %s, CC0-1.0) and tools/css-values/supplement.json. Do not edit by hand." % version,
        "-/",
        "namespace L4Factoidal.Rendering.CssValues.Data",
        "",
        "/-- A CSS property: name, grammar (CSS value definition syntax), inherited, initial value, and for a",
        'shorthand its longhands in canonical order, space separated ("" for a longhand). -/',
        "def properties : Array (String × String × Bool × String × String) := #[",
    ]
    names = sorted(props, key=byte_order)
    for i, name in enumerate(names):
        row = props[name]
        lines.append("  (%s, %s, %s, %s, %s)%s" % (
            lean_string(name), lean_string(row["syntax"]), "true" if row["inherited"] else "false",
            lean_string(row["initial"]), lean_string(" ".join(row["longhands"])),
            "," if i + 1 < len(names) else ""))
    lines += [
        "]",
        "",
        '/-- The non-terminals of the grammars: name (no angle brackets; a function keeps its "()"), grammar. -/',
        "def syntaxes : Array (String × String) := #[",
    ]
    kept = sorted(reached, key=byte_order)
    for i, name in enumerate(kept):
        lines.append("  (%s, %s)%s" % (lean_string(name), lean_string(syntaxes[name]),
                                       "," if i + 1 < len(kept) else ""))
    lines += [
        "]",
        "",
        "/-- Legacy names: alias, the property it stands for. A declaration of an alias is a declaration of",
        "its target (CSS Cascade 4 §3.1 legacy name aliases). -/",
        "def aliases : Array (String × String) := #[",
    ]
    alias_names = sorted(aliases, key=byte_order)
    for i, name in enumerate(alias_names):
        lines.append("  (%s, %s)%s" % (lean_string(name), lean_string(aliases[name]),
                                       "," if i + 1 < len(alias_names) else ""))
    lines += ["]", "", "end L4Factoidal.Rendering.CssValues.Data", ""]
    return "\n".join(lines), errors, warnings, len(names), len(kept)


def main(argv):
    check = "--check" in argv
    quiet = "--quiet" in argv
    text, errors, warnings, nprops, nsyn = build(quiet)
    for w in warnings:
        print("gen-properties: warning: " + w, file=sys.stderr)
    for e in errors:
        print("gen-properties: error: " + e, file=sys.stderr)
    if errors:
        print("gen-properties: %d error(s); nothing written" % len(errors), file=sys.stderr)
        return 2
    if check:
        try:
            with open(OUT, encoding="utf-8") as f:
                on_disk = f.read()
        except FileNotFoundError:
            on_disk = None
        if on_disk != text:
            print("gen-properties: %s is out of date; run tools/css-values/gen-properties.py"
                  % os.path.relpath(OUT, ROOT), file=sys.stderr)
            return 1
        return 0
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as f:
        f.write(text)
    print("gen-properties: wrote %s (%d properties, %d non-terminals)"
          % (os.path.relpath(OUT, ROOT), nprops, nsyn), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
