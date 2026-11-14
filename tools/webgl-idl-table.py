#!/usr/bin/env python3
"""Write formal/lean4/L4Factoidal/PageGl/Table.lean from the WebGL IDL.

    python3 tools/webgl-idl-table.py WPT/interfaces/webgl1.idl WPT/interfaces/webgl2.idl \
        > formal/lean4/L4Factoidal/PageGl/Table.lean

The inputs are the Khronos IDL of WebGL 1.0 and 2.0 as the Web Platform Tests carry them
(`interfaces/webgl1.idl`, `interfaces/webgl2.idl`). The table holds, for each interface mixin of the
two rendering contexts, its constants (name, value), its attributes (name, read-only) and its
operations (name, the smallest number of arguments an overload takes, and the argument types of
each overload as letters, see `SCALARS`). Values are integers
(`TIMEOUT_IGNORED` is -1). Nothing else of the IDL is
kept: argument conversion is the page glue's, validation is `PageGl.State`'s.
"""
import re
import sys


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def split_args(s):
    """Top-level commas of an argument list (generic types hold commas)."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "<(":
            depth += 1
        elif ch in ">)":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [a.strip() for a in out]


def required(args):
    n = 0
    for a in args:
        a = re.sub(r"\[[^\]]*\]\s*", "", a)
        if a.startswith("optional ") or "..." in a:
            break
        n += 1
    return n


# One letter for each IDL type the page glue converts (Web IDL §3.2); a `?` after it: nullable.
SCALARS = {
    "GLenum": "u", "GLbitfield": "u", "GLuint": "u", "unsigned long": "u",
    "GLint": "i", "GLsizei": "i", "GLintptr": "l", "GLsizeiptr": "l", "GLint64": "l", "GLuint64": "l",
    "GLfloat": "f", "GLclampf": "f", "GLboolean": "b", "DOMString": "s", "unsigned long long": "l",
    "Float32List": "F", "Int32List": "I", "Uint32List": "U", "TexImageSource": "T", "object": "a",
    "AllowSharedBufferSource": "B", "ArrayBufferView": "V", "sequence<GLenum>": "Q", "sequence<GLuint>": "Q",
    "sequence<DOMString>": "S", "WebGLContextAttributes": "a",
}


def type_code(arg):
    """`T name` or `optional T name = d`: the letter of T (an interface: `O` and its name)."""
    a = re.sub(r"\[[^\]]*\]\s*", "", arg)
    opt = a.startswith("optional ")
    if opt:
        a = a[len("optional "):]
    a = a.split("=")[0].strip()
    ty = a.rsplit(" ", 1)[0].strip()
    nullable = ty.endswith("?")
    if nullable:
        ty = ty[:-1]
    if ty in SCALARS:
        code = SCALARS[ty]
    elif re.fullmatch(r"WebGL\w+", ty):
        code = "O" + ty
    else:
        raise SystemExit(f"type not read: {ty!r} in {arg!r}")
    return ("~" if opt else "") + code + ("?" if nullable else "")


def mixins(text):
    text = strip_comments(text)
    out = {}
    for m in re.finditer(r"interface\s+mixin\s+(\w+)\s*\{(.*?)\};", text, flags=re.S):
        name, body = m.group(1), m.group(2)
        consts, attrs, ops = [], [], {}
        order = []
        for member in body.split(";"):
            member = " ".join(member.split())
            member = re.sub(r"^(\[[^\]]*\]\s*)+", "", member)
            if not member:
                continue
            c = re.match(r"const \w+ (\w+) = (-?0x[0-9A-Fa-f]+|-?\d+)$", member)
            if c:
                consts.append((c.group(1), int(c.group(2), 0)))
                continue
            a = re.match(r"(readonly )?attribute .*?(\w+)$", member)
            if a:
                attrs.append((a.group(2), bool(a.group(1))))
                continue
            o = re.match(r".*?(\w+)\s*\((.*)\)$", member)
            if not o:
                raise SystemExit(f"{name}: member not read: {member}")
            args = split_args(o.group(2))
            n = required(args)
            sig = ",".join(type_code(a) for a in args)
            if o.group(1) not in ops:
                order.append(o.group(1))
                ops[o.group(1)] = (n, [sig])
            else:
                ops[o.group(1)] = (min(ops[o.group(1)][0], n), ops[o.group(1)][1] + [sig])
        out[name] = (consts, attrs, [(k, ops[k][0], "|".join(ops[k][1])) for k in order])
    return out


def lean_list(items, fmt, width=100):
    lines, cur = [], "  ["
    for i, it in enumerate(items):
        piece = fmt(it) + ("," if i + 1 < len(items) else "]")
        if len(cur) + len(piece) + 1 > width:
            lines.append(cur.rstrip())
            cur = "   "
        cur += piece + " "
    if not items:
        cur += "]"
    lines.append(cur.rstrip())
    return "\n".join(lines)


def main():
    all_mixins = {}
    for path in sys.argv[1:]:
        all_mixins.update(mixins(open(path, encoding="utf-8").read()))
    want = ["WebGLRenderingContextBase", "WebGLRenderingContextOverloads",
            "WebGL2RenderingContextBase", "WebGL2RenderingContextOverloads"]
    short = {"WebGLRenderingContextBase": "base", "WebGLRenderingContextOverloads": "overloads1",
             "WebGL2RenderingContextBase": "base2", "WebGL2RenderingContextOverloads": "overloads2"}
    print("/-")
    print("L4Factoidal.PageGl.Table: the constants, attributes and operations of the WebGL rendering")
    print("contexts, by interface mixin. Written by `tools/webgl-idl-table.py` from the Khronos IDL of")
    print("WebGL 1.0 and 2.0 (the Web Platform Tests' `interfaces/webgl1.idl` and `webgl2.idl`); change")
    print("the IDL and run the tool, do not edit the lists. `PageGl.Idl` reads them.")
    print("-/")
    print("namespace L4Factoidal.PageGl.Table\n")
    for name in want:
        consts, attrs, ops = all_mixins[name]
        s = short[name]
        print(f"/-- Constants of `{name}`: name and value. -/")
        print(f"def {s}Consts : List (String × Int) :=")
        print(lean_list(consts, lambda c: f'("{c[0]}", {c[1] if c[1] < 0 else hex(c[1]).upper().replace("0X", "0x")})'))
        print()
        print(f"/-- Attributes of `{name}`: name, and whether it is read-only. -/")
        print(f"def {s}Attrs : List (String × Bool) :=")
        print(lean_list(attrs, lambda a: f'("{a[0]}", {"true" if a[1] else "false"})'))
        print()
        print(f"/-- Operations of `{name}`: name, the fewest arguments an overload takes, and the argument")
        print("types of each overload (`|` between overloads, `,` between arguments, `~` before an optional")
        print("argument, `?` after a nullable type; the letters are in `tools/webgl-idl-table.py`). -/")
        print(f"def {s}Ops : List (String × Nat × String) :=")
        print(lean_list(ops, lambda o: f'("{o[0]}", {o[1]}, "{o[2]}")'))
        print()
    print("end L4Factoidal.PageGl.Table")


if __name__ == "__main__":
    main()
