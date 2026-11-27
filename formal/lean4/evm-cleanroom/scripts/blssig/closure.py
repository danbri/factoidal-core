#!/usr/bin/env python3
"""Import closure of a module of this package, as the `roots` list another Lake package needs to
take it by source (`srcDir`). Prints one module per line, or with --toml the library stanza.
Fails if a module of the closure imports anything outside EVMCleanroom/Precompiles."""
import os, re, sys

def closure(root, top):
    seen, todo = [], [top]
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.append(module)
        path = os.path.join(root, module.replace(".", "/") + ".lean")
        for line in open(path, encoding="utf-8"):
            m = re.match(r"^\s*(?:public\s+)?import\s+(\S+)", line)
            if m:
                todo.append(m.group(1))
            elif line.strip() and not line.startswith("--") and not re.match(r"^\s*(module|prelude)\b", line):
                break  # imports come first
    return sorted(seen)

def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    root = args[0]; top = args[1] if len(args) > 1 else "EVMCleanroom.Precompiles.BLSSignature"
    modules = closure(root, top)
    outside = [m for m in modules if not m.startswith("EVMCleanroom.Precompiles.")]
    if outside:
        sys.exit("closure leaves EVMCleanroom/Precompiles: " + ", ".join(outside))
    if "--toml" in sys.argv:
        src = [a.split("=", 1)[1] for a in sys.argv if a.startswith("--srcdir=")]
        print("[[lean_lib]]\nname = \"EVMCleanroomBLS\"\nsrcDir = \"%s\"\nroots = [" % (src[0] if src else "../evm-cleanroom"))
        print(",\n".join('  "%s"' % m for m in modules))
        print("]")
    else:
        print("\n".join(modules))

main()
