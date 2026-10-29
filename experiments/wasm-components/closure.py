#!/usr/bin/env python3
"""Print the .lake/build/ir C files of the import closure of a Lean file,
one per line, restricted to modules of the formal/lean4 package.

Usage: closure.py <formal/lean4 dir> <root .lean file>
Fails if a package module of the closure has no generated C (not built)."""
import re, sys, pathlib
lean_dir = pathlib.Path(sys.argv[1]).resolve()
root = pathlib.Path(sys.argv[2]).resolve()
imp = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.«»]+)', re.M)
seen, todo, out = set(), [root], []
while todo:
    f = todo.pop()
    for m in imp.findall(f.read_text(encoding='utf-8')):
        rel = pathlib.Path(*m.split('.'))
        src = lean_dir / rel.with_suffix('.lean')
        if not src.exists() or m in seen:
            continue   # a module of the toolchain (Init, Std, Lean) or seen
        seen.add(m)
        c = lean_dir / '.lake' / 'build' / 'ir' / rel.with_suffix('.c')
        if not c.exists():
            sys.exit(f'closure.py: {m} has no generated C at {c} (lake build it)')
        out.append(str(c))
        todo.append(src)
if not out:
    sys.exit('closure.py: empty closure')
print('\n'.join(sorted(out)))
