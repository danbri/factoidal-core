#!/usr/bin/env python3
"""Print local Lean imports in dependency order, without using compiled artifacts."""
import argparse
from pathlib import Path
import re


def local_imports(text):
    # Module imports precede declarations. Ignore nested Lean comments and strings
    # so example source printed by a module never becomes a build dependency.
    clean = []
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                clean.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                quoted = False
                i += 1
            else:
                clean.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            quoted = True
            i += 1
        else:
            clean.append(text[i])
            i += 1
    for line in ''.join(clean).splitlines():
        match = re.fullmatch(r'\s*(?:public\s+)?import\s+([\w.\s]+)', line)
        if match:
            yield from match[1].split()
        elif line.strip() and line.strip() not in ('prelude', 'module'):
            break  # Imports cannot follow a Lean declaration.


def closure(lean_dir, roots):
    ordered, seen, visiting = [], set(), set()

    def visit(name, root=False):
        name = name.removesuffix('.lean').replace('/', '.')
        if not re.fullmatch(r'[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*', name):
            raise ValueError(f'Invalid module name: {name}')
        source = lean_dir / (name.replace('.', '/') + '.lean')
        if not source.is_file():
            if root:
                raise ValueError(f'Local root does not exist: {source}')
            return  # Supplied by the pinned Lean toolchain.
        if name in visiting:
            raise ValueError(f'Cyclic local import: {name}')
        if name in seen:
            return
        visiting.add(name)
        for dependency in local_imports(source.read_text()):
            visit(dependency)
        visiting.remove(name)
        seen.add(name)
        ordered.append(name)

    for root in roots:
        visit(root, root=True)
    return ordered


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-dir', required=True, type=Path)
    parser.add_argument('--format', choices=['path', 'module'], default='path')
    parser.add_argument('roots', nargs='+')
    args = parser.parse_args()
    try:
        for module in closure(args.lean_dir, args.roots):
            print(module.replace('.', '/') + '.lean' if args.format == 'path' else module)
    except ValueError as error:
        parser.exit(1, str(error) + '\n')
