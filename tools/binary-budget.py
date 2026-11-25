#!/usr/bin/env python3
"""tools/binary-budget.py: size and link-content gate for the shipped engine binaries (issue 551).

On 2026-11-16 leanjs grew from 11.4 MB to 110.9 MB because a proof module that imports
Lean.Elab.Tactic (JS/FuelMono.lean) entered the import closure of JS/Main: the executable linked
Lean's elaborator and meta code (21,363 l_Lean_Elab symbols), and no check noticed. This gate
has two parts:

  imports   (no build; tools/premerge.sh runs it): the import closure of each shipped root
            module imports no Lean module outside Lean.Data. Proof tactics (Lean.Elab, Lean.Meta)
            belong in modules that only proofs import.
  check     (on built binaries; build-web-render.sh and the CI lean job run it): each binary
            carries no Lean.Elab / Lean.Meta symbol, and is at most `tolerance` (2 %) above its
            recorded size in tools/binary-budget.json for this platform. A binary with no
            recorded size on this platform is reported, not failed. A binary well below its
            budget is reported so the budget can be lowered: `--update` writes measured sizes that
            are new or smaller (the ratchet only moves down; raise a budget by hand, saying why).

Usage:
  tools/binary-budget.py imports [FORMAL_LEAN4_DIR]
  tools/binary-budget.py check [--update] NAME=PATH ...
     NAME is a key of the budget file (leanjs, bubblepop-test262, libweb-render.dylib,
     libweb-render.so, web-render.wasm). For web-render.wasm the brotli size (key
     web-render.wasm.br) is checked as well when the brotli command is installed.
"""
import json, os, platform, re, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUDGET = ROOT / 'tools' / 'binary-budget.json'

# Root modules of the shipped binaries. leanjs and bubblepop-test262 are lake executables
# (formal/lean4/lakefile.lean); the web-render engines (native and Wasm) are linked by
# labs/demos/foafnaut/build-web-render.sh from the import closure of its module list, which
# that script's own walk refuses Std in; their Lean imports are checked here from the same list.
EXE_ROOTS = {
    'leanjs': ['L4Factoidal.JS.Main'],
    'bubblepop-test262': ['L4Factoidal.WasmVM.Hosts.Test262Page'],
}
ALLOWED_LEAN = ('Lean.Data.',)
# Module initialisers of Lean's own library (Lean.Elab, Lean.Meta, Lean.Compiler, ...) other than
# Lean.Data. Function names such as l_Lean_Elab_Tactic_Ext_... are not a sign: Init declares
# syntax in those namespaces, and every engine carries them. A Wasm build without a name
# section has no names to find; there the link itself fails (the Wasm runtime has no Lean library).
FORBIDDEN_SYMBOL = re.compile(rb'initialize_Lean_(?!Data_)[A-Za-z0-9_]+')


def web_render_roots():
    script = (ROOT / 'labs/demos/foafnaut/build-web-render.sh').read_text()
    m = re.search(r'^CORE=\(([^)]*)\)', script, re.M)
    if not m:
        sys.exit('binary-budget: no module list in build-web-render.sh (the import walk moved?)')
    return m.group(1).split()


def lean_imports(lean4, roots, lab=None):
    """(module, import) for every Lean.* import in the project closure of `roots`."""
    seen, bad, stack = set(), [], list(roots)
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        src = lean4 / Path(*mod.split('.')).with_suffix('.lean')
        if not src.exists() and lab is not None:
            src = lab / Path(*mod.split('.')).with_suffix('.lean')
        if not src.exists():
            continue  # toolchain module (Init, Std) or a generated module
        for imp in re.findall(r'^import\s+(\S+)', src.read_text(), re.M):
            if imp == 'Lean' or (imp.startswith('Lean.') and not imp.startswith(ALLOWED_LEAN)):
                bad.append((mod, imp))
            else:
                stack.append(imp)
    return bad


def cmd_imports(args):
    lean4 = Path(args[0]) if args else ROOT / 'formal/lean4'
    lab = ROOT / 'labs/demos/foafnaut'
    roots = dict(EXE_ROOTS)
    roots['web-render'] = web_render_roots()
    lab_modules = re.search(r'^LAB_MODULES=\(([^)]*)\)', (lab / 'build-web-render.sh').read_text(), re.M)
    if lab_modules:
        roots['web-render'] += lab_modules.group(1).split()
    failed = False
    for name, rs in roots.items():
        bad = lean_imports(lean4, rs, lab)
        for mod, imp in bad:
            print(f'FAIL {name}: {mod} imports {imp}: a shipped binary would link Lean\'s compiler code; '
                  f'move tactics and proofs to a module the executable does not import (issue 551)')
            failed = True
        if not bad:
            print(f'ok {name}: no Lean import outside Lean.Data in the closure of {len(rs)} root(s)')
    return 1 if failed else 0


def platform_key():
    return f'{platform.system().lower()}-{platform.machine().lower()}'


def brotli_size(path):
    exe = shutil.which('brotli')
    if not exe:
        return None
    out = subprocess.run([exe, '-c', '-q', '11', str(path)], capture_output=True, check=True).stdout
    return len(out)


def cmd_check(args):
    update = '--update' in args
    pairs = [a.split('=', 1) for a in args if a != '--update']
    data = json.loads(BUDGET.read_text())
    tol = data['tolerance']
    key = platform_key()
    failed = False
    measured = {}
    for name, path in pairs:
        p = Path(path)
        if not p.is_file():
            print(f'FAIL {name}: {path} not found'); failed = True; continue
        blob = p.read_bytes()
        syms = sorted(set(FORBIDDEN_SYMBOL.findall(blob)))
        if syms:
            print(f'FAIL {name}: links {len(syms)} modules of Lean\'s own library (e.g. {syms[0].decode()}): '
                  f'a module in its import closure imports Lean\'s elaborator or compiler (issue 551)')
            failed = True
        sizes = {name: len(blob)}
        if name.endswith('.wasm'):
            br = brotli_size(p)
            if br is None:
                print(f'note {name}.br: brotli not installed, compressed size not checked')
            else:
                sizes[name + '.br'] = br
        for n, size in sizes.items():
            measured[n] = size
            budget = data['budgets'].get(key, {}).get(n, data['budgets'].get('any', {}).get(n))
            if budget is None:
                print(f'note {n}: {size:,} B; no budget recorded for {key}')
                continue
            ratio = size / budget - 1
            if size > budget * (1 + tol):
                print(f'FAIL {n}: {size:,} B is {ratio:+.2%} against the budget {budget:,} B '
                      f'(limit {tol:+.0%}; tools/binary-budget.json, issue 551)')
                failed = True
            elif ratio < -tol:
                print(f'ok {n}: {size:,} B, {ratio:+.2%} against {budget:,} B: lower the budget '
                      f'(tools/binary-budget.py check --update)')
            else:
                print(f'ok {n}: {size:,} B, {ratio:+.2%} against {budget:,} B')
    if update and not failed:
        for n, size in measured.items():
            scope = 'any' if n.startswith('web-render.wasm') else key
            old = data['budgets'].setdefault(scope, {}).get(n)
            if old is None or size < old:
                data['budgets'][scope][n] = size
        BUDGET.write_text(json.dumps(data, indent=2) + '\n')
        print(f'binary-budget: recorded in {BUDGET}')
    return 1 if failed else 0


def main(argv):
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__); return 0
    if argv[0] == 'imports':
        return cmd_imports(argv[1:])
    if argv[0] == 'check':
        return cmd_check(argv[1:])
    print(__doc__, file=sys.stderr); return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
