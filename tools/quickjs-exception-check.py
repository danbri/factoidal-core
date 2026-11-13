#!/usr/bin/env python3
"""BubblePopJS is the page script engine everywhere; QuickJS-NG is an exception.

Every tracked code file that chooses QuickJS-NG (the engine id "quickjs" in quotes,
SCRIPT_ENGINE=quickjs, --script-engine quickjs, a --quickjs-wasm option) must say why with
a marker comment containing QUICKJS-EXCEPTION. The exceptions and their reasons are listed in
docs/designissues/2026-11-13-bubblepopjs-everywhere.md.

The check is per file: a file with a marker may hold several choices. The code of QuickJS-NG
itself (its guest build, its WasmVM bench and the older lab server's QuickJS worker) is out of
scope: it is QuickJS, not a choice of it.

  python3 tools/quickjs-exception-check.py            # exit 1 and a list when a file lacks the marker
  python3 tools/quickjs-exception-check.py --self-test
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CODE = ('.ts', '.mjs', '.js', '.lean', '.sh', '.py', '.yml', '.yaml', '.njk', '.c')
# The implementation of QuickJS-NG in this repository, not a choice of it.
OWN = ('tools/wasmvm/quickjs/', 'tools/wasmvm/build-quickjs.sh', 'formal/lean4/L4Factoidal/WasmVM/Bench/',
       'labs/demos/foafnaut/web-render/script-engine/', 'tests/browser-wpt/quickjs-probe.mjs',
       'tools/quickjs-exception-check.py', 'third_party/')
CHOICE = re.compile(r"""["'`]quickjs["'`]|SCRIPT_ENGINE=quickjs|--script-engine[ =]quickjs|--quickjs-wasm|--script-setting[ =]quickjs""")
MARKER = 'QUICKJS-EXCEPTION'


def unmarked(files):
    out = []
    for name, text in files:
        if not name.endswith(CODE) or name.startswith(OWN):
            continue
        if CHOICE.search(text) and MARKER not in text:
            line = next(i for i, l in enumerate(text.splitlines(), 1) if CHOICE.search(l))
            out.append(f'{name}:{line}')
    return out


def self_test():
    assert unmarked([('a.ts', 'run({engine:"quickjs"})')]) == ['a.ts:1']
    assert unmarked([('a.ts', '// QUICKJS-EXCEPTION: differential\nrun({engine:"quickjs"})')]) == []
    assert unmarked([('a.sh', 'SCRIPT_ENGINE=quickjs deno test x')]) == ['a.sh:1']
    assert unmarked([('a.lean', 'def e := "bubblepop"')]) == []
    assert unmarked([('tools/wasmvm/quickjs/x.js', '"quickjs"')]) == []
    assert unmarked([('a.md', '"quickjs"')]) == []
    print('quickjs-exception-check: self-test ok')


def main():
    if '--self-test' in sys.argv:
        return self_test()
    names = subprocess.run(['git', 'ls-files', '-z'], cwd=ROOT, capture_output=True, check=True).stdout.decode().split('\0')
    files = []
    for name in names:
        if name.endswith(CODE) and not name.startswith(OWN):
            p = ROOT / name
            if p.is_file():
                files.append((name, p.read_text(errors='replace')))
    bad = unmarked(files)
    if bad:
        print('QuickJS-NG chosen with no QUICKJS-EXCEPTION marker (BubblePopJS is the default everywhere;')
        print('say why in a comment and list it in docs/designissues/2026-11-13-bubblepopjs-everywhere.md):')
        for b in bad:
            print('  ' + b)
        sys.exit(1)
    print(f'quickjs-exception-check: ok ({len(files)} code files)')


if __name__ == '__main__':
    main()
