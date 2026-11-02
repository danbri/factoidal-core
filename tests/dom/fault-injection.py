#!/usr/bin/env python3
"""tests/dom/fault-injection.py — measure the reach of the jsdom differential
(tests/dom/diff.mjs). Puts one fault at a time into
formal/lean4/L4Factoidal/DOM/Arena.lean, rebuilds l4dom, runs 2000 scripts of
60 operations, and prints the number of scripts that disagree. Each fault must
give at least one disagreement. The file is restored at the end.
Run from the repository root; not part of tests/dom/run.sh (7 rebuilds).
Results of 2026-11-01: docs/designissues/2026-11-01-dom-arena.md.
"""
import subprocess, os
A='formal/lean4/L4Factoidal/DOM/Arena.lean'
orig=open(A).read()
M={
 'M1 step 9 doctype following child': ("      | some c => d.doctypeFollowing parent c\n      | none => false\n    if d.hasElementChildExcept","      | some c => false\n      | none => false\n    if d.hasElementChildExcept"),
 'M2 step 8 Text child of fragment': ("if elems.size > 1 || n.kids.any (fun k => isTextNode (d.get k))","if elems.size > 1"),
 'M3 step 11 element preceding child': ("    | some c => d.elementPreceding parent c\n","    | some c => false\n"),
 'M4 normalize keeps empty Text': ("        if x.data.isEmpty then gone := gone.push k\n","        if false then gone := gone.push k\n"),
 'M5 setAttribute without lowercase': ("then asciiLower qualifiedName\n","then qualifiedName\n"),
 'M6 replace reference child': ("  let ref := if ref0 == some node then d.nextSibling node else ref0\n","  let ref := ref0\n"),
 'M7 deep clone without template contents': ("    | some sc, some cc => (d.get sc).kids.toList.map (·, cc)\n","    | some _, some _ => []\n"),
}
env=dict(os.environ); env['PATH']=os.path.expanduser('~/.elan/bin')+':'+env['PATH']
only = os.environ.get('ONLY')
try:
  for name,(a,b) in M.items():
    if only and not name.startswith(only): continue
    assert orig.count(a)==1,(name)
    open(A,'w').write(orig.replace(a,b))
    r=subprocess.run(['lake','build','l4dom'],cwd='formal/lean4',env=env,capture_output=True,text=True)
    if r.returncode: print(name,'BUILD FAIL',r.stdout[-500:]); continue
    r=subprocess.run(['node','tests/dom/diff.mjs','formal/lean4/.lake/build/bin/l4dom','2000','60','1'],capture_output=True,text=True)
    print(name,'->',r.stdout.strip().splitlines()[-1])
finally:
  open(A,'w').write(orig)
  subprocess.run(['lake','build','l4dom'],cwd='formal/lean4',env=env,capture_output=True)
