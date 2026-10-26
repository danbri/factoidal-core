"""Run production audits against only C reachable from the CI build roots."""
import importlib.util,json,re,tempfile,subprocess
from pathlib import Path
base=Path(__file__).resolve().parent;repo=base/'integrate-core';lean=repo/'formal/lean4'
spec=importlib.util.spec_from_file_location('imports',repo/'tools/lean-unbuilt-modules.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
lake=(lean/'lakefile.lean').read_text();wasm=lake.split('lean_lib l4wasm where',1)[1].split('roots := #[',1)[1].split(']',1)[0]
roots=['L4Factoidal','Harness.Qlvr','Harness.CryptoProbe']+re.findall(r'`([\w.]+)',wasm)
seen=set();stack=roots[:]
while stack:
 mod=stack.pop()
 if mod in seen:continue
 seen.add(mod);stack.extend(i for i in m.imports_of(mod) if Path(m.module_path(i)).is_file())
view=Path(tempfile.mkdtemp(prefix='integration-ci-ir-'));missing=[]
for mod in sorted(seen):
 rel=Path(*mod.split('.')).with_suffix('.c');c=lean/'.lake/build/ir'/rel
 if not c.is_file():missing.append(mod);continue
 target=view/rel;target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(c)
report={'roots':roots,'modules':sorted(seen),'missing':missing,'view':str(view)}
(base/'logs/integration-final-ci-closure-report.json').write_text(json.dumps(report,indent=2)+'\n')
if missing:raise SystemExit('Missing C: '+str(missing))
for tool in ['lean-tail-recursion-audit.py','lean-csimp-reach.py']:
 r=subprocess.run(['python3',str(repo/'tools'/tool),'--ir-dir',str(view),'--gate'],cwd=repo)
 if r.returncode:raise SystemExit(r.returncode)
