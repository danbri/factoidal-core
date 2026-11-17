#!/usr/bin/env python3
"""Measure S1 sets/families with the already-built l4qt4; retain all outcomes."""
import os,sys,subprocess,tempfile,pathlib,concurrent.futures,csv
root=pathlib.Path(__file__).resolve().parents[1]
out=root/'docs'/sys.argv[1];out.mkdir(exist_ok=True)
sets=sorted({l.split('\t')[0] for l in (root/'docs/20261029-version-targets.tsv').read_text().splitlines()[1:]})
set_families={r['set']:pathlib.Path(r['source']).parent.name for r in csv.DictReader(open(root/'docs/20261029-version-targets.tsv'),delimiter='\t')}
families=['fn','op','prod','array','map','ser','xs','misc','app']
jobs=[]
for kind,names in [('set',sets),('family',families)]:
 for name in names:
  for mode in ['xpath','xquery']:
   jobs.append((mode,kind,name))
def run(job):
 mode,kind,name=job
 log=out/f'{mode}-{kind}-{name}.log'
 if log.exists() and 'TOTAL:' in log.read_text() and 'TOTAL: 0 pass, 0 fail, 0 unsupported (out of 0)' not in log.read_text():return
 cmd=['.lake/build/bin/l4qt4','--isolate','60','--lang',mode,'--'+kind,name,'--list-fails','--trace']
 if kind=='set':cmd += ['--family',set_families[name]]
 with tempfile.TemporaryDirectory(prefix='s1-') as tmp,log.open('w') as f:
  env=dict(os.environ,TMPDIR=tmp)
  p=subprocess.run(cmd,cwd=root/'formal/lean4',env=env,stdout=f,stderr=subprocess.STDOUT)
  print(log.name,p.returncode,flush=True)
# Set the stack in the invoking shell: ulimit -s 65520.
with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:list(pool.map(run,jobs))
