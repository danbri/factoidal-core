#!/usr/bin/env python3
"""Summarize per-target trace evidence without treating missing outcomes as passes."""
import csv,pathlib,re,collections,sys
root=pathlib.Path(__file__).resolve().parents[1];directory=root/'docs'/sys.argv[1]
rows=list(csv.DictReader(open(root/'docs/20261029-version-targets.tsv'),delimiter='\t'))
results={}
timeouts={}
for f in directory.glob('*-set-*.log'):
 mode=f.name.split('-set-')[0]
 setname=f.name.split('-set-')[1][:-4]
 if 'TIMEOUT or crash' in f.read_text():
  timeouts[mode,setname]='Set timed out/crashed; per-case trace unavailable (aggregate tally does not establish this case)'
 for line in f.read_text().splitlines():
  line=line.strip()
  m=re.match(r'(PASS|FAIL|UNSUP|EXCLUDED) ([^/]+)/([^:]+)(?:: (.*))?$',line)
  if m: results[mode,m[2],m[3]]=(m[1],m[4] or '')
counts=collections.Counter();cats=collections.Counter();pending=[]
for r in rows:
 vals=[results.get((m,r['set'],r['case']),('MISSING',timeouts.get((m,r['set']),'No recorded outcome'))) for m in ['xpath','xquery']]
 passed=any(v[0]=='PASS' for v in vals)
 counts['pass' if passed else 'nonpass']+=1
 if not passed:pending.append((r,vals));cats[r['category']]+=1
print(counts);print(cats)
with open(directory/'targets.tsv','w') as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['set','case','category','xpath','xpath cause','xquery','xquery cause'])
 for r in rows:
  xp=results.get(('xpath',r['set'],r['case']),('MISSING',timeouts.get(('xpath',r['set']),'No recorded outcome')));xq=results.get(('xquery',r['set'],r['case']),('MISSING',timeouts.get(('xquery',r['set']),'No recorded outcome')))
  w.writerow([r['set'],r['case'],r['category'],*xp,*xq])
for f in sorted(directory.glob('*-family-*.log')):
 totals=[l for l in f.read_text().splitlines() if l.startswith('TOTAL:')]
 print(f.name,totals[-1] if totals else 'INCOMPLETE')

# Keep the exact processor diagnostics beside every nonpassing target.
with (directory/'remaining.md').open('w') as f:
 f.write('# Nonpassing S1 targets\n\nUnsupported and missing outcomes are not passes.\n\n')
 f.write('| Test set / case | XPath outcome | XQuery outcome |\n| --- | --- | --- |\n')
 for r, vals in pending:
  def cell(v):
   return (v[0] + (': ' + v[1] if v[1] else '')).replace('|', '&#124;').replace('\n', ' ')
  f.write('| `'+r['set']+'/'+r['case']+'` | '+cell(vals[0])+' | '+cell(vals[1])+' |\n')
