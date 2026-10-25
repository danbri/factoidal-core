import re,json,sys,os
d=sys.argv[1]; out=[]
JS=r'"((?:[^"\\]|\\.)*)"'
pats=[
 ('bool', re.compile(r'@Test\s+public void (\w+)\(\)\s*\{\s*testBoolean\(\s*'+JS+r'\s*,\s*(true|false)\s*\)\s*;\s*\}')),
 ('num',  re.compile(r'@Test\s+public void (\w+)\(\)\s*\{\s*testNumeric\(\s*'+JS+r'\s*,\s*(-?[0-9]+)\s*\)\s*;\s*\}')),
 ('str',  re.compile(r'@Test\s+public void (\w+)\(\)\s*\{\s*testString\(\s*'+JS+r'\s*,\s*'+JS+r'\s*\)\s*;\s*\}')),
 ('err',  re.compile(r'@Test\s+public void (\w+)\(\)\s*\{\s*testEvalException\(\s*'+JS+r'\s*\)\s*;\s*\}')),
 ('nv',   re.compile(r'@Test\s+public void (\w+)\(\)\s*\{\s*test\(\s*'+JS+r'\s*,\s*NodeValue\.make(Integer|String|Boolean|Double|Decimal)\(\s*("?(?:[^"\\)]|\\.)*"?)\s*\)\s*\)\s*;\s*\}')),
 ('nvparse', re.compile(r'@Test\s+public void (\w+)\(\)\s*\{\s*test\(\s*'+JS+r'\s*,\s*'+JS+r'\s*\)\s*;\s*\}')),
]
for f in sorted(os.listdir(d)):
  if not f.endswith('.java'): continue
  s=open(os.path.join(d,f)).read()
  for kind,p in pats:
    for m in p.finditer(s):
      g=m.groups()
      try: expr=json.loads('"'+g[1]+'"')
      except Exception: continue
      rec={'cls':f[:-5],'name':g[0],'kind':kind,'expr':expr}
      if kind=='bool': rec['exp']=g[2]=='true'
      elif kind=='num': rec['exp']=int(g[2])
      elif kind=='str': rec['exp']=json.loads('"'+g[2]+'"')
      elif kind=='nv': rec['type']=g[2]; rec['exp']=g[3].strip('"')
      elif kind=='nvparse': rec['exp']=json.loads('"'+g[2]+'"')
      out.append(rec)
json.dump(out,open(sys.argv[2],'w'),indent=0)
import collections; print(len(out), collections.Counter(r['kind'] for r in out))
