import sys,re,os
root=sys.argv[1]
idx={}
for dp,dn,fn in os.walk(root):
  if '/src/main/java/' not in dp: continue
  for f in fn:
    if f.endswith('.java'): idx.setdefault(f[:-5],[]).append(os.path.join(dp,f))
meth=re.compile(r'^    (?:@\w+\s+)*(public\s+|default\s+|static\s+|abstract\s+|final\s+|synchronized\s+)*(?:<[^>]+>\s+)?[\w.<>\[\],? ]+?\s+(\w+)\s*\([^;{]*', re.M)
for name in sys.argv[2:]:
  ps=[p for p in idx.get(name,[]) ]
  if not ps: print(f"{name}: NOT FOUND"); continue
  p=ps[0]; s=open(p).read()
  isint=re.search(r'public\s+(?:\w+\s+)*interface\s+'+name,s) is not None
  # strip comments
  s2=re.sub(r'/\*.*?\*/','',s,flags=re.S); s2=re.sub(r'//[^\n]*','',s2)
  ms=[]
  for m in meth.finditer(s2):
    line=m.group(0)
    mods=m.group(1) or ''
    if m.group(2) in ('if','for','while','switch','return','new','catch'): continue
    if not isint and 'public' not in line.split('(')[0]: continue
    if 'private' in line.split('(')[0] or 'protected' in line.split('(')[0]: continue
    ms.append(m.group(2))
  ext=re.search(r'(?:interface|class)\s+'+name+r'\b[^{]*',s2)
  print(f"{name}: {'interface' if isint else 'class'} methods={len(ms)} distinct_names={len(set(ms))} file={p.split('/src/main/java/')[1]}  decl='{' '.join(ext.group(0).split())[:150] if ext else ''}'")
