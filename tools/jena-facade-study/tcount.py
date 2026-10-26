import sys,os,re,collections
root=sys.argv[1]; depth=int(sys.argv[2]) if len(sys.argv)>2 else 0
ann=re.compile(r'^\s*@(Test|ParameterizedTest|RepeatedTest|TestFactory)\b',re.M)
j3=re.compile(r'^\s*public\s+void\s+test\w*\s*\(',re.M)
agg=collections.defaultdict(lambda:[0,0])
for dp,dn,fn in os.walk(root):
  if '/src/test/java' not in dp: continue
  for f in fn:
    if not f.endswith('.java'): continue
    p=os.path.join(dp,f); s=open(p,errors='ignore').read()
    a=len(ann.findall(s)); n=a if a else len(j3.findall(s))
    if n==0: continue
    rel=p.split('/src/test/java/')[1]; key='/'.join(rel.split('/')[:-1][:depth]) if depth else rel.split('/src')[0]
    agg[key][0]+=1; agg[key][1]+=n
for k,(c,n) in sorted(agg.items(),key=lambda x:-x[1][1]): print(f"{n:6d} methods {c:4d} classes  {k}")
