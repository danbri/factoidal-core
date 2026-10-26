import sys,os,re,collections
J=sys.argv[1]
ann=re.compile(r'^\s*@(Test|ParameterizedTest|RepeatedTest|TestFactory)\b',re.M)
j3=re.compile(r'^\s*public\s+void\s+test\w*\s*\(',re.M)
# (stage, class) rules: first match wins, by path prefix under src/test/java
R=[
 # (a) manifest runners / W3C-derived
 ('a','jena-arq','org/apache/jena/arq/junit'),('a','jena-arq','org/apache/jena/riot/Scripts_'),('a','jena-arq','org/apache/jena/sparql/Scripts_'),
 ('a','jena-arq','org/apache/jena/riot/lang/rdfxml/converted_legacy'),('a','jena-arq','org/apache/jena/riot/lang/rdfxml/Scripts_'),
 ('a','jena-core','org/apache/jena/rdfxml/arp1tests'),('a','jena-core','org/apache/jena/core_ttl'),('a','jena-core','org/apache/jena/reasoner/test/WG'),
 ('a','jena-shacl',''),('a','jena-shex',''),
 # (c) JVM / engine internals
 ('c','jena-core','org/apache/jena/mem'),('c','jena-core','org/apache/jena/test'),('c','jena-core','org/apache/jena/assembler'),
 ('c','jena-arq','org/apache/jena/sparql/algebra'),('c','jena-arq','org/apache/jena/sparql/sse'),('c','jena-arq','org/apache/jena/sparql/engine'),
 ('c','jena-arq','org/apache/jena/riot/tokens'),('c','jena-arq','org/apache/jena/riot/thrift'),('c','jena-arq','org/apache/jena/riot/protobuf'),
 ('c','jena-arq','org/apache/jena/atlas'),('c','jena-arq','org/apache/jena/system/buffering'),('c','jena-arq','org/apache/jena/system/TestThread'),('c','jena-arq','org/apache/jena/system/TestTxn'),
 ('c','jena-arq','org/apache/jena/sparql/transaction'),('c','jena-arq','org/apache/jena/http'),('c','jena-arq','org/apache/jena/riot/stream'),
 ('c','jena-arq','org/apache/jena/riot/web'),('c','jena-arq','org/apache/jena/riot/adapters'),('c','jena-arq','org/apache/jena/sparql/solver'),
 ('c','jena-arq','org/apache/jena/sparql/lib'),('c','jena-arq','org/apache/jena/arq/examples'),('c','jena-arq','org/apache/jena/sparql/api/TestQueryExecutionTimeout'),('c','jena-arq','org/apache/jena/sparql/api/TestTimeouts'),('c','jena-arq','org/apache/jena/sparql/api/TestQueryExecutionCancel'),('c','jena-arq','org/apache/jena/sparql/api/TestUpdateExecutionCancel'),
 ('c','jena-arq','org/apache/jena/sparql/expr/TestExprTransform'),('c','jena-arq','org/apache/jena/sparql/expr/TestExprFunctionOp'),('c','jena-arq','org/apache/jena/sparql/util'),
]
STAGE={  # stage of a (b) path
 'jena-core':[('3','org/apache/jena/reasoner'),('3','org/apache/jena/ontology'),('1','')],
 'jena-arq':[('3','org/apache/jena/rdfs'),('2','org/apache/jena/sparql'),('2','org/apache/jena/query'),('1','')],
}
tot=collections.Counter(); files=collections.Counter()
for mod in ['jena-core','jena-arq','jena-shacl','jena-shex']:
  base=os.path.join(J,mod,'src/test/java')
  for dp,dn,fn in os.walk(base):
    for f in fn:
      if not f.endswith('.java'): continue
      p=os.path.join(dp,f); s=open(p,errors='ignore').read()
      a=len(ann.findall(s)); n=a if a else len(j3.findall(s))
      if not n: continue
      rel=os.path.relpath(p,base)
      cls=None
      for c,m,pre in R:
        if m==mod and rel.startswith(pre): cls=c; break
      if cls is None:
        cls='b'
      st=''
      if cls=='b':
        for sname,pre in STAGE[mod]:
          if rel.startswith(pre): st=sname; break
        if mod=='jena-arq' and rel.startswith('org/apache/jena/sparql/expr'): st='2expr'
      key=(mod,cls,st); tot[key]+=n; files[key]+=1
for k in sorted(tot): print(k, tot[k],'methods',files[k],'classes')
