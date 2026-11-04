#!/usr/bin/env python3
"""Run the HarfBuzz shaping test suite (test/shape/data of a HarfBuzz source
tree, same version as the local hb-shape) against the Lean shaper.
https://github.com/danbri/factoidal/issues/1233

usage: run-harfbuzz-suite.py L4FONT_SHAPE FONT_SHAPE HB_TEST_SHAPE_DATA OUT.json

A test passes when hb-shape gives the expected string AND the Lean adapter
equals hb-shape in glyph-id form (ids, clusters, advances, offsets). Tests
with options that change shaping are "not applicable" (option named); tests
HarfBuzz itself does not pass are "oracle mismatch". The suite is not
vendored: see docs/designissues/2026-11-03-font-trust-and-safety-policy.md
section 8 for the licence record.
"""
import json,os,re,subprocess,sys,collections,glob
lean,glyphmode,root,out=sys.argv[1:5]
DISPLAY={'--no-glyph-names','--no-positions','--no-clusters','--ned','--font-funcs=ot','--shaper=ot','--single-par'}
env=dict(os.environ,FACTOIDAL_FONT_SHAPE=glyphmode)
res=collections.Counter(); na=collections.Counter(); rows=[]
def hb(font,opts,cps):
  r=subprocess.run(['hb-shape',*opts,'--unicodes='+','.join('U+%04X'%c for c in cps),font],capture_output=True,text=True,timeout=60)
  return r.returncode,r.stdout.strip(),r.stderr.strip()
for suite in ['in-house','aots','text-rendering-tests']:
  for tf in sorted(glob.glob(f'{root}/{suite}/tests/*.tests')):
    for line in open(tf,encoding='utf-8'):
      line=line.rstrip('\n')
      if not line or line.startswith('#'): continue
      parts=line.split(';')
      if line.startswith('@'): res['directive']+=1; continue
      if len(parts)!=4: res['malformed line']+=1; continue
      fontrel,opts,uni,exp=parts
      font=os.path.normpath(os.path.join(os.path.dirname(tf),fontrel))
      key=f"{suite}/{os.path.basename(tf)}"
      o=opts.split()
      # Whole-text --features settings are passed to Lean; a range or a value
      # other than 0 or 1 stays not applicable.
      feats=''
      fo=[x for x in o if x.startswith('--features=')]
      if len(fo)==1:
        feats=fo[0][len('--features='):].strip('"\'')
        okf=all(re.fullmatch(r'[+-]?[A-Za-z0-9 ]{1,4}(=[01])?',it.strip()) for it in feats.split(',') if it.strip())
        if okf: o=[x for x in o if x!=fo[0]]
        else: feats=''
      bad=[x for x in o if x not in DISPLAY and not x.startswith('--font-funcs=ot')]
      if bad: na[bad[0].split('=')[0]]+=1; res['not applicable']+=1; continue
      if exp=='*': res['not applicable']+=1; na['expected *']+=1; continue
      try: cps=[int(u[2:] if u[:2] in ('U+','u+') else u,16) for u in uni.split(',') if u]
      except ValueError: res['not applicable']+=1; na['unicodes form']+=1; continue
      if any(c==0 or 0xD800<=c<=0xDFFF or c>0x10FFFF for c in cps) or '@' in fontrel or not os.path.exists(font):
        res['not applicable']+=1; na['input not passable']+=1; continue
      fopt=['--features='+feats] if feats else []
      rc,got,_=hb(font,o+fopt,cps)
      if rc!=0 or got!=exp: res['oracle mismatch']+=1; continue
      rc,ids,_=hb(font,['--font-funcs=ot','--no-glyph-names']+fopt,cps)
      text=''.join(map(chr,cps))
      l=subprocess.run([lean,font,text,'16','0']+([feats] if feats else []),capture_output=True,text=True,env=env,timeout=120)
      if l.returncode!=0:
        res['lean refused']+=1; rows.append((key,'REFUSED',l.stderr.strip().splitlines()[-1][:160] if l.stderr.strip() else '?',line)); continue
      rec=json.loads(l.stdout)
      b=text.encode('utf-8'); byte2cp={}; off=0
      for i,ch in enumerate(text): byte2cp[off]=i; off+=len(ch.encode('utf-8'))
      def fmt(g):
        s=f"{g['id']}={byte2cp.get(g['cluster'],g['cluster'])}"
        if g['xOffset'] or g['yOffset']: s+=f"@{g['xOffset']},{g['yOffset']}"
        s+=f"+{g['xAdvance']}"
        if g['yAdvance']: s+=f",{g['yAdvance']}"
        return s
      mine='['+'|'.join(fmt(g) for g in rec['glyphs'])+']'
      if mine==ids: res['pass']+=1
      else: res['fail']+=1; rows.append((key,'FAIL',f"hb={ids[:140]} lean={mine[:140]}",line))
summary={'results':dict(res),'not_applicable_by_option':dict(na)}
json.dump({'summary':summary,'rows':rows},open(out,'w'),indent=1)
print(json.dumps(summary,indent=1))
