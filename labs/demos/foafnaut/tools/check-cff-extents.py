#!/usr/bin/env python3
"""Differential: Lean CFF glyph extents (SfntCff) against hb-shape --show-extents.
usage: check-cff-extents.py PROBE.lean FORMAL_LEAN4_DIR FONT_ROOT (every */fonts/* with a CFF table)
https://github.com/danbri/factoidal/issues/1233"""
import subprocess,sys,os,glob,struct
probe,W,root=sys.argv[1:4]
fonts=set()
for tf in glob.glob(root+'/*/fonts/*'):
  try: b=open(tf,'rb').read(12+16*64)
  except: continue
  if len(b)<12: continue
  n=struct.unpack('>H',b[4:6])[0]
  if any(b[12+16*i:16+16*i]==b'CFF ' for i in range(min(n,64))): fonts.add(tf)
tot=same=0; bad=[]
for f in sorted(fonts):
  r=subprocess.run(['lake','env','lean','--run',probe,f,'400'],capture_output=True,text=True,cwd=W,timeout=600)
  lean={}
  for line in r.stdout.split('\n'):
    p=line.split()
    if len(p)==5: lean[int(p[0])]=tuple(map(int,p[1:]))
    elif len(p)>=2: lean[int(p[0])]=' '.join(p[1:])
  if not lean: bad.append((os.path.basename(f),'probe',r.stderr[:120])); continue
  gl=','.join(f'gid{g}' for g in sorted(lean))
  h=subprocess.run(['hb-shape','--glyphs','--show-extents','--no-positions','--no-clusters',f,'['+'|'.join(f'gid{g}' for g in sorted(lean))+']'],capture_output=True,text=True)
  import re
  hb={int(m.group(1)):tuple(map(int,m.group(2,3,4,5))) for m in re.finditer(r'gid(\d+)<(-?\d+),(-?\d+),(-?\d+),(-?\d+)>',h.stdout)}
  for g,v in lean.items():
    if g not in hb: continue
    tot+=1
    if v==hb[g]: same+=1
    elif len(bad)<8: bad.append((os.path.basename(f),g,v,hb[g]))
print(f"CFF glyph extents: {same} same, {tot-same} different (out of {tot}) over {len(fonts)} fonts")
for x in bad: print(' ',x)
