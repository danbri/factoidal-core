#!/usr/bin/env python3
"""Differential check: complete factoidal-font-data-v1 records from the Lean
shaper (l4font-shape) against the HarfBuzz path of font-shape.
https://github.com/danbri/factoidal/issues/1233

usage: check-lean-shaper.py L4FONT_SHAPE FONT_SHAPE NAME=FONT_FILE ...
Only harfbuzzVersion, language and script may differ. A Lean refusal is
counted apart. Exit 1 when any record differs. Fonts are not distributed.
"""
import json,subprocess,sys,os
if len(sys.argv)<4: sys.exit(__doc__)
lean,hb=sys.argv[1],sys.argv[2]
fonts=dict(a.split('=',1) for a in sys.argv[3:])
texts=["Hello world","Zoë Ωμέγα Жж 123","AVATAR To Wa","office fifty","€100 — “quoted” ½ ñ","Typography: LT, Yo, P.","Ωμέγα ΑΥΤΟ","ТАК Жук","WAVE YAWN Fly away, Tom",
 "Café ñ Å","î j́ i̇́","é̂ ȫ","fi fl ffl","x"]
env=dict(os.environ,FACTOIDAL_FONT_SHAPE=hb)
same=total=refused=0
for fn,fp in fonts.items():
  for t in texts:
    h=subprocess.run([hb,fp,t,'20','0'],capture_output=True,text=True)
    l=subprocess.run([lean,fp,t,'20','0'],capture_output=True,text=True,env=env)
    if h.returncode!=0:
      print(f"{fn:18} {t!r}: HarfBuzz path refused ({h.stderr.strip()}); lean rc={l.returncode} {l.stderr.strip()[:100]}"); continue
    total+=1
    if l.returncode!=0:
      refused+=1; print(f"{fn:18} {t!r}: LEAN REFUSED {l.stderr.strip()[:200]}"); continue
    a=json.loads(h.stdout); b=json.loads(l.stdout)
    for k in ['harfbuzzVersion','language','script']: a.pop(k); b.pop(k)
    ok=a==b; same+=ok
    if not ok:
      diff=[k for k in a if a[k]!=b.get(k)]
      gl=[(x,y) for x,y in zip(a['glyphs'],b['glyphs']) if x!=y][:2]
      print(f"{fn:18} {t!r}: DIFF fields={diff} first glyph diffs={gl}")
print(f"complete records: {same} same, {total-same-refused} different, {refused} refused by Lean (out of {total})")
sys.exit(0 if same+refused==total else 1)
