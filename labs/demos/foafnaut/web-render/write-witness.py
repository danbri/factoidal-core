#!/usr/bin/env python3
"""Record exact source/C/engine bytes for the local targeted build."""
from pathlib import Path
import hashlib,json,subprocess
lab=Path(__file__).resolve().parents[1]
root=lab.parents[2]
build=lab/'.build/web-render'
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
core_files=[Path(p) for p in (build/'core-c-files.txt').read_text().splitlines()]
sources=[root/'formal/lean4'/p.relative_to(root/'formal/lean4/.lake/build/ir').with_suffix('.lean') for p in core_files]
sources += [root/'formal/lean4/lean-toolchain']
sources += [lab/name for name in ['Graphics.lean','Font.lean','SVGPath.lean','SVGCSS.lean','SVGDash.lean','SVGDashUnits.lean','SVGStroke.lean','SVG.lean','WebRenderSVG.lean','WebRender.lean','WebRenderCLI.lean','RenderPlan.lean','web_render_shim.c','render_plan_shim.c','build-web-render.sh','toolchain-versions.env']]
record={'format':'factoidal-web-render-source-witness-v1','commit':subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip(),'workingTree':subprocess.check_output(['git','-C',str(root),'status','--short'],text=True).splitlines(),'scope':'Fresh targeted Lean source/C closure; generated engines are local test artifacts, not a release. Runtime cache reused read only with ABI/patch witness.','files':{str(p.relative_to(root)):digest(p) for p in sources},'generatedC':{str(p.relative_to(root)):digest(p) for p in core_files+sorted((build/'ir').glob('*.c'))},'engines':{str(p.relative_to(root)):digest(p) for p in sorted((build/'engines').glob('*'))}}
if (build/'web-render-native').exists():
    native=build/'web-render-native'
    record['nativeSha256']=digest(native)
    record['nativeProducedAfterCurrentC']=all(p.stat().st_mtime<=native.stat().st_mtime for p in core_files+sorted((build/'ir').glob('*.c')))
    record['nativeNote']='The native SHA identifies bytes. If nativeProducedAfterCurrentC is false, native belongs to an earlier checkpoint; it is not evidence for this current source/C closure.'
if (build/'runtime-object-witness.txt').exists():record['runtimeObjectWitness']=(build/'runtime-object-witness.txt').read_text()
(build/'source-witness.json').write_text(json.dumps(record,indent=2)+'\n')
print(build/'source-witness.json')
