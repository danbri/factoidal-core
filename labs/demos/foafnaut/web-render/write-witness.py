#!/usr/bin/env python3
import re
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
# The build script's module list is the source of truth: a typed copy drifted (WebXslt, 2026-11-05).
modules=re.search(r'^LAB_MODULES=\(([^)]*)\)',(lab/'build-web-render.sh').read_text(),re.M).group(1).split()
sources += [lab/name for name in ['Graphics.lean','GraphicsPrepared.lean','Font.lean','SVGPathData.lean','SVGCurves.lean','SVGPath.lean','SVGReferences.lean','SVGCSS.lean','SVGDash.lean','SVGDashUnits.lean','SVGStroke.lean','ImagePNG.lean','ImageJPEG.lean','ImageGIF.lean','ImageData.lean','SVG.lean','WebRenderSVG.lean','WebRender.lean','WebRenderRDF.lean','WebRenderFont.lean','WebRenderFontRequests.lean','WebRenderScript.lean','WebDocument.lean','WebRenderFontRequestsTests.lean','WebRenderScriptTests.lean','WebDocumentTests.lean','WebRenderCLI.lean','WebRenderTests.lean','WebRenderCurveTests.lean','RenderPlan.lean','web_render_shim.c','render_plan_shim.c','build-web-render.sh','toolchain-versions.env','web-render/write-witness.py']]
sources += [lab/(name+'.lean') for name in modules if lab/(name+'.lean') not in sources]
record={'format':'factoidal-web-render-source-witness-v1','commit':subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip(),'workingTree':subprocess.check_output(['git','-C',str(root),'status','--short'],text=True).splitlines(),'scope':'Fresh targeted Lean source/C closure; generated engines are local test artifacts, not a release. Runtime cache reused read only with ABI/patch witness.','files':{str(p.relative_to(root)):digest(p) for p in sources},'generatedC':{str(p.relative_to(root)):digest(p) for p in core_files+sorted((build/'ir').glob('*.c'))},'engines':{str(p.relative_to(root)):digest(p) for p in sorted((build/'engines').glob('*'))}}
if (build/'web-render-native').exists():
    native=build/'web-render-native'
    record['nativeSha256']=digest(native)
    record['nativeProducedAfterCurrentC']=all(p.stat().st_mtime<=native.stat().st_mtime for p in core_files+sorted((build/'ir').glob('*.c')))
    record['nativeNote']='The native SHA identifies bytes. If nativeProducedAfterCurrentC is false, native belongs to an earlier checkpoint; it is not evidence for this current source/C closure.'
if (build/'runtime-object-witness.txt').exists():record['runtimeObjectWitness']=(build/'runtime-object-witness.txt').read_text()
# The Lean hygiene ratchet's counts (LabHygiene.lean, written by build-web-render.sh this run).
# No counts, no record: a build that skipped the ratchet does not get one.
hygiene=build/'hygiene.json'
if not hygiene.exists():
    raise SystemExit('write-witness: no hygiene.json from this build (LabHygiene.lean did not run); record refused')
record['hygiene']={'counts':json.loads(hygiene.read_text()),'commit':record['commit'],'theorem':'lab_ratchet','module':'labs/demos/foafnaut/LabHygiene.lean'}
record['files']['labs/demos/foafnaut/LabHygiene.lean']=digest(lab/'LabHygiene.lean')
(build/'source-witness.json').write_text(json.dumps(record,indent=2)+'\n')
print(build/'source-witness.json')
