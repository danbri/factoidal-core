#!/usr/bin/env python3
"""build-units.py: one manifest to deployable wasm units.

  tools/deploy/build-units.py deploy/units/web-render.json --build DIR --runtime DIR --out DIR
      [--shake-only] [--jobs 3] [--opt -O2]

Steps: lean-c-shake (lazy) -> cached emcc -> link -O1 with relocs -> plan-units -> wasm-split ->
wasm-opt for each part -> strip. --build holds core-c-files.txt and ir/ from
labs/demos/foafnaut/build-web-render.sh --source-only. Run the corpus with check-units.mjs.
Design and measurements: docs/20261106-deployable-modules.md
"""
import argparse, concurrent.futures as cf, glob, gzip, json, os, shlex, shutil, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__)); ROOT = os.path.dirname(os.path.dirname(HERE))
FEATURES = '--enable-exception-handling --enable-bulk-memory --enable-bulk-memory-opt --enable-nontrapping-float-to-int --enable-sign-ext --enable-mutable-globals --enable-reference-types --enable-multivalue --enable-call-indirect-overlong'.split()
def run(cmd, **k):
    r = subprocess.run(cmd, capture_output=True, text=True, **k)
    if r.returncode: sys.exit(f'failed: {" ".join(map(str, cmd))[:400]}\n{r.stdout[-800:]}{r.stderr[-800:]}')
    return r.stdout
ap = argparse.ArgumentParser()
ap.add_argument('manifest'); ap.add_argument('--build', required=True); ap.add_argument('--runtime', required=True)
ap.add_argument('--out', required=True); ap.add_argument('--jobs', type=int, default=3); ap.add_argument('--opt', default='-O2')
ap.add_argument('--stop-after-link', action='store_true')
a = ap.parse_args()
m = json.load(open(a.manifest)); out = os.path.abspath(a.out); build = os.path.abspath(a.build); rt = os.path.abspath(a.runtime)
os.makedirs(out, exist_ok=True); t0 = time.time(); steps = {}
def lap(n):
    global t0; steps[n] = round(time.time() - t0, 1); t0 = time.time(); print(n, steps[n], 's', flush=True)
toolchain = run(['lean', '--print-prefix'], cwd=ROOT + '/formal/lean4').strip()
llvm = os.path.join(os.path.dirname(os.path.dirname(os.path.realpath(shutil.which('emcc')))), 'libexec/llvm/bin')
if not os.path.isdir(llvm): llvm = '/opt/homebrew/opt/emscripten/libexec/llvm/bin'
# 1. sources
exclude = set(m.get('exclude-ir', []))
files = [l.strip() for l in open(build + '/core-c-files.txt') if l.strip()]
files += [f for f in sorted(glob.glob(build + '/ir/*.c')) if os.path.basename(f)[:-2] not in exclude]
files += sorted(glob.glob(rt + '/core-c/*.c'))
open(out + '/cfiles.txt', 'w').write('\n'.join(files) + '\n')
undef = run([llvm + '/llvm-nm', '-u', '--no-sort'] + glob.glob(rt + '/rt-obj/*.o'))
open(out + '/rt-undef.txt', 'w').write('\n'.join(sorted({l.split()[-1] for l in undef.split('\n') if l.strip()})) + '\n')
shim = os.path.join(ROOT, m['shim'])
# 2. the C pass
shutil.rmtree(out + '/c', ignore_errors=True)
print(run([sys.executable, HERE + '/lean-c-shake.py', '--files', out + '/cfiles.txt', '--root-file', shim, '--nm-undefined', out + '/rt-undef.txt', '--mode', 'lazy', '--out', out + '/c']))
lap('shake')
# 3. compile, content addressed
objs = out + '/obj'; shutil.rmtree(objs, ignore_errors=True); os.makedirs(objs)
cache = os.environ.get('UNIT_OBJ_CACHE', out + '/objcache')
base = ['-DNDEBUG', '-DLEAN_EMSCRIPTEN', '-fwasm-exceptions', '-I', rt + '/wasm-include', '-I', toolchain + '/include']
jobs = []
for x in m.get('extra-c', []):
    src = os.path.join(ROOT, x['src'])
    jobs.append([HERE + '/cc-cache.sh', cache, f'{objs}/{x.get("name", os.path.basename(src)[:-2])}.o', src, 'emcc', '-O3'] + base + [f.replace('$ROOT', ROOT) for f in x.get('flags', [])])
for src, cfile in json.load(open(out + '/c/files.json')) + [[shim, shim]]:
    name = os.path.basename(src)[:-2]
    if '/.lake/' in src: name = 'Core_' + src.split('/ir/')[1][:-2].replace('/', '_')
    opt = '-O3' if '/core-c/' in src else '-O2'
    jobs.append([HERE + '/cc-cache.sh', cache, f'{objs}/{name}.o', cfile, 'emcc', opt] + base)
fails = []
def one(j):
    r = subprocess.run(j, capture_output=True, text=True)
    if r.returncode: fails.append(j[3])
with cf.ThreadPoolExecutor(a.jobs) as ex: list(ex.map(one, jobs))
if fails: sys.exit('compile failed: ' + ' '.join(fails[:5]))
lap('compile')
# 4. link. -O1: Binaryen must not inline a gate or merge functions before the split.
link = out + '/link'; shutil.rmtree(link, ignore_errors=True); os.makedirs(link + '/tmp')
env = dict(os.environ, EMCC_DEBUG='1', TMPDIR=link + '/tmp')
exports = ','.join('_' + e for e in m['entries'])
run(['em++', '-O1', '-DNDEBUG', '-fwasm-exceptions', '--no-entry', '-Wl,--emit-relocs', '--profiling-funcs'] + sorted(glob.glob(objs + '/*.o')) + sorted(glob.glob(rt + '/rt-obj/*.o')) +
    ['-o', link + '/' + m['engine'] + '.mjs', '-sMODULARIZE=1', '-sEXPORT_ES6=1', '-sINVOKE_RUN=0', '-sEXPORTED_FUNCTIONS=' + exports,
     '-sEXPORTED_RUNTIME_METHODS=ccall,UTF8ToString', '-sALLOW_MEMORY_GROWTH=1', '-sSTACK_SIZE=' + m.get('stack', '4MB'), '-sENVIRONMENT=node,web,worker', '-sASSERTIONS=1', '-Wl,-Map=' + link + '/link.map'], env=env)
shutil.copy(link + '/tmp/emscripten_temp/emcc-01-base.wasm', link + '/base.wasm'); shutil.rmtree(link + '/tmp')
lap('link')
if a.stop_after_link: sys.exit(0)
# 5. plan
plan = run(['node', HERE + '/plan-units.mjs', a.manifest, link + '/base.wasm', '--names', f'{link}/{m["engine"]}.wasm', '--out', out + '/plan'])
print(' '.join(plan.split()))
lap('plan')
# 6. split, optimise each part, strip
dist = out + '/dist'; shutil.rmtree(dist, ignore_errors=True); os.makedirs(dist)
run(['wasm-split'] + FEATURES + ['--multi-split', f'{link}/{m["engine"]}.wasm', '--manifest', out + '/plan/split.manifest', '--out-prefix', dist + '/', '-o', dist + '/primary.wasm', '--export-prefix=%', '--placeholdermap'])
sizes = {}
for f in sorted(glob.glob(dist + '/*.wasm')):
    if a.opt != 'none': run(['wasm-opt'] + FEATURES + [a.opt, f, '-o', f])
    run(['node', HERE + '/wasm-strip-custom.mjs', f, f])
    sizes[os.path.basename(f)[:-5]] = {'raw': os.path.getsize(f), 'gzip': len(gzip.compress(open(f, 'rb').read(), 9))}
shutil.copy(f'{link}/{m["engine"]}.mjs', dist)
lap('split')
report = {'engine': m['engine'], 'units': sizes, 'plan': json.loads(plan), 'steps': steps}
json.dump(report, open(out + '/report.json', 'w'), indent=1)
b = m.get('budgets', {}).get('primaryWasmBytes')
print(json.dumps(sizes))
if b and sizes['primary']['raw'] > b: sys.exit(f'primary {sizes["primary"]["raw"]} over budget {b}')
