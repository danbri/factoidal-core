#!/usr/bin/env python3
"""Packaging controls, plus opt-in real relocated Chrome/Lean/WebGPU smoke.

Default: python3 tests/test_package_web_render.py
Actual: ... --integration --core CHECKOUT --out NEW_DIR --node NODE22
  --playwright PLAYWRIGHT_CORE_MJS --chrome CHROME --font LICENSED_ARIAL
Use --prepare-only, then the printed Node command, then --finish when the
execution environment requires launching the browser directly through Node.
No build, download, package install or source rewrite is performed.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('package_web_render', REPO / 'tools/package-web-render.py')
PKG = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PKG)
NODE = shutil.which('node')


class PackageTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='browser package test ')
        self.base = Path(self.tmp.name)
        self.core = self.base / 'core'
        self.core.mkdir()
        self.source = set()

        def put(name, data=b'// fixture\n', source=True):
            dest = self.core / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            if source:
                self.source.add(name)
        lab, build = PKG.LAB, PKG.BUILD
        for name in PKG.HOST:
            put(lab + '/web-render/' + name)
        for name in PKG.FIXTURES:
            put(lab + '/web-render/fixtures/' + name)
        for name in PKG.SCRIPT:
            put(lab + '/web-render/script-engine/' + name)
        for name in ['gpu_transport.ts', 'render_plan.ts', 'build-font-adapter.sh',
                     'build-web-render.sh', 'web_render_shim.c', 'render_plan_shim.c', 'toolchain-versions.env']:
            put(lab + '/' + name)
        for name in ['font-broker.mjs', 'font-shape.c', 'FONT_DATA.md']:
            put(lab + '/tools/' + name)
        for module in ['WebRender', 'WebRenderRDF', 'WebRenderFont', 'WebDocument', 'RenderPlan']:
            put(lab + '/' + module + '.lean', b'import L4Factoidal.Nested\n')
        put('formal/lean4/L4Factoidal/Nested.lean', b'def nested := 1\n')
        put(lab + '/web_render_shim.c', b'void init(){initialize_WebRenderRDF(1);initialize_WebRenderFont(1);initialize_WebDocument(1);}\n')
        put('formal/lean4/lean-toolchain', b'leanprover/lean4:v4.33.1\n')
        put('LICENSE', b'fixture license\n')
        wasm = b'\x00asm\x01\x00\x00\x00'
        for name in PKG.ENGINES:
            put(build + '/engines/' + name, wasm if name.endswith('.wasm') else b'// fake engine\n', False)
        put(lab + '/.build/script-engine/qjs-wasi-reactor.wasm', wasm, False)
        put(lab + '/web-render/script-engine/quickjs.mjs',
            ("export const QUICKJS_SHA256 = '" + PKG.sha(wasm) + "';\n" +
             "export const QUICKJS_URL = 'https://example.test/pinned.wasm';\n").encode())
        put(lab + '/.build/font-shape', b'not executed in structural fixture', False)
        put('formal/lean4/.lake/build/ir/Fixture.c', b'// generated fixture\n', False)
        generated = {'formal/lean4/.lake/build/ir/Fixture.c'}
        for name in self.source:
            if name.endswith('.lean'):
                output = PKG.generated_path(name)
                put(output, b'// generated fixture\n', False)
                generated.add(output)
        subprocess.run(['git', 'init', '-q', str(self.core)], check=True)
        subprocess.run(['git', '-C', str(self.core), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.core), '-c', 'user.name=Package Test',
                        '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'fixture'], check=True)
        head = PKG.git(self.core, 'rev-parse', 'HEAD').decode().strip()
        self.witness = {'format': 'factoidal-web-render-source-witness-v1', 'commit': head,
            'runtimeObjectWitness': 'wasm32-string-list-v1\n' + '1' * 64 + '\n' + '2' * 64,
            'files': {name: PKG.sha((self.core / name).read_bytes()) for name in sorted(self.source)
                      if name.endswith('.lean') or name in {lab + '/' + n for n in
                        ['build-web-render.sh', 'web_render_shim.c', 'render_plan_shim.c', 'toolchain-versions.env']}
                      or name == 'formal/lean4/lean-toolchain'},
            'generatedC': {name: PKG.sha(b'// generated fixture\n') for name in generated},
            'engines': {build + '/engines/' + name: PKG.sha((self.core / build / 'engines' / name).read_bytes())
                        for name in PKG.ENGINES}}
        self.save_witness()
        self.native_mock = patch.object(PKG, 'native_dependencies', return_value={
            'platform': sys.platform, 'arch': 'arm64', 'libraries': ['libharfbuzz.external', 'libfreetype.external']})
        self.native_mock.start()

    def tearDown(self):
        self.native_mock.stop()
        self.tmp.cleanup()

    def save_witness(self):
        (self.core / PKG.BUILD / 'source-witness.json').write_text(json.dumps(self.witness))

    def build(self, name='bundle', archive=False):
        return PKG.package(self.core, self.base / name, self.base / (name + '.tar.gz') if archive else None)

    def test_deterministic_archive_and_exact_source_inventory(self):
        first = self.build('one', True)
        second = self.build('two', True)
        self.assertEqual(first, second)
        self.assertEqual((self.base / 'one.tar.gz').read_bytes(), (self.base / 'two.tar.gz').read_bytes())
        self.assertEqual((self.base / 'one/lab/web-render/app.mjs').read_bytes(),
                         (self.core / PKG.LAB / 'web-render/app.mjs').read_bytes())
        self.assertFalse(any(p.suffix.lower() in ('.ttf', '.otf') for p in (self.base / 'one').rglob('*')))
        with self.assertRaisesRegex(ValueError, 'already exist'):
            self.build('one')
        with self.assertRaisesRegex(ValueError, 'separate from output'):
            PKG.package(self.core, self.base / 'nested', self.base / 'nested/package.tar.gz')

    def test_missing_transitive_source_witness_refused(self):
        del self.witness['files']['formal/lean4/L4Factoidal/Nested.lean']
        self.save_witness()
        with self.assertRaisesRegex(ValueError, 'omits source dependency'):
            self.build()

    def test_stale_generated_and_source_bytes_refused(self):
        generated = self.core / 'formal/lean4/.lake/build/ir/Fixture.c'
        generated.write_text('tampered')
        with self.assertRaisesRegex(ValueError, 'Stale generatedC'):
            self.build()
        generated.write_bytes(b'// generated fixture\n')
        (self.core / PKG.LAB / 'web-render/app.mjs').write_text('tampered')
        with self.assertRaisesRegex(ValueError, 'Uncommitted source input'):
            self.build()

    def test_missing_generated_dependency_refused(self):
        del self.witness['generatedC'][PKG.BUILD + '/ir/WebDocument.c']
        self.save_witness()
        with self.assertRaisesRegex(ValueError, 'omits generated dependency'):
            self.build()

    def test_unreviewed_initializer_refused(self):
        shim = self.core / PKG.LAB / 'web_render_shim.c'
        shim.write_bytes(shim.read_bytes() + b'void other(){initialize_Unreviewed(1);}\n')
        subprocess.run(['git', '-C', str(self.core), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.core), '-c', 'user.name=Package Test',
                        '-c', 'user.email=test@example.invalid', 'commit', '-qm', 'new initializer'], check=True)
        self.witness['commit'] = PKG.git(self.core, 'rev-parse', 'HEAD').decode().strip()
        self.witness['files'][PKG.LAB + '/web_render_shim.c'] = PKG.sha(shim.read_bytes())
        self.save_witness()
        with self.assertRaisesRegex(ValueError, 'initializer requires review'):
            self.build()

    def test_wrong_source_quickjs_and_unsafe_path_refused(self):
        with self.assertRaisesRegex(ValueError, 'Requested source commit'):
            PKG.package(self.core, self.base / 'bundle', source_commit='0' * 40)
        quickjs = self.core / PKG.LAB / '.build/script-engine/qjs-wasi-reactor.wasm'
        saved = quickjs.read_bytes()
        quickjs.write_bytes(saved + b'x')
        with self.assertRaisesRegex(ValueError, 'QuickJS reactor'):
            self.build()
        quickjs.write_bytes(saved)
        self.witness['generatedC']['../escape'] = '0' * 64
        self.save_witness()
        with self.assertRaisesRegex(ValueError, 'Unsafe source path'):
            self.build()

    @unittest.skipUnless(NODE, 'Node required for actual launcher verification')
    def test_relocated_launcher_verifies_and_refuses_tampering(self):
        self.build()
        relocated = self.base / 'relocated bundle with spaces'
        shutil.copytree(self.base / 'bundle', relocated)
        command = [NODE, str(relocated / 'start.mjs'), '--verify']
        okay = subprocess.run(command, cwd=self.base, text=True, capture_output=True)
        self.assertEqual(okay.returncode, 0, okay.stderr)
        self.assertEqual(json.loads(okay.stdout)['status'], 'PASS')
        (relocated / 'lab/web-render/app.mjs').write_text('changed after packaging')
        changed = subprocess.run(command, cwd=self.base, text=True, capture_output=True)
        self.assertNotEqual(changed.returncode, 0)
        self.assertIn('Bundle integrity failure', changed.stderr)


SMOKE = r'''
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {readFile,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
const [bundle,playwright,chrome,font,output]=process.argv.slice(2),{chromium}=await import(pathToFileURL(playwright));
const server=spawn(process.execPath,[bundle+'/start.mjs','0'],{cwd:output,env:{...process.env,FACTOIDAL_FONT_FILE:font},stdio:['ignore','pipe','pipe']});
let stderr='';server.stderr.on('data',data=>stderr+=data);let browser;
try{
 const origin=await new Promise((resolve,reject)=>{let buffer='';const timer=setTimeout(()=>reject(Error('Bundle server timeout: '+stderr)),30000);server.on('exit',code=>{clearTimeout(timer);reject(Error('Bundle server exited '+code+': '+stderr));});server.stdout.on('data',chunk=>{buffer+=chunk;for(const line of buffer.split('\n')){try{const event=JSON.parse(line);if(event.type==='factoidal-browser-development'){clearTimeout(timer);resolve(event.url);}}catch{}}});});
 browser=await chromium.launch({executablePath:chrome,headless:true,args:['--enable-unsafe-webgpu']});
 const page=await browser.newPage({viewport:{width:1440,height:1050}}),errors=[];page.on('pageerror',error=>errors.push(error.message));await page.goto(origin);await page.waitForFunction(()=>window.webRenderResult?.artifact||window.webRenderResult?.error,{},{timeout:90000});
 assert(!await page.evaluate(()=>window.webRenderResult.error),await page.locator('#status').textContent());
 const initial=await page.evaluate(()=>({url:window.webBrowserState.url,profile:window.webRenderResult.artifact.webRender.profile,font:window.webRenderResult.artifact.webRender.fontResource}));assert.equal(initial.profile,'lean-block-inline-font-data-v1');assert.equal(initial.font.family,'Arial');
 const fixture=await readFile(bundle+'/lab/web-render/fixtures/mvp.html','utf8');assert.equal(await page.locator('#source').inputValue(),fixture);
 async function click(suffix){const link=await page.evaluate(suffix=>window.webRenderResult.artifact.webRender.links.find(row=>row[1].endsWith(suffix)),suffix);assert(link);const point=await page.locator('#output').evaluate((canvas,row)=>{const r=canvas.getBoundingClientRect();return{x:r.left+(row[2]+row[4]/2)*canvas.clientWidth/canvas.width,y:r.top+(row[3]+row[5]/2)*canvas.clientHeight/canvas.height};},link);await page.mouse.click(point.x,point.y);}
 await click('#counter');await page.waitForFunction(()=>window.webRenderResult.artifact.webRender.glyphRuns.some(run=>run.text==='1'),{},{timeout:90000});
 await page.screenshot({path:output+'/relocated-browser.png',fullPage:true});
 await click('/fixtures/default.html');await page.waitForFunction(()=>window.webBrowserState.url.endsWith('/fixtures/default.html')&&!window.webBrowserState.loading,{},{timeout:90000});assert.equal(await page.evaluate(()=>window.webRenderResult.artifact.webRender.profile),'lean-block-inline-ascii-bitmap-v1');await page.locator('#back').click();await page.waitForFunction(()=>window.webBrowserState.url.endsWith('/fixtures/mvp.html')&&!window.webBrowserState.loading,{},{timeout:90000});assert.deepEqual(errors,[]);
 const report={status:'PASS',scope:'Actual relocated bundle page, unchanged source, real Arial/QuickJS/Lean WASM/WebGPU, click mutation and link/Back; no full browser conformance claim.',checks:4,initial};await writeFile(output+'/browser-report.json',JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));
}finally{await browser?.close();server.kill('SIGTERM');}
'''


def integration(args):
    out = args.out.absolute()
    relocated = out / 'Relocated browser with spaces'
    if args.finish:
        first = json.loads((out / 'first/manifest.json').read_text())
    else:
        out.mkdir(parents=True, exist_ok=False)
        first = PKG.package(args.core, out / 'first', out / 'first.tar.gz')
        PKG.package(args.core, out / 'second', out / 'second.tar.gz')
        assert (out / 'first.tar.gz').read_bytes() == (out / 'second.tar.gz').read_bytes()
        with tarfile.open(out / 'first.tar.gz', 'r:gz') as archive:
            archive.extractall(relocated, filter='data')
        subprocess.run([str(args.node), str(relocated / 'start.mjs'), '--verify'], cwd=out, check=True)
        smoke = out / 'smoke.mjs'
        smoke.write_text(SMOKE)
        command = [str(args.node), str(smoke), str(relocated), str(args.playwright), str(args.chrome),
                   str(args.font), str(out)]
        if args.prepare_only:
            print(json.dumps({'status': 'PREPARED', 'browserCommand': command, 'finish': 'Repeat this command with --finish instead of --prepare-only'}))
            return
        subprocess.run(command, cwd=out, check=True, timeout=180)
    browser_report = json.loads((out / 'browser-report.json').read_text())
    assert browser_report['status'] == 'PASS' and browser_report['checks'] == 4
    assert (out / 'first.tar.gz').read_bytes() == (out / 'second.tar.gz').read_bytes()
    target = relocated / 'lab/web-render/app.mjs'
    target.write_bytes(target.read_bytes() + b'\n// tampered\n')
    bad = subprocess.run([str(args.node), str(relocated / 'start.mjs'), '--verify'], cwd=out, capture_output=True)
    assert bad.returncode != 0 and b'Bundle integrity failure' in bad.stderr
    report = {'status': 'PASS', 'archiveSha256': hashlib.sha256((out / 'first.tar.gz').read_bytes()).hexdigest(),
              'packagedFiles': len(first['files']), 'checks': ['byte-identical repeated archives',
              'relocated launcher integrity', 'actual browser smoke', 'tamper refusal'],
              'browserReport': str(out / 'browser-report.json')}
    (out / 'package-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    if '--integration' not in sys.argv:
        unittest.main()
    else:
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument('--integration', action='store_true')
        modes = parser.add_mutually_exclusive_group()
        modes.add_argument('--prepare-only', action='store_true')
        modes.add_argument('--finish', action='store_true')
        for name in ['core', 'out', 'node', 'playwright', 'chrome', 'font']:
            parser.add_argument('--' + name, type=Path, required=True)
        integration(parser.parse_args())
