#!/usr/bin/env python3
"""Package a witnessed local browser development bundle; never compile or fetch.

The bundle retains the lab's relative paths. No HTML/CSS/JS host source is
rewritten. Native font libraries, a licensed Arial file, Node and a WebGPU
browser remain external dependencies. This is not a standalone macOS app.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import struct
import subprocess
import tarfile
import tempfile

LAB = 'labs/demos/foafnaut'
BUILD = LAB + '/.build/web-render'
HOST = ['index.html', 'app.mjs', 'engine.mjs', 'style.css', 'server.mjs',
        'navigation.mjs', 'resource-client.mjs', 'resource-broker.mjs', 'document-client.mjs']
FIXTURES = ['default.html', 'mvp.html', 'boxes.html', 'flow.html', 'links.html', 'graph.nt', 'scripted.html']
SCRIPT = ['session.mjs', 'worker.mjs', 'quickjs.mjs', 'guest.mjs', 'NOTICE']
ENGINES = ['web-render.mjs', 'web-render.wasm', 'render-plan.mjs', 'render-plan.wasm']

LAUNCHER = r'''// Generated local-development launcher. Does not parse page markup.
import {readFile,lstat,realpath} from 'node:fs/promises';
import {dirname,resolve,relative,isAbsolute,sep} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
const root=dirname(fileURLToPath(import.meta.url));
const [major,minor]=process.versions.node.split('.').map(Number);
if(major<22||(major===22&&minor<13))throw Error('Node22.13 or newer is required');
const manifest=JSON.parse(await readFile(resolve(root,'manifest.json'),'utf8'));
if(manifest.format!=='factoidal-browser-development-v1'||!Array.isArray(manifest.files))throw Error('Invalid bundle manifest');
const seen=new Set();
for(const entry of manifest.files){
 if(typeof entry.path!=='string'||entry.path.includes('\\')||entry.path.split('/').some(p=>!p||p==='.'||p==='..')||isAbsolute(entry.path)||seen.has(entry.path))throw Error('Unsafe bundle inventory path');
 seen.add(entry.path);const name=resolve(root,entry.path),info=await lstat(name);
 if(!info.isFile()||info.isSymbolicLink())throw Error('Bundle requires regular files: '+entry.path);
 const rel=relative(root,await realpath(name));if(rel==='..'||rel.startsWith('..'+sep)||isAbsolute(rel))throw Error('Bundle path escapes root');
 const data=await readFile(name);
 if(data.length!==entry.bytes||createHash('sha256').update(data).digest('hex')!==entry.sha256)throw Error('Bundle integrity failure: '+entry.path);
}
if(process.argv[2]==='--verify'){console.log(JSON.stringify({status:'PASS',profile:manifest.format,files:seen.size}));}
else{
 const target=manifest.externalDependencies.fontAdapterTarget;
 if(process.platform!==target.platform||process.arch!==target.arch)throw Error('Native font adapter requires '+target.platform+'/'+target.arch);
 const font=process.env.FACTOIDAL_FONT_FILE;
 if(!font||!(await lstat(font)).isFile())throw Error('Set FACTOIDAL_FONT_FILE to a licensed Arial font file (font is not included)');
 const adapter=resolve(root,'lab/.build/font-shape'),probe=spawnSync(adapter,[font,' ', '16'],{encoding:'utf8',timeout:30000,maxBuffer:1048576});
 if(probe.status!==0)throw Error('Native font adapter or external libraries unavailable: '+(probe.stderr||probe.error?.message||probe.signal));
 const shaped=JSON.parse(probe.stdout);if(shaped.schema!=='factoidal-font-data-v1'||shaped.family?.toLowerCase()!=='arial')throw Error('Font must have the exact Arial family identity');
 const port=Number(process.argv[2]??8099);if(!Number.isInteger(port)||port<0||port>65535)throw Error('Port must be 0..65535');
 const {makeServer}=await import('./lab/web-render/server.mjs'),server=makeServer();
 server.listen(port,'127.0.0.1',()=>console.log(JSON.stringify({type:'factoidal-browser-development',url:'http://127.0.0.1:'+server.address().port+'/',profile:manifest.format,fontSha256:shaped.fontSha256})));
}
'''


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_path(value: str) -> str:
    if not isinstance(value, str) or not value or '\\' in value or any(ord(c) < 32 for c in value):
        raise ValueError('Unsafe source path')
    path = PurePosixPath(value)
    if path.is_absolute() or any(p in ('', '.', '..') for p in value.split('/')):
        raise ValueError('Unsafe source path: ' + value)
    return value


def read_regular(root: Path, name: str) -> bytes:
    path = root / safe_path(name)
    if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):
        raise ValueError('Expected regular file inside checkout: ' + name)
    return path.read_bytes()


def git(root: Path, *args: str) -> bytes:
    return subprocess.check_output(['git', '-C', str(root), *args], stderr=subprocess.PIPE)


def committed(root: Path, name: str, head: str) -> bytes:
    data = read_regular(root, name)
    row = git(root, 'ls-tree', head, '--', safe_path(name)).decode().strip()
    if not re.match(r'^100(?:644|755) blob [0-9a-f]+\t', row) or data != git(root, 'show', head + ':' + name):
        raise ValueError('Uncommitted source input: ' + name)
    return data


def source_closure(root: Path) -> set[str]:
    found: set[str] = set()

    def visit(module: str) -> None:
        if module.startswith('L4Factoidal.'):
            name = 'formal/lean4/' + module.replace('.', '/') + '.lean'
        elif '.' not in module and module not in ('Init', 'Std', 'Lean'):
            name = LAB + '/' + module + '.lean'
        else:
            return
        if name in found:
            return
        found.add(name)
        for imports in re.findall(r'^import\s+([^\r\n]+)', read_regular(root, name).decode(), re.M):
            for child in imports.split('--', 1)[0].split():
                visit(child)
    shim = read_regular(root, LAB + '/web_render_shim.c').decode()
    initializers = set(re.findall(r'initialize_([A-Za-z][A-Za-z0-9_]*)\s*\(\s*1\s*\)', shim))
    if not initializers or not initializers.issubset({'WebRender', 'WebRenderRDF', 'WebRenderFont', 'WebDocument'}):
        raise ValueError('Renderer initializer requires review')
    if not {'WebRenderRDF', 'WebRenderFont', 'WebDocument'}.issubset(initializers):
        raise ValueError('Browser profile requires RDF, font and document initializers')
    for module in sorted(initializers | {'RenderPlan'}):
        visit(module)
    return found


def generated_path(source: str) -> str:
    if source.startswith('formal/lean4/'):
        return 'formal/lean4/.lake/build/ir/' + source[len('formal/lean4/'):].removesuffix('.lean') + '.c'
    return BUILD + '/ir/' + Path(source).stem + '.c'


def native_dependencies(data: bytes, adapter: Path) -> dict:
    if data[:4] == b'\xcf\xfa\xed\xfe':
        cpu = struct.unpack_from('<I', data, 4)[0]
        arch = {0x100000C: 'arm64', 0x1000007: 'x64'}.get(cpu)
        if not arch:
            raise ValueError('Unsupported Mach-O adapter architecture')
        text = subprocess.check_output(['otool', '-L', str(adapter)], text=True)
        libraries = [line.strip().split(' (', 1)[0] for line in text.splitlines()[1:] if line.strip()]
        return {'platform': 'darwin', 'arch': arch, 'libraries': libraries}
    if data[:4] == b'\x7fELF' and data[5] == 1:
        cpu = struct.unpack_from('<H', data, 18)[0]
        arch = {183: 'arm64', 62: 'x64'}.get(cpu)
        if not arch:
            raise ValueError('Unsupported ELF adapter architecture')
        text = subprocess.check_output(['readelf', '-d', str(adapter)], text=True)
        return {'platform': 'linux', 'arch': arch,
                'libraries': re.findall(r'\(NEEDED\).*?\[([^\]]+)\]', text)}
    raise ValueError('Unsupported native font adapter format')


def deterministic_tar(folder: Path, target: Path) -> None:
    with target.open('xb') as raw, gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode='w', format=tarfile.PAX_FORMAT) as tar:
            for path in sorted(p for p in folder.rglob('*') if p.is_file()):
                data = path.read_bytes()
                info = tarfile.TarInfo(path.relative_to(folder).as_posix())
                info.size, info.mode = len(data), path.stat().st_mode & 0o777
                info.mtime, info.uid, info.gid = 0, 0, 0
                info.uname = info.gname = ''
                tar.addfile(info, io.BytesIO(data))


def package(core: Path, out: Path, archive: Path | None = None, source_commit: str | None = None) -> dict:
    core, out = core.resolve(), out.absolute()
    if archive:
        archive = archive.absolute()
        if archive == out or archive.is_relative_to(out) or out.is_relative_to(archive):
            raise ValueError('Archive must be separate from output directory')
    if out.exists() or out.is_symlink() or (archive and (archive.exists() or archive.is_symlink())):
        raise ValueError('Output must not already exist')
    head = git(core, 'rev-parse', 'HEAD').decode().strip()
    if source_commit and source_commit != head:
        raise ValueError('Requested source commit differs from checkout HEAD')
    witness_bytes = read_regular(core, BUILD + '/source-witness.json')
    witness = json.loads(witness_bytes)
    if witness.get('format') != 'factoidal-web-render-source-witness-v1' or witness.get('commit') != head:
        raise ValueError('Missing or wrong-source build witness')
    for group in ('files', 'generatedC', 'engines'):
        if not isinstance(witness.get(group), dict) or not witness[group]:
            raise ValueError('Missing build witness group: ' + group)
        for name, expected in witness[group].items():
            data = committed(core, name, head) if group == 'files' else read_regular(core, name)
            if not isinstance(expected, str) or not re.fullmatch('[0-9a-f]{64}', expected) or sha(data) != expected:
                raise ValueError('Stale ' + group + ' witness: ' + name)
    closure = source_closure(core)
    missing_c = {generated_path(source) for source in closure} - witness['generatedC'].keys()
    if missing_c:
        raise ValueError('Witness omits generated dependency: ' + ', '.join(sorted(missing_c)))
    required = closure | {LAB + '/' + name for name in
        ['build-web-render.sh', 'web_render_shim.c', 'render_plan_shim.c', 'toolchain-versions.env']}
    required.add('formal/lean4/lean-toolchain')
    if not required.issubset(witness['files']):
        raise ValueError('Witness omits source dependency: ' + ', '.join(sorted(required - witness['files'].keys())))
    if not re.match(r'^wasm32-string-list-v1\n[0-9a-f]{64}\n[0-9a-f]{64}', witness.get('runtimeObjectWitness', '')):
        raise ValueError('Verified wasm32 runtime witness required')
    products: dict[str, tuple[bytes, int]] = {}
    inputs: dict[str, str] = {}

    def add_source(name: str, target: str) -> None:
        data = committed(core, name, head)
        inputs[name] = sha(data)
        products[safe_path(target)] = (data, 0o644)

    for name in HOST:
        add_source(LAB + '/web-render/' + name, 'lab/web-render/' + name)
    for name in FIXTURES:
        add_source(LAB + '/web-render/fixtures/' + name, 'lab/web-render/fixtures/' + name)
    for name in SCRIPT:
        add_source(LAB + '/web-render/script-engine/' + name, 'lab/web-render/script-engine/' + name)
    for name in ['gpu_transport.ts', 'render_plan.ts', 'build-font-adapter.sh']:
        add_source(LAB + '/' + name, 'lab/' + name)
    for name in ['font-broker.mjs', 'font-shape.c', 'FONT_DATA.md']:
        add_source(LAB + '/tools/' + name, 'lab/tools/' + name)
    add_source('LICENSE', 'LICENSE')
    for name in ENGINES:
        path = BUILD + '/engines/' + name
        data = read_regular(core, path)
        if witness['engines'].get(path) != sha(data):
            raise ValueError('Missing engine witness: ' + name)
        if name.endswith('.wasm') and data[:8] != b'\x00asm\x01\x00\x00\x00':
            raise ValueError('Invalid WASM engine: ' + name)
        products['lab/.build/web-render/engines/' + name] = (data, 0o644)
    products['lab/.build/web-render/source-witness.json'] = (witness_bytes, 0o644)
    quickjs = read_regular(core, LAB + '/.build/script-engine/qjs-wasi-reactor.wasm')
    bridge = products['lab/web-render/script-engine/quickjs.mjs'][0].decode()
    pin = re.search(r"export const QUICKJS_SHA256 = '([0-9a-f]{64})';", bridge)
    url = re.search(r"export const QUICKJS_URL = '(https://[^']+)';", bridge)
    if not pin or not url or sha(quickjs) != pin[1] or quickjs[:8] != b'\x00asm\x01\x00\x00\x00':
        raise ValueError('QuickJS reactor differs from separately pinned dependency')
    products['lab/.build/script-engine/qjs-wasi-reactor.wasm'] = (quickjs, 0o644)
    adapter = read_regular(core, LAB + '/.build/font-shape')
    target = native_dependencies(adapter, core / LAB / '.build/font-shape')
    products['lab/.build/font-shape'] = (adapter, 0o755)
    products['start.mjs'] = (LAUNCHER.encode(), 0o644)
    readme = '''Factoidal browser development bundle

Verify: node start.mjs --verify
Run: set FACTOIDAL_FONT_FILE to a licensed Arial .ttf file, then node start.mjs 8099
Open the printed loopback URL in a WebGPU-capable browser. Port 0 chooses a free port.

Requires Node22.13 or newer. The included native font adapter requires the target
OS/architecture and external dynamic libraries listed in manifest.json. Those
libraries and the font are NOT bundled. This is not a standalone portable app.
The launcher probes the actual font adapter before binding the loopback server.
The original host modules and fixtures are copied without rewriting. Page markup,
CSS/layout, DOM commands and link picking remain in Lean. Page scripts use the
separately pinned QuickJS reactor; its upstream NOTICE is included.

The Lean source/C/engine witness is verified during packaging. Manifest hashes
identify all packaged bytes and runtime source inputs. The native font adapter
has an exact binary hash and source hash; this packager does not recompile it or
prove that it was built from that source. No font bytes are redistributed.
Checksums detect changed bytes, not authenticity; there is no package signature.
No browser/GPU/conformance pass is implied by creating this bundle.
'''
    products['README.txt'] = (readme.encode(), 0o644)
    manifest = {'format': 'factoidal-browser-development-v1', 'kind': 'development', 'sourceCommit': head,
        'sourceWitnessSha256': sha(witness_bytes), 'runtimeSourceInputs': inputs,
        'builderSha256': sha(Path(__file__).read_bytes()),
        'quickjs': {'url': url[1], 'sha256': pin[1], 'notice': 'lab/web-render/script-engine/NOTICE'},
        'externalDependencies': {'node': '>=22.13', 'browser': 'WebGPU-capable browser',
            'font': {'family': 'Arial', 'environment': 'FACTOIDAL_FONT_FILE', 'bundled': False},
            'fontAdapterTarget': target, 'nativeLibrariesBundled': False},
        'fontAdapter': {'sha256': sha(adapter), 'sourceSha256': inputs[LAB + '/tools/font-shape.c'],
                        'buildCorrespondence': 'Not verified by this packager'},
        'files': [{'path': path, 'bytes': len(data), 'sha256': sha(data), 'mode': format(mode, '04o')}
                  for path, (data, mode) in sorted(products.items())]}
    products['manifest.json'] = ((json.dumps(manifest, sort_keys=True, indent=2) + '\n').encode(), 0o644)
    sums = ''.join(sha(data) + '  ' + path + '\n' for path, (data, _) in sorted(products.items()))
    products['SHA256SUMS'] = (sums.encode(), 0o644)
    out.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix='.browser-package-', dir=out.parent))
    try:
        for path, (data, mode) in products.items():
            dest = stage / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(data)
            dest.chmod(mode)
        if archive:
            archive.parent.mkdir(parents=True, exist_ok=True)
            deterministic_tar(stage, archive)
        stage.rename(out)
    finally:
        if stage.exists():
            shutil.rmtree(stage)
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--core', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--source-commit')
    args = parser.parse_args()
    try:
        result = package(args.core, args.out, args.archive, args.source_commit)
    except (ValueError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        parser.exit(1, str(error) + '\n')
    print(json.dumps({'status': 'PACKAGED', 'profile': result['format'], 'files': len(result['files']),
                      'sourceCommit': result['sourceCommit']}))


if __name__ == '__main__':
    main()
