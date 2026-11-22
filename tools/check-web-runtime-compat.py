#!/usr/bin/env python3
"""Check a fetched web release against runtime inputs and the current browser host.

Run after tools/fetch-builds.sh --set web, then again with --site after Eleventy.
This does not replace fetch-builds' archive verification or the browser tests.
See docs/designissues/2026-11-22-web-runtime-compatibility.md.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess


PAR = 'docs/web/hub/assets/l4/paralliverse'
STAMPED = ('npm/factoidal/l4-assets/version.json', 'npm/factoidal-lean/version.json')
EXTERNAL_INPUTS = {
    'tools/lean-wasm-runtime-closure.py', 'tools/lean-module-closure.py',
    'tools/wasm32-nat-literals.py', 'tools/wasm-size-profile.py',
    'tools/wasmvm/quickjs/prelude.js', 'tools/wasmvm/quickjs/webassembly.js',
    'docs/web/hub/assets/l4/l4factoidal.js',
}
PAR_SOURCES = {
    'formal/lean4/lean-toolchain', 'formal/lean4/Wasm/build-wasm.sh',
    'formal/lean4/Wasm/build-paralliverse.sh', 'formal/lean4/Wasm/paralliverse_shim.c',
    'formal/lean4/Wasm/paralliverse-smoke.mjs', 'tools/wasm32-nat-literals.py',
    'tools/lean-module-closure.py', 'docs/web/hub/paralliverse/worker.mjs',
    'docs/web/hub/paralliverse/gpu.mjs', 'docs/web/hub/paralliverse/word-gpu.mjs',
}
INPUT_ROOTS = ['formal/lean4', 'third_party/hacl', *sorted(EXTERNAL_INPUTS)]
HOST_ROOTS = ['npm/factoidal', 'docs/web/hub/paralliverse', 'docs/.eleventy.js',
              'docs/_includes/hub-app.njk', 'tools/paralliverse-browser-smoke.mjs']
NPM_PASSTHROUGH = ('browser.js', 'api.mjs', 'rdfjs.mjs', 'gdsl.mjs',
                   'lib/', 'l4-assets/', 'store-host/', 'store-http/')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], stderr=subprocess.PIPE)


def facts(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def safe_path(root, name):
    path = PurePosixPath(name)
    require(not path.is_absolute() and '..' not in path.parts and str(path) == name,
            f'Invalid manifest path: {name}')
    result = root / name
    require(not result.is_symlink() and result.resolve().is_relative_to(root.resolve()),
            f'Manifest path escapes the checkout: {name}')
    return result


def check_facts(data, entry, label, size_key='bytes'):
    actual = facts(data)
    require(actual['sha256'] == entry.get('sha256') and actual['bytes'] == entry.get(size_key),
            f'Hash/size mismatch: {label}')
    return actual


def runtime_input(path):
    # The full builder compiles the whole library, including its Lean test modules.
    # Markdown, native harness fixtures and JS host tests do not produce the Wasm.
    if path.startswith('formal/lean4/'):
        return (Path(path).suffix in ('.lean', '.c', '.h') or path in {
            'formal/lean4/lean-toolchain', 'formal/lean4/lake-manifest.json',
            'formal/lean4/Wasm/build-wasm.sh', 'formal/lean4/Wasm/build-paralliverse.sh',
        })
    return (path.startswith(('third_party/hacl/src/', 'third_party/hacl/include/')) or
            path in EXTERNAL_INPUTS)


def tree(root, revision, paths):
    entries = {}
    for record in git(root, 'ls-tree', '-rz', revision, '--', *paths).split(b'\0'):
        if record:
            meta, name = record.decode().split('\t', 1)
            mode, kind, oid = meta.split()
            require(kind == 'blob', f'Expected a tracked file: {name}')
            entries[name] = (mode, oid)
    return entries


def current_source(root, entries):
    # Verify bytes AND mode against HEAD, without one git process per file.
    algorithm = git(root, 'rev-parse', '--show-object-format').decode().strip()
    output = {}
    for name, (mode, oid) in sorted(entries.items()):
        path = safe_path(root, name)
        data = path.read_bytes()
        blob = hashlib.new(algorithm, b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        actual_mode = '100755' if path.stat().st_mode & 0o111 else '100644'
        require(blob == oid and actual_mode == mode, f'Source differs from HEAD: {name}')
        output[name] = facts(data)
    return output


def rendered_path(name):
    if name.startswith('npm/factoidal/'):
        rel = name.removeprefix('npm/factoidal/')
        if any(rel.startswith(p) if p.endswith('/') else rel == p for p in NPM_PASSTHROUGH):
            return name
    if name.startswith('docs/web/hub/paralliverse/') and Path(name).suffix in ('.mjs', '.css'):
        return name.removeprefix('docs/')
    if name == 'docs/web/hub/assets/l4/l4factoidal.js':
        return name.removeprefix('docs/')
    return None


def verify(root, site=None):
    root = root.resolve()
    source = git(root, 'rev-parse', 'HEAD').decode().strip()
    info = json.loads((root / '.factoidal-builds/web.build-info.json').read_text())
    runtime = info.get('source_commit', '')
    require(re.fullmatch(r'[0-9a-f]{40}', runtime), 'Invalid release source_commit')
    require(info.get('source_repo') == 'danbri/factoidal-core' and info.get('set') == 'web',
            'Wrong release source_repo or set')
    tag = (root / '.factoidal-builds/web.tag').read_text().strip()
    require(tag == f'build-{runtime[:12]}-web', 'Release tag/source metadata mismatch')
    git(root, 'merge-base', '--is-ancestor', runtime, source)

    released = {p: v for p, v in tree(root, runtime, INPUT_ROOTS).items() if runtime_input(p)}
    current = {p: v for p, v in tree(root, source, INPUT_ROOTS).items() if runtime_input(p)}
    drift = sorted(p for p in released.keys() | current.keys() if released.get(p) != current.get(p))
    require(not drift, 'Runtime producer drift requires a new build: ' + ', '.join(drift))
    untracked = git(root, 'ls-files', '--others', '--exclude-standard', '-z', '--',
                    *INPUT_ROOTS, *HOST_ROOTS).decode().split('\0')
    require(not any(p and (runtime_input(p) or any(p == h or p.startswith(h + '/') for h in HOST_ROOTS))
                    for p in untracked), 'Untracked runtime or host source')
    producer_facts = current_source(root, current)

    # Keep every installed-file check; fetch-builds has already checked the archive
    # digest, missing/unlisted entries and modes before installing these files.
    files = info['artifacts']['web.tar.gz']['files']
    required = {f'{PAR}/{name}' for name in ('manifest.json', 'paralliverse.mjs', 'paralliverse.wasm')}
    for directory in ('docs/npm/lean', 'docs/web/hub/assets/l4',
                      'npm/factoidal-lean', 'npm/factoidal/l4-assets'):
        required.update(f'{directory}/l4factoidal.{ext}' for ext in ('mjs', 'wasm'))
        if directory != 'docs/web/hub/assets/l4':
            required.add(f'{directory}/l4factoidal.js')
    required.update('docs/web/hub/assets/l4/l4factoidal-core.' + ext for ext in ('js', 'mjs', 'wasm'))
    required.add('docs/npm/lean/version.json')
    require(required <= files.keys(), 'Release manifest is missing required runtime files')
    installed = {}
    for name, entry in sorted(files.items()):
        path = safe_path(root, name)
        installed[name] = check_facts(path.read_bytes(), entry, name, 'size')
        require(path.stat().st_mode & 0o777 == int(entry['mode'], 8), f'Mode mismatch: {name}')

    manifest = json.loads((root / PAR / 'manifest.json').read_text())
    require(manifest.get('sourceCommit') == runtime, 'Paralliverse sourceCommit metadata mismatch')
    require(manifest.get('abiVersion') == 1 and manifest.get('inputLayoutVersion') == 1,
            'Paralliverse ABI/layout mismatch')
    toolchain = (root / 'formal/lean4/lean-toolchain').read_text().strip()
    require(manifest.get('leanToolchain') == toolchain, 'Paralliverse Lean toolchain mismatch')
    lean_version = re.search(r'\bversion (\d+\.\d+\.\d+)\b', info['toolchains']['lean'])
    require(lean_version and toolchain == f'leanprover/lean4:v{lean_version[1]}',
            'Release Lean toolchain mismatch')
    emscripten = info['toolchains']['emscripten']
    require(re.fullmatch(r'\d+\.\d+\.\d+', emscripten) and
            re.search(r'(?<![\d.])' + re.escape(emscripten) + r'(?![\d.])', manifest['emscripten']),
            'Paralliverse Emscripten mismatch')
    modules = subprocess.check_output([
        'python3', str(root / 'tools/lean-module-closure.py'), '--lean-dir',
        str(root / 'formal/lean4'), 'Wasm.ParalliverseHub'], text=True).splitlines()
    expected_sources = PAR_SOURCES | {'formal/lean4/' + module for module in modules}
    require(set(manifest['sources']) == expected_sources, 'Paralliverse source manifest is incomplete or unexpected')
    for name, entry in manifest['sources'].items():
        # These hashes describe the RELEASE checkout. Host files can subsequently
        # change, but must be recorded and tested as the current host below.
        safe_path(root, name)
        check_facts(git(root, 'show', f'{runtime}:{name}'), entry, f'released source {name}')
    require(set(manifest['files']) == {'paralliverse.mjs', 'paralliverse.wasm'},
            'Paralliverse runtime file manifest mismatch')
    for name, entry in manifest['files'].items():
        check_facts((root / PAR / name).read_bytes(), entry, f'Paralliverse {name}')
    patch = manifest['runtimePatch']
    require(patch['scheme'] == 'wasm32-string-list-v1', 'Unexpected runtime patch scheme')
    require(all(re.fullmatch(r'[0-9a-f]{64}', patch[key]) for key in ('sourceSha256', 'objectSha256')),
            'Invalid runtime patch hash')
    witness = '\n'.join((patch['scheme'], patch['sourceSha256'], patch['objectSha256'], '')).encode()
    check_facts(witness, patch['witness'], 'runtime patch witness')

    for name in (*STAMPED, 'docs/npm/lean/version.json'):
        version = json.loads((root / name).read_text())
        full = installed[name.rsplit('/', 1)[0] + '/l4factoidal.wasm']
        require(version.get('stamped') is True and version.get('gitSha') == runtime and
                version.get('leanToolchain') == toolchain and str(version.get('abiVersion')) == '1' and
                version.get('wasmSha256') == full['sha256'] and version.get('wasmBytes') == full['bytes'],
                f'Full runtime metadata mismatch: {name}')
        if name in STAMPED:
            require(version.get('release') == f'danbri/factoidal-builds {tag}' and
                    version.get('builtAt') == info['built_at'] and version.get('releaseRun') == info['run_url'] and
                    version.get('emscripten') == emscripten, f'Stamped release metadata mismatch: {name}')

    hosts = tree(root, source, HOST_ROOTS)
    hosts = {p: v for p, v in hosts.items() if p not in STAMPED}
    host_facts = current_source(root, hosts)
    rendered = {}
    if site is not None:
        for name, entry in {**host_facts, 'docs/web/hub/assets/l4/l4factoidal.js':
                            producer_facts['docs/web/hub/assets/l4/l4factoidal.js']}.items():
            dest = rendered_path(name)
            if dest:
                rendered[dest] = check_facts(safe_path(site, dest).read_bytes(), entry, f'rendered current host {dest}')
        for name, entry in installed.items():
            # docs/npm/lean is the legacy package mirror, not a Pages passthrough.
            dest = name.removeprefix('docs/') if name.startswith('docs/web/hub/assets/l4/') else rendered_path(name)
            if dest:
                check_facts(safe_path(site, dest).read_bytes(), entry, f'rendered runtime {dest}')
        name = STAMPED[0]
        check_facts(safe_path(site, name).read_bytes(), facts((root / name).read_bytes()),
                    f'rendered stamped metadata {name}')

    return {'sourceCommit': source, 'runtimeCommit': runtime, 'releaseTag': tag,
            'runtimeInputs': producer_facts, 'installedFiles': installed,
            'hostSource': host_facts, 'renderedHostFiles': rendered}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--site', type=Path)
    parser.add_argument('--evidence', type=Path, required=True)
    args = parser.parse_args()
    try:
        report = verify(args.repo, args.site)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'web-runtime-compat: {error}\n')
    args.evidence.parent.mkdir(parents=True, exist_ok=True)
    args.evidence.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(f"web-runtime-compat: {len(report['runtimeInputs'])} unchanged runtime inputs; "
          f"{len(report['installedFiles'])} release files verified; "
          f"{len(report['hostSource'])} current host/source files recorded; "
          f"{len(report['renderedHostFiles'])} rendered host files verified")
    print(f"host {report['sourceCommit']}; runtime {report['runtimeCommit']}")


if __name__ == '__main__':
    main()
