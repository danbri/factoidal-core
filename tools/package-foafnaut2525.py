#!/usr/bin/env python3
"""Verify published 988 payloads and package the native development app.

No Lean/native compilation or downloads. --prepare-only installs verified
release bytes at ignored Deno import paths. Packaging can compile the new Deno
HTML host, using a separately checksum-pinned official denort archive.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import plistlib
import shutil
import stat
import subprocess
import tarfile
import tempfile
import zipfile

RELEASE = '98896de16950c39d19f7791d49e31b3c9d5e607c'
DENORT_SHA256 = '81bced8c72f5a1a64d6b1d85ac96aabef5fa559712ac54d2cdfbaa80002246ec'
LAB = 'labs/demos/foafnaut'
RUNTIME = 'docs/web/hub/html-webgpu/runtime/'
HOSTS = ['run_html.ts', 'native_html_engine.ts', 'native_html_document.ts',
         'native_html_session.ts', 'native_window.ts', 'native_preflight.ts',
         'cocoa_surface.ts', 'surface_lifecycle.ts', 'render_plan.ts',
         'gpu_transport.ts', 'ui_cleanup.ts']


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1048576), b''):
            h.update(chunk)
    return h.hexdigest()


def safe_path(value: str) -> str:
    if not isinstance(value, str) or not value or '\\' in value or any(ord(c) < 32 for c in value):
        raise ValueError('Unsafe payload path')
    if PurePosixPath(value).is_absolute() or any(p in ('', '.', '..') for p in value.split('/')):
        raise ValueError('Unsafe payload path: ' + value)
    return value


def inventory(root: Path) -> dict:
    result = {}
    if not root.is_dir() or root.is_symlink():
        raise ValueError('Expected regular payload directory: ' + str(root))
    for path in sorted(root.rglob('*')):
        if path.is_symlink():
            raise ValueError('Payload symlink: ' + str(path))
        if path.is_file():
            result[path.relative_to(root).as_posix()] = {
                'sha256': sha(path), 'size': path.stat().st_size,
                'mode': format(stat.S_IMODE(path.stat().st_mode), 'o')}
        elif not path.is_dir():
            raise ValueError('Nonregular payload entry: ' + str(path))
    return result


def release_info(path: Path, artifact: str) -> tuple[dict, dict]:
    info = json.loads(path.read_text())
    if info.get('source_commit') != RELEASE or info.get('source_repo') != 'danbri/factoidal-core':
        raise ValueError('Expected official factoidal-core 98896de release metadata')
    art = info['artifacts'][artifact]
    if not isinstance(art.get('files'), dict) or not art['files']:
        raise ValueError('Missing release file inventory')
    for name, row in art['files'].items():
        safe_path(name)
        if row.get('mode') not in ('644', '755'):
            raise ValueError('Unexpected published payload mode')
    return info, art


def verify_tree(root: Path, expected: dict) -> dict:
    actual = inventory(root)
    if actual != expected:
        missing = sorted(expected.keys() - actual.keys())
        extra = sorted(actual.keys() - expected.keys())
        changed = sorted(k for k in actual.keys() & expected.keys() if actual[k] != expected[k])
        raise ValueError(f'Published payload mismatch: missing={missing}, extra={extra}, changed={changed}')
    return actual


def extract_release(archive: Path, art: dict, destination: Path) -> None:
    if sha(archive) != art['sha256'] or archive.stat().st_size != art['size']:
        raise ValueError('Release archive hash/size mismatch')
    with tarfile.open(archive, 'r:gz') as tar:
        seen = set()
        for member in tar:
            name = member.name.rstrip('/')
            if name.startswith('./'):
                name = name[2:]
            safe_path(name)
            if name in seen:
                raise ValueError('Duplicate archive path')
            seen.add(name)
            target = destination / name
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if not member.isfile() or name not in art['files']:
                raise ValueError('Unlisted/nonregular archive entry: ' + name)
            row = art['files'][name]
            if member.size != row['size'] or format(member.mode & 0o7777, 'o') != row['mode']:
                raise ValueError('Archive mode/size differs: ' + name)
            target.parent.mkdir(parents=True, exist_ok=True)
            with tar.extractfile(member) as source, target.open('xb') as output:
                shutil.copyfileobj(source, output)
            target.chmod(int(row['mode'], 8))
    verify_tree(destination, art['files'])


def copy_verified(source: Path, target: Path, row: dict) -> None:
    if source.is_symlink() or not source.is_file() or sha(source) != row['sha256'] or source.stat().st_size != row['size']:
        raise ValueError('Release input changed before copy: ' + str(source))
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
    target.chmod(int(row['mode'], 8))
    if sha(target) != row['sha256']:
        raise ValueError('Release copy mismatch')


def host_hashes(root: Path) -> dict:
    lab = root / LAB
    sources = {LAB + '/' + name: sha(lab / name) for name in HOSTS}
    sources.update({LAB + '/native-html/' + name: sha(lab / 'native-html' / name)
                    for name in ['default.html', 'next.html']})
    sources['tools/package-foafnaut2525.py'] = sha(root / 'tools/package-foafnaut2525.py')
    return sources


def unchanged_inputs(root: Path, source_hashes: dict, installed: dict) -> None:
    if host_hashes(root) != source_hashes:
        raise ValueError('Host source changed during Deno compile; refusing provenance')
    for name, row in installed.items():
        path = root / name
        if path.is_symlink() or not path.is_file() or sha(path) != row['sha256'] or path.stat().st_size != row['size']:
            raise ValueError('Published runtime changed during Deno compile: ' + name)


def prepare(root: Path, args: argparse.Namespace, temp: Path) -> dict:
    _, native = release_info(args.native_build_info, 'foafnaut-darwin-arm64.tar.gz')
    _, web = release_info(args.web_build_info, 'foafnaut-web.tar.gz')
    if args.native_archive:
        if sha(args.native_archive) != native['sha256'] or args.native_archive.stat().st_size != native['size']:
            raise ValueError('Native archive hash/size mismatch')
    native_files = {}
    for name, row in native['files'].items():
        if not name.startswith('foafnaut/'):
            raise ValueError('Unexpected native package root')
        native_files[name[len('foafnaut/'):]] = row
    verify_tree(args.native_package, native_files)
    extracted = temp / 'web'
    extracted.mkdir()
    extract_release(args.web_archive, web, extracted)
    lab = root / LAB
    installed = {}
    for name, row in web['files'].items():
        if name.startswith(RUNTIME):
            target = lab / '.build/native-html/runtime' / name[len(RUNTIME):]
            copy_verified(extracted / name, target, row)
            installed[target.relative_to(root).as_posix()] = row
    for name in ['render-plan.mjs', 'render-plan.wasm']:
        source = RUNTIME + name
        target = lab / '.build/engines' / name
        copy_verified(extracted / source, target, web['files'][source])
        installed[target.relative_to(root).as_posix()] = web['files'][source]
    dylib = 'libnative-window.dylib'
    copy_verified(args.native_package / dylib, lab / '.build/native' / dylib, native_files[dylib])
    installed[(lab / '.build/native' / dylib).relative_to(root).as_posix()] = native_files[dylib]
    for name in ['web-render.mjs', 'web-render.wasm', 'render-plan.mjs', 'render-plan.wasm']:
        if RUNTIME + name not in web['files']:
            raise ValueError('Required published runtime missing: ' + name)
    receipt = {'profile': 'factoidal-native-html-release-inputs-v1', 'engineSourceCommit': RELEASE,
               'webArchiveSha256': web['sha256'], 'nativeArchiveSha256': native['sha256'],
               'nativeFiles': native_files, 'installed': installed,
               'nativeBuildInfoSha256': sha(args.native_build_info),
               'webBuildInfoSha256': sha(args.web_build_info)}
    (lab / '.build/native-html/release-inputs.json').write_text(json.dumps(receipt, indent=2) + '\n')
    shutil.copy2(args.native_build_info, lab / '.build/native-html/native-build-info.json')
    shutil.copy2(args.web_build_info, lab / '.build/native-html/web-build-info.json')
    return receipt


LAUNCHER = '''#!/bin/sh
set -eu
CONTENTS_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd -P)
cd "$CONTENTS_DIR/Resources/foafnaut"
if [ "${1-}" = "--html-default" ]; then
  shift
  exec ./native-webgpu-html-darwin-arm64 --html "$CONTENTS_DIR/Resources/native-html/default.html" --follow-links "$@"
fi
case "${1-}" in
  --html|--url) exec ./native-webgpu-html-darwin-arm64 "$@" ;;
esac
DEFAULT
'''


def package(root: Path, args: argparse.Namespace, receipt: dict, temp: Path) -> dict:
    output = args.output.resolve()
    if output.exists() or output.is_relative_to(root) and not output.is_relative_to(root / LAB / '.build'):
        raise ValueError('Output must be new and outside tracked source')
    if not args.denort_archive or sha(args.denort_archive) != DENORT_SHA256:
        raise ValueError('Provide the checksum-pinned official Deno 2.9.4 ARM64 denort zip')
    if shutil.disk_usage(output.parent).free < 3 * 1024**3:
        raise ValueError('Native packaging requires at least 3 GiB free before Deno compile')
    version = subprocess.check_output([args.deno, '--version'], text=True)
    if not version.startswith('deno 2.9.4 '):
        raise ValueError('Deno compiler must be pinned to 2.9.4')
    with zipfile.ZipFile(args.denort_archive) as archive:
        if archive.namelist() != ['denort']:
            raise ValueError('Unexpected denort archive inventory')
        denort = temp / 'denort'
        denort.write_bytes(archive.read('denort'))
        denort.chmod(0o755)
    lab = root / LAB
    binary = temp / 'native-webgpu-html-darwin-arm64'
    command = [args.deno, 'compile', '--no-check', '--no-config', '--no-npm', '--node-modules-dir=none',
               '--unstable-webgpu', '--unstable-ffi', '--allow-read', '--allow-net', '--allow-ffi',
               '--include', str(lab / '.build/native-html/runtime/web-render.wasm'),
               '--include', str(lab / '.build/engines/render-plan.wasm'),
               '--include', str(lab / 'native-html/default.html'),
               '--include', str(lab / 'native-html/next.html'),
               '--output', str(binary), str(lab / 'run_html.ts')]
    environment = {**os.environ, 'DENORT_BIN': str(denort)}
    host_sources = host_hashes(root)
    subprocess.run(command, cwd=root, env=environment, check=True)
    unchanged_inputs(root, host_sources, receipt['installed'])
    # Recheck the original package immediately before copying the release bytes.
    verify_tree(args.native_package, receipt['nativeFiles'])
    output.mkdir()
    provenance = output / 'provenance'
    provenance.mkdir()
    shutil.copy2(args.native_build_info, provenance / 'native-build-info.json')
    shutil.copy2(args.web_build_info, provenance / 'web-build-info.json')
    shutil.copy2(root / 'tools/package-foafnaut2525.py', provenance / 'package-foafnaut2525.py')
    report = {'profile': 'foafnaut2525-native-development-v1', 'engineSourceCommit': RELEASE,
              'hostBaseCommit': subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip(),
              'hostSourceSha256': host_sources, 'releaseInputs': receipt,
              'denortArchiveSha256': DENORT_SHA256, 'denoVersion': version,
              'htmlExecutableSha256': sha(binary), 'compileCommand': command,
              'permissions': ['read:all', 'net:all', 'ffi:all'], 'apps': []}
    for mode in ['foaf', 'html'] if args.html_shortcut else ['foaf']:
        name = 'foafnaut2525' if mode == 'foaf' else 'foafnaut2525-html'
        app = output / (name + '.app')
        contents = app / 'Contents'
        (contents / 'MacOS').mkdir(parents=True)
        resources = contents / 'Resources'
        resources.mkdir()
        shutil.copytree(args.native_package, resources / 'foafnaut', copy_function=shutil.copy2)
        verify_tree(resources / 'foafnaut', receipt['nativeFiles'])
        shutil.copy2(binary, resources / 'foafnaut' / binary.name)
        shutil.copytree(lab / 'native-html', resources / 'native-html')
        default = ('exec ./native-webgpu-ui-darwin-arm64 --demo foafnaut "$@"' if mode == 'foaf' else
                   'exec ./native-webgpu-html-darwin-arm64 --html "$CONTENTS_DIR/Resources/native-html/default.html" --follow-links "$@"')
        launcher = contents / 'MacOS/foafnaut2525'
        launcher.write_text(LAUNCHER.replace('DEFAULT', default))
        launcher.chmod(0o755)
        plist = {'CFBundleExecutable': 'foafnaut2525', 'CFBundleIdentifier': 'org.factoidal.' + name + '.development',
                 'CFBundleName': name, 'CFBundleDisplayName': name, 'CFBundlePackageType': 'APPL',
                 'CFBundleInfoDictionaryVersion': '6.0', 'CFBundleShortVersionString': '0.1.0',
                 'CFBundleVersion': '1', 'NSHighResolutionCapable': True,
                 'FactoidalEngineSourceCommit': RELEASE}
        (contents / 'Info.plist').write_bytes(plistlib.dumps(plist, sort_keys=True))
        subprocess.run(['/bin/sh', '-n', str(launcher)], check=True)
        subprocess.run(['/usr/bin/plutil', '-lint', str(contents / 'Info.plist')], check=True)
        # Original package bytes remain covered by the original manifest, and the
        # extra executable is covered by this separate development-host inventory.
        (resources / 'development-provenance.json').write_text(json.dumps(report, indent=2) + '\n')
        report['apps'].append({'path': app.name, 'defaultMode': mode, 'files': inventory(app)})
    (output / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--native-package', type=Path, required=True)
    parser.add_argument('--native-build-info', type=Path, required=True)
    parser.add_argument('--native-archive', type=Path)
    parser.add_argument('--web-archive', type=Path, required=True)
    parser.add_argument('--web-build-info', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--html-shortcut', action='store_true')
    parser.add_argument('--denort-archive', type=Path)
    parser.add_argument('--deno', default='deno')
    args = parser.parse_args()
    if not args.prepare_only and args.output is None:
        parser.error('--output is required for packaging')
    root = args.root.resolve()
    with tempfile.TemporaryDirectory(prefix='foafnaut2525-package-') as temporary:
        receipt = prepare(root, args, Path(temporary))
        report = receipt if args.prepare_only else package(root, args, receipt, Path(temporary))
    print(json.dumps({'status': 'PASS', 'profile': report['profile'],
                      'engineSourceCommit': RELEASE, 'output': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
