#!/usr/bin/env python3
"""Verify a release into private staging; never write to its destination root."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import tarfile


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate manifest key: ' + key)
        result[key] = value
    return result


def regular(path):
    handle = os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), 'rb')
    try:
        require(stat.S_ISREG(os.fstat(handle.fileno()).st_mode), 'input is not a regular file')
    except BaseException:
        handle.close()
        raise
    return handle


def safe(name):
    require(isinstance(name, str) and name and '\\' not in name and
            not any(ord(c) < 32 for c in name), 'unsafe release path')
    require(not PurePosixPath(name).is_absolute() and
            not any(p in ('', '.', '..') for p in name.split('/')), 'unsafe release path: ' + name)
    require(name.split('/')[0] not in ('.git', '.factoidal-builds') and name not in (
        'tools/fetch-builds.sh', 'tools/verify-builds-release.py', 'tools/stamp-l4-version.mjs'),
        'release may not replace installer or Git metadata')
    return name


def preflight(root, names):
    for name in names:
        parts = name.split('/')
        current = root
        for index, part in enumerate(parts):
            current = current / part
            require(not current.is_symlink(), 'destination symlink: ' + str(current))
            if current.exists():
                require(current.is_file() if index == len(parts) - 1 else current.is_dir(),
                        'unexpected destination type: ' + str(current))
                if index == len(parts) - 1:
                    require(current.lstat().st_nlink == 1, 'destination hardlink: ' + str(current))


def verify(info_path, archive_path, stage, selected, expected, destination, manifest_copy):
    require(selected in ('web', 'foafnaut-web', 'linux-x86_64', 'darwin-arm64'), 'unknown set')
    require(re.fullmatch(r'[0-9a-f]{12}|[0-9a-f]{40}', expected) is not None, 'bad expected source')
    require(not Path(info_path).parent.is_symlink() and not Path(archive_path).parent.is_symlink(),
            'release input directory is a symlink')
    with regular(info_path) as source:
        info_bytes = source.read()
    info = json.loads(info_bytes, object_pairs_hook=unique_object)
    commit = info.get('source_commit', '')
    require(isinstance(commit, str) and re.fullmatch(r'[0-9a-f]{40}', commit) is not None and
            commit.startswith(expected), 'release source mismatch')
    require(info.get('source_repo') == 'danbri/factoidal-core', 'release repository mismatch')
    require(info.get('set') == selected, 'release set mismatch')
    artifact = info['artifacts'][selected + '.tar.gz']
    require(type(artifact['size']) is int and artifact['size'] >= 0, 'bad archive size')
    require(isinstance(artifact['sha256'], str) and re.fullmatch(r'[0-9a-f]{64}', artifact['sha256']), 'bad archive digest')
    listed = artifact['files']
    require(isinstance(listed, dict) and listed, 'empty or invalid file inventory')
    directories = {''}
    for name, row in listed.items():
        safe(name)
        require(type(row['size']) is int and row['size'] >= 0, 'bad file size')
        require(isinstance(row['sha256'], str) and re.fullmatch(r'[0-9a-f]{64}', row['sha256']), 'bad file digest')
        mode = row.get('mode', '644')
        require(isinstance(mode, str) and re.fullmatch(r'0?[0-7]{3}', mode), 'bad file mode')
        for parent in PurePosixPath(name).parents:
            if str(parent) != '.':
                require(str(parent) not in listed, 'file is also a parent directory')
                directories.add(str(parent))
    destination = Path(destination)
    preflight(destination, list(listed) + [f'.factoidal-builds/{selected}.tag',
        f'.factoidal-builds/{selected}.build-info.json'] +
        (['npm/factoidal/l4-assets/version.json', 'npm/factoidal-lean/version.json'] if selected == 'web' else []))
    seen = set()
    with regular(archive_path) as archive:
        require(os.fstat(archive.fileno()).st_size == artifact['size'], 'archive size mismatch')
        digest = hashlib.sha256()
        for chunk in iter(lambda: archive.read(1 << 20), b''):
            digest.update(chunk)
        require(digest.hexdigest() == artifact['sha256'], 'archive digest mismatch')
        archive.seek(0)
        with tarfile.open(fileobj=archive, mode='r:gz') as tar:
            for member in tar:
                name = member.name
                if name.startswith('./'):
                    name = name[2:]
                if name == '.':
                    name = ''
                if name:
                    safe(name)
                require(name not in seen, 'duplicate archive path: ' + name)
                seen.add(name)
                if member.isdir():
                    require(name in directories, 'unlisted directory: ' + name)
                    continue
                require(member.isfile() and name in listed, 'unlisted or nonregular member: ' + name)
                row = listed[name]
                require(member.size == row['size'], 'file size mismatch: ' + name)
                target = Path(stage) / name
                target.parent.mkdir(parents=True, exist_ok=True)
                digest = hashlib.sha256()
                with tar.extractfile(member) as source, target.open('xb') as output:
                    for chunk in iter(lambda: source.read(1 << 20), b''):
                        digest.update(chunk)
                        output.write(chunk)
                require(digest.hexdigest() == row['sha256'], 'file digest mismatch: ' + name)
                target.chmod(int(row.get('mode', '644'), 8))
    require(set(listed).issubset(seen), 'missing manifest files: ' + ', '.join(sorted(set(listed) - seen)[:5]))
    Path(manifest_copy).write_bytes(info_bytes)
    print(f'verified {len(listed)} files from {commit[:12]}', file=sys.stderr)


if __name__ == '__main__':
    try:
        verify(*sys.argv[1:])
    except (ValueError, KeyError, TypeError, OSError, tarfile.TarError) as error:
        print('fetch-builds verification: ' + str(error), file=sys.stderr)
        sys.exit(1)
