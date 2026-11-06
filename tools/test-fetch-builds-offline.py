"""Tiny local fixture archives and check/error paths only: no artifact installs."""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest

SOURCE = Path(__file__).resolve().parent


class Offline(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='offline-fetch-test-')
        self.base = Path(self.temp.name)
        self.repo = self.base / 'repo'
        (self.repo / 'tools').mkdir(parents=True)
        for name in ['fetch-builds.sh', 'verify-builds-release.py', 'stamp-l4-version.mjs']:
            shutil.copy2(SOURCE / name, self.repo / 'tools' / name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        self.git('config', 'commit.gpgsign', 'false')
        (self.repo / 'npm').mkdir()
        (self.repo / 'npm/source.txt').write_text('v1')
        self.git('add', 'npm/source.txt')
        self.git('commit', '-qm', 'fixture')
        self.sha = self.git('rev-parse', 'HEAD').strip()
        self.release = self.base / 'release'
        self.release.mkdir()
        self.path = 'npm/factoidal/l4-assets/fixture.txt'
        self.body = b'tiny fixture, not a binary'
        self.entries = [(self.path, self.body, tarfile.REGTYPE)]
        self.info = {'source_repo': 'danbri/factoidal-core', 'source_commit': self.sha, 'set': 'web',
                     'artifacts': {'web.tar.gz': {'files': {self.path: {
                         'sha256': hashlib.sha256(self.body).hexdigest(), 'size': len(self.body), 'mode': '644'}}}}}
        self.bin = self.base / 'bin'
        self.bin.mkdir()
        self.network = self.base / 'NETWORK_CALLED'
        (self.bin / 'curl').write_text('#!/bin/sh\ntouch "' + str(self.network) + '"\nexit 99\n')
        (self.bin / 'curl').chmod(0o755)
        self.write_archive()

    def tearDown(self):
        self.temp.cleanup()

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.repo), *args], text=True, stderr=subprocess.PIPE)

    def write_archive(self):
        with tarfile.open(self.release / 'web.tar.gz', 'w:gz') as tar:
            for name, body, kind in self.entries:
                entry = tarfile.TarInfo(name)
                entry.type = kind
                entry.size = len(body) if kind == tarfile.REGTYPE else 0
                if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE):
                    entry.linkname = '../../outside'
                tar.addfile(entry, io.BytesIO(body) if kind == tarfile.REGTYPE else None)
        data = (self.release / 'web.tar.gz').read_bytes()
        self.info['artifacts']['web.tar.gz'].update(size=len(data), sha256=hashlib.sha256(data).hexdigest())
        self.write_info()

    def write_info(self):
        (self.release / 'build-info.json').write_text(json.dumps(self.info))

    def run_check(self, *flags, directory=None, check=True):
        result = subprocess.run(['bash', str(self.repo / 'tools/fetch-builds.sh'), '--set', 'web',
            '--commit', self.sha, '--release-dir', str(directory or self.release), *(['--check'] if check else []), *flags],
            cwd=self.repo, env={**os.environ, 'PATH': str(self.bin) + os.pathsep + os.environ['PATH'],
                               'PYTHONOPTIMIZE': '1'}, text=True, capture_output=True, timeout=5)
        self.assertFalse(self.network.exists(), result.stderr)
        return result

    def refused(self):
        result = self.run_check(check=False)
        self.assertNotEqual(result.returncode, 0, result.stderr)
        self.assertFalse((self.repo / '.factoidal-builds').exists())
        self.assertFalse((self.repo / self.path).exists())
        return result

    def test_valid_check_and_dot_prefixed_archive_touch_no_destination(self):
        self.entries[0] = ('./' + self.path, self.body, tarfile.REGTYPE)
        self.write_archive()
        result = self.run_check('--strict')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('verified; would install', result.stderr)
        self.assertFalse((self.repo / self.path).exists())
        self.assertFalse((self.repo / '.factoidal-builds').exists())

    def test_wrong_source_repository_and_set(self):
        for key, value in [('source_commit', '0'*40), ('source_repo', 'other/repo'), ('set', 'native')]:
            with self.subTest(key=key):
                saved = self.info[key]; self.info[key] = value; self.write_info()
                self.refused(); self.info[key] = saved

    def test_outer_archive_size_and_digest(self):
        for key, value in [('size', 0), ('sha256', '0'*64)]:
            with self.subTest(key=key):
                saved = self.info['artifacts']['web.tar.gz'][key]
                self.info['artifacts']['web.tar.gz'][key] = value; self.write_info(); self.refused()
                self.info['artifacts']['web.tar.gz'][key] = saved

    def test_manifest_paths_and_member_traversal(self):
        original = self.info['artifacts']['web.tar.gz']['files']
        for name in ['../outside', '/absolute', 'a//b', 'a/./b', 'a\\b', '.git/config']:
            with self.subTest(name=name):
                self.info['artifacts']['web.tar.gz']['files'] = {name: original[self.path]}
                self.entries = [(name, self.body, tarfile.REGTYPE)]; self.write_archive(); self.refused()
        self.assertFalse((self.base / 'outside').exists())

    def test_unlisted_missing_duplicates_and_bad_file_hash_or_size(self):
        for case in ['unlisted', 'missing', 'duplicate', 'hash', 'size']:
            with self.subTest(case=case):
                self.entries = [(self.path, self.body, tarfile.REGTYPE)]
                row = {'sha256': hashlib.sha256(self.body).hexdigest(), 'size': len(self.body), 'mode': '644'}
                self.info['artifacts']['web.tar.gz']['files'] = {self.path: row}
                if case == 'unlisted': self.entries.append(('unlisted', b'x', tarfile.REGTYPE))
                if case == 'missing': self.info['artifacts']['web.tar.gz']['files']['missing'] = dict(row)
                if case == 'duplicate': self.entries += self.entries[:]
                if case == 'hash': row['sha256'] = '0'*64
                if case == 'size': row['size'] += 1
                self.write_archive(); self.refused()

    def test_archive_links_and_special_files(self):
        for kind in [tarfile.SYMTYPE, tarfile.LNKTYPE, tarfile.FIFOTYPE]:
            with self.subTest(kind=kind):
                self.entries = [(self.path, b'', kind)]; self.write_archive(); self.refused()

    def test_input_symlinks_and_destination_ancestor_symlink(self):
        for name in ['build-info.json', 'web.tar.gz']:
            with self.subTest(name=name):
                path = self.release / name; real = self.base / ('real-' + name)
                path.rename(real); path.symlink_to(real); self.refused(); path.unlink(); real.rename(path)
        linked = self.base / 'linked-release'; linked.symlink_to(self.release, target_is_directory=True)
        self.assertNotEqual(self.run_check(directory=linked).returncode, 0)
        outside = self.base / 'outside-dir'; outside.mkdir()
        (self.repo / 'npm/factoidal').symlink_to(outside, target_is_directory=True)
        self.refused(); self.assertEqual(list(outside.iterdir()), [])

    def test_strict_drift_refuses_but_preview_warns(self):
        (self.repo / 'npm/source.txt').write_text('v2')
        self.git('add', 'npm/source.txt'); self.git('commit', '-qm', 'new source')
        self.assertNotEqual(self.run_check('--strict', check=False).returncode, 0)
        self.assertFalse((self.repo / self.path).exists())
        preview = self.run_check()
        self.assertEqual(preview.returncode, 0, preview.stderr)
        self.assertIn('differs from it', preview.stderr)
        self.assertFalse((self.repo / '.factoidal-builds').exists())

    def test_missing_archive_and_duplicate_manifest_keys(self):
        path = self.release / 'web.tar.gz'; path.unlink(); self.refused(); self.write_archive()
        path = self.release / 'build-info.json'
        text = path.read_text().replace('"set": "web"', '"set":"web","set":"web"')
        path.write_text(text); self.refused()

    def test_nonregular_input_refuses_without_waiting_on_fifo(self):
        path = self.release / 'web.tar.gz'; path.unlink(); os.mkfifo(path)
        self.refused()

    def test_destination_hardlinks_refuse_before_any_write(self):
        for name in [self.path, '.factoidal-builds/web.tag',
                     '.factoidal-builds/web.build-info.json', 'npm/factoidal/l4-assets/version.json']:
            with self.subTest(name=name):
                outside = self.base / 'external-sentinel'
                outside.write_bytes(b'unchanged hardlink sentinel')
                target = self.repo / name
                target.parent.mkdir(parents=True, exist_ok=True)
                os.link(outside, target)
                result = self.run_check(check=False)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('destination hardlink', result.stderr)
                self.assertEqual(outside.read_bytes(), b'unchanged hardlink sentinel')
                self.assertEqual(target.read_bytes(), b'unchanged hardlink sentinel')
                target.unlink(); outside.unlink()
        self.assertFalse((self.repo / self.path).exists())

    def test_full_commit_and_known_history_are_required(self):
        self.assertNotEqual(self.run_check('--release-dir', '').returncode, 0)
        self.assertNotEqual(self.run_check('--commit', self.sha[:12]).returncode, 0)
        tree = self.git('rev-parse', 'HEAD^{tree}').strip()
        unrelated = subprocess.check_output(['git', '-C', str(self.repo), 'commit-tree', tree],
            input='unrelated fixture\n', text=True).strip()
        self.info['source_commit'] = unrelated; self.write_info()
        result = self.run_check('--commit', unrelated)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('not in this checkout', result.stderr)

    def test_check_never_creates_legacy_native_symlinks(self):
        import platform
        machine = {'arm64': 'arm64', 'x86_64': 'x86_64'}.get(platform.machine())
        system = {'Darwin': 'darwin', 'Linux': 'linux'}.get(platform.system())
        if not machine or not system:
            return
        binary = self.repo / f'bin/{system}-{machine}/factoidal'
        binary.parent.mkdir(parents=True); binary.write_text('fixture'); binary.chmod(0o755)
        legacy = self.repo / 'formal/fstar/ocaml-output'; legacy.mkdir(parents=True)
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(list(legacy.iterdir()), [])


if __name__ == '__main__':
    unittest.main()
