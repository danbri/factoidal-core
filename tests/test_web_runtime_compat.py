#!/usr/bin/env python3
"""Refusal tests for released Wasm plus the current browser host; no build/download."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


REPO = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('web_runtime_compat', REPO / 'tools/check-web-runtime-compat.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


class CompatibilityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='web runtime compatibility ')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / 'repo'
        self.root.mkdir()
        self.put('.gitignore', '.factoidal-builds/\ndocs/npm/lean/\n'
                 'docs/web/hub/assets/l4/*.mjs\ndocs/web/hub/assets/l4/*.wasm\n'
                 'docs/web/hub/assets/l4/l4factoidal-core.js\n'
                 'docs/web/hub/assets/l4/paralliverse/\nnpm/factoidal-lean/\n'
                 'npm/factoidal/l4-assets/\n')
        for path in CHECK.PAR_SOURCES | CHECK.EXTERNAL_INPUTS:
            self.put(path, '// source fixture\n')
        self.put('tools/lean-module-closure.py', (REPO / 'tools/lean-module-closure.py').read_bytes())
        self.put('formal/lean4/lean-toolchain', 'leanprover/lean4:v4.33.1\n')
        self.put('formal/lean4/Wasm/ParalliverseHub.lean', 'import L4Factoidal.Demo\n')
        self.put('formal/lean4/L4Factoidal/Demo.lean', 'def value : Nat := 1\n')
        self.put('formal/lean4/Wasm/l4_shim.c', 'int fixture(void) { return 1; }\n')
        self.put('formal/lean4/lakefile.lean', '-- Lake fixture\n')
        self.put('third_party/hacl/src/fixture.c', 'int fixture(void) { return 1; }\n')
        self.put('third_party/hacl/include/fixture.h', 'int fixture(void);\n')
        self.put('npm/factoidal/lib/gdsl-gpu.mjs', 'export const value = 1;\n')
        self.put('npm/factoidal/browser.js', '// browser host\n')
        self.put('npm/factoidal/README.md', 'Host documentation.\n')
        self.put('docs/.eleventy.js', '// build configuration\n')
        self.put('docs/web/hub/paralliverse/app.mjs', '// page host\n')
        self.put('docs/web/hub/paralliverse/index.njk', 'Page template\n')
        self.put('docs/web/hub/gdsl-app/app.mjs', '// app host\n')
        self.git('init', '-q')
        self.commit()
        self.release = self.git('rev-parse', 'HEAD').strip()

        # Deliberately tiny synthetic artifact files. The real browser run, not
        # this fixture, establishes runtime behaviour. These tests pin provenance.
        self.info = {'source_repo': 'danbri/factoidal-core', 'source_commit': self.release,
                     'set': 'web', 'built_at': '2026-11-22T00:00:00Z', 'run_url': 'https://example.test/run',
                     'toolchains': {'lean': 'Lean (version 4.33.1, test)', 'emscripten': '6.0.8'},
                     'artifacts': {'web.tar.gz': {'files': {}}}}
        self.tag = f'build-{self.release[:12]}-web'
        for directory in ('docs/npm/lean', 'docs/web/hub/assets/l4',
                          'npm/factoidal-lean', 'npm/factoidal/l4-assets'):
            for ext in ('mjs', 'wasm'):
                self.artifact(f'{directory}/l4factoidal.{ext}', b'fixture ' + ext.encode())
            if directory != 'docs/web/hub/assets/l4':
                self.artifact(f'{directory}/l4factoidal.js', b'fixture loader')
        for ext in ('js', 'mjs', 'wasm'):
            self.artifact('docs/web/hub/assets/l4/l4factoidal-core.' + ext, b'fixture core ' + ext.encode())
        for name in ('paralliverse.mjs', 'paralliverse.wasm'):
            self.artifact(f'{CHECK.PAR}/{name}', b'fixture standalone ' + name.encode())
        self.artifact('docs/npm/lean/LICENSE', b'fixture license')
        sources = CHECK.PAR_SOURCES | {'formal/lean4/Wasm/ParalliverseHub.lean', 'formal/lean4/L4Factoidal/Demo.lean'}
        witness = ('wasm32-string-list-v1\n' + 'a' * 64 + '\n' + 'b' * 64 + '\n').encode()
        self.manifest = {
            'sourceCommit': self.release, 'abiVersion': 1, 'inputLayoutVersion': 1,
            'leanToolchain': 'leanprover/lean4:v4.33.1', 'emscripten': 'emcc 6.0.8 fixture',
            'sources': {p: CHECK.facts((self.root / p).read_bytes()) for p in sources},
            'runtimePatch': {'scheme': 'wasm32-string-list-v1', 'sourceSha256': 'a' * 64,
                             'objectSha256': 'b' * 64, 'witness': CHECK.facts(witness)},
            'files': {p: CHECK.facts((self.root / CHECK.PAR / p).read_bytes())
                      for p in ('paralliverse.mjs', 'paralliverse.wasm')},
        }
        self.save_manifest()
        full = CHECK.facts((self.root / 'npm/factoidal/l4-assets/l4factoidal.wasm').read_bytes())
        self.version = {'stamped': True, 'gitSha': self.release, 'abiVersion': '1',
                        'leanToolchain': 'leanprover/lean4:v4.33.1', 'emscripten': '6.0.8',
                        'wasmSha256': full['sha256'], 'wasmBytes': full['bytes'],
                        'release': 'danbri/factoidal-builds ' + self.tag,
                        'builtAt': self.info['built_at'], 'releaseRun': self.info['run_url']}
        for path in CHECK.STAMPED:
            self.put(path, json.dumps(self.version))
        self.artifact('docs/npm/lean/version.json', json.dumps(self.version).encode())
        self.put('.factoidal-builds/web.tag', self.tag + '\n')
        self.save_info()

    def put(self, name, data):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data.encode() if isinstance(data, str) else data)

    def git(self, *args):
        return subprocess.check_output(['git', '-C', str(self.root), *args], text=True, stderr=subprocess.PIPE)

    def commit(self):
        self.git('add', '.')
        self.git('-c', 'user.name=Test', '-c', 'user.email=test@example.test', 'commit', '-qm', 'fixture')

    def artifact(self, name, data):
        self.put(name, data)
        entry = CHECK.facts(data)
        self.info['artifacts']['web.tar.gz']['files'][name] = {
            'sha256': entry['sha256'], 'size': entry['bytes'], 'mode': '644'}

    def save_info(self):
        self.put('.factoidal-builds/web.build-info.json', json.dumps(self.info))

    def save_manifest(self):
        self.artifact(CHECK.PAR + '/manifest.json', json.dumps(self.manifest).encode())
        self.save_info()

    def render(self):
        site = Path(self.tmp.name) / 'site'
        report = CHECK.verify(self.root)
        files = {**report['hostSource'], **report['installedFiles'],
                 'docs/web/hub/assets/l4/l4factoidal.js': {}, CHECK.STAMPED[0]: {}}
        for name in files:
            dest = CHECK.rendered_path(name)
            if name in report['installedFiles'] and name.startswith('docs/'):
                dest = name.removeprefix('docs/')
            if dest:
                target = site / dest
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(self.root / name, target)
        return site

    def test_host_only_change_is_accepted_and_current_module_is_exercised(self):
        name = 'npm/factoidal/lib/gdsl-gpu.mjs'
        self.put(name, 'export const value = 2;\n')
        self.put('npm/factoidal/README.md', 'Updated host documentation.\n')
        self.put('tests/host.test.mjs', '// new host test\n')
        self.put('formal/lean4/PORT_NOTES.md', 'Updated source notes.\n')
        self.put('formal/lean4/Harness/TestData/example.ttl', '<s> <p> <o> .\n')
        self.put('docs/web/hub/gdsl-app/app.mjs', '// current independent app host\n')
        self.commit()
        site = self.render()
        report = CHECK.verify(self.root, site)
        self.assertNotEqual(report['sourceCommit'], report['runtimeCommit'])
        self.assertEqual(report['runtimeCommit'], self.release)
        self.assertEqual(report['hostSource'][name], CHECK.facts(b'export const value = 2;\n'))
        self.assertEqual(report['renderedHostFiles'][name], report['hostSource'][name])
        self.assertEqual(report['renderedHostFiles']['web/hub/gdsl-app/app.mjs'],
                         CHECK.facts(b'// current independent app host\n'))
        subprocess.run(['node', '--input-type=module', '-e',
                        'import assert from "node:assert/strict"; const m = await import(' +
                        json.dumps((site / name).as_uri()) + '); assert.equal(m.value, 2);'], check=True)

    def test_lean_drift_is_refused(self):
        self.put('formal/lean4/L4Factoidal/Demo.lean', 'def value : Nat := 2\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*Demo.lean'):
            CHECK.verify(self.root)

    def test_c_drift_is_refused(self):
        self.put('formal/lean4/Wasm/l4_shim.c', 'int fixture(void) { return 2; }\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*l4_shim.c'):
            CHECK.verify(self.root)

    def test_build_tool_drift_outside_formal_is_refused(self):
        self.put('tools/lean-wasm-runtime-closure.py', '# changed tool\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*lean-wasm-runtime-closure'):
            CHECK.verify(self.root)

    def test_build_script_drift_is_refused(self):
        self.put('formal/lean4/Wasm/build-wasm.sh', '# changed build flags\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*build-wasm.sh'):
            CHECK.verify(self.root)

    def test_embedded_javascript_drift_is_refused(self):
        self.put('tools/wasmvm/quickjs/prelude.js', '// changed embedded bytes\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*prelude.js'):
            CHECK.verify(self.root)

    def test_vendored_header_drift_is_refused(self):
        self.put('third_party/hacl/include/fixture.h', 'int changed(void);\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*fixture.h'):
            CHECK.verify(self.root)

    def test_new_runtime_source_is_refused(self):
        self.put('formal/lean4/L4Factoidal/New.lean', 'def newValue := 1\n')
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*New.lean'):
            CHECK.verify(self.root)

    def test_removed_runtime_source_is_refused(self):
        (self.root / 'formal/lean4/L4Factoidal/Demo.lean').unlink()
        self.commit()
        with self.assertRaisesRegex(ValueError, 'Runtime producer drift.*Demo.lean'):
            CHECK.verify(self.root)

    def test_dirty_producer_is_refused(self):
        self.put('formal/lean4/Wasm/l4_shim.c', '// uncommitted change\n')
        with self.assertRaisesRegex(ValueError, 'Source differs from HEAD.*l4_shim.c'):
            CHECK.verify(self.root)

    def test_dirty_host_is_refused(self):
        self.put('npm/factoidal/lib/gdsl-gpu.mjs', 'export const value = 3;\n')
        with self.assertRaisesRegex(ValueError, 'Source differs from HEAD.*gdsl-gpu.mjs'):
            CHECK.verify(self.root)

    def test_untracked_host_is_refused(self):
        self.put('npm/factoidal/lib/new.mjs', '// untracked host\n')
        with self.assertRaisesRegex(ValueError, 'Untracked runtime or host'):
            CHECK.verify(self.root)

    def test_stale_rendered_host_is_refused(self):
        site = self.render()
        (site / 'npm/factoidal/lib/gdsl-gpu.mjs').write_text('export const value = 0;\n')
        with self.assertRaisesRegex(ValueError, 'Hash/size mismatch: rendered current host'):
            CHECK.verify(self.root, site)

    def test_release_tag_mismatch_is_refused(self):
        self.put('.factoidal-builds/web.tag', 'build-000000000000-web\n')
        with self.assertRaisesRegex(ValueError, 'Release tag/source metadata mismatch'):
            CHECK.verify(self.root)

    def test_manifest_commit_mismatch_survives_consistent_archive_hash(self):
        self.manifest['sourceCommit'] = 'a' * 40
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'sourceCommit metadata mismatch'):
            CHECK.verify(self.root)

    def test_missing_manifest_source_is_refused(self):
        del self.manifest['sources']['tools/wasm32-nat-literals.py']
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'source manifest is incomplete'):
            CHECK.verify(self.root)

    def test_manifest_source_hash_mismatch_is_refused(self):
        self.manifest['sources']['tools/wasm32-nat-literals.py']['sha256'] = 'f' * 64
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'Hash/size mismatch: released source'):
            CHECK.verify(self.root)

    def test_paralliverse_artifact_hash_remains_checked(self):
        self.artifact(CHECK.PAR + '/paralliverse.wasm', b'a different runtime')
        self.save_info()
        with self.assertRaisesRegex(ValueError, 'Hash/size mismatch: Paralliverse paralliverse.wasm'):
            CHECK.verify(self.root)

    def test_all_release_artifact_hashes_remain_checked(self):
        self.put('docs/npm/lean/LICENSE', 'tampered ancillary artifact')
        with self.assertRaisesRegex(ValueError, 'Hash/size mismatch: docs/npm/lean/LICENSE'):
            CHECK.verify(self.root)

    def test_stamped_metadata_mismatch_is_refused(self):
        self.version['gitSha'] = 'f' * 40
        self.put(CHECK.STAMPED[0], json.dumps(self.version))
        with self.assertRaisesRegex(ValueError, 'Full runtime metadata mismatch'):
            CHECK.verify(self.root)

    def test_toolchain_metadata_mismatch_is_refused(self):
        self.manifest['leanToolchain'] = 'leanprover/lean4:v4.30.0'
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, 'Paralliverse Lean toolchain mismatch'):
            CHECK.verify(self.root)

    def test_current_host_in_release_source_manifest_may_change(self):
        self.put('docs/web/hub/paralliverse/worker.mjs', '// changed current worker\n')
        self.commit()
        report = CHECK.verify(self.root, self.render())
        name = 'docs/web/hub/paralliverse/worker.mjs'
        self.assertNotEqual(report['hostSource'][name], self.manifest['sources'][name])


if __name__ == '__main__':
    unittest.main()
