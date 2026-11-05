#!/usr/bin/env python3
"""Packaging integrity controls; no compiler, native application or network."""
import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

SPEC=importlib.util.spec_from_file_location('packager',Path(__file__).with_name('package-foafnaut2525.py'))
P=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)


class Packaging(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='factoidal-native-package-test-')
        self.root=Path(self.tmp.name)
        self.native=self.root/'native';self.native.mkdir()
        (self.native/'libnative-window.dylib').write_bytes(b'fixture dylib')
        (self.native/'native-webgpu-ui-darwin-arm64').write_bytes(b'fixture executable')
        (self.native/'native-webgpu-ui-darwin-arm64').chmod(0o755)
        native={'foafnaut/'+name:row for name,row in P.inventory(self.native).items()}
        self.native_info=self.root/'native-info.json'
        self.native_info.write_text(json.dumps({'source_commit':P.RELEASE,'source_repo':'danbri/factoidal-core',
          'artifacts':{'foafnaut-darwin-arm64.tar.gz':{'files':native,'sha256':'unused','size':0}}}))
        data={P.RUNTIME+name:('fixture '+name).encode() for name in
              ['web-render.mjs','web-render.wasm','render-plan.mjs','render-plan.wasm','source-witness.json']}
        self.archive=self.root/'web.tar.gz'
        with tarfile.open(self.archive,'w:gz') as tar:
            for name,body in data.items():
                entry=tarfile.TarInfo(name);entry.size=len(body);entry.mode=0o644
                tar.addfile(entry,io.BytesIO(body))
        self.files={name:{'size':len(body),'mode':'644','sha256':hashlib.sha256(body).hexdigest()} for name,body in data.items()}
        self.web_info=self.root/'web-info.json'
        self.web_info.write_text(json.dumps({'source_commit':P.RELEASE,'source_repo':'danbri/factoidal-core',
          'artifacts':{'foafnaut-web.tar.gz':{'files':self.files,'sha256':P.sha(self.archive),'size':self.archive.stat().st_size}}}))
        self.args=argparse.Namespace(native_build_info=self.native_info,web_build_info=self.web_info,
          native_package=self.native,native_archive=None,web_archive=self.archive)

    def tearDown(self):
        self.tmp.cleanup()

    def prepare(self):
        temporary=Path(tempfile.mkdtemp(dir=self.root,prefix='extract-'))
        return P.prepare(self.root/'checkout',self.args,temporary)

    def test_verified_runtime_and_adjacent_library_keep_published_bytes(self):
        receipt=self.prepare()
        self.assertEqual(receipt['engineSourceCommit'],P.RELEASE)
        for name,row in receipt['installed'].items():
            self.assertEqual(P.sha(self.root/'checkout'/name),row['sha256'])

    def test_native_extra_file_and_changed_library_refused(self):
        (self.native/'extra').write_text('unlisted')
        with self.assertRaisesRegex(ValueError,'extra='):self.prepare()
        (self.native/'extra').unlink()
        (self.native/'libnative-window.dylib').write_text('wrong bytes')
        with self.assertRaisesRegex(ValueError,'changed='):self.prepare()

    def test_missing_manifest_member_and_wrong_commit_refused(self):
        info=json.loads(self.web_info.read_text())
        del info['artifacts']['foafnaut-web.tar.gz']['files'][P.RUNTIME+'web-render.wasm']
        self.web_info.write_text(json.dumps(info))
        with self.assertRaisesRegex(ValueError,'Unlisted'):self.prepare()
        info['source_commit']='0'*40;self.web_info.write_text(json.dumps(info))
        with self.assertRaisesRegex(ValueError,'98896de'):self.prepare()

    def test_archive_corruption_and_unsafe_paths_refused(self):
        with self.archive.open('ab') as stream:stream.write(b'changed')
        with self.assertRaisesRegex(ValueError,'hash/size'):self.prepare()
        for path in ['../escape','/absolute','foo//bar','foo/./bar','foo\\bar']:
            with self.assertRaises(ValueError):P.safe_path(path)

    def test_host_or_runtime_change_during_compile_refused(self):
        checkout=self.root/'checkout'
        for name in P.HOSTS:
            path=checkout/P.LAB/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('host '+name)
        for name in ['default.html','next.html']:
            path=checkout/P.LAB/'native-html'/name;path.parent.mkdir(exist_ok=True);path.write_text(name)
        tool=checkout/'tools/package-foafnaut2525.py';tool.parent.mkdir();tool.write_text('tool')
        runtime=checkout/'runtime.wasm';runtime.write_bytes(b'release runtime')
        installed={'runtime.wasm':{'sha256':P.sha(runtime),'size':runtime.stat().st_size}}
        before=P.host_hashes(checkout)
        P.unchanged_inputs(checkout,before,installed)
        host=checkout/P.LAB/P.HOSTS[0];original=host.read_text();host.write_text('concurrent edit')
        with self.assertRaisesRegex(ValueError,'Host source changed'):P.unchanged_inputs(checkout,before,installed)
        host.write_text(original);runtime.write_bytes(b'changed runtime')
        with self.assertRaisesRegex(ValueError,'runtime changed'):P.unchanged_inputs(checkout,before,installed)


if __name__=='__main__':unittest.main()
