"""Mutation controls for producer selection/identity, before any browser runs."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

HERE=Path(__file__).resolve().parent
NODE=Path('/opt/homebrew/opt/node@22/bin/node')

class TransportIdentity(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.node=str(NODE) if NODE.exists() else shutil.which('node')
        if not cls.node:raise unittest.SkipTest('Node22+ required for transport controls')
        version=subprocess.check_output([cls.node,'--version'],text=True)
        if int(version.lstrip('v').split('.')[0])<22:raise unittest.SkipTest('Node22+ required')

    def refused(self,extra,reason):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            args=extra(root)
            result=subprocess.run([self.node,str(HERE/'capture.mjs'),'--output',str(root/'out'),
              '--browser',str(root/'browser-must-not-be-read'),'--playwright',str(root/'must-not-load'),*args],
              capture_output=True,text=True,timeout=20)
            self.assertNotEqual(result.returncode,0)
            self.assertIn(reason,result.stderr)
            self.assertNotIn('browser-must-not-be-read',result.stderr)

    def test_mismatched_wasm_witness_fails_before_browser(self):
        def setup(root):
            lab=root/'lab';engines={}
            for name in ['web-render/engine.mjs','.build/web-render/engines/web-render.mjs','.build/web-render/engines/web-render.wasm']:
                p=lab/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b'not executable: identity mutation only')
                if name.startswith('.build/'):engines['labs/demos/foafnaut/'+name]=hashlib.sha256(p.read_bytes()).hexdigest()
            engines['labs/demos/foafnaut/.build/web-render/engines/web-render.wasm']='0'*64
            witness=root/'witness.json';witness.write_text(json.dumps({'format':'factoidal-web-render-source-witness-v1','engines':engines}))
            return ['--html-lab',str(lab),'--html-witness',str(witness)]
        self.refused(setup,'Frozen HTML engine differs from source witness')

    def test_mismatched_native_witness_fails_before_browser(self):
        def setup(root):
            native=root/'native';native.write_bytes(b'must not execute')
            witness=root/'witness.json';witness.write_text(json.dumps({'nativeSha256':'0'*64}))
            return ['--html-engine',str(native),'--html-witness',str(witness)]
        self.refused(setup,'Native HTML executable differs from source witness')

    def test_two_html_producers_are_not_silently_prioritized(self):
        self.refused(lambda root:['--html-lab',str(root/'lab'),'--html-engine',str(root/'native')],
          'Select one original HTML producer')

if __name__=='__main__':unittest.main()
