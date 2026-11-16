#!/usr/bin/env python3
"""Regression checks for zone coverage, import evidence and the public CLI. No Lean."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import zones


class ScannerTests(unittest.TestCase):
    def test_lean_nested_comments_strings_and_multiple_imports(self):
        text = '''/- import Wrong.One /- import Wrong.Two -/ -/
public import L4Factoidal.DOM.Arena L4Factoidal.HTML.TreeBuilder -- comment
-- import Wrong.Three
private meta import L4Factoidal.XML.Document
 def s := "multiline
import Wrong.Four
"
 def quote := '\\"'
 def char := '-'
 def body := "import Bad" ++ "include"
'''
        self.assertEqual(list(zones.lean_imports(text)), [
            ('L4Factoidal.DOM.Arena', 2, 'lean'),
            ('L4Factoidal.HTML.TreeBuilder', 2, 'lean'),
            ('L4Factoidal.XML.Document', 4, 'lean')])

    def test_javascript_forms_and_false_positives(self):
        text = '''// import 'wrong-a';
/* export * from 'wrong-b'; */
const text = "import 'wrong-c'";
const template = `import 'wrong-d'`;
const re = /import 'wrong-e'/;
import './side.js';
import type { A,
 B } from './types.ts';
export { A as B } from './export.js';
export * from './star.js';
const module = await import('./lazy.js');
const common = require('./common.cjs');
import alias = require('./alias.cjs');
const unknown = import(prefix + name);
obj.import('wrong-f');
import.meta.url;
'''
        self.assertEqual([(s,k) for s,_,k in zones.js_imports(text)], [
            ('./side.js','import'),('./types.ts','import'),('./export.js','export'),
            ('./star.js','export'),('./lazy.js','dynamic-import'),('./common.cjs','require'),
            ('./alias.cjs','require'),(None,'computed-import')])

    def test_relative_resolution_extensions_and_outside_paths(self):
        paths = {'a/b.ts','a/c/index.js','assets/data.json'}
        self.assertEqual(zones.resolve_js('a/main.ts','./b.js',paths),('a/b.ts','resolved'))
        self.assertEqual(zones.resolve_js('a/main.ts','./c',paths),('a/c/index.js','resolved'))
        self.assertEqual(zones.resolve_js('a/main.ts','../assets/data.json?x=1',paths),('assets/data.json','resolved'))
        self.assertEqual(zones.resolve_js('a/main.ts','node:fs',paths),(None,'external'))
        self.assertEqual(zones.resolve_js('a/main.ts','./missing',paths),(None,'unresolved-local'))

    def test_cycles_include_three_zone_cycle(self):
        self.assertEqual(zones.strongly_connected(['a','b','c','d'],
                         [('a','b'),('b','c'),('c','a'),('d','a')]), [['a','b','c']])
        self.assertEqual(zones.strongly_connected(['a','b'], [('a','b')]), [])


class RepositoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = json.loads((zones.ROOT / 'zones/zones.json').read_text())
        cls.report = zones.analyse(zones.ROOT, cls.config)

    def test_every_file_maps_once(self):
        for field in ('unmapped_files','ambiguous_files','missing_files','stale_unmapped_files','unused_rules'):
            self.assertEqual(self.report[field], [], field)
        paths = zones.inventory(zones.ROOT, self.config['roots'])
        self.assertEqual(len(self.report['files']),len(paths))
        self.assertEqual(sum(z['files'] for z in self.report['sizes']),len(paths))
        for path in paths:
            with self.subTest(path=path):
                self.assertEqual(len(zones.classify(path,self.config)),1)
        # The mapping file is an explicit declaration, never a catch-all unknown zone.
        self.assertEqual(self.config['unmapped_files'],[])

    def test_new_core_subtree_cannot_fall_through(self):
        self.assertEqual(zones.classify('formal/lean4/L4Factoidal/NewArea/New.lean',self.config), [])

    def test_overlap_is_visible_even_with_same_zone(self):
        config = copy.deepcopy(self.config)
        config['rules'].append(dict(id='duplicate',zone='dom',paths=['formal/lean4/L4Factoidal/DOM/**']))
        self.assertEqual(len(zones.classify('formal/lean4/L4Factoidal/DOM/Arena.lean',config)),2)

    def test_named_integration_and_style_boundaries(self):
        expected = {'formal/lean4/L4Factoidal/WasmVM/Hosts/Page.lean':'browser',
                    'formal/lean4/L4Factoidal/WasmVM/Exec/Step.lean':'wasm',
                    'formal/lean4/L4Factoidal/Rendering/Style.lean':'style',
                    'formal/lean4/L4Factoidal/Rendering/Layout.lean':'rendering',
                    'labs/demos/foafnaut/SVGCSS.lean':'style',
                    'labs/demos/foafnaut/SVG.lean':'graphics'}
        for path,zone in expected.items():
            self.assertEqual([r['zone'] for r in zones.classify(path,self.config)],[zone])
        self.assertEqual(zones.policy('style','network','style.lean','net.lean',self.config)[0],'unexpected')
        self.assertEqual(zones.policy('json','network','json.lean',
            'formal/lean4/L4Factoidal/Net/FetchRules.lean',self.config)[0],'interface')
        self.assertEqual(zones.policy('json','network','json.lean',
            'formal/lean4/L4Factoidal/Net/Egress.lean',self.config)[0],'interface-review')

    def test_edges_reconcile_with_import_sites(self):
        cross=[i for i in self.report['imports'] if i['source_zone']!=i['target_zone']]
        self.assertEqual(len(cross),sum(e['count'] for e in self.report['edges']))
        self.assertEqual(self.report['totals']['import_sites'],
                         len(self.report['imports'])+len(self.report['other_imports']))
        self.assertTrue(any(i['kind']=='lean' for i in cross))
        self.assertTrue(any(i['kind']=='import' for i in cross))
        self.assertTrue(any(i['status']=='computed' for i in self.report['other_imports']))

    def test_cli_writes_both_formats_without_a_build(self):
        with tempfile.TemporaryDirectory(prefix='zones-test-') as tmp:
            md,js=Path(tmp)/'report.md',Path(tmp)/'report.json'
            result=subprocess.run([sys.executable,str(zones.ROOT/'tools/zones.py'),
                '--check','--json',str(js),'--markdown',str(md)],capture_output=True,text=True,timeout=60)
            self.assertEqual(result.returncode,0,result.stderr)
            report=json.loads(js.read_text())
            self.assertEqual(report['totals'],self.report['totals'])
            self.assertEqual(report['inventory_sha256'],self.report['inventory_sha256'])
            self.assertIn('## Dependency matrix',md.read_text())


class WorkingTreeTests(unittest.TestCase):
    def test_new_deleted_ignored_and_symlink_files(self):
        with tempfile.TemporaryDirectory(prefix='zones-tree-') as tmp:
            root=Path(tmp)
            subprocess.run(['git','init','-q',str(root)],check=True)
            (root/'src').mkdir()
            (root/'src/a.py').write_text('print(1)\n')
            (root/'src/deleted.py').write_text('print(0)\n')
            (root/'.gitignore').write_text('src/ignored.py\n')
            subprocess.run(['git','-C',str(root),'add','.'],check=True)
            subprocess.run(['git','-C',str(root),'-c','user.name=Dan Brickley',
                '-c','user.email=danbri@danbri.org','-c','commit.gpgsign=false','commit','-qm','Fixture'],check=True)
            (root/'src/new.ts').write_text('import "./a.py";\n')
            (root/'src/ignored.py').write_text('print(2)\n')
            (root/'src/deleted.py').unlink()
            (root/'src/external').symlink_to('/not-present-zones-test')
            config=dict(schema_version=1,roots=['src'],zones=[dict(id='one',name='One',definition='Fixture.')],
                rules=[dict(id='one',zone='one',paths=['src/**'])],allowed_dependencies={},interfaces=[],unmapped_files=[])
            r=zones.analyse(root,config)
            self.assertEqual(r['totals']['files'],4)
            self.assertEqual(r['missing_files'],['src/deleted.py'])
            self.assertEqual(r['symlink_files'],['src/external'])
            self.assertTrue(any(f['path']=='src/new.ts' for f in r['files']))
            self.assertFalse(any(f['path']=='src/ignored.py' for f in r['files']))
            mapping=root/'mapping.json';mapping.write_text(json.dumps(config))
            proc=subprocess.run([sys.executable,str(zones.ROOT/'tools/zones.py'),'--root',str(root),
                '--mapping',str(mapping),'--check','--json',str(root/'result.json')],capture_output=True,text=True)
            self.assertEqual(proc.returncode,1)

    def test_empty_inventory_is_an_error(self):
        with tempfile.TemporaryDirectory(prefix='zones-empty-') as tmp:
            subprocess.run(['git','init','-q',tmp],check=True)
            with self.assertRaisesRegex(ValueError,'Empty inventory'):
                zones.inventory(Path(tmp),['no-files'])


if __name__=='__main__':
    unittest.main()
