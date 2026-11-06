import contextlib
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
import corpus


class CorpusIntegrityTests(unittest.TestCase):
    def fixture(self,inventory_mutation=None,source_mutation=None):
        original=corpus.ROOT
        with tempfile.TemporaryDirectory(prefix='svg-corpus-integrity-') as directory:
            root=Path(directory)
            for name in ('source.json','inventory.json','tree.json','git-proof.json'):
                shutil.copyfile(original/name,root/name)
            # Original input bytes remain read-only; only copied metadata is mutated.
            (root/'upstream').symlink_to(original/'upstream',target_is_directory=True)
            for name,mutate in [('inventory.json',inventory_mutation),('source.json',source_mutation)]:
                if mutate:
                    value=json.loads((root/name).read_text());mutate(value)
                    (root/name).write_text(json.dumps(value))
            with patch.object(corpus,'ROOT',root),contextlib.redirect_stdout(io.StringIO()):
                corpus.check()

    def test_original_complete_corpus_passes_integrity_only(self):self.fixture()
    def test_removed_case_fails(self):
        with self.assertRaisesRegex(ValueError,'Inventory'):self.fixture(lambda p:p['cases'].pop())
    def test_changed_fuzzy_limit_fails(self):
        def change(p):next(c for c in p['cases'] if c['fuzzy'] is not None)['fuzzy']=[[0,255],[0,480000]]
        with self.assertRaisesRegex(ValueError,'Inventory'):self.fixture(change)
    def test_changed_reference_fails(self):
        def change(p):next(c for c in p['cases'] if c['reference'] and c['reference'].get('path'))['reference']['path']='svg/historical.html'
        with self.assertRaisesRegex(ValueError,'Inventory'):self.fixture(change)
    def test_bad_resource_hash_fails(self):
        def change(p):next(e for e in p['files'] if e['scope']=='dependency')['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'identity mismatch'):self.fixture(source_mutation=change)
    def test_empty_inventory_fails(self):
        def change(p):p.clear()
        with self.assertRaisesRegex(ValueError,'Inventory'):self.fixture(change)
    def test_html_first_base_and_fuzzy_reference_share_base(self):
        info=corpus.inspect('svg/example.html',b'<base href="/first/"><base href="/second/"><link rel="match" href="ref.html">')
        self.assertEqual(info['references'][0]['target']['path'],'first/ref.html')
        self.assertEqual(corpus.fuzzy(['ref.html:1;2'],'/first/ref.html','svg/example.html',info['base']),[[1,1],[2,2]])
    def test_xml_base_is_explicitly_unavailable(self):
        info=corpus.inspect('svg/example.svg',b'<svg xml:base="/other/"><link rel="match" href="ref.svg"/></svg>')
        self.assertIn('xml-base-context-unresolved',info['requirements']);self.assertIsNone(info['references'][0]['target'])


if __name__=='__main__':unittest.main()
