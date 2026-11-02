#!/usr/bin/env python3
"""Exercise actual HB/FT font data, independently checking HB's public CLI.

No font file is bundled. Set FACTOIDAL_TEST_FONT and HB_SHAPE on other hosts.
This checks the adapter contract; it is not CSS/text conformance.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import unittest

LAB = Path(__file__).resolve().parent.parent
ADAPTER = LAB / '.build/font-shape'
FONT = Path(os.environ.get('FACTOIDAL_TEST_FONT', '/System/Library/Fonts/Supplemental/Arial.ttf'))
HB = os.environ.get('HB_SHAPE') or shutil.which('hb-shape')


def adapted(text, size=20):
    result = subprocess.run([str(ADAPTER), str(FONT), text, str(size)],
                            check=True, capture_output=True, text=True, timeout=20)
    return json.loads(result.stdout)


def cli_shape(text):
    result = subprocess.run([HB, '--font-funcs=ot', '--font-size=upem',
                             '--utf8-clusters', '--cluster-level=0',
                             '--no-glyph-names', '--output-format=json', str(FONT), text],
                            check=True, capture_output=True, text=True, timeout=20)
    return json.loads(result.stdout)


class FontDataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not ADAPTER.is_file() or not FONT.is_file() or not HB:
            raise RuntimeError('Build font-shape and supply a real font and hb-shape; no zero-test pass')

    def test_shaping_agrees_with_independent_cli(self):
        # Each input is one shaping run; paragraph bidi segmentation belongs to Lean.
        for text in ['AVATAR office', 'λόγος', 'سلام', 'A\u0301', 'a\u200db']:
            with self.subTest(text=text):
                actual = adapted(text)
                expected = cli_shape(text)
                mapped = [dict(g=g['id'], cl=g['cluster'], ax=g['xAdvance'],
                               ay=g['yAdvance'], dx=g['xOffset'], dy=g['yOffset'])
                          for g in actual['glyphs']]
                self.assertEqual(mapped, expected)

    def test_empty_run_has_no_glyphs_or_coverage(self):
        # hb-shape CLI emits no record for an empty line; the adapter has an
        # explicit empty-run record, so test its contract separately.
        result = adapted('')
        self.assertEqual(result['text'], '')
        self.assertEqual(result['glyphs'], [])
        self.assertEqual(result['outlines'], [])
        self.assertEqual(result['bitmaps'], [])

    def test_font_identity_hashes_actual_font_bytes(self):
        result = adapted('A')
        self.assertEqual(result['fontSha256'], hashlib.sha256(FONT.read_bytes()).hexdigest())
        self.assertEqual(result['fontBytes'], FONT.stat().st_size)
        self.assertEqual(result['clusterUnits'], 'UTF-8 byte offsets')
        self.assertGreater(result['ascender'], 0)
        self.assertLessEqual(result['descender'], 0)
        self.assertGreater(result['unitsPerEm'], 0)

    def test_utf8_clusters_and_rtl_are_retained(self):
        result = adapted('سلام')
        self.assertEqual(result['direction'], 'rtl')
        self.assertEqual(result['script'], 'Arab')
        boundaries = {0}
        offset = 0
        for char in result['text']:
            offset += len(char.encode('utf-8'))
            boundaries.add(offset)
        self.assertTrue(all(g['cluster'] in boundaries for g in result['glyphs']))
        self.assertEqual([g['cluster'] for g in result['glyphs']],
                         sorted([g['cluster'] for g in result['glyphs']], reverse=True))

    def test_outline_contours_and_unique_glyph_data(self):
        result = adapted('AA OO ')  # O exercises a hole and quadratic outlines.
        ids = {g['id'] for g in result['glyphs']}
        self.assertEqual({o['id'] for o in result['outlines']}, ids)
        self.assertEqual(len(result['outlines']), len(ids))
        saw_curve = False
        for outline in result['outlines']:
            opened = False
            for command in outline['commands']:
                op = command[0]
                self.assertEqual(len(command), {'M':3,'L':3,'Q':5,'C':7,'Z':1}[op])
                self.assertTrue(all(isinstance(v,int) for v in command[1:]))
                if op == 'M':
                    self.assertFalse(opened)
                    opened = True
                elif op == 'Z':
                    self.assertTrue(opened)
                    opened = False
                else:
                    self.assertTrue(opened)
                    saw_curve |= op in ('Q', 'C')
            self.assertFalse(opened)
        self.assertTrue(saw_curve)

    def test_real_gray_coverage_and_size_scaling(self):
        small, large = adapted('A ',12), adapted('A ',24)
        self.assertEqual(small['glyphs'], large['glyphs'])  # positions stay in font units
        small_a = next(b for b in small['bitmaps'] if b['width'])
        large_a = next(b for b in large['bitmaps'] if b['id']==small_a['id'])
        self.assertGreater(large_a['height'], small_a['height'])
        self.assertGreater(large_a['width'], small_a['width'])
        self.assertTrue(any(0<v<255 for v in large_a['alpha']))
        for bitmap in small['bitmaps'] + large['bitmaps']:
            self.assertEqual(len(bitmap['alpha']), bitmap['width']*bitmap['height'])
            self.assertTrue(all(0<=v<=255 for v in bitmap['alpha']))

    def test_invalid_inputs_fail_without_json(self):
        for args in [[str(FONT),'A','0'],[str(FONT),'A','513'],
                     [str(FONT),'A','NaN'],[str(FONT),'A','20','99999'],
                     ['/nonexistent/font.ttf','A','20']]:
            with self.subTest(args=args):
                result=subprocess.run([str(ADAPTER),*args],capture_output=True,timeout=20)
                self.assertNotEqual(result.returncode,0)
                self.assertEqual(result.stdout,b'')
        result=subprocess.run([os.fsencode(ADAPTER),os.fsencode(FONT),b'\xff',b'20'],
                              capture_output=True,timeout=20)
        self.assertNotEqual(result.returncode,0)
        self.assertEqual(result.stdout,b'')


if __name__ == '__main__':
    unittest.main(verbosity=2)
