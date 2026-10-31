import struct
import json
import tempfile
import unittest
import zlib
from pathlib import Path
import oracle


def chunk(kind,body):
    return struct.pack('>I',len(body))+kind+body+struct.pack('>I',zlib.crc32(kind+body)&0xffffffff)


def image(w,h,raw,color=2):
    return b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',w,h,8,color,0,0,0))+chunk(b'IDAT',zlib.compress(raw))+chunk(b'IEND',b'')


class OracleTests(unittest.TestCase):
    def decode(self,data):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'image.png';p.write_bytes(data);return oracle.png(p)

    def test_all_png_filters_reconstruct_known_rgb(self):
        # Equal pixels make left/up predictors observable on both rows.
        for f in range(5):
            previous=[0]*6; rows=[]
            for actual in ([10,20,30,40,50,60],[70,80,90,100,110,120]):
                encoded=[]
                for x,v in enumerate(actual):
                    a=actual[x-3] if x>=3 else 0;b=previous[x];c=previous[x-3] if x>=3 else 0
                    # Independent conventional Paeth branches.
                    p=a+b-c;pa,pb,pc=abs(p-a),abs(p-b),abs(p-c)
                    predictor=a if pa<=pb and pa<=pc else b if pb<=pc else c
                    encoded.append((v-(0,a,b,(a+b)//2,predictor)[f])%256)
                rows.extend([f,*encoded]);previous=list(actual)
            self.assertEqual(self.decode(image(2,2,bytes(rows))),(2,2,bytes(range(10,121,10))))

    def test_alpha_composites_on_white_and_corrupt_png_refused(self):
        self.assertEqual(self.decode(image(1,1,bytes([0,255,0,0,128]),6)),(1,1,bytes([255,127,127])))
        bad=bytearray(image(1,1,bytes([0,1,2,3])));bad[-1]^=1
        with self.assertRaisesRegex(ValueError,'CRC'): self.decode(bad)
        with self.assertRaises(ValueError): self.decode(image(1,1,bytes([0,1,2,3,4])))
        with self.assertRaises(ValueError): self.decode(image(1,1,bytes([5,1,2,3])))

    def test_full_image_and_fuzzy_minimum_maximum_are_not_weakened(self):
        zero=bytes(800*600*3); changed=bytearray(zero);changed[3]=2
        actual=(800,600,bytes(changed));expected=(800,600,zero)
        ok,metrics,diff=oracle.metrics(actual,expected,[[2,2],[1,1]])
        self.assertTrue(ok);self.assertEqual(metrics,{'maxChannelDifference':2,'differentPixels':1});self.assertEqual(diff,actual)
        self.assertFalse(oracle.metrics(actual,expected,[[0,1],[0,1]])[0])
        self.assertFalse(oracle.metrics(expected,expected,[[1,2],[1,1]])[0])
        with self.assertRaises(ValueError): oracle.metrics((1,1,b'\0\0\0'),expected,[[0,0],[0,0]])

    def test_capture_conditions_and_missing_oracles_cannot_pass(self):
        manifest,errors=oracle.suite.fixtures();self.assertEqual(errors,[])
        report={'revision':manifest['revision'],'viewport':{'width':800,'height':600,'deviceScaleFactor':1},'scripts':False,'externalFetch':False,
          'cases':[{'test':c['test'],'reference':c['reference'],'status':'unavailable'} for c in manifest['cases']]}
        with tempfile.TemporaryDirectory() as d:
            path=Path(d)/'oracle.json';path.write_text(json.dumps(report))
            result=oracle.compare_oracle(d)
            self.assertEqual(result['total'],38);self.assertEqual(result['counts']['unavailable'],38);self.assertEqual(result['counts']['match'],0)
            report['viewport']['deviceScaleFactor']=2;path.write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError,'conditions'): oracle.compare_oracle(d)


if __name__=='__main__': unittest.main()
