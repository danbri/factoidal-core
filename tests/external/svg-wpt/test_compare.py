"""Adversarial scoring checks, independent of a working renderer."""
import unittest
import numpy as np
import compare

class ScoringGuards(unittest.TestCase):
    def test_blank_negative_is_not_image_match(self):
        white=np.full((600,800,3),255,dtype=np.uint8)
        reference=white.copy();reference[10:30,10:30]=0
        test=white.copy();test[40:60,40:60]=0
        equal,_,_=compare.metrics(white,reference,[[0,0],[0,0]])
        exact,_,_=compare.metrics(white,test,[[0,0],[0,0]])
        self.assertEqual(compare.relation_state('mismatch',equal,exact),('negative-only',True))
        self.assertEqual(compare.relation_state('mismatch',False,True),('match',True))
        self.assertEqual(compare.relation_state('mismatch',True,True),('mismatch',False))

    def test_original_fuzzy_minimum_and_maximum_are_inclusive(self):
        a=np.zeros((600,800,3),dtype=np.uint8);b=a.copy();b[599,799,2]=7
        accepted,detail,_=compare.metrics(a,b,[[7,7],[1,1]])
        self.assertTrue(accepted);self.assertEqual(detail,{'maxChannelDifference':7,'differentPixels':1})
        self.assertFalse(compare.metrics(a,a,[[7,7],[1,1]])[0])
        b[599,798,0]=1
        self.assertFalse(compare.metrics(a,b,[[7,7],[1,1]])[0])

    def test_last_pixel_cannot_escape_full_image_comparison(self):
        a=np.zeros((600,800,3),dtype=np.uint8);b=a.copy();b[-1,-1,-1]=1
        self.assertFalse(compare.metrics(a,b,[[0,0],[0,0]])[0])
        with self.assertRaises(ValueError):compare.metrics(a[:100],b[:100],[[0,0],[0,0]])

if __name__=='__main__':unittest.main()
