#!/usr/bin/env python3
"""Independent NumPy checks of actual Lean-emitted shared affine fixtures.
Requires installed NumPy; no dependency download. This is numerical testing,
not a proof or GPU execution. IEEE bit strings avoid decimal oracle rounding.
"""
import argparse
import json
import struct
import numpy as np


def vector(encoded):
    return np.array([struct.unpack('>d',struct.pack('>Q',int(x)))[0] for x in encoded],dtype=np.float64)


def matrix(encoded):
    a,b,c,d,e,f=vector(encoded)
    return np.array([[a,c,e],[b,d,f],[0,0,1]],dtype=np.float64)


def verify(path):
    with open(path) as stream: data=json.load(stream)
    if data['encoding']!='ieee754-binary64-bits-decimal': raise ValueError('wrong fixture encoding')
    maximum=0.;count=0
    for case in data['cases']:
        p,q=matrix(case['p']),matrix(case['q'])
        np.testing.assert_allclose(matrix(case['compose']),p@q,rtol=1e-12,atol=1e-12)
        np.testing.assert_allclose(matrix(case['inverse']),np.linalg.inv(p),rtol=1e-12,atol=1e-12)
        np.testing.assert_allclose(vector(case['normal']),np.linalg.inv(p[:2,:2]).T@np.array([1.,0.]),rtol=1e-12,atol=1e-12)
        corners=np.array([[-2.,-1.,1.],[4.,-1.,1.],[4.,3.,1.],[-2.,3.,1.]])
        actual_corners=np.array([vector(c) for c in case['corners']])
        expected_corners=(p@corners.T).T[:,:2]
        np.testing.assert_allclose(actual_corners,expected_corners,rtol=1e-12,atol=1e-12)
        np.testing.assert_allclose([actual_corners.min(axis=0),actual_corners.max(axis=0)],[expected_corners.min(axis=0),expected_corners.max(axis=0)],rtol=1e-12,atol=1e-12)
        point=np.array([3.25,-2.5,1.]);direction=np.array([3.25,-2.5,0.])
        np.testing.assert_allclose(vector(case['point']),(p@point)[:2],rtol=1e-12,atol=1e-12)
        np.testing.assert_allclose(vector(case['direction']),(p@direction)[:2],rtol=1e-12,atol=1e-12)
        # Explicitly measured small-fixture f32 round trip, not a general bound.
        restored=matrix(case['inverse']).astype(np.float32)@(p.astype(np.float32)@point.astype(np.float32))
        maximum=max(maximum,float(np.max(np.abs(restored-point))))
        count+=1
    if count!=16: raise ValueError('expected all16 emitted matrix pairs')
    if maximum>1e-5: raise ValueError(f'f32 fixture roundtrip exceeds stated1e-5 tolerance: {maximum}')
    return {'numpy':np.__version__,'matrixPairs':count,'float64Rtol':1e-12,'float64Atol':1e-12,'fixtureFloat32MaxRoundtripError':maximum,'fixtureFloat32Tolerance':1e-5,'gpuExecuted':False,'proved':False}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('fixtures');args=parser.parse_args()
    print(json.dumps(verify(args.fixtures)))
