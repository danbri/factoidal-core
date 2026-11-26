#!/usr/bin/env python3
"""Pin fresh six-case Prague EELS execution to independently published roots.

This checks an actual runner JSON report, not historical v1's old 4/2
evidence. It does NOT independently implement Keccak/MPT or signatures.
"""
import argparse
import copy
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'evidence/active-claim-manifest-v2.json'

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def check(evidence, result):
    roots=evidence['expected_roots_by_transaction_type']
    require(len(roots)==6 and set(roots)=={
        'type_0_protected','type_0_unprotected','type_1',
        'type_2','type_3','type_4'},'wrong reference inventory')
    require(result['kind']=='EELS-state-test-real-execution-restricted-Lean' and
        result['status']=='pass' and result['actualLeanStateTestsExecuted']==6
        and result['passed']==6 and result['failed']==0 and
        result['unsupported']==0 and result['provenance']['totalFixtureCases']==6
        and result['provenance']['sha256']==evidence['fixture_sha256'],
        'six-case mandatory evidence/count/fixture mismatch')
    actual={}
    for case in result['cases']:
        require(case['status']=='pass' and case['fork']=='Prague',
                'non-passing Prague case')
        suffix=re.search(r'(type_\d(?:_(?:protected|unprotected))?)\]$',case['id'])
        require(suffix is not None,'unidentified Prague vector')
        kind=suffix.group(1)
        require(kind in roots and kind not in actual,'duplicate/unknown Prague vector')
        require(case['expectedStateRoot']==case['computedStateRoot']==roots[kind],
                'root mismatch in '+kind)
        require(int(case['chargedGas'])>=int(case['intrinsicGas']) and
                int(case['chargedGas'])>=int(case['calldataFloorGas']) and
                int(case['chargedGas'])<=int(case['gasLimit']) and
                int(case['baseFeeBurn'])>=0,'gas/fee bounds mismatched')
        if kind=='type_3':
            require(case['blobGasUsed']=='131072' and
                    case['blobFeeBurn']=='131072' and
                    case['authorizationAccounts']==[],
                    'blob burn or authority corruption')
        elif kind=='type_4':
            authorizers=case['authorizationAccounts']
            require(case['blobFeeBurn']=='0' and
                    len(authorizers)==1 and
                    authorizers[0]['nonce']=='1' and
                    re.fullmatch(r'0xef0100[0-9a-f]{40}',authorizers[0]['code']) and
                    authorizers[0]['refund']=='0',
                    'authorization code/nonce or refund corruption')
        else:
            require(case['blobFeeBurn']=='0' and
                    case['authorizationAccounts']==[],
                    'unexpected blob/authorization effects')
        actual[kind]=case['computedStateRoot']
    require(actual==roots,'one or more published vectors missing')

def selftest(evidence, result):
    controls=[
        lambda r:r['cases'][0].update(computedStateRoot='0x'+'00'*32),
        lambda r:r.update(passed=5),
        lambda r:r['cases'].pop(),
        lambda r:next(c for c in r['cases'] if 'type_3]' in c['id']).update(blobFeeBurn='0'),
        lambda r:next(c for c in r['cases'] if 'type_4]' in c['id'])
                  ['authorizationAccounts'][0].update(nonce='2'),
        lambda r:r.update(unsupported=1),
    ]
    caught=0
    for control in controls:
        falsified=copy.deepcopy(result)
        control(falsified)
        try:
            check(evidence,falsified)
        except (ValueError,KeyError,TypeError):
            caught+=1
    require(caught==len(controls),'evidence ledger mutation comparator failed')
    return caught

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('report',type=Path)
    args=parser.parse_args()
    manifest=json.loads(MANIFEST.read_text())
    evidence=manifest['external_evidence']['official_prague_all_six_candidate']
    report=json.loads(args.report.read_text())
    check(evidence,report)
    controlled=selftest(evidence,report)
    print(json.dumps({'status':'six-published-prague-roots-confirmed',
      'passed':6,'unsupported':0,'adversarialLedgerMutationsRejected':controlled,
      'evidenceStatus':'replayed-with-trusted-MPT-not-proved-normative-refinement'}))

if __name__=='__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as e:
        print('Prague six-case ledger failed:',e,file=sys.stderr)
        sys.exit(1)
