#!/usr/bin/env python3
"""Falsify the independent historical Frontier account proof validator.

All expected pass/fail labels here apply only to the pinned block 46146
witness; they are not a conformance census of the wider Ethereum protocol.
"""
import copy
import importlib.util
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('frontier_independent',
    HERE/'independent-frontier-trie.py')
checker=importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)

def require(cond,message):
    if not cond:raise AssertionError(message)

def mutate_hex(s):
    return s[:-1]+('0' if s[-1]!='0' else '1')

def main():
    if len(sys.argv)!=2:
        raise SystemExit('usage: frontier-independent-negative.py PINNED_WITNESS.json')
    baseline=json.loads(Path(sys.argv[1]).read_text())
    genuine=checker.verify_historical(baseline)
    require(genuine['status']=='pass' and genuine['accountsVerified']==3 and
        genuine['recipientNonexistentBeforeTransaction'],
        'independent first historical replay failed')
    bad_cases=[
      ('forged-sender-proof-node',lambda b:
        b['accounts'][0]['accountProof'].__setitem__(0,
          mutate_hex(b['accounts'][0]['accountProof'][0]))),
      ('forged-recipient-nonmembership-codehash',lambda b:
        b['accounts'][1].__setitem__('codeHash','0x'+'11'*32)),
      ('forged-parent-state-root',lambda b:
        b['parentHeader'].__setitem__('stateRoot','0x'+'00'*32)),
      ('forged-sender-balance',lambda b:
        b['accounts'][0].__setitem__('balance','0x01')),
      ('forged-miner-proof',lambda b:
        b['accounts'][2]['accountProof'].__setitem__(0,'0xdeadbeef')),
      ('forged-recipient-nonce',lambda b:
        b['accounts'][1].__setitem__('nonce','0x01')),
    ]
    rejected=[]
    for name,alter in bad_cases:
        forged=copy.deepcopy(baseline)
        alter(forged)
        try:
            checker.verify_historical(forged)
        except (ValueError,AssertionError,KeyError,TypeError):
            rejected.append(name)
    require(len(rejected)==len(bad_cases),
        'independent witness proof accepted one or more falsifications')
    print(json.dumps({'status':'pass','mainnetReplayVerified':True,
      'originalTransactionAndBlockRootsReplayed':2,
      'adversarialControlsRejected':len(rejected),
      'rejectedKinds':rejected,
      'preStateRoot':genuine['prestateRoot'],
      'intermediateRoot':genuine['intermediateRoot'],
      'postBlockRoot':genuine['postBlockRoot']}))
if __name__=='__main__':
    main()
