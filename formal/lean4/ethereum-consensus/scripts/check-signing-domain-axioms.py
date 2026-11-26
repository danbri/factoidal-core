#!/usr/bin/env python3
"""Audit actual printed axiom names and exact checked-out source objects."""
import json
import re
import subprocess
import sys
from pathlib import Path

repo=Path(__file__).resolve().parents[4]
def git(*args):
    return subprocess.check_output(["git","-C",str(repo),*args],text=True).strip()
prefix="formal/lean4/ethereum-consensus/"
paths=[prefix+"EthereumConsensus/SSZ/"+x+".lean" for x in
       ("SigningDomains","ContainerRoots","BasicTypes","ByteProof","MultiProofHelpers","CheckedBranch","GIndex")]
paths += [prefix+"ContainerRootsMain.lean",prefix+"EthereumConsensus.lean",
          "formal/lean4/L4Factoidal/Crypto/SHA2.lean",
          "formal/lean4/L4Factoidal/Crypto/SHA2Theorems.lean"]
names = {"EthereumConsensus.SSZ."+x for x in (
    "selectSigningVersion_before","selectSigningVersion_current","computeSigningDomain_bad_type",
    "getSigningDomain_bad_previous","getSigningDomain_bad_current","computeSigningDomain_delegates",
    "headerProposerSigningRoot_delegates")}
actual={}
for name, body, empty in re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$",
                                   Path(sys.argv[1]).read_text(),re.M):
    if name in actual: raise SystemExit("duplicate axiom result: "+name)
    actual[name]=[] if empty else [x.strip() for x in body.split(",") if x.strip()]
if set(actual)!=names: raise SystemExit("wrong theorem inventory: "+str(actual))
for name, axioms in actual.items():
    if not set(axioms)<={"propext","Classical.choice","Quot.sound"}:
        raise SystemExit("unpermitted axiom: "+name)
pins={}
for path in paths:
    actual_sha=git("hash-object",path)
    committed=git("rev-parse","HEAD:"+path)
    if actual_sha!=committed: raise SystemExit("dirty proof source: "+path)
    pins[path]=actual_sha
print(json.dumps(dict(commit=git("rev-parse","HEAD"),tree=git("rev-parse","HEAD^{tree}"),
                      theorem_axioms=actual,sources=pins),sort_keys=True))
