#!/usr/bin/env python3
"""Check actual printed axiom inventory and exact git blob pins; never infer proof success."""
import json
import re
import subprocess
import sys
from pathlib import Path

repo=Path(__file__).resolve().parents[4]
def git(*args):
    return subprocess.check_output(["git","-C",str(repo),*args],text=True).strip()

pins={
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/AttestationData.lean": "066e9adcb47a0beed6ce9258722b9beb2ef8fd7f",
    "formal/lean4/ethereum-consensus/ContainerRootsMain.lean": "cc3635b29abf0905fa1e4eab318602ac18c196e9",
    "formal/lean4/ethereum-consensus/EthereumConsensus.lean": "e697564e6eae6ccf7c5942ace1a3feaa470935ec",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/SigningDomains.lean": "f3195b4b96a80ea2b5ba86317b1d89052594a1c0",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ContainerRoots.lean": "c26954c1514b0d216f4aa4a3918a1bc4291af93c",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/BasicTypes.lean": "e2d3b3e2b4eb29c0ed2cea820a36713ae93ebb6d",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/ByteProof.lean": "ff547b1c8547769ec36673c0f6dde3fb29bf40a1",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/MultiProofHelpers.lean": "3bb33d5661020979c55ca7d188bc8af20054132d",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/CheckedBranch.lean": "9c3ebadf0100b86d4e6f9d20b87d6d0311a6e734",
    "formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/GIndex.lean": "ec69368d7bf3d4ec1bbe533560ae93e3aaecbb2b",
    "formal/lean4/L4Factoidal/Crypto/SHA2.lean": "92737f4d83035745dba29ef2c3867b01b8dfa50f",
    "formal/lean4/ethereum-consensus/scripts/check-attestation-data.py": "c80f83a57d5088bc4b7668d28acb1a001e063755",
    "formal/lean4/ethereum-consensus/lakefile.toml": "b08203129886735a8fbfc2c31fb7027024665d1f",
    "formal/lean4/ethereum-consensus/lake-manifest.json": "15728fe01a01ed2369565ec5be9afdf6abcf2f91",
    "formal/lean4/ethereum-consensus/lean-toolchain": "a8afa7d1b02d96f0671eba854a8dc4b416beb473"
}
names={"EthereumConsensus.SSZ."+x for x in (
    "checkedAttestationData_bad_beacon","attestationDataWire_size",
    "attestationDataRoot_delegates","attesterSigningRoot_delegates",
    "attesterSigningRoot_bad_domain")}
actual={}
for name,body,empty in re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))\s*$",
                                   Path(sys.argv[1]).read_text(),re.M):
    if name in actual:
        raise SystemExit("duplicate axiom result: "+name)
    actual[name]=[] if empty else [x.strip() for x in body.split(",") if x.strip()]
if set(actual)!=names:
    raise SystemExit("wrong theorem inventory: "+str(actual))
for name,axioms in actual.items():
    if not set(axioms)<={"propext","Classical.choice","Quot.sound"}:
        raise SystemExit("unpermitted axiom: "+name)
for path,sha in pins.items():
    if git("hash-object",path)!=sha or git("rev-parse","HEAD:"+path)!=sha:
        raise SystemExit("source pin mismatch: "+path)
print(json.dumps(dict(commit=git("rev-parse","HEAD"),tree=git("rev-parse","HEAD^{tree}"),
                      theorem_axioms=actual,sources=pins),sort_keys=True))
