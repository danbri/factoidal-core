#!/usr/bin/env python3
"""Verify a two-file public ASK package against independent caller authority."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import stat
import tempfile

from common import (PUBLIC_FILES, Refusal, check_provenance, load_policy, public_proof,
                    read_bytes, require, run_child, snapshot_software, write_new)


class Parser(argparse.ArgumentParser):
    def error(self, message: str) -> None:
        # argparse's normal error can include arbitrary input/argument text.
        raise Refusal("invalid-arguments")


def verify_package(package: Path, policy: dict, verifier: Path, verifier_sha256: str) -> dict:
    require(stat.S_ISDIR(package.lstat().st_mode), "invalid-public-directory")
    require({entry.name for entry in package.iterdir()} == PUBLIC_FILES, "public-file-allowlist")
    # Take byte snapshots before validation. The SDK sees exactly the bounded
    # bytes validated here even if a submitted package changes concurrently.
    proof_data = read_bytes(package / "ask-proof.json", 4096)
    provenance_data = read_bytes(package / "public-provenance.json", 8192)
    proof = public_proof(proof_data, policy)
    check_provenance(provenance_data, policy)
    with tempfile.TemporaryDirectory(prefix="factoidal-ask-verify-") as name:
        work = Path(name)
        snapshot_software(verifier, work / "verifier", verifier_sha256, True)
        write_new(work / "ask-proof.json", proof_data)
        run_child([str(work / "verifier"), "verify-public", policy["imageId"], policy["policyHash"],
                   policy["contextHash"], str(work / "ask-proof.json")], work, "public-verification")
    return proof


def main() -> None:
    os.umask(0o077)
    parser = Parser(description=__doc__)
    parser.add_argument("--policy", required=True, type=Path)
    parser.add_argument("--verifier-tool", required=True, type=Path)
    parser.add_argument("--verifier-sha256", required=True)
    parser.add_argument("--package", required=True, type=Path)
    args = parser.parse_args()
    verify_package(args.package, load_policy(args.policy), args.verifier_tool, args.verifier_sha256)
    print("verified-true-public-package")


if __name__ == "__main__":
    try:
        main()
    except Refusal as error:
        print("refused:" + str(error))
        raise SystemExit(2) from None
    except (Exception, KeyboardInterrupt):
        print("refused:operation-failed")
        raise SystemExit(2) from None
