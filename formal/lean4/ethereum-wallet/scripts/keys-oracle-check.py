#!/usr/bin/env python3
"""Differential check of the key modules against reference libraries, on fresh material.

Test oracle only (dev and CI). The reference libraries (`mnemonic`, `eth-account`) are
never imported, linked, wrapped or translated by the wallet: this script runs the Lean
executables as separate processes and compares their answers with the libraries'.

Every mnemonic, key and password here is made fresh in this run from `secrets`, is
used for nothing else, lives in memory or in a private temporary directory that is
removed at the end, and is never printed. The report has counts only; a mismatch is
reported by case number and field name.

usage: keys-oracle-check.py <wallet-keys-tests> <wallet-keystore-tests> [cases-per-size]
"""
import json
import os
import secrets
import subprocess
import sys
import tempfile

from eth_account import Account
from mnemonic import Mnemonic


# The Lean executables refuse to touch secrets without this flag (EthereumWallet/Keys/Risk.lean).
RISK_FLAG = "--dangerously-enable-variable-time-secrets"


def compare(field, ours, theirs, mismatches, case):
    if ours != theirs:
        mismatches.append((case, field))
        return 0
    return 1


def derive_check(keys_exe, per_size):
    Account.enable_unaudited_hdwallet_features()
    english = Mnemonic("english")
    entropies = [secrets.token_bytes(size) for size in (16, 20, 24, 28, 32) for _ in range(per_size)]
    out = subprocess.run([keys_exe, RISK_FLAG, "--derive"], input="".join(e.hex() + "\n" for e in entropies),
                         capture_output=True, text=True, check=True).stdout.split("\n")
    matched = {"mnemonic": 0, "masterXprv": 0, "address0": 0, "address1": 0}
    mismatches = []
    for case, entropy in enumerate(entropies):
        fields = out[case].split("\t")
        if len(fields) != 4:
            mismatches.append((case, "output shape"))
            continue
        # The libraries' exceptions can quote the mnemonic: catch them and keep only the
        # case number and the exception's type name.
        try:
            words = english.to_mnemonic(entropy)
            seed = Mnemonic.to_seed(words, passphrase="")
            xprv = Mnemonic.to_hd_master_key(seed)
            addresses = [Account.from_mnemonic(words, account_path=f"m/44'/60'/0'/0/{index}").address
                         for index in (0, 1)]
        except Exception as error:  # noqa: BLE001
            mismatches.append((case, "reference library refused: " + type(error).__name__))
            continue
        matched["mnemonic"] += compare("mnemonic", fields[0], words, mismatches, case)
        matched["masterXprv"] += compare("masterXprv", fields[1], xprv, mismatches, case)
        for index in (0, 1):
            matched[f"address{index}"] += compare(f"address{index}", fields[2 + index],
                                                  addresses[index], mismatches, case)
    # Negative control of the comparison itself: a changed character must be reported.
    control = []
    compare("control", "0xabc", "0xabd", control, -1)
    return {"cases": len(entropies), "matched": matched, "mismatches": mismatches,
            "controlDetected": len(control) == 1}


def keystore_check(keystore_exe, rounds):
    """The reference library makes keystores; our executable must accept the right password
    and refuse a wrong one (key derivation and MAC). Decryption, and keystores made by us,
    are not compared: the repository has no implementation of the keystore's cipher."""
    result = {"cases": rounds, "scryptPasswordAcceptedByUs": 0, "pbkdf2PasswordAcceptedByUs": 0,
              "wrongPasswordRefusedByUs": 0,
              "oursDecryptedByThem": "not run: no AES-128-CTR provider in the tree",
              "mismatches": []}

    def verify(ks_path, pw_path):
        return subprocess.run([keystore_exe, RISK_FLAG, "--verify-password-file", ks_path, pw_path],
                              capture_output=True, text=True)

    with tempfile.TemporaryDirectory() as tmp:
        os.chmod(tmp, 0o700)
        for case in range(rounds):
            key = secrets.token_bytes(32)
            password = secrets.token_urlsafe(18)
            pw_path = os.path.join(tmp, "pw")
            wrong_path = os.path.join(tmp, "pw-wrong")
            ks_path = os.path.join(tmp, "ks.json")
            with open(pw_path, "w") as f:
                f.write(password)
            with open(wrong_path, "w") as f:
                f.write(password + "x")
            for kdf, iterations, field in (("scrypt", 4096, "scryptPasswordAcceptedByUs"),
                                           ("pbkdf2", 2000, "pbkdf2PasswordAcceptedByUs")):
                with open(ks_path, "w") as f:
                    json.dump(Account.encrypt(key, password, kdf=kdf, iterations=iterations), f)
                ours = verify(ks_path, pw_path)
                if ours.returncode == 0 and ours.stdout.strip() == "OK":
                    result[field] += 1
                else:
                    result["mismatches"].append((case, kdf + " right password"))
            # The last keystore written (PBKDF2), with a wrong password: refused with macMismatch.
            refused = verify(ks_path, wrong_path)
            if refused.returncode == 1 and "macMismatch" in refused.stdout:
                result["wrongPasswordRefusedByUs"] += 1
            else:
                result["mismatches"].append((case, "wrong password"))
    return result


def main():
    keys_exe, keystore_exe = sys.argv[1], sys.argv[2]
    per_size = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    report = {"derive": derive_check(keys_exe, per_size), "keystore": keystore_check(keystore_exe, 6)}
    d, k = report["derive"], report["keystore"]
    report["passed"] = (not d["mismatches"] and d["controlDetected"]
                        and all(v == d["cases"] for v in d["matched"].values())
                        and not k["mismatches"]
                        and all(k[f] == k["cases"] for f in ("scryptPasswordAcceptedByUs",
                                                             "pbkdf2PasswordAcceptedByUs",
                                                             "wrongPasswordRefusedByUs")))
    print(json.dumps(report))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
