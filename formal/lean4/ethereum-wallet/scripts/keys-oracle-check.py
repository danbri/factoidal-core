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


def compare(field, ours, theirs, mismatches, case):
    if ours != theirs:
        mismatches.append((case, field))
        return 0
    return 1


def derive_check(keys_exe, per_size):
    Account.enable_unaudited_hdwallet_features()
    english = Mnemonic("english")
    entropies = [secrets.token_bytes(size) for size in (16, 20, 24, 28, 32) for _ in range(per_size)]
    out = subprocess.run([keys_exe, "--derive"], input="".join(e.hex() + "\n" for e in entropies),
                         capture_output=True, text=True, check=True).stdout.split("\n")
    matched = {"mnemonic": 0, "masterXprv": 0, "address0": 0, "address1": 0}
    mismatches = []
    for case, entropy in enumerate(entropies):
        fields = out[case].split("\t")
        if len(fields) != 4:
            mismatches.append((case, "output shape"))
            continue
        words = english.to_mnemonic(entropy)
        seed = Mnemonic.to_seed(words, passphrase="")
        matched["mnemonic"] += compare("mnemonic", fields[0], words, mismatches, case)
        matched["masterXprv"] += compare("masterXprv", fields[1], Mnemonic.to_hd_master_key(seed),
                                         mismatches, case)
        for index in (0, 1):
            address = Account.from_mnemonic(words, account_path=f"m/44'/60'/0'/0/{index}").address
            matched[f"address{index}"] += compare(f"address{index}", fields[2 + index], address,
                                                  mismatches, case)
    # Negative control of the comparison itself: a changed character must be reported.
    control = []
    compare("control", "0xabc", "0xabd", control, -1)
    return {"cases": len(entropies), "matched": matched, "mismatches": mismatches,
            "controlDetected": len(control) == 1}


def keystore_check(keystore_exe, rounds):
    result = {"cases": rounds, "theirsDecryptedByUs": 0, "oursDecryptedByThem": 0,
              "wrongPasswordRefusedByUs": 0, "pbkdf2DecryptedByUs": 0, "mismatches": []}
    with tempfile.TemporaryDirectory() as tmp:
        os.chmod(tmp, 0o700)
        for case in range(rounds):
            key = secrets.token_bytes(32)
            password = secrets.token_urlsafe(18)
            pw_path = os.path.join(tmp, "pw")
            ks_path = os.path.join(tmp, "ks.json")
            with open(pw_path, "w") as f:
                f.write(password)
            # Reference library encrypts (scrypt, n = 4096), we decrypt.
            with open(ks_path, "w") as f:
                json.dump(Account.encrypt(key, password, kdf="scrypt", iterations=4096), f)
            ours = subprocess.run([keystore_exe, "--decrypt-file", ks_path, pw_path],
                                  capture_output=True, text=True).stdout.strip()
            if ours == key.hex():
                result["theirsDecryptedByUs"] += 1
            else:
                result["mismatches"].append((case, "scrypt decrypt"))
            # A wrong password must be refused with macMismatch.
            with open(pw_path, "w") as f:
                f.write(password + "x")
            refused = subprocess.run([keystore_exe, "--decrypt-file", ks_path, pw_path],
                                     capture_output=True, text=True)
            if refused.returncode != 0 and "macMismatch" in refused.stdout:
                result["wrongPasswordRefusedByUs"] += 1
            else:
                result["mismatches"].append((case, "wrong password"))
            with open(pw_path, "w") as f:
                f.write(password)
            # Reference library encrypts with PBKDF2 (c = 2000), we decrypt.
            with open(ks_path, "w") as f:
                json.dump(Account.encrypt(key, password, kdf="pbkdf2", iterations=2000), f)
            ours = subprocess.run([keystore_exe, "--decrypt-file", ks_path, pw_path],
                                  capture_output=True, text=True).stdout.strip()
            if ours == key.hex():
                result["pbkdf2DecryptedByUs"] += 1
            else:
                result["mismatches"].append((case, "pbkdf2 decrypt"))
            # We encrypt (salt and IV supplied here, as the host would), the library decrypts.
            secret_path = os.path.join(tmp, "secret")
            with open(secret_path, "w") as f:
                f.write(key.hex())
            made = subprocess.run([keystore_exe, "--encrypt-file", secret_path, pw_path,
                                   secrets.token_hex(32), secrets.token_hex(16), "4096", "8", "1"],
                                  capture_output=True, text=True).stdout
            try:
                if bytes(Account.decrypt(json.loads(made), password)) == key:
                    result["oursDecryptedByThem"] += 1
                else:
                    result["mismatches"].append((case, "our keystore, their decrypt"))
            except Exception as error:  # the library's own refusal; no secret in its type name
                result["mismatches"].append((case, "our keystore refused: " + type(error).__name__))
    return result


def main():
    keys_exe, keystore_exe = sys.argv[1], sys.argv[2]
    per_size = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    report = {"derive": derive_check(keys_exe, per_size), "keystore": keystore_check(keystore_exe, 6)}
    d, k = report["derive"], report["keystore"]
    report["passed"] = (not d["mismatches"] and d["controlDetected"]
                        and all(v == d["cases"] for v in d["matched"].values())
                        and not k["mismatches"]
                        and all(k[f] == k["cases"] for f in ("theirsDecryptedByUs", "oursDecryptedByThem",
                                                             "wrongPasswordRefusedByUs", "pbkdf2DecryptedByUs")))
    print(json.dumps(report))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
