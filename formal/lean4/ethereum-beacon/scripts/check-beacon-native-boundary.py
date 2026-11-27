#!/usr/bin/env python3
"""Static diagnostic of the actual native Fulu vector runner, not a node claim."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
CHECKER = HERE.parent.parent / "evm-cleanroom/scripts/check-witness-runtime.py"
SPEC = importlib.util.spec_from_file_location("witness_runtime", CHECKER)
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)

BINARY = "beacon-spec-tests"
TRANSITION = re.compile(
    r"^(?:lp_ethereum__beacon_|l_)Beacon_stateTransition(?:___(?:redArg|rarg))?$"
)
INITIALIZER = re.compile(
    r"^initialize_(?:ethereum__beacon_)?BeaconSpecTestsMain$"
)
CRYPTO = re.compile(
    r"lib(?:crypto|ssl|secp256k1|blst|bls|mcl|sodium|gcrypt|nettle|mbedcrypto|"
    r"kzg|relic|botan|hacl|evercrypt|snappy)", re.I
)


def crypto_libraries(names):
    return sorted(n for n in names if CRYPTO.search(n))


def select_symbols(symbols):
    definitions = {n for n, k in symbols if k in ("T", "t")}
    transition = sorted(n for n in definitions if TRANSITION.fullmatch(n))
    initializer = sorted(n for n in definitions if INITIALIZER.fullmatch(n))
    return (transition or ["lp_ethereum__beacon_Beacon_stateTransition"],
            initializer or ["initialize_ethereum__beacon_BeaconSpecTestsMain"])


def controls():
    shared = audit.selftest()
    transition = "lp_ethereum__beacon_Beacon_stateTransition___redArg"
    initializer = "initialize_ethereum__beacon_BeaconSpecTestsMain"
    good = [(n, "T") for n in ("main", "run_main", "lean_initialize_runtime_module",
                              transition, initializer)]
    assert select_symbols(good) == ([transition], [initializer])
    assert select_symbols([(transition, "U")])[0] != [transition]
    audit.REQUIRED_SYMBOLS[BINARY] = {n for n, _ in good}
    assert not audit.analyse_symbols(BINARY, good)["issues"]
    mutations = [
        [(n, k) for n, k in good if n != transition],
        [(n, "U" if n == transition else k) for n, k in good],
        [(n, k) for n, k in good if n != initializer],
        good + [("lean_initialize", "T")],
        good + [("l_Lean_Elab_Term_elabTerm", "T")],
    ]
    for bad in mutations:
        assert audit.analyse_symbols(BINARY, bad)["issues"]
    assert crypto_libraries(["libcrypto.so.3", "libblst.so", "libsnappy.so"])
    assert not crypto_libraries(["libc.so.6", "libgmp.so.10"])
    return shared, len(mutations) + 2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    shared, specific = controls()
    p = args.binary
    sha = hashlib.sha256(p.read_bytes()).hexdigest()
    symbols = audit.symbols_from_nm(
        audit.command(["nm", "--demangle", "--no-sort", str(p)])[0]
    )
    transition, initializer = select_symbols(symbols)
    audit.REQUIRED_SYMBOLS[BINARY] = {
        "main", "run_main", "lean_initialize_runtime_module",
        *transition, *initializer,
    }
    result = audit.inspect_binary(BINARY, p, sha)
    try:
        audit.inspect_binary(BINARY, p, "0" * 64 if sha != "0" * 64 else "1" * 64)
    except ValueError as exc:
        assert "binary differs" in str(exc)
    else:
        raise AssertionError("wrong binary identity survived")
    result["externalCryptoLibraries"] = crypto_libraries(result["neededLibraries"])
    result["issues"].extend("foreign crypto or Snappy library: " + n
                            for n in result["externalCryptoLibraries"])
    result["passed"] = not result["issues"]
    result["checkerSha256"] = hashlib.sha256(CHECKER.read_bytes()).hexdigest()
    result["beaconCheckerSha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["sharedControls"] = shared
    result["beaconControls"] = specific + 1
    result["sourceCommit"] = audit.command(["git", "rev-parse", "HEAD"])[0].strip()
    result["sourceTree"] = audit.command(["git", "rev-parse", "HEAD^{tree}"])[0].strip()
    result["scope"] = "Static runner ELF and direct dependencies; not execution tracing or semantic refinement."
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
