#!/usr/bin/env python3
"""Turn execution-specs state-test fixtures into transaction signing vectors.

A state-test fixture gives the transaction fields, the published test private
key (`secretKey`) and, for each case, the raw signed bytes (`txbytes`). That
is exactly a signing vector: fields + key -> raw. This script reads fixtures
only; it runs no part of any Ethereum implementation.

usage: eest-sign-vectors.py <state_tests/for_X dir> <out.json> [--per-kind N] [--max-raw BYTES]

Without --per-kind every distinct signed transaction is written. With it, the
N first by SHA-256 of the raw bytes are kept for each transaction kind, so the
committed subset is stable. Cases the fixture marks `expectException` are kept
and flagged: the wallet may refuse them, but if it signs, bytes must match.
"""
import glob
import hashlib
import json
import sys


def rlp_items(b):
    """Top-level list members (raw encodings are enough to find `v`)."""
    def read(i):
        t = b[i]
        if t < 0x80:
            return i, i + 1, False
        if t < 0xb8:
            return i + 1, i + 1 + t - 0x80, False
        if t < 0xc0:
            n = t - 0xb7
            return i + 1 + n, i + 1 + n + int.from_bytes(b[i + 1:i + 1 + n], "big"), False
        if t < 0xf8:
            return i + 1, i + 1 + t - 0xc0, True
        n = t - 0xf7
        return i + 1 + n, i + 1 + n + int.from_bytes(b[i + 1:i + 1 + n], "big"), True
    start, stop, is_list = read(0)
    assert is_list and stop == len(b)
    out = []
    i = start
    while i < stop:
        s, e, _ = read(i)
        out.append(b[s:e])
        i = e
    return out


def kind_of(tx):
    if "authorizationList" in tx:
        return 4
    if "blobVersionedHashes" in tx:
        return 3
    if "maxFeePerGas" in tx:
        return 2
    if "accessLists" in tx:
        return 1
    return 0


def main():
    args = sys.argv[1:]
    per_kind = None
    max_raw = None
    if "--per-kind" in args:
        i = args.index("--per-kind")
        per_kind = int(args[i + 1])
        del args[i:i + 2]
    if "--max-raw" in args:
        i = args.index("--max-raw")
        max_raw = int(args[i + 1])
        del args[i:i + 2]
    root, out_path = args
    seen = {}
    for path in sorted(glob.glob(root + "/**/*.json", recursive=True)):
        with open(path) as handle:
            doc = json.load(handle)
        for name, test in doc.items():
            tx = test["transaction"]
            if "secretKey" not in tx:
                continue
            kind = kind_of(tx)
            for fork, posts in test["post"].items():
                for post in posts:
                    raw = post.get("txbytes")
                    if not raw or raw in seen:
                        continue
                    idx = post["indexes"]
                    data = tx["data"][idx["data"]]
                    if max_raw is not None and (len(raw) - 2) // 2 > max_raw:
                        continue
                    chain = tx.get("chainId")
                    if kind == 0:
                        items = rlp_items(bytes.fromhex(raw[2:]))
                        v = int.from_bytes(items[6], "big")
                        if v in (27, 28):
                            chain = None
                    fields = {
                        "type": hex(kind),
                        "chainId": chain,
                        "nonce": tx["nonce"],
                        "gas": tx["gasLimit"][idx["gas"]],
                        "to": tx.get("to") or None,
                        "value": tx["value"][idx["value"]],
                        "input": data,
                    }
                    if kind < 2:
                        fields["gasPrice"] = tx["gasPrice"]
                    else:
                        fields["maxFeePerGas"] = tx["maxFeePerGas"]
                        fields["maxPriorityFeePerGas"] = tx["maxPriorityFeePerGas"]
                    if kind >= 1:
                        lists = tx.get("accessLists") or [[]]
                        access = lists[idx["data"]] if idx["data"] < len(lists) else []
                        fields["accessList"] = access or []
                    if kind == 3:
                        fields["maxFeePerBlobGas"] = tx["maxFeePerBlobGas"]
                        fields["blobVersionedHashes"] = tx["blobVersionedHashes"]
                    if kind == 4:
                        fields["authorizationList"] = [
                            {k: a[k] for k in ("chainId", "address", "nonce", "yParity", "r", "s")}
                            for a in tx["authorizationList"]
                        ]
                    seen[raw] = {
                        "name": name.split("::")[-1][:160],
                        "kind": kind,
                        "testKey": tx["secretKey"],
                        "sender": tx.get("sender"),
                        "tx": fields,
                        "raw": raw,
                        "fixtureExpectsException": post.get("expectException"),
                    }
    vectors = list(seen.values())
    vectors.sort(key=lambda v: hashlib.sha256(bytes.fromhex(v["raw"][2:])).hexdigest())
    if per_kind is not None:
        kept = []
        count = {}
        for v in vectors:
            if count.get(v["kind"], 0) < per_kind:
                kept.append(v)
                count[v["kind"]] = count.get(v["kind"], 0) + 1
        vectors = kept
    by_kind = {}
    for v in vectors:
        by_kind[v["kind"]] = by_kind.get(v["kind"], 0) + 1
    doc = {
        "source": "ethereum/execution-specs release tests@v21.0.3, fixtures.tar.gz "
                  "(sha256 46bd48fb71a23da084218fe856fe442ab0c8d00c85c1c1aead0d2a965804fd24), "
                  "state_tests: transaction fields, published test key and txbytes of each case",
        "note": "Test oracle data only. testKey values are published fixture keys; they must never hold funds.",
        "selection": "all distinct txbytes" if per_kind is None else
                     f"first {per_kind} per kind by SHA-256 of txbytes"
                     + ("" if max_raw is None else f", raw transaction at most {max_raw} bytes"),
        "countByKind": {str(k): by_kind[k] for k in sorted(by_kind)},
        "vectors": vectors,
    }
    with open(out_path, "w") as handle:
        json.dump(doc, handle, separators=(",", ":"))
        handle.write("\n")
    print(json.dumps({"written": len(vectors), "byKind": doc["countByKind"]}))


if __name__ == "__main__":
    main()
