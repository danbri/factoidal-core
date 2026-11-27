#!/usr/bin/env python3
"""Every recursive function the tail-recursion audit finds in the ABI, typed-data
and call modules must be listed here with what bounds its depth. A function the
audit reports that is not listed fails the check, so a new recursion over an
input length cannot arrive unnoticed.

usage: check-abi-recursion.py <tail-audit.txt>
"""
import re
import sys

TYPE = "nesting of the ABI type, at most maxTypeDepth (32) for types from outside"
ARITY = "number of members of one tuple type, at most maxSigChars (2048) characters of type string"
BOUNDS = {
    "EthereumWallet_Abi_beNat": "at most 32 (bytes of a word)",
    "EthereumWallet_Abi_AbiType_isDynamic": TYPE,
    "EthereumWallet_Abi_anyDynamic": ARITY,
    "EthereumWallet_Abi_AbiType_headSize": TYPE,
    "EthereumWallet_Abi_headSizeL": ARITY,
    "EthereumWallet_Abi_AbiType_wf": TYPE,
    "EthereumWallet_Abi_wfL": ARITY,
    "EthereumWallet_Abi_AbiType_depth": TYPE,
    "EthereumWallet_Abi_depthL": ARITY,
    "EthereumWallet_Abi_AbiType_canonical": TYPE,
    "EthereumWallet_Abi_canonicalL": ARITY,
    "EthereumWallet_Abi_AbiType_check": TYPE,
    "EthereumWallet_Abi_checkL": ARITY,
    "EthereumWallet_Abi_AbiType_enc": TYPE,
    "EthereumWallet_Abi_encL": ARITY,
    "EthereumWallet_Abi_AbiType_encBA": TYPE,
    "EthereumWallet_Abi_encLBA": ARITY,
    "EthereumWallet_Abi_AbiType_decodeAt": TYPE,
    "EthereumWallet_Abi_fieldDecs": ARITY,
    "EthereumWallet_Abi_parseTy": "tuple nesting, refused past maxTypeDepth (32)",
    "EthereumWallet_Abi_parseItems": "tuple nesting, refused past maxTypeDepth (32); the member loop is a tail call",
    "EthereumWallet_Eip712_parseValue": "JSON nesting, refused past maxJsonDepth (64)",
    "EthereumWallet_Eip712_parseElems": "JSON nesting, refused past maxJsonDepth (64); the element loop is a tail call",
    "EthereumWallet_Eip712_parseMembers": "JSON nesting, refused past maxJsonDepth (64); the member loop is a tail call",
    "EthereumWallet_Eip712_encodeField": "fuel maxDataDepth + 1 (33); encodeField_depth_refused",
    "EthereumWallet_Calls_Rlp_encode": "applied only to the two-item CREATE preimage",
    "EthereumWallet_Calls_Rlp_encodeList": "applied only to the two-item CREATE preimage",
    "valueOfJson": "test tool only: nesting of the ABI type",
    "valuesOfJson": "test tool only: members of one tuple type",
}


def main():
    text = open(sys.argv[1]).read()
    found = set(re.findall(r"^\d+\s+(\S+)\s+(?:length|depth|counter|unknown)\s", text, re.M))
    count = re.search(r"NOT a `goto _start` loop: (\d+)", text)
    if not count or int(count.group(1)) == 0 or not found:
        print("the audit found no recursion at all: it did not read this package's symbols")
        sys.exit(1)
    unlisted = sorted(found - set(BOUNDS))
    for name in sorted(found):
        print(f"{name}: {BOUNDS.get(name, 'NOT LISTED')}")
    if unlisted:
        print("recursive functions with no stated bound:", unlisted)
        sys.exit(1)
    print(f"{len(found)} recursive declarations, each with a stated bound")


if __name__ == "__main__":
    main()
