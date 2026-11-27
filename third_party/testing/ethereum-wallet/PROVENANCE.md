# Ethereum wallet: published specification data and test vectors

Used by `formal/lean4/ethereum-wallet` (keys: BIP-39, BIP-32, EIP-55, keystore v3).
Everything here is published specification data or published test vectors, copied
unmodified, fetched 2026-11-27. None of it is an implementation, and none of it is
linked into or translated into the wallet code. The BIP-39 English wordlist is the
one piece that reaches a runtime executable: it is specification data, and
`formal/lean4/ethereum-wallet/scripts/gen-keys-data.py` turns it into the generated
module `EthereumWallet/Keys/Bip39English.lean` (CI regenerates and compares).

The secrets in these files are published test vectors. They are public: never use
any of these keys, mnemonics or passwords for anything of value.

| File | Source | Upstream commit | Licence | sha256 |
|---|---|---|---|---|
| `bip-0039/english.txt` | https://github.com/bitcoin/bips/blob/master/bip-0039/english.txt | 9f3d3bc6a60db16efbdc71ac8f7ea30217fc0c39 | MIT (BIP-39) | 2f5eed53a4727b4bf8880d8f3f199efc90e58503646d9ff8eff3a2ed3b24dbda |
| `bip-0039/bip-0039.mediawiki` | https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki | 9f3d3bc6a60db16efbdc71ac8f7ea30217fc0c39 | MIT (stated in the file) | afcbcbed36fe9eb734bd607398a8c124683ded2a75c3830e1b16c47b043a9134 |
| `bip-0039/vectors.json` | https://github.com/trezor/python-mnemonic/blob/master/vectors.json (the vectors BIP-39 names as its test vectors) | b57a5ad77a981e743f4167ab2f7927a55c1e82a8 | MIT (`bip-0039/python-mnemonic-LICENSE`) | fa3b937b7cff9c9b8ecd3aa011faeb8d6dd67993174b72326e83f4de8fdb30f8 |
| `bip-0032/bip-0032.mediawiki` | https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki (test vectors 1 to 5) | 9f3d3bc6a60db16efbdc71ac8f7ea30217fc0c39 | BSD-2-Clause (stated in the file) | e5e00a8289db2f681052cf24a745320afc225e66b25d1e489a7c884d2fc7f11f |
| `erc-55/erc-55.md` | https://github.com/ethereum/ERCs/blob/master/ERCS/erc-55.md | 00fb734f812e7428ee1732eb4afbf31b93d2ba0d | CC0 (stated in the file) | 54a9b25ffcd12966c60d6abd6584734d2793734f266fbe41118e6ee52b05dc9e |
| `go-ethereum/v3_test_vector.json` | https://github.com/ethereum/go-ethereum/blob/master/accounts/keystore/testdata/v3_test_vector.json | bbafd66b66f5e37e877bf1efe3506ad74a6eda98 | LGPL-3.0-or-later (go-ethereum library); test data only, unmodified, kept separate, never linked | e3a43355d86d11c78f4025597b2e9012aa4fedfcfd07daeabd4b67fafbad5d7d |

Only the `english` entry of `bip-0039/vectors.json` is used so far; the other eleven
languages need their wordlists and Unicode NFKD, which are later work.

Vectors from RFC 7914 (scrypt, Salsa20/8, BlockMix, ROMix, and section 11's
PBKDF2-HMAC-SHA256), RFC 4231 (HMAC) and the RIPEMD-160 paper are short and are written
out in the test modules with their section numbers. PBKDF2-HMAC-SHA512 is covered by the
BIP-39 seeds. RFC 6070 (PBKDF2-HMAC-SHA1) is not used: the wallet has no SHA-1 PBKDF2.
There are no AES vectors because the tree has no AES (skills/aes-hardware-only).
