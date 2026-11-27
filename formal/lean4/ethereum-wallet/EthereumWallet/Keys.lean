import EthereumWallet.Keys.Bip39Theorems
import EthereumWallet.Keys.Bip39Seed
import EthereumWallet.Keys.Bip32Theorems
import EthereumWallet.Keys.Address
import EthereumWallet.Keys.KeystoreJson
import EthereumWallet.Keys.KeystoreAxioms

/-!
# Ethereum wallet: keys

| Module | What |
|---|---|
| `Keys/Bip39*` | BIP-39 English mnemonics: entropy to sentence and back (proved inverse), seed |
| `Keys/Pbkdf2` | PBKDF2 over HMAC-SHA-512 and HMAC-SHA-256, bounded |
| `Keys/Bip32*` | BIP-32 master, private and public child keys, paths, xprv / xpub; BIP-44 path for Ethereum |
| `Keys/Address` | address of a public point; ERC-55 checksum encoding and strict validation |
| `Keys/Scrypt`, `Salsa`, `Aes` | scrypt (RFC 7914) with a memory bound, AES-128-CTR |
| `Keys/Keystore*`, `Json` | Web3 Secret Storage v3: decrypt, encrypt, JSON |
| `Keys/Ripemd160`, `Base58` | for extended-key fingerprints and text |
| `Keys/Hash`, `Keys/Curve` | the only places that reach Keccak-256 and secp256k1 |

## Rules this code keeps

* No network code. Nothing here sends anything anywhere.
* No random number generator. Entropy, salts and IVs are inputs supplied by the host from
  the operating system; every function refuses a wrong length. Whether the bytes are
  random, and never reused, is the host's duty and is not checked here.
* No external implementation. SHA-2 and HMAC are `L4Factoidal.Crypto` (pure Lean);
  Keccak and the curve are `EVMCleanroom` modules; the rest is in this directory.
  Published vectors and the BIP-39 wordlist (specification data) are under
  `third_party/testing/ethereum-wallet`.

## Constant time

Nothing here is claimed to be constant-time.

* **Not constant-time, known.** Private keys, entropy and Base58 payloads are Lean `Nat`s:
  arbitrary-precision (GMP), with timing that depends on the values. Secret-to-public
  derivation (`Secp.pubOfSecret`) is a double-and-add loop branching on key bits. AES uses
  an S-box table indexed by secret bytes. scrypt indexes memory by secret-dependent
  values (by design). BIP-39 word lookup and digit conversion depend on the entropy.
* **Fixed-width word code, not measured.** SHA-256, SHA-512, HMAC, PBKDF2, Keccak and
  RIPEMD-160 have no secret-dependent branches or indices at source level. The Lean
  compiler, the C compiler and the runtime are trusted; no machine-level timing was measured.
* **MAC comparison.** The keystore MAC is compared with `ctEqBytes`, whose source-level
  time depends only on the length. Compiled code not examined.

So this code is for a setting where the attacker cannot time the process or share its
caches. It is not hardened against local side channels.

## Where secrets live, and for how long

Passwords, mnemonics, entropy, seeds, private keys, chain codes, derived keys, AES key
schedules, keystreams and plaintext are ordinary immutable Lean heap values (`ByteArray`,
`String`, `Nat`, lists). They live until the last reference is dropped, then the runtime
frees the memory without clearing it; the allocator may keep and reuse the pages, and
intermediate copies are made freely (appends, slices, big-number temporaries). There is
no zeroisation and no locking of memory against swap. A caller should hold secrets for
as short a time as it can, never log them, and treat the whole process as holding them
until it exits. Errors and refusals carry lengths and reasons, never secret bytes.

## What is proved and what is tested

Proved (theorem names and axioms are printed by the theorem modules and by
`KeystoreAxioms.lean`): BIP-39 `parse` accepts exactly what `generate` produces and
returns its entropy; the refusals (lengths, counts, unknown words, checksum, over-long
input); the BIP-32 invalid-child decision and the shape of derived keys; PBKDF2 and scrypt
parameter bounds, refused before any allocation; the keystore MAC is checked before AES
and a mismatch yields no plaintext; AES-CTR is its own inverse; strict ERC-55 acceptance
implies the text is the checksummed form.

Tested against published vectors, not proved: that the hash, KDF, cipher and curve
functions compute the standard ones; that public child derivation agrees with private
(that needs the curve's group law); JSON reading and writing.
-/
