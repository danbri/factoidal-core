# W3C XML Encryption 1.1 interop test cases (subset)

Source: the XML Security Working Group's test-case document for XML
Encryption 1.1, https://www.w3.org/TR/xmlenc-core1-testcases/ (editor's
draft and files: https://www.w3.org/2008/xmlsec/Drafts/xmlenc-core-11/test-cases/,
directory `files/`). Fetched 2026-10-27. The files are unmodified copies,
except that two Microsoft files carry a `microsoft-` prefix in their names.
Licence: W3C Document License
(https://www.w3.org/Consortium/Legal/2015/doc-license), as the test-case
document states for the Working Group's material.

| file here | original path under `files/` | case |
| --- | --- | --- |
| `cipherText__RSA-2048__aes128-gcm__rsa-oaep-mgf1p.xml` | `oracle/` | WRAP.1 |
| `cipherText__RSA-3072__aes192-gcm__rsa-oaep-mgf1p__Sha256.xml` | `oracle/` | WRAP.2 |
| `cipherText__RSA-3072__aes256-gcm__rsa-oaep__Sha384-MGF_Sha1.xml` | `oracle/` | WRAP.3 |
| `cipherText__RSA-4096__aes256-gcm__rsa-oaep__Sha512-MGF_Sha1_PSource.xml` | `oracle/` | WRAP.4 |
| `cipherText__EC-P256__aes128-gcm__kw-aes128__ECDH-ES__ConcatKDF.xml` | `oracle/` | AGRMNT.1 |
| `cipherText__EC-P384__aes192-gcm__kw-aes192__ECDH-ES__ConcatKDF.xml` | `oracle/` | AGRMNT.2 |
| `cipherText__EC-P521__aes256-gcm__kw-aes256__ECDH-ES__ConcatKDF.xml` | `oracle/` | AGRMNT.3 |
| `cipherText__DH-1024__aes128-gcm__kw-aes128__dh-es__ConcatKDF.xml` | `oracle/` | AGRMNT.7 |
| `cipherText__EC-P256__aes128-gcm__kw-aes256__ECDH-ES__pbkdf2.xml` | `oracle/` | AGRMNT.9 (key agreement with PBKDF2) |
| `plaintext.xml` | `oracle/` | the plaintext of the Oracle cases |
| `microsoft-xenc11-example-AES128-GCM.xml` | `microsoft/xenc11-example-AES128-GCM.xml` | SYM.1 |
| `microsoft-dkey-example-ConcatKDF-crypto.xml` | `microsoft/dkey-example-ConcatKDF-crypto.xml` | DRV.1 |
| `microsoft-dkey-example-PBKDF2-crypto.xml` | `microsoft/dkey-example-PBKDF2-crypto.xml` | DRV.2 (added 2026-11-22) |

`keys.json`: the private keys of `oracle/RSA-2048_SHA256WithRSA.p12` and
`oracle/EC-P256_SHA256WithECDSA.p12` (password `passwd`, as the test-case
document gives), converted to JWKs with
`openssl pkcs12 -legacy -nocerts -nodes` and Node's
`KeyObject.export({format: "jwk"})`. They are published test keys. On 2026-11-17 the keys of
`oracle/RSA-3072_SHA256WithRSA.p12` and `oracle/RSA-4096_SHA256WithRSA.p12`
were added in the same way (kids `oracle-RSA-3072`, `oracle-RSA-4096`), for
WRAP.2 to WRAP.4. A case's `key` in `cases.json` names the one key the
harnesses give it, because the documents name their keys by certificate only.

`cases.json` records the expected outcomes of the XML Encryption profile.
The native and Wasm harnesses require WRAP.1, WRAP.3 and WRAP.4 to recover
`plaintext.xml`. AGRMNT.1 requires AES Key Wrap on the JavaScript host.
AGRMNT.9 is an expected failure: the reader accepts its PBKDF2 key
derivation (§5.4.2), but no derivation found gives a key encryption key
that unwraps its key (https://github.com/danbri/factoidal/issues/1303).
Natively it must reach the AES Key Wrap request; on Wasm it must fail with
the decryption error, and the test fails if it ever decrypts.
The remaining cases expect the named refusals for AES-192, P-521 or finite
field Diffie-Hellman.

Added 2026-11-22. SYM.1 has no `Type`: the harnesses ask for its plaintext
octets (`xmlDecrypt` member `octets`) and compare them with the hex string of
the test-case document (`d9313225f88406e5a55909c5aff5269a`, key
`feffe9928665731c6d6a8f9467308308`, kid `Test Key 1` in `keys.json`). DRV.1
(Concat KDF) and DRV.2 (PBKDF2, HMAC-SHA-256, 1024 iterations) use
`xenc11:DerivedKey`. Their master keys are from the test-case document and
`microsoft/KDF-test-data.txt`: the 32 octets `00 01 ... 37` (kid `Secret1`)
and the octets of `PASSWORD` (kid `Our shared secret`). Both are defective
test data: the 336-octet CipherValue is the IV and exactly the 320-octet
plaintext of `KDF-test-data.txt`, with no padding block, but XML
Encryption 1.1 §5.2 says the padding always adds at least one octet. This
was checked with Node's crypto (AES-256-CBC with automatic padding off, keys
from `sha256(00000001 || Z || OtherInfo)` and from PBKDF2). The harnesses
count them apart, as "excluded (defective test data)". They check that the
key Lean derives is the key Node derives (`derivedKeyHex`). The Wasm test
also checks that the octets are not the stated plaintext, and fails if they
ever are. Evidence: https://github.com/danbri/factoidal/issues/1303. Run `lake exe l4xmlenc-probe`
and `node --test tests/xmlenc/wasm.mjs` using a Wasm build of the same source.

Not used: the key derivation cases DRV.3 and DRV.4 (binary files), the Microsoft
key agreement cases (binary plaintext under `Type` Element, and P-384,
P-521 and DH), AGRMNT.4 to AGRMNT.8 and AGRMNT.10 (binary plaintext, P-384, P-521, DH).
