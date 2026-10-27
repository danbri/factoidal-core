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
| `cipherText__EC-P256__aes128-gcm__kw-aes256__ECDH-ES__pbkdf2.xml` | `oracle/` | key agreement with PBKDF2 |
| `plaintext.xml` | `oracle/` | the plaintext of the Oracle cases |
| `microsoft-xenc11-example-AES128-GCM.xml` | `microsoft/xenc11-example-AES128-GCM.xml` | SYM.1 |
| `microsoft-dkey-example-ConcatKDF-crypto.xml` | `microsoft/dkey-example-ConcatKDF-crypto.xml` | DRV.1 |

`keys.json`: the private keys of `oracle/RSA-2048_SHA256WithRSA.p12` and
`oracle/EC-P256_SHA256WithECDSA.p12` (password `passwd`, as the test-case
document gives), converted to JWKs with
`openssl pkcs12 -legacy -nocerts -nodes` and Node's
`KeyObject.export({format: "jwk"})`. They are published test keys.

`cases.json` gives the outcome each case has in the profile of
`formal/lean4/L4Factoidal/XML/Enc.lean`: WRAP.1 decrypts (natively and in
the wasm); AGRMNT.1 decrypts where AES Key Wrap is available (the wasm with
WebCrypto); the others are refused by the allowlist (AES-192, OAEP with
SHA-384 or SHA-512 digests and MGF1-SHA-1, P-521, finite
field Diffie-Hellman, PBKDF2, no `Type`). Run by `lake exe l4xmlenc-probe`
(section `w3c`) and `node --test tests/xmlenc/wasm.mjs`.

Not used: the IBM and Microsoft key derivation cases DRV.2 to DRV.4 (PBKDF2
and `xenc11:DerivedKey`, outside the profile, like DRV.1), the Microsoft
key agreement cases (binary plaintext under `Type` Element, and P-384,
P-521 and DH), AGRMNT.4 to AGRMNT.9 (binary plaintext, P-384, P-521, DH).
