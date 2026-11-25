# XML Signature 1.1: DSA, ECDSA P-384 and P-521, and 1024-bit RSA

Status record, 2026-11-17. Track B item 4 of
https://github.com/danbri/factoidal/issues/1165 (XML specification tracks).

## Owner decisions, 2026-11-17 (verbatim)

> "1223 1224 1227 - do not implement currently. Investigate usage, libraries. Are they obsolete?
> Widely used? Both? 🤢"
> "1227 - off by default and make user pass in a "dangerously_and_regrettsbly_.... " symbol as we
> have done elsewhere somehow."

- https://github.com/danbri/factoidal/issues/1223 (ECDSA P-384 and P-521): not implemented now.
  The 18 interop vectors stay expected failures that name the issue. The issue stays open.
- https://github.com/danbri/factoidal/issues/1224 (DSA): not implemented now. The 15 expected
  failures stay. The issue stays open.
- https://github.com/danbri/factoidal/issues/1227 (1024-bit RSA keys): verification is refused by
  default and is accepted only after an explicit opt-in:
  - Lean: `XML.DSig11.nativeBackendRsa1024`, which needs `Risk.dangerouslyAccept .rsa1024Verify`
    (`L4Factoidal/Risk.lean`, `skills/lean-risk-flags` §5).
  - wasm op `xmlVerify` and npm `xmlVerify`: the option `dangerouslyAndRegrettablyAcceptRsa1024: true`.
    The result then has a `warnings` array.
  - The C entry `l4_hacl_rsa_public_op_1024` (`formal/lean4/ffi/hacl_rsa.c`) is HACL\*'s operation
    for a 128-byte modulus only. `rsaPublicOp` keeps the 2048-bit minimum, so JWS `RS256` does not
    change. Signing keys also keep the 2048-bit minimum.
- Coordinator's reading (not the owner's words): "do not implement currently" means 1223 and 1224
  are deferred, so they no longer block item 4. When the 1227 change is merged, the track B runs
  can start item 5 (XML Encryption 1.1). If the owner reads it differently, this line changes.

## Answer to "obsolete, widely used, or both?"

- **DSA: obsolete. XML Signature 1.1 still REQUIRES DSA-SHA1 verification.** NIST removed DSA
  from FIPS 186-5 (2023) and keeps it only to verify existing signatures. TLS 1.3 forbids it, and
  OpenSSH removed it in 10.0 (2025). WebCrypto never had it. The OpenJDK XML signature code
  refuses `dsa-sha1` by default. No formally verified DSA implementation is known.
- **ECDSA P-384: current, and widely used.** CNSA 1.0 requires it, Let's Encrypt's intermediates
  E5 to E9 use it, and eIDAS lists it. WebCrypto has it everywhere. Upstream HACL\* does not have
  it, but Mozilla NSS ships HACL\*-generated `Hacl_P384` code.
- **ECDSA P-521: current, but rare.** It is approved and in WebCrypto, but browsers removed it
  from TLS key exchange in 2015.
- **1024-bit RSA: obsolete for new signatures, but it is in legacy documents.** It is the
  `rsa1024Verify` risk of this record.

The research notes, with sources, follow. They were made by a research agent on 2026-11-17 from
web sources only. "Unconfirmed" means the claim was not found in a primary source.

---


## 1. What XML Signature 1.1 itself says

Source: https://www.w3.org/TR/xmldsig-core1/ (W3C Recommendation, 11 April 2013), section 6.1 table and sections 6.4.1, 6.4.3, 4.5.2.3.

- Section 6.1 table, "Signature / Required": RSAwithSHA256, ECDSAwithSHA256, and "DSAwithSHA1 (signature verification)" (`http://www.w3.org/2000/09/xmldsig#dsa-sha1`). DSAwithSHA256 (`http://www.w3.org/2009/xmldsig11#dsa-sha256`) is Optional.
- Section 6.4.1, verbatim: "XML Signature 1.1 implementations MAY but are NOT REQUIRED to support DSA-based signature generation. Given the short key size and SP800-57 guidelines, DSA with 1024-bit prime moduli SHOULD NOT be used to create signatures. DSA with 1024-bit prime moduli MAY be used to verify older legacy signatures, with an understanding of the associated risks. Important older signatures SHOULD be re-signed with stronger signatures."
- Section 6.4.1 maps (1024,160) to dsa-sha1, (2048,256) and (3072,256) to dsa-sha256; (2048,224) is not used. SignatureValue is r||s, each I2OSP with l = 20 (the text says 20 even for dsa-sha256; the q = 256-bit case needs 32 octets, so a reader must handle this; the spec text is as quoted).
- Section 6.4.3: "This specification REQUIRES implementations to implement ... ECDSA over the P-256 prime curve ... (and using the SHA-256 hash algorithm) ... It is further RECOMMENDED that implementations also implement algorithms that lead to the same results as ECDSA over the P-384 and P-521 prime curves". r and s are I2OSP'd to the byte size of the base point order (32 for P-256, 66 for P-521).
- Section 4.5.2.3: "Conformant applications MUST support the dsig11:NamedCurve element and the 256-bit prime field curve as identified by the OID 1.2.840.10045.3.1.7." P-384 and P-521 in ECKeyValue are not required.

So: dsa-sha1 verification is REQUIRED; P-384 and P-521 are RECOMMENDED, not required.

XML Signature 2.0 (W3C Working Group Note, 23 July 2015, https://www.w3.org/TR/xmldsig-core2/): same table (DSAwithSHA1 verification Required) and the same 1024-bit DSA text, plus "XML Signature 2.0 maintains compatibility with XML Signature 1.1 for this functionality." There is no later W3C XML Signature work.

XML Signature Best Practices (W3C Working Group Note, 11 April 2013, https://www.w3.org/TR/xmldsig-bestpractices/): informative; I did not find any DSA-specific guidance in it (unconfirmed absence; search only).

## 2. DSA

### 2.1 Standards status

- **FIPS 186-5** (published 3 February 2023, https://csrc.nist.gov/pubs/fips/186-5/final; Federal Register notice https://www.govinfo.gov/content/pkg/FR-2023-02-03/html/2023-02273.htm). The notice says the standard "removes DSA as an approved digital signature algorithm" due to limited industry use and vulnerability concerns, and that DSA "is retained only for the purposes of verifying existing signatures". NIST's comment response: continued verification of existing signatures "will be addressed in a revision to NIST SP 800-131A". The DSA algorithm text is no longer in FIPS 186-5; it stays in FIPS 186-4.
- **NIST SP 800-131A Rev. 2** (March 2019, https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-131Ar2.pdf): DSA (L,N) = (2048,224), (2048,256), (3072,256) "Acceptable" for generation and verification; DSA with L < 2048 or N < 224 is "Legacy use" for verification.
- **NIST SP 800-131A Rev. 3, initial public draft** (October 2024, comments closed 4 December 2024, https://csrc.nist.gov/pubs/sp/800/131/a/r3/ipd; PDF https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-131Ar3.ipd.pdf), section 3, verbatim: "Signature generation using DSA is disallowed." and "Verification of DSA digital signatures is allowed for legacy use when using previously approved domain parameters and private keys." Table: "DSA generation: Disallowed", "DSA verification: Legacy use". I did not find a final Rev. 3 (unconfirmed whether one has been published).
- **ETSI TS 119 312 V1.5.1 (2024-12)** (EU eIDAS cryptographic suites, https://www.etsi.org/deliver/etsi_ts/119300_119399/119312/01.05.01_60/ts_119312v010501p.pdf), clause 6.2.2.2: "The DSA algorithm may be used (SOG-IS recommended mechanism) if the key length is chosen according to clause 8." NOTE: "The dissemination of DSA in trust services is low. Therefore it is suggested to use other more widely deployed algorithms unless it is the only alternative for interoperability. Due to this fact signature suites based on DSA are not listed in annex A." Table 7: log2(p) 1900 to 3000 is legacy to 2028-12-31; log2(p) >= 3000 recommended. 1024-bit DSA is below every listed row. The XAdES annex (A.3) lists RSA, RSA-PSS and ECDSA URIs and no DSA URI. A V2.1.1 exists; its table of contents still has clause 6.2.2.2 DSA (seen in search only; content unconfirmed).
- **IETF TLS**: RFC 8446 (TLS 1.3, August 2018, https://www.rfc-editor.org/rfc/rfc8446) section 1.2 lists "the removal of ... the Digital Signature Algorithm (DSA)"; section 4.2.3: "In particular, MD5 [SLOTH], SHA-224, and DSA MUST NOT be used."
- **IETF JOSE**: RFC 7518 (JWA, May 2015, https://www.rfc-editor.org/rfc/rfc7518) defines no DSA algorithm (checked: no non-ECDSA "DSA" string in the text).
- **SSH**: OpenSSH 7.0 (2015, https://www.openssh.com/txt/release-7.0): "Support for ssh-dss, ssh-dss-cert-* host and user keys is disabled by default at run-time." OpenSSH 10.0 (released 2025-04-09, https://www.openssh.com/txt/release-10.0): "This release removes support for the weak DSA signature algorithm, completing the deprecation process that began in 2015". RFC 9142 (January 2022) is about key exchange methods only; I found no RFC 9142 text about ssh-dss. An IETF list post (https://mail-index.netbsd.org/ietf-ssh/2022/08/26/msg005365.html) says ssh-dss was never formally removed from REQUIRED status in RFC 4253. Whether a later RFC deprecates ssh-dss: unconfirmed.

### 2.2 Real use in XML signatures

No measurement of DSA share in deployed XML signatures was found. Evidence is indirect:

- ETSI (eIDAS, XAdES) says DSA dissemination in trust services is low and gives no XAdES DSA suite (above).
- OpenJDK default `jdk.xml.dsig.secureValidationPolicy` (current `java.security`, https://raw.githubusercontent.com/openjdk/jdk/master/src/java.base/share/conf/security/java.security) has `disallowAlg http://www.w3.org/2000/09/xmldsig#dsa-sha1` (and rsa-sha1, ecdsa-sha1, sha1) plus `minKeySize DSA 1024`. So the JDK's XML signature implementation (derived from Apache Santuario) refuses the W3C-REQUIRED dsa-sha1 by default; dsa-sha256 is not disallowed. Change history: JDK-8259709 "Disable SHA-1 XML Signatures" (2021, https://mail.openjdk.org/pipermail/security-dev/2021-February/024656.html); the exact shipping JDK release was not confirmed from the bug tracker (403).
- Apache Santuario (standalone Java): its secure validation is opt-in in old releases (1.5.0 notes); whether current Santuario blocks dsa-sha1 by default is unconfirmed.
- xmlsec1 (Aleksey Sanin, news page https://www.aleksey.com/xmlsec/news.html; newest 1.3.13, 27 October 2026): still supports DSA and keeps adding to it (DSA-SHA256 for GnuTLS in 1.3.0, April 2023; for MSCNG in 1.3.10, April 2026). 1.3.3 (January 2024) "Disabled KeyValue and DEREncodedKeyValue XML nodes by default"; 1.3.10 "Disabled all raw key value data for all key types by default". So a `ds:DSAKeyValue` (and `ECKeyValue`, `RSAKeyValue`) in KeyInfo is ignored by default in current xmlsec1; keys must come from certificates or configuration.
- signxml (Python, https://github.com/XML-Security/signxml, `signxml/algorithms.py`): defines DSA_SHA1 and DSA_SHA256. Source comment: "SHA1 based algorithms are not secure for use in digital signatures. They are included for legacy compatibility only and disabled by default." So dsa-sha1 is off by default; DSA_SHA256 is present. No changelog entry removing DSA was found.
- .NET `SignedXml`: `XmlDsigDSAUrl` = dsa-sha1 exists (https://apisof.net). Microsoft docs on DSA: "The creators of the DSA algorithm have withdrawn their support for it ... Use DSA only for compatibility with legacy applications and data." .NET 11 removes DSA on macOS (breaking-change page dated 2026-11-10, https://learn.microsoft.com/en-us/dotnet/core/compatibility/cryptography/11/dsa-removed-macos): "Starting in .NET 11, the Digital Signature Algorithm (DSA) is no longer supported on macOS"; Apple's implementation "only supported DSA-1024 with SHA-1"; "iOS, tvOS, and MacCatalyst never supported DSA." Whether .NET SignedXml supports dsa-sha256: unconfirmed.
- Shibboleth XmlSecTool docs list a DSA signing default (DSA + SHA-1) (https://shibboleth.atlassian.net/wiki/spaces/XSTJ4/pages/4227465345/Signing+SAML+Metadata); no current statement on SAML IdPs using DSA was found.

Reading: DSA in XML signatures is a legacy-verification case. No source showed new DSA XML signatures being produced at scale.

### 2.3 Libraries

- OpenSSL 3.x: low-level `DSA_*` functions deprecated since 3.0 (https://docs.openssl.org/3.0/man7/migration_guide/); DSA stays available through the EVP provider API. `no-dsa` build behaviour unconfirmed.
- BoringSSL: `include/openssl/dsa.h` (https://boringssl.googlesource.com/boringssl/+/HEAD/include/openssl/dsa.h): "This module is deprecated and retained for legacy reasons only. It is not considered a priority for performance or hardening work. Do not use it in new code." DSA EVP_PKEY_CTX creation always fails (stub commit); DSA printing removed (https://boringssl.googlesource.com/boringssl/+/ffd31c7c8cae802d7e617c83af3a7d4cf5715c47). Low-level DSA verify still exists.
- Go `crypto/dsa` (https://pkg.go.dev/crypto/dsa): marked Deprecated, "DSA is a legacy algorithm, and modern alternatives such as Ed25519 ... should be used instead"; not constant-time; key generation errors in FIPS 140-only mode.
- RustCrypto `dsa` crate (https://docs.rs/dsa): FIPS 186-4 DSA with RFC 6979; "has never been independently audited for security"; may have timing side channels.
- libgcrypt: still has DSA (used by xmlsec1's gcrypt backend, which xmlsec1 1.3.7 disabled by default). Current libgcrypt DSA status not checked (unconfirmed).
- WebCrypto (W3C Web Cryptography API, https://www.w3.org/TR/WebCryptoAPI/): no DSA algorithm. Node, Deno and browsers therefore offer no DSA through `crypto.subtle`. (Node's non-WebCrypto `crypto` module has DSA through OpenSSL.)

### 2.4 Formally verified DSA

None found. Checked: HACL* (no DSA module in `dist/gcc-compatible`), AWS-LC verification (no DSA; https://github.com/awslabs/aws-lc-verification), Fiat-Crypto (field arithmetic only; no DSA), libjade, SymCrypt verification (published work covers SHA-3 and ML-KEM; https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/). Absence is from search, so "none known" rather than "none exists".

A path that uses only verified primitives: DSA verification is w = s^-1 mod q, u1 = H*w mod q, u2 = r*w mod q, v = (g^u1 * y^u2 mod p) mod q, check v = r. HACL*'s verified generic bignum (`Hacl_Bignum64.h` in https://github.com/hacl-star/hacl-star/tree/main/dist/gcc-compatible) has `Hacl_Bignum64_mod_exp_vartime` (preconditions n odd, 1 < n, a < n), `Hacl_Bignum64_mod_inv_prime_vartime` (n prime), `Hacl_Bignum64_mod`, and multiplication. p and q are odd primes, so these preconditions can be met. The DSA composition itself (the equation above, domain-parameter checks, 0 < r,s < q) would then be ours, written in Lean and proved there, with HACL* as the arithmetic. This is a design option, not an existing verified DSA.

## 3. ECDSA over P-384 and P-521

### 3.1 Standards status and use

- FIPS 186-5 + SP 800-186 (3 February 2023, https://csrc.nist.gov/News/2023/nist-releases-fips-186-5-and-sp-800-186): P-224, P-256, P-384, P-521 remain recommended; binary-field curves (K-/B-) were deprecated. No source found that deprecates P-521 specifically.
- SP 800-131A Rev. 3 draft (October 2024): ECDSA with >= 128-bit strength (len(n) >= 256, so P-256, P-384, P-521) "acceptable"; 112-bit curves (224 <= len(n) < 256) acceptable to 31 December 2030, then deprecated.
- NIST IR 8547 (post-quantum transition): secondary sources report ECDSA (all quantum-vulnerable signatures) deprecated after 2030 and disallowed after 2035 (e.g. https://labs.cloudsecurityalliance.org/research/csa-research-note-nist-ir8547-pqc-transition-20261030-csa-st/). NIST primary text not checked; whether final IR 8547 is published is reported inconsistently (unconfirmed).
- CNSA 1.0: RFC 9206 (NSA, February 2022, https://www.rfc-editor.org/rfc/rfc9206) profiles TLS with "ECDSA [FIPS186] (using the NIST P-384 elliptic curve)" and ECDH P-384. CNSA 2.0 (NSA, September 2022; FAQ updates April and December 2024) moves signatures to ML-DSA-87 (and LMS/XMSS for firmware). NSA primary PDF returned 403; dates for retiring P-384 in National Security Systems (2030 / 2033 / 2035) differ between secondary sources (unconfirmed).
- ETSI TS 119 312 V1.5.1 (2024-12): P-384 and P-521 (and brainpoolP256r1/384r1/512r1) are "R" (recommended) for EC-DSA; XAdES annex lists ecdsa-sha384 and ecdsa-sha512 URIs.
- TLS 1.3 (RFC 8446) defines `ecdsa_secp384r1_sha384` and `ecdsa_secp521r1_sha512`.
- Web PKI: Let's Encrypt's ECDSA intermediates E5 to E9, created 13 March 2024, are ECDSA P-384 (https://letsencrypt.org/2024/03/19/new-intermediate-certificates, https://letsencrypt.org/certificates/). P-384 is in wide production use.
- P-521 in TLS: BoringSSL commit "Remove P-521 from the default supported curves list" (https://boringssl.googlesource.com/boringssl/+/e9fc3e547e557492316932b62881c3386973ceb2); Chrome stopped offering P-521 for key exchange around Chrome 42-46, 2015 (Chromium issue 478225 thread, https://groups.google.com/a/chromium.org/g/chromium-bugs/c/g025fJE5PPs/m/9K8C3nzYlAcJ). Mozilla discussion says this removed P-521 ECDH(E) in TLS, not P-521 from WebCrypto (https://bugzilla.mozilla.org/show_bug.cgi?id=1128792). This is the only "dropping P-521" action found; it concerns TLS key agreement, not ECDSA verification and not standards status.

Reading: P-384 is widely used and mandated in CNSA 1.0. P-521 is approved everywhere, rarely deployed, and was dropped from browser TLS key exchange in 2015.

### 3.2 WebCrypto

- Specification: ECDSA named curves P-256, P-384, P-521.
- Chrome/Chromium: P-256, P-384, P-521 (source `components/webcrypto/algorithms/ec.cc` and `ecdsa.cc`, https://chromium.googlesource.com/chromium/src/+/HEAD/components/webcrypto/algorithms/ec.cc).
- Firefox: P-521 in WebCrypto through NSS (Mozilla bug comments above; Firefox test `dom/crypto/test/test_WebCrypto_ECDSA.html`). Shipping version not checked.
- Safari/WebKit: P-521 on Mac was missing (WebKit bug 216755, filed 2020-09-20); fixed 2021-07-07 in r279688 (https://bugs.webkit.org/show_bug.cgi?id=216755). The Safari version that shipped it is unconfirmed.
- Node.js `crypto.subtle`: P-256/384/521 (Node docs, https://nodejs.org/download/release/v26.3.0/docs/api/webcrypto.html). Deno P-521 support: unconfirmed.

### 3.3 Libraries with formal verification for P-384 / P-521

- **HACL\* (upstream hacl-star)**: `dist/gcc-compatible` on `main` has `Hacl_P256.h` and `Hacl_K256_ECDSA.h`; `Hacl_P384.h` and `Hacl_P521.h` return 404 (checked 2026-11-17). hacl-packages (Cryspen) lists ECDSA P-256 only; issue "enable support for P384 and P521 curves" (https://github.com/cryspen/hacl-packages/issues/431, opened 2023-11-09) is open; the maintainer said in November 2023 they were "in the process of adding P384 and P521 to hacl-star".
- **HACL\* in Mozilla NSS**: NSS 3.101 (released 6 June 2024, https://firefox-source-docs.mozilla.org/security/nss/releases/nss_3_101.html) "Bug 1854439 - Integrate HACL* P-521" and "Bug 1854438 - Integrate HACL* P-384". `security/nss/lib/freebl/verified/Hacl_P384.h` and `Hacl_P521.h` (https://searchfox.org/mozilla-central/source/security/nss/lib/freebl/verified/Hacl_P384.h) are described as "Verified C library for ECDSA and ECDH functions over the P-384 [P-521] NIST curve", MIT licence, "Copyright (c) 2022-2023 HACL* Contributors", with `Hacl_P384_ecdsa_verif_without_hash`, `Hacl_P521_ecdsa_verif_without_hash`, key validation, point conversion, ECDH. NSS 3.95 (November 2023) had "Include P-384 and P-521 Scalar Validation from HACL*". Where the F* source and proofs for this C code live (it is not in upstream hacl-star `main` dist) is unconfirmed. This is the closest thing to a HACL\* P-384/P-521 ECDSA verifier, available as C inside NSS.
- **Fiat-Crypto** (Coq): generates verified field arithmetic for P-384 and P-521 (field layer only; curve and ECDSA logic are not covered). Users: AWS-LC (`third_party/fiat/p384_64.h`, `p521_64.h`; `crypto/fipsmodule/ec/p521.c`: "Implementation of P-521 that uses Fiat-crypto for the field arithmetic"); Go standard library (`crypto/internal/fips140/nistec/fiat/p384_fiat64.go`, `p521_fiat64.go`; README: "autogenerated by the fiat-crypto project at version v0.0.9 from a formally verified model"); RustCrypto `p384` and `p521` crates (field modules state fiat-crypto synthesis). BoringSSL uses fiat for P-256 only (`third_party/fiat/p384_64.h` 404 in BoringSSL). ECCKiila (NSS 3.63 P-384/P-521 code, March 2021) takes "most of the GF(p) arithmetic" from fiat-crypto and states the formal boundary is the field layer (paper https://arxiv.org/pdf/2007.11481).
- **AWS-LC verification** (https://github.com/awslabs/aws-lc-verification): the README has rows for "ECDSA with P-384, SHA-384" (EVP_DigestSign/Verify, SandyBridge+, SAW + Coq) and ECDH P-384, but these rows are now commented out (`<!--- ... --->`) in the current README; the active "Verified Code" table lists only SHA-384/512, HMAC-SHA-384, AES-KW(P), AES-GCM. When present, the ECDSA proof carried caveats, including "EC_Pub_Mul_Correct" (the aG + bP multiplication used by verification is assumed correct) and "ECDSA_k_Valid". The README says AWS now concentrates on s2n-bignum (HOL Light) and CBMC. No P-521 ECDSA proof.
- **s2n-bignum** (AWS, HOL Light, https://github.com/awslabs/s2n-bignum): machine-checked proofs of x86-64 and AArch64 assembly for P-384 and P-521 field operations, point operations, and scalar multiplication (`p384_montjscalarmul`, `p521_jscalarmul` with proof scripts present). Used by AWS-LC when `EC_NISTP_USE_S2N_BIGNUM`. ECDSA verification logic above these routines is C in AWS-LC, not proved by s2n-bignum.
- **libcrux** (Cryspen): `libcrux-ecdsa` is P-256 only (docs "for now only P-256 is supported", https://docs.rs/libcrux-ecdsa/0.0.4/libcrux_ecdsa). No P-384.
- **SymCrypt** (Microsoft): implements ECDSA on NIST curves; published verification (Aeneas + Lean) covers SHA-3 and ML-KEM; nothing found for ECDSA (unconfirmed absence).
- **libjade / Jasmin**: no P-384/P-521 ECDSA found (search not exhaustive; unconfirmed).

## 4. Comparison

| Algorithm | Standards status | Real use in XML signatures | Verified implementation options | WebCrypto |
|---|---|---|---|---|
| DSA-SHA1 (1024-bit) | XMLDSig 1.1: REQUIRED for verification only. FIPS 186-5 (2023): not approved; verify existing only. SP 800-131A r3 draft (2024): generation disallowed, verification legacy use. TLS 1.3: MUST NOT. OpenSSH 10.0 (2025): removed. ETSI: below any listed size, no XAdES suite. | Legacy only. Off by default in OpenJDK XML DSig and signxml. xmlsec1 still verifies, but ignores DSAKeyValue by default. | None known. Option: compose from HACL* verified bignum (modexp, modinv) with a Lean proof of the DSA equation. | No |
| DSA-SHA256 (2048/3072) | XMLDSig 1.1: optional. Same NIST status as above. ETSI: 2048-bit legacy to 2028, 3072-bit recommended, but no XAdES suite. | Very rare (no evidence of use found). Supported by xmlsec1, signxml; not blocked by OpenJDK policy. | Same as above. | No |
| ECDSA P-384 | XMLDSig 1.1: RECOMMENDED. FIPS 186-5 / SP 800-186 approved. CNSA 1.0 mandated (RFC 9206); CNSA 2.0 moves to ML-DSA-87. NIST IR 8547: ECDSA deprecated after 2030, disallowed after 2035 (secondary sources). ETSI: R. | Normal; ETSI XAdES lists ecdsa-sha384; Let's Encrypt intermediates E5-E9 are P-384. | HACL*-generated C in NSS 3.101 (`Hacl_P384`, full ECDSA verify; F* source location unconfirmed). Fiat-Crypto field arithmetic (AWS-LC, Go, RustCrypto). s2n-bignum HOL Light (field, point ops, scalar mult, assembly). AWS-LC SAW/Coq ECDSA P-384 proof now commented out of its README. | Yes (Chrome, Firefox, Safari, Node) |
| ECDSA P-521 | XMLDSig 1.1: RECOMMENDED. FIPS 186-5 / SP 800-186 approved; ETSI R. Not in CNSA 1.0 (Suite B had P-256/P-384 only). No deprecation found. | Rare. ETSI lists ecdsa-sha512 URI (curve not tied to hash). | HACL*-generated C in NSS 3.101 (`Hacl_P521`). Fiat-Crypto field arithmetic (AWS-LC, Go, RustCrypto). s2n-bignum (field, point ops, `p521_jscalarmul`). No end-to-end ECDSA P-521 proof found. | Yes in Chrome, Firefox, Node; Safari since WebKit r279688 (July 2021; shipping version unconfirmed). Removed from Chrome TLS key exchange in 2015, not from WebCrypto. |

## 5. Conclusions

**DSA.** DSA is obsolete. NIST removed it from FIPS 186-5 in 2023 and keeps it only to verify old signatures; TLS 1.3 forbids it; OpenSSH removed it in 2025; Go, BoringSSL, OpenSSL and .NET mark it deprecated or legacy; WebCrypto never had it. ETSI says DSA use in EU trust services is low and gives no XAdES suite for it. No source showed current production of DSA XML signatures. But XML Signature 1.1 (and the 2.0 Note) still make dsa-sha1 verification REQUIRED, and xmlsec1 still verifies it, while the OpenJDK XML signature code refuses dsa-sha1 by default. No formally verified DSA implementation was found. If the project wants a conformant dsa-sha1 verifier from verified parts, the option is HACL*'s verified bignum modular exponentiation and modular inverse, with the DSA equation and parameter checks written and proved in Lean. Otherwise, refusing DSA by default (as OpenJDK does) and recording the gap against the REQUIRED row is in line with current practice.

**ECDSA P-384 / P-521.** These are current, not obsolete. P-384 is widely used (CNSA 1.0, Let's Encrypt intermediates, eIDAS) until the post-quantum move to ML-DSA in the 2030s. P-521 is approved but rare, and browsers dropped it from TLS key exchange in 2015; no standard deprecates it. WebCrypto supports both on all major browsers and Node, so the JavaScript path is available now. For native code, upstream HACL* (`main`) and hacl-packages have only P-256; the HACL*-labelled `Hacl_P384` and `Hacl_P521` ECDSA code is shipped in Mozilla NSS since 3.101 (June 2024), but where its F* proofs are published is unconfirmed. Other verified parts cover only lower layers: Fiat-Crypto field arithmetic (used by AWS-LC, Go, RustCrypto) and s2n-bignum assembly with HOL Light proofs up to scalar multiplication; AWS-LC's earlier end-to-end ECDSA P-384 proof is no longer listed as current.
