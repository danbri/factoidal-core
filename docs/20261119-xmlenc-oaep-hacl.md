# Checked RSA-OAEP hashes for XML Encryption

XML Encryption 1.1 lets the label digest differ from the MGF1 hash. The 1.0
URI fixes MGF1-SHA-1. Both default the label digest to SHA-1. The 1.1 URI
also defaults MGF1 to SHA-1. The XML writer continues to emit its two
equal-hash configurations. [W3C RSA-OAEP](https://www.w3.org/TR/xmlenc-core1/#sec-RSA-OAEP)
and [track B, item 5](https://github.com/danbri/factoidal/issues/1165).

## Runtime and trust

Native and Wasm XML operations both use `Enc.nativePrims`. Its checked
digest provider uses HACL* for all five hashes. SHA-224 uses internal code
5 on the existing hash extern. The shim calls `Hacl_Hash_SHA2_hash_224`
from the same vendored SHA-2 unit as SHA-256, SHA-384 and SHA-512.
The page-facing WebCrypto hash names have their existing four values.

Every OAEP hash call can refuse. MGF1 checks each digest length and the
final mask length before XOR. A failed check during key transport reaches
the existing XML decryption error. The pure model and the runtime share
the EME encoding, unmasking and final padding checks.

`RsaOaep.mgf1Checked_length` states the length of every successful mask.
`checked_none_of_no_sized_digest` and `mgf1Checked_none_of_block` describe
refusal on a missing or wrong-sized digest.
`mgf1Checked_agrees`, `emeEncodeChecked_agrees` and
`emeDecodeChecked_agrees` relate successful results to the pure functions
if each successful digest agrees with its specified value and the sizes
match. `WebHacl.sha224ForXml?_size` states the successful output size.
These are Lean statements about the construction. SHA values depend on
HACL* and its shim. Compiled constant-time behaviour of the Lean EME code
has no proof here. The earlier pure round-trip theorems retain their
statements, including the RSA-inversion hypothesis in
`oaepDecrypt_oaepEncrypt`.

## Independent interop cases

`tests/xmlenc/openssl-oaep.json` uses the public example key from RFC 7516
Appendix A.1, already present in `tests/jose/jwe-vectors.json`. OpenSSL
`pkeyutl -encrypt` produced two independent RSA wraps with
`rsa_padding_mode:oaep` and the label `XML OAEP interop`. The digest and
MGF1 options were SHA-224/SHA-512 and SHA-384/SHA-224. OpenSSL decrypted
both wraps back to the expected 16-byte key during fixture generation.
Node's AES-128-GCM encrypted the one shared plaintext and verified its
tag. The fixture stores the IV, ciphertext and tag as one XML CipherValue.
The cases use only published example key material.
[RFC 7516 Appendix A.1](https://www.rfc-editor.org/rfc/rfc7516#appendix-A.1).

`l4vc-probe` checks the SHA-224 digest of `abc` at the HACL* binding.
The native XML probe checks the same vector through the XML provider, both
OpenSSL documents and the W3C WRAP.3/WRAP.4 documents. The Wasm test decrypts the
same four documents. Build-time guards inject a refusing digest and a
short digest at a later MGF counter in an otherwise valid XML document.

## Validation

Use the full corpus gate and run the following in `formal/lean4/`.

```sh
lake build L4Factoidal.Crypto.RsaOaepChecked L4Factoidal.XML.EncTests l4xmlenc-probe
lake exe l4vc-probe
lake exe l4xmlenc-probe
lake exe l4jwe-probe 20
```

Build Wasm from the same candidate commit. From the repository root run
the following against its installed assets.

```sh
node --test tests/xmlenc/wasm.mjs
node tests/jose/jwe-wasm.mjs
```

The earlier native result was 25 pass, 0 fail and 6 host-only out of 31
at `d81ec759`. The new candidate needs its own native and Wasm results.
[Earlier native run](https://github.com/danbri/factoidal-core/actions/runs/44154819750/job/134292595848).

## Independent review checkpoint

A separate strongest-model review accepted the checked XML OAEP design for
exact-head validation. Source tracing found no checked XML path converting a
refused or short digest to a zero-padded successful mask. The generic
`withMasks` helper itself accepts arbitrary masks; its callers retain the
width obligation. Both writer configurations agree with their emitted metadata.
At `cba8bc578`, Lean 4.33.1 compiled 26 modules from fresh source, ran the XML
guards and printed the axioms for all seven new statements and the three
existing OAEP theorems. The hygiene audit passed. [Compiler run and generated
C](https://github.com/danbri/factoidal-core/actions/runs/44472399316/job/135384789246).

## wasm32 bound checks

At that commit, the generated bodies of `mgf1Checked` and `sha224ForXml?`
each constructed `lean_cstr_to_nat("4294967296")`. On wasm32, the runtime
allocates a heap object for this value. Multiplication borrowed the first
object and comparison borrowed the second. Both bodies lost the reference
on return. This leaves one allocation per MGF1 call with a nonzero digest
size and one per SHA-224 call. The diagnosis comes from the generated C
and the pinned runtime. Measuring the effect on OAEP heap use would require
an instrumented Wasm run.
[Lean allocation code](https://github.com/leanprover/lean4/blob/v4.33.1/src/runtime/object.cpp#L1386-L1400).

The two guards now use `L4Factoidal.two32`, the existing
`@[reducible, noinline]` constant for this wasm32 representation. The
WebHacl guard keeps its named `u32Bound` definition and marks it
`@[noinline]`. The compiler check for this change is that each guard reads
a module constant that the runtime marks persistent during initialisation.
The bounded workflow preserves generated C for both guards and the shared
constant so this can be checked on each candidate. [Earlier wasm32 bound
measurements](designissues/2026-09-07-wasm-packer-memory.md).

The change covers XML RSA-OAEP. Pre-existing XML ECDH-ES ConcatKDF still hashes
its shared secret with pure SHA-256, and JOSE still uses pure OAEP hash
profiles. Those runtime policy gaps remain separate; this patch establishes
no whole-XML or whole-JOSE policy-completion claim. Same-source **full** Wasm
is required because the core module refuses XML operations. Tests of digest
values and independent fixtures remain test evidence, not proofs of the
extern's agreement hypothesis or compiled constant-time behaviour.
