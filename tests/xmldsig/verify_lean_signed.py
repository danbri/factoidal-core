"""Verify the XML Signatures that Lean made (`lake exe l4xmldsig ../.. --sign-out DIR`)
with signxml, an independent implementation (lxml canonicalization, pyca/cryptography).

Usage (in a virtual environment with signxml installed):
  python verify_lean_signed.py DIR
DIR/manifest.tsv lists file and key source ('keyvalue': the key of ds:KeyValue;
'hmac': the HMAC key of signing-keys.tsv). Each document is verified, then
verified again after one character of the signed content changed, which must
be refused. Exit 0 when every case gives the expected verdict.

Two known differences of signxml 5.2, each handled by name, not skipped:
  * `SIGNXML_COMMENTS`: a reference `URI=""` gives the document "minus any
    comment nodes" (XML Signature 1.1 §4.4.3.3), also when a WithComments
    method follows. signxml digests the comments, so it must REFUSE these
    signatures; the case fails (STALE) if signxml accepts it.
  * signxml's copy of the XML Signature schema has no declaration for
    `ec:InclusiveNamespaces` (Exclusive XML Canonicalization §4.1), which
    `ds:CanonicalizationMethod` requires under its strict wildcard. A
    document refused by that schema check only is verified again without
    it, and the line says so.
"""
import os, sys
from signxml import XMLVerifier, SignatureMethod, DigestAlgorithm
from signxml.verifier import SignatureConfiguration
from signxml.exceptions import InvalidSignature, InvalidDigest, InvalidInput
from lxml.etree import DocumentInvalid

SIGNXML_COMMENTS = {"rsa-sha256-c14n10c.xml"}

here = os.path.dirname(os.path.abspath(__file__))
keys = dict(l.rstrip("\n").split("\t") for l in open(os.path.join(here, "signing-keys.tsv")) if not l.startswith("#"))
hmac_key = bytes.fromhex(keys["hmac"])
cfg = SignatureConfiguration(require_x509=False, signature_methods=frozenset(SignatureMethod),
                             digest_algorithms=frozenset(DigestAlgorithm))
hcfg = SignatureConfiguration(require_x509=False,
                              signature_methods=frozenset(m for m in SignatureMethod if m.name.startswith("HMAC")),
                              digest_algorithms=frozenset(DigestAlgorithm))

class V(XMLVerifier):
    """XML Signature 1.1 §6.4.2 requires rsa-sha1 for verification; signxml refuses it by default."""
    def check_deprecated_methods(self):
        pass

notes = []

def verify(data, kind, schema=True):
    kw = {"hmac_key": hmac_key} if kind == "hmac" else {}
    try:
        V().verify(data, expect_config=hcfg if kind == "hmac" else cfg, validate_schema=schema, **kw)
        return None
    except DocumentInvalid as e:
        if not schema:
            raise
        notes.append(f"schema check of signxml refused it ({e}); verified without the schema check")
        return verify(data, kind, schema=False)
    except (InvalidSignature, InvalidDigest, InvalidInput) as e:
        return str(e) or type(e).__name__

d = sys.argv[1]
ok = bad = 0
for line in open(os.path.join(d, "manifest.tsv")):
    f, kind = line.rstrip("\n").split("\t")
    data = open(os.path.join(d, f), "rb").read()
    err = verify(data, kind)
    tampered = data.replace(b">one<", b">One<", 1)
    terr = verify(tampered, kind)
    note = f" (note: {notes[0]})" if notes else ""
    notes.clear()
    if f in SIGNXML_COMMENTS:
        if err is not None:
            print(f"PASS {f}: signxml refuses it as expected (it digests the comments that §4.4.3.3 removes): {err}"); ok += 1
        else:
            print(f"FAIL {f}: STALE: signxml accepts it now; remove it from SIGNXML_COMMENTS"); bad += 1
    elif err is None and terr is not None:
        print(f"PASS {f}{note}"); ok += 1
    else:
        print(f"FAIL {f}: verify {err or 'ok'}; tampered {terr or 'accepted'}"); bad += 1
print(f"signxml verification of Lean signatures: {ok} pass, {bad} fail (out of {ok + bad})")
sys.exit(0 if bad == 0 else 1)
