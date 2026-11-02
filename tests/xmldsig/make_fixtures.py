"""Make the project-local XML Signature 1.1 fixtures of tests/xmldsig/fixtures/.

The signatures are made by signxml (lxml canonicalization, pyca/cryptography
keys and signatures), an implementation independent of the Lean one. The
2012 W3C interop vectors use 1024-bit RSA keys, which the HACL* RSA public
operation refuses; these fixtures give the RSA-2048 cases.

Usage (in a virtual environment with signxml installed):
  python make_fixtures.py OUTDIR
Writes OUTDIR/*.xml, OUTDIR/manifest.tsv (file, expected outcome, HMAC key
or '-', description). The keys are generated per run and are not kept.
"""
import os, sys
from lxml import etree
from cryptography.hazmat.primitives.asymmetric import rsa, ec
from cryptography.hazmat.primitives import serialization
from signxml import XMLSigner, XMLVerifier, SignatureMethod, DigestAlgorithm, CanonicalizationMethod as C
from signxml.algorithms import SignatureConstructionMethod as SCM

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
rsa_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
ec_key = ec.generate_private_key(ec.SECP256R1())

DOC = b'<doc xmlns="urn:example:doc" xmlns:x="urn:example:x" ID="d1"><x:item n="1">one</x:item><!--c--><item n="2">two &amp; &lt;three&gt;</item></doc>'
rows = []

class Signer(XMLSigner):
    """XML Signature 1.1 §6.2.1 and §6.4.2 still require SHA-1 for
    verification; signxml refuses it by default, so the fixtures turn the
    refusal off to make the SHA-1 cases."""
    def check_deprecated_methods(self):
        pass

def sign(fname, key, sm, dm, c14n=C.EXCLUSIVE_XML_CANONICALIZATION_1_0, method=SCM.enveloped, ref=None, doc=DOC, desc=""):
    root = etree.fromstring(doc)
    s = Signer(method=method, signature_algorithm=sm, digest_algorithm=dm, c14n_algorithm=c14n)
    kw = {}
    if ref is not None: kw["reference_uri"] = ref
    if sm.name.startswith("HMAC"):
        signed = s.sign(root, key=key, **kw)
    else:
        signed = s.sign(root, key=key, always_add_key_value=True, **kw)
    data = etree.tostring(signed)
    open(os.path.join(out, fname), "wb").write(data)
    rows.append((fname, "valid", key.decode() if isinstance(key, bytes) else "-", desc))
    return data

H = {"sha1": DigestAlgorithm.SHA1, "sha224": DigestAlgorithm.SHA224, "sha256": DigestAlgorithm.SHA256,
     "sha384": DigestAlgorithm.SHA384, "sha512": DigestAlgorithm.SHA512}
for h, dm in H.items():
    sign(f"rsa2048-{h}.xml", rsa_key, getattr(SignatureMethod, "RSA_" + h.upper()), dm,
         desc=f"enveloped, URI '', RSA-2048 PKCS#1 v1.5 {h}, exc-c14n")
for h in ("sha1", "sha224", "sha256", "sha384", "sha512"):
    sign(f"hmac-{h}.xml", b"secret", getattr(SignatureMethod, "HMAC_" + h.upper()), DigestAlgorithm.SHA256,
         desc=f"enveloped, HMAC-{h}, key 'secret'")
sign("p256-sha256.xml", ec_key, SignatureMethod.ECDSA_SHA256, DigestAlgorithm.SHA256,
     desc="enveloped, ECDSA P-256 SHA-256, ECKeyValue")
for nm, c in (("c14n10", C.CANONICAL_XML_1_0), ("c14n10c", C.CANONICAL_XML_1_0_WITH_COMMENTS),
              ("c14n11", C.CANONICAL_XML_1_1), ("c14n11c", C.CANONICAL_XML_1_1_WITH_COMMENTS),
              ("exc10c", C.EXCLUSIVE_XML_CANONICALIZATION_1_0_WITH_COMMENTS)):
    sign(f"rsa2048-sha256-{nm}.xml", rsa_key, SignatureMethod.RSA_SHA256, DigestAlgorithm.SHA256, c14n=c,
         desc=f"enveloped, RSA-2048 SHA-256, {nm}")
    if nm.endswith("c"):
        # signxml digests the comment of the referenced element. XML Signature
        # 1.1 §4.4.3.3: a '#ID' reference gives the element and its descendants
        # "but not comments", so the digest does not match and core validation
        # refuses the signature.
        f, _, k, _ = rows[-1]
        rows[-1] = (f, "invalid", k, f"enveloped, URI '#d1', {nm}: signxml digested the comment that §4.4.3.3 removes")
sign("rsa2048-sha256-id.xml", rsa_key, SignatureMethod.RSA_SHA256, DigestAlgorithm.SHA256, ref="#d1",
     desc="enveloped, URI '#d1' (an ID attribute)")
sign("rsa2048-sha256-enveloping.xml", rsa_key, SignatureMethod.RSA_SHA256, DigestAlgorithm.SHA256,
     method=SCM.enveloping, desc="enveloping, ds:Object")

def mutate(src, dst, old, new, desc):
    data = open(os.path.join(out, src), "rb").read()
    assert old in data, (src, old)
    open(os.path.join(out, dst), "wb").write(data.replace(old, new, 1))
    rows.append((dst, "invalid", "-", desc))

mutate("rsa2048-sha256.xml", "neg-content-changed.xml", b">one<", b">One<", "content changed after signing: digest mismatch")
mutate("rsa2048-sha256-id.xml", "neg-wrapped-duplicate-id.xml", b'<doc xmlns="urn:example:doc" xmlns:x="urn:example:x" ID="d1">',
       b'<doc xmlns="urn:example:doc" xmlns:x="urn:example:x" ID="d1"><evil ID="d1"/>', "a second element with the referenced ID (signature wrapping)")
d = open(os.path.join(out, "rsa2048-sha256.xml"), "rb").read()
i = d.index(b"<ds:SignatureValue>") + len(b"<ds:SignatureValue>")
c = d[i:i+1]; d2 = d[:i] + (b"B" if c != b"B" else b"C") + d[i+1:]
open(os.path.join(out, "neg-signature-value.xml"), "wb").write(d2)
rows.append(("neg-signature-value.xml", "invalid", "-", "first character of SignatureValue changed"))
mutate("hmac-sha256.xml", "neg-hmac-wrong-key.xml", b"", b"", "HMAC with the wrong key")
rows[-1] = ("neg-hmac-wrong-key.xml", "invalid", "Secret", "HMAC verified with the key 'Secret'")

with open(os.path.join(out, "manifest.tsv"), "w") as f:
    for r in rows: f.write("\t".join(r) + "\n")
print(len(rows), "fixtures")
