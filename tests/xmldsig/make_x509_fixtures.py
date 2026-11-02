"""Make the ds:X509Data fixtures of tests/xmldsig/x509/ (XML Signature 1.1
§4.5.4; https://github.com/danbri/factoidal/issues/1226).

signxml (lxml canonicalization, pyca/cryptography keys and certificates)
signs each document; this script then rewrites the unsigned ds:KeyInfo to
the X509Data form of the case. The keys and certificates are generated per
run; the certificates are written next to the fixtures (*.der) because some
cases name them only by an identifier, and the caller supplies them.

Usage (in a virtual environment with signxml installed):
  python make_x509_fixtures.py OUTDIR
Writes OUTDIR/*.xml, OUTDIR/*.der and OUTDIR/manifest.tsv with the columns
file, expected outcome, certificates the caller gives (comma-separated or
'-'), description.
"""
import base64, datetime, hashlib, os, re, sys
from lxml import etree
from cryptography import x509
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import rsa, ec
from signxml import XMLSigner, SignatureMethod, DigestAlgorithm

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
now = datetime.datetime(2026, 11, 1, tzinfo=datetime.timezone.utc)

def name(cn):
    return x509.Name([x509.NameAttribute(NameOID.COUNTRY_NAME, "GB"),
                      x509.NameAttribute(NameOID.ORGANIZATION_NAME, "Factoidal Test, Ltd."),
                      x509.NameAttribute(NameOID.COMMON_NAME, cn)])

def cert(subject_key, cn, issuer_key, issuer_cn, serial, ca=False):
    b = (x509.CertificateBuilder().subject_name(name(cn)).issuer_name(name(issuer_cn))
         .public_key(subject_key.public_key()).serial_number(serial)
         .not_valid_before(now).not_valid_after(now + datetime.timedelta(days=3650))
         .add_extension(x509.SubjectKeyIdentifier.from_public_key(subject_key.public_key()), critical=False)
         .add_extension(x509.BasicConstraints(ca=ca, path_length=None), critical=True))
    return b.sign(issuer_key, hashes.SHA256())

ca_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
rsa_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
ec_key = ec.generate_private_key(ec.SECP256R1())
other_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
ca = cert(ca_key, "Test CA", ca_key, "Test CA", 1, ca=True)
leaf = cert(rsa_key, "RSA Signer", ca_key, "Test CA", 4096)
leaf_ec = cert(ec_key, "EC Signer", ca_key, "Test CA", 0x0102030405060708090A)
other = cert(other_key, "Other", other_key, "Other", 7)
certs = {"ca": ca, "leaf-rsa": leaf, "leaf-ec": leaf_ec, "other": other}
for k, c in certs.items():
    open(os.path.join(out, k + ".der"), "wb").write(c.public_bytes(serialization.Encoding.DER))

def der(c): return c.public_bytes(serialization.Encoding.DER)
def b64(b): return base64.b64encode(b).decode()
def ski(c): return c.extensions.get_extension_for_class(x509.SubjectKeyIdentifier).value.digest

DOC = b'<doc xmlns="urn:example:doc"><item n="1">one</item><item n="2">two</item></doc>'
DS = "http://www.w3.org/2000/09/xmldsig#"
rows = []

def sign(key, sm):
    s = XMLSigner(signature_algorithm=sm, digest_algorithm=DigestAlgorithm.SHA256)
    return etree.tostring(s.sign(etree.fromstring(DOC), key=key, always_add_key_value=True))

def with_keyinfo(signed, inner):
    """Replace the unsigned ds:KeyInfo by <ds:KeyInfo><ds:X509Data>inner</ds:X509Data></ds:KeyInfo>."""
    s = signed.decode()
    s2, n = re.subn(r"<ds:KeyInfo>.*</ds:KeyInfo>",
                    "<ds:KeyInfo><ds:X509Data>" + inner + "</ds:X509Data></ds:KeyInfo>", s, flags=re.S)
    assert n == 1
    return s2.encode()

def crt(c): return "<ds:X509Certificate>" + b64(der(c)) + "</ds:X509Certificate>"
def dn(n): return n.rfc4514_string().replace("&", "&amp;").replace("<", "&lt;")

def case(fname, want, given, desc, data):
    open(os.path.join(out, fname), "wb").write(data)
    rows.append((fname, want, ",".join(k + ".der" for k in given) or "-", desc))

s_rsa = sign(rsa_key, SignatureMethod.RSA_SHA256)
s_ec = sign(ec_key, SignatureMethod.ECDSA_SHA256)
case("x509-rsa-crt.xml", "valid", [], "X509Certificate of the RSA-2048 signer", with_keyinfo(s_rsa, crt(leaf)))
case("x509-ec-crt.xml", "valid", [], "X509Certificate of the P-256 signer", with_keyinfo(s_ec, crt(leaf_ec)))
case("x509-rsa-chain-leaf-first.xml", "valid", [], "end-entity certificate, then its CA",
     with_keyinfo(s_rsa, crt(leaf) + crt(ca)))
case("x509-rsa-chain-ca-first.xml", "valid", [], "CA certificate, then the end-entity one",
     with_keyinfo(s_rsa, crt(ca) + crt(leaf)))
case("x509-rsa-digest.xml", "valid", ["ca", "leaf-rsa", "other"], "only dsig11:X509Digest (SHA-256); the caller gives three certificates",
     with_keyinfo(s_rsa, '<dsig11:X509Digest xmlns:dsig11="http://www.w3.org/2009/xmldsig11#" Algorithm="http://www.w3.org/2001/04/xmlenc#sha256">'
                  + b64(hashlib.sha256(der(leaf)).digest()) + "</dsig11:X509Digest>"))
case("x509-rsa-digest-sha512.xml", "valid", ["ca", "leaf-rsa"], "only dsig11:X509Digest (SHA-512)",
     with_keyinfo(s_rsa, '<dsig11:X509Digest xmlns:dsig11="http://www.w3.org/2009/xmldsig11#" Algorithm="http://www.w3.org/2001/04/xmlenc#sha512">'
                  + b64(hashlib.sha512(der(leaf)).digest()) + "</dsig11:X509Digest>"))
case("x509-rsa-ski.xml", "valid", ["ca", "leaf-rsa"], "only X509SKI",
     with_keyinfo(s_rsa, "<ds:X509SKI>" + b64(ski(leaf)) + "</ds:X509SKI>"))
case("x509-rsa-subject.xml", "valid", ["ca", "leaf-rsa"], "only X509SubjectName (RFC 4514, with an escaped comma)",
     with_keyinfo(s_rsa, "<ds:X509SubjectName>" + dn(leaf.subject) + "</ds:X509SubjectName>"))
case("x509-ec-issuer-serial.xml", "valid", ["ca", "leaf-rsa", "leaf-ec"], "only X509IssuerSerial (an 80-bit serial number)",
     with_keyinfo(s_ec, "<ds:X509IssuerSerial><ds:X509IssuerName>" + dn(leaf_ec.issuer) + "</ds:X509IssuerName><ds:X509SerialNumber>"
                  + str(leaf_ec.serial_number) + "</ds:X509SerialNumber></ds:X509IssuerSerial>"))
case("x509-rsa-all.xml", "valid", [], "certificate, subject name, issuer and serial, SKI and digest together",
     with_keyinfo(s_rsa, crt(ca) + crt(leaf) + "<ds:X509SubjectName>" + dn(leaf.subject) + "</ds:X509SubjectName>"
                  + "<ds:X509IssuerSerial><ds:X509IssuerName>" + dn(leaf.issuer) + "</ds:X509IssuerName><ds:X509SerialNumber>4096</ds:X509SerialNumber></ds:X509IssuerSerial>"
                  + "<ds:X509SKI>" + b64(ski(leaf)) + "</ds:X509SKI>"))
# negative cases
case("neg-x509-wrong-crt.xml", "invalid", [], "the X509Certificate is of another key: the signature does not verify",
     with_keyinfo(s_rsa, crt(other)))
case("neg-x509-digest-unknown.xml", "invalid", ["ca", "other"], "X509Digest of a certificate the caller does not give",
     with_keyinfo(s_rsa, '<dsig11:X509Digest xmlns:dsig11="http://www.w3.org/2009/xmldsig11#" Algorithm="http://www.w3.org/2001/04/xmlenc#sha256">'
                  + b64(hashlib.sha256(der(leaf)).digest()) + "</dsig11:X509Digest>"))
case("neg-x509-conflict.xml", "invalid", ["ca", "leaf-rsa"], "X509SubjectName of the signer and X509SKI of the CA: no certificate matches both",
     with_keyinfo(s_rsa, "<ds:X509SubjectName>" + dn(leaf.subject) + "</ds:X509SubjectName><ds:X509SKI>" + b64(ski(ca)) + "</ds:X509SKI>"))
case("neg-x509-two-leaves.xml", "invalid", [], "two unrelated certificates and no identifier: no single end-entity certificate",
     with_keyinfo(s_rsa, crt(leaf) + crt(other)))
case("neg-x509-wrong-serial.xml", "invalid", ["ca", "leaf-rsa"], "X509IssuerSerial with a serial number no certificate has",
     with_keyinfo(s_rsa, "<ds:X509IssuerSerial><ds:X509IssuerName>" + dn(leaf.issuer) + "</ds:X509IssuerName><ds:X509SerialNumber>4097</ds:X509SerialNumber></ds:X509IssuerSerial>"))
case("neg-x509-content-changed.xml", "invalid", [], "content changed after signing",
     with_keyinfo(s_rsa, crt(leaf)).replace(b">one<", b">One<", 1))

with open(os.path.join(out, "manifest.tsv"), "w") as f:
    for r in rows: f.write("\t".join(r) + "\n")
print(len(rows), "fixtures")
