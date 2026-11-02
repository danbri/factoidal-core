"""Check the ds:X509Data fixtures of tests/xmldsig/x509/ with signxml, an
implementation independent of the Lean one: each case marked 'valid'
must verify under the signer's certificate, and
'neg-x509-content-changed' must not. (The other negative cases differ only
in the unsigned ds:KeyInfo, so they verify under the signer's certificate.) Key selection itself (the
identifier forms) is the Lean verifier's; signxml is given the
certificate directly.

Usage: python verify_x509_fixtures.py DIR   (exit 0 when all agree)
"""
import os, sys
from cryptography import x509
from signxml import XMLVerifier
from signxml.exceptions import InvalidSignature

d = sys.argv[1]
def pem(n):
    return x509.load_der_x509_certificate(open(os.path.join(d, n), "rb").read()).public_bytes(
        __import__("cryptography.hazmat.primitives.serialization", fromlist=["Encoding"]).Encoding.PEM).decode()
ok = bad = 0
for line in open(os.path.join(d, "manifest.tsv")):
    f, want, _, desc = line.rstrip("\n").split("\t")
    if want == "invalid" and f != "neg-x509-content-changed.xml":
        continue
    cert = pem("leaf-ec.der" if "-ec-" in f else "leaf-rsa.der")
    data = open(os.path.join(d, f), "rb").read()
    try:
        XMLVerifier().verify(data, x509_cert=cert, ignore_ambiguous_key_info=True)
        got = "valid"
    except InvalidSignature:
        got = "invalid"
    res = "PASS" if got == want else "FAIL"
    ok += res == "PASS"; bad += res == "FAIL"
    print(f"{res} {f}: signxml {got}, expected {want}")
print(f"signxml x509 check: {ok} pass, {bad} fail (out of {ok + bad})")
sys.exit(1 if bad else 0)
