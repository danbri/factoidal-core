"""Make the ds:RetrievalMethod fixtures of tests/xmldsig/retrieval/
(XML Signature 1.1 §4.5.3; https://github.com/danbri/factoidal/issues/1228).

Input: the signxml-made fixtures of tests/xmldsig/x509/ (see
make_x509_fixtures.py), x509-rsa-crt.xml (RSA-2048 signer) and
x509-ec-crt.xml (P-256 signer), and their certificates. Each case
replaces the unsigned ds:KeyInfo by a ds:RetrievalMethod and adds the
ds:Object elements it points to. The references of these signatures are
enveloped (URI="" with the enveloped-signature transform), so the
ds:Signature subtree, its ds:KeyInfo and ds:Object included, is outside
what they digest, and the signature value stays valid. Only the Python
standard library and the openssl command are used.

Usage: python3 make_retrieval_fixtures.py X509DIR OUTDIR
Writes OUTDIR/*.xml, copies the certificates the cases name to OUTDIR,
and writes OUTDIR/manifest.tsv with the columns: file, expected outcome,
a text the refusal must contain ('-' for any), description.
"""
import base64, os, re, shutil, subprocess, sys

src, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
DS = "http://www.w3.org/2000/09/xmldsig#"
DS11 = "http://www.w3.org/2009/xmldsig11#"
XPATH = "http://www.w3.org/TR/1999/REC-xpath-19991116"
B64 = "http://www.w3.org/2000/09/xmldsig#base64"
RAW = DS + "rawX509Certificate"


def read(name):
    return open(os.path.join(src, name), encoding="utf-8").read()


def spki(der_file):
    pem = subprocess.run(["openssl", "x509", "-inform", "DER", "-in", os.path.join(src, der_file),
                          "-pubkey", "-noout"], check=True, capture_output=True).stdout
    return subprocess.run(["openssl", "pkey", "-pubin", "-outform", "DER"], input=pem,
                          check=True, capture_output=True).stdout


def rsa_modulus(der_file):
    o = subprocess.run(["openssl", "x509", "-inform", "DER", "-in", os.path.join(src, der_file),
                        "-noout", "-modulus"], check=True, capture_output=True, text=True).stdout
    return bytes.fromhex(o.strip().split("=", 1)[1])


def b64(b):
    return base64.b64encode(b).decode()


def x509data(xml):
    return re.search(r"<ds:X509Data>.*?</ds:X509Data>", xml, re.S).group(0)


def rewrite(xml, keyinfo, objects):
    """Replace ds:KeyInfo and add ds:Object elements after it."""
    new, n = re.subn(r"<ds:KeyInfo>.*?</ds:KeyInfo>", lambda _: keyinfo + objects, xml, flags=re.S)
    assert n == 1
    return new


def rm(uri=None, typ=None, transforms=""):
    a = ""
    if typ is not None:
        a += f' Type="{typ}"'
    if uri is not None:
        a += f' URI="{uri}"'
    body = f"<ds:Transforms>{transforms}</ds:Transforms>" if transforms else ""
    return f"<ds:KeyInfo><ds:RetrievalMethod{a}>{body}</ds:RetrievalMethod></ds:KeyInfo>"


def xpath(expr):
    return f'<ds:Transform Algorithm="{XPATH}"><ds:XPath>{expr}</ds:XPath></ds:Transform>'


B64T = f'<ds:Transform Algorithm="{B64}"/>'

rsa_doc = read("x509-rsa-crt.xml")
ec_doc = read("x509-ec-crt.xml")
rsa_x509 = x509data(rsa_doc)
rsa_der = open(os.path.join(src, "leaf-rsa.der"), "rb").read()
rsa_spki = spki("leaf-rsa.der")
ec_spki = spki("leaf-ec.der")
ec_point = ec_spki[-65:]
assert ec_point[0] == 4

o_keys = f'<ds:Object Id="keys">{rsa_x509}</ds:Object>'
o_crt = f'<ds:Object Id="crt">{b64(rsa_der)}</ds:Object>'
o_spki = (f'<ds:Object><dsig11:DEREncodedKeyValue xmlns:dsig11="{DS11}" Id="spki">'
          f'{b64(rsa_spki)}</dsig11:DEREncodedKeyValue></ds:Object>')
o_kv = (f'<ds:Object Id="kv"><ds:RSAKeyValue><ds:Modulus>{b64(rsa_modulus("leaf-rsa.der"))}</ds:Modulus>'
        f'<ds:Exponent>AQAB</ds:Exponent></ds:RSAKeyValue></ds:Object>')
o_eck = (f'<ds:Object><dsig11:ECKeyValue xmlns:dsig11="{DS11}" Id="eck">'
         f'<dsig11:NamedCurve URI="urn:oid:1.2.840.10045.3.1.7"/>'
         f'<dsig11:PublicKey>{b64(ec_point)}</dsig11:PublicKey></dsig11:ECKeyValue></ds:Object>')
o_inner = f'<ds:Object Id="inner">{rm("leaf-rsa.der", RAW)[len("<ds:KeyInfo>"):-len("</ds:KeyInfo>")]}</ds:Object>'
o_two = f'<ds:Object Id="two">{rsa_x509}{rsa_x509}</ds:Object>'

cases = [
    ("rm-x509data-xpath.xml", rsa_doc, rm("#keys", DS + "X509Data", xpath("ancestor-or-self::ds:X509Data")), o_keys,
     "valid", "-", "Type X509Data; same-document URI and an XPath transform (as Merlin's signature.xml)"),
    ("rm-raw-base64.xml", rsa_doc, rm("#crt", RAW, B64T), o_crt,
     "valid", "-", "Type rawX509Certificate; a ds:Object with base64 DER and the base64 transform"),
    ("rm-raw-external.xml", rsa_doc, rm("leaf-rsa.der", RAW), "",
     "valid", "-", "Type rawX509Certificate; a relative URI that the caller's resolver gives"),
    ("rm-der-encoded.xml", rsa_doc, rm("#spki", DS11 + "DEREncodedKeyValue"), o_spki,
     "valid", "-", "Type dsig11:DEREncodedKeyValue; the element's Id"),
    ("rm-rsa-keyvalue.xml", rsa_doc, rm("#kv", DS + "RSAKeyValue", xpath("ancestor-or-self::ds:RSAKeyValue")), o_kv,
     "valid", "-", "Type RSAKeyValue; an XPath transform selects it in a ds:Object"),
    ("rm-no-type.xml", rsa_doc, rm("#spki"), o_spki,
     "valid", "-", "no Type; the element's name says what it is"),
    ("rm-ec-keyvalue.xml", ec_doc, rm("#eck", DS11 + "ECKeyValue"), o_eck,
     "valid", "-", "Type dsig11:ECKeyValue (P-256, named curve)"),
    ("neg-rm-type-mismatch.xml", rsa_doc, rm("#spki", DS + "RSAKeyValue"), o_spki,
     "invalid", "not its Type", "Type RSAKeyValue, but the URI gives dsig11:DEREncodedKeyValue"),
    ("neg-rm-no-transform.xml", rsa_doc, rm("#keys", DS + "X509Data"), o_keys,
     "invalid", "not its Type", "Type X509Data without the XPath transform: the URI gives the ds:Object"),
    ("neg-rm-chained.xml", rsa_doc, rm("#inner", None, xpath("ancestor-or-self::ds:RetrievalMethod")), o_inner,
     "invalid", "is not followed", "the URI gives another ds:RetrievalMethod: one level only"),
    ("neg-rm-wrong-key.xml", rsa_doc, rm("other.der", RAW), "",
     "invalid", "-", "the certificate is of another key: the signature does not verify"),
    ("neg-rm-no-uri.xml", rsa_doc, rm(None, RAW), "",
     "invalid", "has no URI", "no URI (§4.5.3 makes it mandatory)"),
    ("neg-rm-missing-id.xml", rsa_doc, rm("#nothere", DS + "X509Data"), o_keys,
     "invalid", "no element has the ID", "a same-document URI with an ID no element has"),
    ("neg-rm-raw-nodeset.xml", rsa_doc, rm("#crt", RAW), o_crt,
     "invalid", "must give octets", "Type rawX509Certificate without the base64 transform: a node-set"),
    ("neg-rm-unresolved.xml", rsa_doc, rm("http://example.org/missing.der", RAW), "",
     "invalid", "cannot dereference", "a URI the caller's resolver does not give; nothing is fetched"),
    ("neg-rm-two-elements.xml", rsa_doc, rm("#two", DS + "X509Data", xpath("ancestor-or-self::ds:X509Data")), o_two,
     "invalid", "more than one element", "the transform gives two ds:X509Data elements"),
]

rows = []
for name, doc, ki, objs, want, needle, desc in cases:
    open(os.path.join(out, name), "w", encoding="utf-8").write(rewrite(doc, ki, objs))
    rows.append((name, want, needle, desc))
# content changed after signing: the first case with one item changed
changed = rewrite(rsa_doc, cases[0][2], cases[0][3]).replace(">one<", ">One<", 1)
open(os.path.join(out, "neg-rm-content-changed.xml"), "w", encoding="utf-8").write(changed)
rows.append(("neg-rm-content-changed.xml", "invalid", "does not match", "content changed after signing"))
for f in ["leaf-rsa.der", "other.der"]:
    shutil.copy(os.path.join(src, f), os.path.join(out, f))
with open(os.path.join(out, "manifest.tsv"), "w", encoding="utf-8") as m:
    for r in rows:
        m.write("\t".join(r) + "\n")
print(f"{len(rows)} cases written to {out}")
