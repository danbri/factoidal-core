// Makes the XML Encryption 1.1 fixtures of tests/xmlenc/fixtures.json
// (https://github.com/danbri/factoidal/issues/1084, SAML:
// https://github.com/danbri/factoidal/issues/1073) with Apache Santuario
// (org.apache.santuario:xmlsec 4.0.4) and the JDK's XML Signature API.
// Independent of the Lean code.
//
//   CP=$(cat cp.txt)   # xmlsec 4.0.4 and its runtime dependencies, from Maven Central
//   java -cp "$CP" tests/xmlenc/MakeFixtures.java > tests/xmlenc/fixtures.json
//
// Each run makes new keys and new random content keys, so the output
// changes; the checks (`lake exe l4xmlenc-probe`, tests/xmlenc/wasm.mjs) do not.
import java.io.StringWriter;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.*;
import java.security.interfaces.*;
import java.security.spec.*;
import java.time.Instant;
import java.util.*;
import javax.crypto.KeyGenerator;
import javax.crypto.SecretKey;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.XMLConstants;
import javax.xml.crypto.dsig.*;
import javax.xml.crypto.dsig.dom.DOMSignContext;
import javax.xml.crypto.dsig.keyinfo.*;
import javax.xml.crypto.dsig.spec.*;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.apache.xml.security.encryption.*;
import org.apache.xml.security.encryption.params.*;
import org.apache.xml.security.keys.KeyInfo;
import org.apache.xml.security.utils.EncryptionConstants;
import org.w3c.dom.*;

public class MakeFixtures {
    static final String SAML = "urn:oasis:names:tc:SAML:2.0:assertion";
    static final long NB = 1761313600L;
    static final SecureRandom RNG = new SecureRandom();

    static KeyPair rsa, idp, ec, x25519;
    static SecretKey kek128, kek256;

    public static void main(String[] a) throws Exception {
        org.apache.xml.security.Init.init();
        KeyPairGenerator g = KeyPairGenerator.getInstance("RSA");
        g.initialize(2048);
        rsa = g.generateKeyPair();
        idp = g.generateKeyPair();
        KeyPairGenerator eg = KeyPairGenerator.getInstance("EC");
        eg.initialize(new ECGenParameterSpec("secp256r1"));
        ec = eg.generateKeyPair();
        x25519 = KeyPairGenerator.getInstance("X25519").generateKeyPair();
        kek128 = aesKey(128);
        kek256 = aesKey(256);

        List<String> cases = new ArrayList<>();
        // Key transport with RSA-OAEP: decrypted natively and through the wasm.
        cases.add(elementCase("gcm128-oaep-mgf1p", XMLCipher.AES_128_GCM, 128, "oaep-mgf1p", false, true, null));
        cases.add(elementCase("gcm256-oaep11-sha256", XMLCipher.AES_256_GCM, 256, "oaep11-sha256", false, true, null));
        cases.add(elementCase("gcm256-oaep11-default", XMLCipher.AES_256_GCM, 256, "oaep11-sha1", false, true, null));
        cases.add(elementCase("content-gcm128-oaep-mgf1p", XMLCipher.AES_128_GCM, 128, "oaep-mgf1p", true, true, null));
        cases.add(elementCase("gcm128-oaep-mgf1p-retrieval", XMLCipher.AES_128_GCM, 128, "oaep-mgf1p", false, true, "retrieval"));
        // Key agreement and key wrap: AES Key Wrap is a host (WebCrypto) operation.
        cases.add(elementCase("gcm128-ecdh-p256-kw128", XMLCipher.AES_128_GCM, 128, "ecdh-p256", false, false, null));
        cases.add(elementCase("gcm256-x25519-kw256", XMLCipher.AES_256_GCM, 256, "x25519", false, false, null));
        cases.add(elementCase("gcm128-kek-kw128", XMLCipher.AES_128_GCM, 128, "kek128", false, false, null));
        cases.add(elementCase("gcm256-kek-kw256", XMLCipher.AES_256_GCM, 256, "kek256", false, false, null));
        // CBC: refused unless the caller opts in; then a host operation.
        cases.add(elementCase("cbc128-oaep-mgf1p", XMLCipher.AES_128, 128, "oaep-mgf1p", false, false, "cbc"));
        // RSA PKCS #1 v1.5 key transport: always refused.
        cases.add(elementCase("gcm128-rsa15", XMLCipher.AES_128_GCM, 128, "rsa15", false, true, "refused"));

        // SAML: a signed assertion, encrypted as a whole (RSA-OAEP, AES-128-GCM).
        Document signed = build("_e1", "https://id.example/end-user", idp);
        String samlEncAssertion = b64url(serialize(encryptedAssertion(signed)));
        // SAML: an assertion whose NameID is encrypted (saml:EncryptedID), then signed.
        Document withEid = assertion("_e2", "https://id.example/hidden-user");
        encryptNameId(withEid);
        sign(withEid, idp);
        String samlEncId = b64url(serialize(withEid));
        // SAML: an encrypted assertion whose content is NOT signed.
        String samlUnsigned = b64url(serialize(encryptedAssertion(assertion("_e3", "https://id.example/end-user"))));

        RSAPublicKey ipk = (RSAPublicKey) idp.getPublic();
        StringBuilder b = new StringBuilder();
        b.append("{\n \"generator\": \"tests/xmlenc/MakeFixtures.java, Apache Santuario xmlsec 4.0.4, ")
         .append(System.getProperty("java.vendor")).append(" ").append(System.getProperty("java.version")).append("\",\n")
         .append(" \"keys\": [").append(rsaJwk(rsa, "rsa-1")).append(",\n  ")
         .append(ecJwk(ec, "ec-1")).append(",\n  ")
         .append(okpJwk(x25519, "x-1")).append(",\n  ")
         .append(octJwk(kek128, "kek128")).append(",\n  ")
         .append(octJwk(kek256, "kek256")).append("],\n")
         .append(" \"cases\": [\n  ").append(String.join(",\n  ", cases)).append("],\n")
         .append(" \"saml\": {\"idpN\": \"").append(hex(ipk.getModulus())).append("\", \"idpE\": \"")
         .append(hex(ipk.getPublicExponent())).append("\", \"now\": ").append(NB + 10)
         .append(", \"encryptedAssertion\": \"").append(samlEncAssertion)
         .append("\", \"encryptedId\": \"").append(samlEncId)
         .append("\", \"unsignedInside\": \"").append(samlUnsigned).append("\"}\n}\n");
        new java.io.PrintStream(System.out, true, StandardCharsets.UTF_8).print(b);
    }

    // ---------------------------------------------------------------- cases

    static String sampleDoc() {
        return "<r:order xmlns:r=\"urn:example:order\" xmlns:p=\"urn:example:pay\" id=\"o1\">"
             + "<r:item n=\"2\">tea &amp; cake</r:item>"
             + "<p:card r:kind=\"debit\"><p:number>4019 2445 0277 5567</p:number><!-- c --><p:exp>2028-04</p:exp><p:holder>Zo\u00eb \u6771\u4eac</p:holder></p:card>"
             + "<r:note>&lt;not markup&gt; é</r:note></r:order>";
    }

    /** One case: the p:card element (or its content) of `sampleDoc` encrypted. */
    static String elementCase(String name, String dataAlg, int bits, String kt, boolean content,
                              boolean nativeOk, String variant) throws Exception {
        Document doc = parse(sampleDoc());
        String expected = serialize(doc);
        Element card = (Element) doc.getElementsByTagNameNS("urn:example:pay", "card").item(0);
        SecretKey cek = aesKey(bits);
        XMLCipher c = XMLCipher.getInstance(dataAlg);
        c.init(XMLCipher.ENCRYPT_MODE, cek);
        EncryptedData ed = c.getEncryptedData();
        EncryptedKey ek = encryptKey(doc, cek, kt);
        KeyInfo ki = new KeyInfo(doc);
        if ("retrieval".equals(variant)) {
            ek.setId("ek1");
            org.apache.xml.security.keys.content.RetrievalMethod rm =
                new org.apache.xml.security.keys.content.RetrievalMethod(doc, "#ek1", null,
                    "http://www.w3.org/2001/04/xmlenc#EncryptedKey");
            ki.add(rm);
        } else {
            ki.add(ek);
        }
        ed.setKeyInfo(ki);
        c.doFinal(doc, card, content);
        if ("retrieval".equals(variant)) {
            Element ekEl = c.martial(doc, ek);
            doc.getDocumentElement().appendChild(ekEl);
        }
        String outcome = "refused".equals(variant) ? "refused" : "cbc".equals(variant) ? "needsAllowCbc" : "ok";
        String encrypted = serialize(doc);
        // The expected plaintext document is Santuario's own decryption of the
        // encrypted document; with no RetrievalMethod it must be the original.
        String santuario = santuarioDecrypt(encrypted, kekFor(kt));
        if (!"retrieval".equals(variant) && !santuario.equals(expected))
            throw new IllegalStateException(name + ": Santuario's decryption differs from the original");
        return "{\"name\": \"" + name + "\", \"native\": " + nativeOk + ", \"outcome\": \"" + outcome
            + "\", \"document\": " + json(encrypted) + ", \"expected\": " + json(santuario) + "}";
    }

    static Key kekFor(String kt) {
        switch (kt) {
            case "kek128": return kek128;
            case "kek256": return kek256;
            case "ecdh-p256": return ec.getPrivate();
            case "x25519": return x25519.getPrivate();
            default: return rsa.getPrivate();
        }
    }

    static String santuarioDecrypt(String text, Key kek) throws Exception {
        Document d = parse(text);
        NodeList eks = d.getElementsByTagNameNS(EncryptionConstants.EncryptionSpecNS, "EncryptedKey");
        for (int i = 0; i < eks.getLength(); i++) {
            Element k = (Element) eks.item(i);
            if (k.hasAttribute("Id")) k.setIdAttribute("Id", true);
        }
        Element ed = (Element) d.getElementsByTagNameNS(EncryptionConstants.EncryptionSpecNS, "EncryptedData").item(0);
        XMLCipher c = XMLCipher.getInstance();
        if (d.getElementsByTagNameNS("http://www.w3.org/2000/09/xmldsig#", "RetrievalMethod").getLength() > 0) {
            // Santuario's key resolvers do not follow a RetrievalMethod to an
            // EncryptedKey here; unwrap the referenced key explicitly.
            XMLCipher kc = XMLCipher.getInstance();
            kc.init(XMLCipher.UNWRAP_MODE, kek);
            EncryptedKey ek = kc.loadEncryptedKey(d, (Element) eks.item(0));
            Element em = (Element) ed.getElementsByTagNameNS(EncryptionConstants.EncryptionSpecNS, "EncryptionMethod").item(0);
            Key cek = kc.decryptKey(ek, em.getAttribute("Algorithm"));
            c.init(XMLCipher.DECRYPT_MODE, cek);
        } else {
            c.init(XMLCipher.DECRYPT_MODE, null);
            c.setKEK(kek);
        }
        c.doFinal(d, ed);
        return serialize(d);
    }

    static EncryptedKey encryptKey(Document doc, SecretKey cek, String kt) throws Exception {
        switch (kt) {
            case "oaep-mgf1p": {
                XMLCipher k = XMLCipher.getInstance(XMLCipher.RSA_OAEP);
                k.init(XMLCipher.WRAP_MODE, rsa.getPublic());
                return named(doc, k.encryptKey(doc, cek), "rsa-1");
            }
            case "oaep11-sha256": {
                XMLCipher k = XMLCipher.getInstance(XMLCipher.RSA_OAEP_11, null, XMLCipher.SHA256);
                k.init(XMLCipher.WRAP_MODE, rsa.getPublic());
                return named(doc, k.encryptKey(doc, cek, EncryptionConstants.MGF1_SHA256, null), "rsa-1");
            }
            case "oaep11-sha1": {
                XMLCipher k = XMLCipher.getInstance(XMLCipher.RSA_OAEP_11);
                k.init(XMLCipher.WRAP_MODE, rsa.getPublic());
                return named(doc, k.encryptKey(doc, cek), "rsa-1");
            }
            case "rsa15": {
                XMLCipher k = XMLCipher.getInstance(XMLCipher.RSA_v1dot5);
                k.init(XMLCipher.WRAP_MODE, rsa.getPublic());
                return named(doc, k.encryptKey(doc, cek), "rsa-1");
            }
            case "kek128":
            case "kek256": {
                XMLCipher k = XMLCipher.getInstance(kt.equals("kek128") ? XMLCipher.AES_128_KeyWrap : XMLCipher.AES_256_KeyWrap);
                k.init(XMLCipher.WRAP_MODE, kt.equals("kek128") ? kek128 : kek256);
                return named(doc, k.encryptKey(doc, cek), kt);
            }
            case "ecdh-p256":
            case "x25519": {
                boolean p256 = kt.equals("ecdh-p256");
                int kwBits = p256 ? 128 : 256;
                String kwAlg = p256 ? XMLCipher.AES_128_KeyWrap : XMLCipher.AES_256_KeyWrap;
                ConcatKDFParams kdf = ConcatKDFParams.createBuilder(kwBits, XMLCipher.SHA256)
                    .algorithmID("00" + hexBytes(kwAlg.getBytes(StandardCharsets.UTF_8)))
                    .partyUInfo("00" + hexBytes("originator".getBytes(StandardCharsets.UTF_8)))
                    .partyVInfo("00" + hexBytes("recipient".getBytes(StandardCharsets.UTF_8)))
                    .build();
                KeyAgreementParameters kap = new KeyAgreementParameters(
                    KeyAgreementParameters.ActorType.ORIGINATOR,
                    p256 ? EncryptionConstants.ALGO_ID_KEYAGREEMENT_ECDH_ES
                         : EncryptionConstants.ALGO_ID_KEYAGREEMENT_X25519, kdf);
                KeyPair recipient = p256 ? ec : x25519;
                kap.setRecipientPublicKey(recipient.getPublic());
                KeyPairGenerator eg = p256 ? KeyPairGenerator.getInstance("EC") : KeyPairGenerator.getInstance("X25519");
                if (p256) eg.initialize(new ECGenParameterSpec("secp256r1"));
                kap.setOriginatorKeyPair(eg.generateKeyPair());
                XMLCipher k = XMLCipher.getInstance(kwAlg);
                k.init(XMLCipher.WRAP_MODE, recipient.getPublic());
                return k.encryptKey(doc, cek, kap, null);
            }
            default: throw new IllegalArgumentException(kt);
        }
    }

    static EncryptedKey named(Document doc, EncryptedKey ek, String name) {
        KeyInfo ki = new KeyInfo(doc);
        ki.addKeyName(name);
        ek.setKeyInfo(ki);
        return ek;
    }

    // ----------------------------------------------------------------- SAML

    /** saml:EncryptedAssertion holding the encrypted document element of `assertion`. */
    static Document encryptedAssertion(Document assertion) throws Exception {
        Element as = assertion.getDocumentElement();
        Element wrap = assertion.createElementNS(SAML, "saml:EncryptedAssertion");
        wrap.setAttributeNS(XMLConstants.XMLNS_ATTRIBUTE_NS_URI, "xmlns:saml", SAML);
        assertion.replaceChild(wrap, as);
        wrap.appendChild(as);
        SecretKey cek = aesKey(128);
        XMLCipher c = XMLCipher.getInstance(XMLCipher.AES_128_GCM);
        c.init(XMLCipher.ENCRYPT_MODE, cek);
        KeyInfo ki = new KeyInfo(assertion);
        ki.add(encryptKey(assertion, cek, "oaep-mgf1p"));
        c.getEncryptedData().setKeyInfo(ki);
        c.doFinal(assertion, as, false);
        return assertion;
    }

    static void encryptNameId(Document doc) throws Exception {
        Element nid = (Element) doc.getElementsByTagNameNS(SAML, "NameID").item(0);
        Element subject = (Element) nid.getParentNode();
        Element eid = doc.createElementNS(SAML, "saml:EncryptedID");
        subject.replaceChild(eid, nid);
        eid.appendChild(nid);
        SecretKey cek = aesKey(256);
        XMLCipher c = XMLCipher.getInstance(XMLCipher.AES_256_GCM);
        c.init(XMLCipher.ENCRYPT_MODE, cek);
        KeyInfo ki = new KeyInfo(doc);
        ki.add(encryptKey(doc, cek, "oaep11-sha256"));
        c.getEncryptedData().setKeyInfo(ki);
        c.doFinal(doc, nid, false);
    }

    static String instant(long s) { return Instant.ofEpochSecond(s).toString(); }

    static Element child(Element p, String n) {
        Element e = p.getOwnerDocument().createElementNS(SAML, n);
        p.appendChild(e);
        return e;
    }

    static Document assertion(String id, String subjectId) throws Exception {
        Document doc = newDoc();
        Element as = doc.createElementNS(SAML, "saml:Assertion");
        as.setAttributeNS(XMLConstants.XMLNS_ATTRIBUTE_NS_URI, "xmlns:saml", SAML);
        as.setAttribute("ID", id);
        as.setIdAttribute("ID", true);
        as.setAttribute("Version", "2.0");
        as.setAttribute("IssueInstant", instant(NB));
        doc.appendChild(as);
        child(as, "saml:Issuer").setTextContent("https://idp.example");
        Element subject = child(as, "saml:Subject");
        Element nid = child(subject, "saml:NameID");
        nid.setAttribute("Format", "urn:oasis:names:tc:SAML:2.0:nameid-format:persistent");
        nid.setTextContent(subjectId);
        Element sc = child(subject, "saml:SubjectConfirmation");
        sc.setAttribute("Method", "urn:oasis:names:tc:SAML:2.0:cm:bearer");
        Element scd = child(sc, "saml:SubjectConfirmationData");
        scd.setAttribute("NotOnOrAfter", instant(NB + 300));
        scd.setAttribute("Recipient", "https://app.example/SAML");
        Element c = child(as, "saml:Conditions");
        c.setAttribute("NotBefore", instant(NB));
        c.setAttribute("NotOnOrAfter", instant(NB + 300));
        Element ar = child(c, "saml:AudienceRestriction");
        child(ar, "saml:Audience").setTextContent("https://as.example");
        Element st = child(as, "saml:AuthnStatement");
        st.setAttribute("AuthnInstant", instant(NB));
        child(child(st, "saml:AuthnContext"), "saml:AuthnContextClassRef")
            .setTextContent("urn:oasis:names:tc:SAML:2.0:ac:classes:unspecified");
        return doc;
    }

    static Document build(String id, String subjectId, KeyPair key) throws Exception {
        Document doc = assertion(id, subjectId);
        sign(doc, key);
        return doc;
    }

    static void sign(Document doc, KeyPair key) throws Exception {
        Element as = doc.getDocumentElement();
        as.setIdAttribute("ID", true);
        String id = as.getAttribute("ID");
        XMLSignatureFactory fac = XMLSignatureFactory.getInstance("DOM");
        javax.xml.crypto.dsig.Reference ref = fac.newReference("#" + id, fac.newDigestMethod(DigestMethod.SHA256, null),
            List.of(fac.newTransform(Transform.ENVELOPED, (TransformParameterSpec) null),
                    fac.newTransform(CanonicalizationMethod.EXCLUSIVE, (TransformParameterSpec) null)), null, null);
        SignedInfo si = fac.newSignedInfo(
            fac.newCanonicalizationMethod(CanonicalizationMethod.EXCLUSIVE, (C14NMethodParameterSpec) null),
            fac.newSignatureMethod(SignatureMethod.RSA_SHA256, null), List.of(ref));
        Node subject = as.getElementsByTagNameNS(SAML, "Subject").item(0);
        DOMSignContext ctx = new DOMSignContext(key.getPrivate(), as, subject);
        ctx.setDefaultNamespacePrefix("ds");
        fac.newXMLSignature(si, null).sign(ctx);
    }

    // -------------------------------------------------------------- helpers

    static SecretKey aesKey(int bits) throws Exception {
        KeyGenerator kg = KeyGenerator.getInstance("AES");
        kg.init(bits, RNG);
        return kg.generateKey();
    }

    static Document newDoc() throws Exception {
        DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
        f.setNamespaceAware(true);
        f.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
        return f.newDocumentBuilder().newDocument();
    }

    static Document parse(String s) throws Exception {
        DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
        f.setNamespaceAware(true);
        f.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
        return f.newDocumentBuilder().parse(new java.io.ByteArrayInputStream(s.getBytes(StandardCharsets.UTF_8)));
    }

    static String serialize(Document doc) throws Exception {
        Transformer t = TransformerFactory.newInstance().newTransformer();
        t.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
        StringWriter w = new StringWriter();
        t.transform(new DOMSource(doc), new StreamResult(w));
        return w.toString();
    }

    static String b64url(String s) {
        return Base64.getUrlEncoder().withoutPadding().encodeToString(s.getBytes(StandardCharsets.UTF_8));
    }

    static String b64u(byte[] b) { return Base64.getUrlEncoder().withoutPadding().encodeToString(b); }

    /** Unsigned big-endian octets of `v`, `len` octets long (0 = minimal). */
    static byte[] be(BigInteger v, int len) {
        byte[] b = v.toByteArray();
        if (b.length > 1 && b[0] == 0) b = Arrays.copyOfRange(b, 1, b.length);
        if (len == 0 || b.length == len) return b;
        byte[] o = new byte[len];
        System.arraycopy(b, 0, o, len - b.length, b.length);
        return o;
    }

    static String hex(BigInteger v) {
        String h = v.toString(16);
        return h.length() % 2 == 0 ? h : "0" + h;
    }

    static String hexBytes(byte[] b) {
        StringBuilder s = new StringBuilder();
        for (byte x : b) s.append(String.format("%02x", x));
        return s.toString();
    }

    static String rsaJwk(KeyPair k, String kid) {
        RSAPrivateKey d = (RSAPrivateKey) k.getPrivate();
        RSAPublicKey p = (RSAPublicKey) k.getPublic();
        return "{\"kty\": \"RSA\", \"kid\": \"" + kid + "\", \"n\": \"" + b64u(be(p.getModulus(), 0))
            + "\", \"e\": \"" + b64u(be(p.getPublicExponent(), 0)) + "\", \"d\": \"" + b64u(be(d.getPrivateExponent(), 0)) + "\"}";
    }

    static String ecJwk(KeyPair k, String kid) {
        ECPrivateKey d = (ECPrivateKey) k.getPrivate();
        ECPublicKey p = (ECPublicKey) k.getPublic();
        return "{\"kty\": \"EC\", \"crv\": \"P-256\", \"kid\": \"" + kid + "\", \"x\": \"" + b64u(be(p.getW().getAffineX(), 32))
            + "\", \"y\": \"" + b64u(be(p.getW().getAffineY(), 32)) + "\", \"d\": \"" + b64u(be(d.getS(), 32)) + "\"}";
    }

    /** X25519 keys as RFC 8037 OKP JWKs: the raw 32 octets of the PKCS #8 / SPKI encodings. */
    static String okpJwk(KeyPair k, String kid) {
        byte[] spki = k.getPublic().getEncoded();
        byte[] pkcs8 = k.getPrivate().getEncoded();
        byte[] x = Arrays.copyOfRange(spki, spki.length - 32, spki.length);
        byte[] d = Arrays.copyOfRange(pkcs8, pkcs8.length - 32, pkcs8.length);
        return "{\"kty\": \"OKP\", \"crv\": \"X25519\", \"kid\": \"" + kid + "\", \"x\": \"" + b64u(x) + "\", \"d\": \"" + b64u(d) + "\"}";
    }

    static String octJwk(SecretKey k, String kid) {
        return "{\"kty\": \"oct\", \"kid\": \"" + kid + "\", \"k\": \"" + b64u(k.getEncoded()) + "\"}";
    }

    static String json(String s) {
        StringBuilder b = new StringBuilder("\"");
        for (char c : s.toCharArray()) {
            if (c == '"' || c == '\\') b.append('\\').append(c);
            else if (c < 0x20) b.append(String.format("\\u%04x", (int) c));
            else b.append(c);
        }
        return b.append('"').toString();
    }
}
