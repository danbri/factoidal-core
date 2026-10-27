// Apache Santuario decrypts the documents the Lean engine encrypted
// (https://github.com/danbri/factoidal/issues/1084): the other direction of
// tests/xmlenc/MakeFixtures.java.
//
//   XMLENC_DUMP=/tmp/lean-xmlenc.json node --test tests/xmlenc/wasm.mjs
//   java -cp "$CP" tests/xmlenc/CheckLeanOutput.java /tmp/lean-xmlenc.json
//
// $CP: org.apache.santuario:xmlsec 4.0.4 and its runtime dependencies.
// The input is the line file tests/xmlenc/wasm.mjs writes. Prints one line per document and a score line; exit 1 on any failure.
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.security.*;
import java.security.spec.*;
import java.util.*;
import javax.crypto.spec.SecretKeySpec;
import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilderFactory;
import org.apache.xml.security.encryption.XMLCipher;
import org.apache.xml.security.utils.EncryptionConstants;
import org.w3c.dom.*;

public class CheckLeanOutput {
    public static void main(String[] a) throws Exception {
        org.apache.xml.security.Init.init();
        List<Map<String, String>> keys = new ArrayList<>();
        List<Map<String, String>> docs = new ArrayList<>();
        for (String line : Files.readAllLines(Path.of(a[0]), StandardCharsets.UTF_8)) {
            String[] f = line.split(" ");
            Map<String, String> m = new LinkedHashMap<>();
            if (f[0].equals("key")) {
                for (int i = 1; i < f.length; i++) m.put(f[i].substring(0, f[i].indexOf('=')), f[i].substring(f[i].indexOf('=') + 1));
                keys.add(m);
            } else if (f[0].equals("doc")) {
                m.put("name", text(f[1]));
                m.put("document", text(f[2]));
                m.put("expected", text(f[3]));
                docs.add(m);
            }
        }
        int pass = 0, fail = 0;
        for (Map<String, String> d : docs) {
            String name = d.get("name");
            try {
                Document doc = parse(d.get("document"));
                Element ed = (Element) doc.getElementsByTagNameNS(EncryptionConstants.EncryptionSpecNS, "EncryptedData").item(0);
                String km = ((Element) ed.getElementsByTagNameNS(EncryptionConstants.EncryptionSpecNS, "EncryptedKey").item(0)
                    .getFirstChild()).getAttribute("Algorithm");
                boolean agreement = ed.getElementsByTagNameNS(EncryptionConstants.EncryptionSpecNS, "AgreementMethod").getLength() > 0;
                Key kek = kekFor(keys, km, agreement, d.get("document"));
                XMLCipher c = XMLCipher.getInstance();
                c.init(XMLCipher.DECRYPT_MODE, null);
                c.setKEK(kek);
                c.doFinal(doc, ed);
                Document expected = parse(d.get("expected"));
                boolean same = doc.getDocumentElement().isEqualNode(expected.getDocumentElement());
                System.out.println((same ? "PASS " : "FAIL ") + name);
                if (same) pass++; else fail++;
            } catch (Exception e) {
                System.out.println("FAIL " + name + ": " + e);
                fail++;
            }
        }
        System.out.println("santuario-decrypts-lean: " + pass + " pass, " + fail + " fail (out of " + (pass + fail) + ")");
        System.exit(fail == 0 ? 0 : 1);
    }

    static Key kekFor(List<Map<String, String>> keys, String method, boolean agreement, String doc) throws Exception {
        if (method.contains("rsa-oaep")) return rsa(find(keys, "RSA", null));
        if (agreement) {
            return doc.contains("xmldsig-more#x25519") ? x25519(find(keys, "OKP", null)) : ec(find(keys, "EC", null));
        }
        int len = method.endsWith("kw-aes128") ? 16 : 32;
        for (Map<String, String> k : keys) {
            if ("oct".equals(k.get("kty")) && b64(k.get("k")).length == len) return new SecretKeySpec(b64(k.get("k")), "AES");
        }
        throw new IllegalStateException("no key for " + method);
    }

    static Map<String, String> find(List<Map<String, String>> keys, String kty, String kid) {
        for (Map<String, String> k : keys) if (kty.equals(k.get("kty"))) return k;
        throw new IllegalStateException("no " + kty + " key");
    }

    static String text(String b) { return new String(Base64.getDecoder().decode(b), StandardCharsets.UTF_8); }

    static PrivateKey rsa(Map<String, String> k) throws Exception {
        return KeyFactory.getInstance("RSA").generatePrivate(new RSAPrivateKeySpec(
            new BigInteger(1, b64(k.get("n"))), new BigInteger(1, b64(k.get("d")))));
    }

    static PrivateKey ec(Map<String, String> k) throws Exception {
        AlgorithmParameters p = AlgorithmParameters.getInstance("EC");
        p.init(new ECGenParameterSpec("secp256r1"));
        return KeyFactory.getInstance("EC").generatePrivate(
            new ECPrivateKeySpec(new BigInteger(1, b64(k.get("d"))), p.getParameterSpec(ECParameterSpec.class)));
    }

    static PrivateKey x25519(Map<String, String> k) throws Exception {
        return KeyFactory.getInstance("X25519").generatePrivate(
            new XECPrivateKeySpec(NamedParameterSpec.X25519, b64(k.get("d"))));
    }

    static byte[] b64(String s) { return Base64.getUrlDecoder().decode(s.replace('+', '-').replace('/', '_').replace("=", "")); }

    static Document parse(String s) throws Exception {
        DocumentBuilderFactory f = DocumentBuilderFactory.newInstance();
        f.setNamespaceAware(true);
        f.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
        return f.newDocumentBuilder().parse(new java.io.ByteArrayInputStream(s.getBytes(StandardCharsets.UTF_8)));
    }
}
