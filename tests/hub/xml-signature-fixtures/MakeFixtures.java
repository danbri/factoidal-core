// Independent JDK JSR105 oracle/fixture producer. No private key is exported.
// Regeneration intentionally chooses a fresh RSA-2048 key; never use for credentials.
import java.io.*;
import java.security.*;
import java.security.interfaces.RSAPublicKey;
import java.util.*;
import javax.xml.crypto.dom.DOMStructure;
import javax.xml.crypto.dsig.*;
import javax.xml.crypto.dsig.dom.*;
import javax.xml.crypto.dsig.spec.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import org.w3c.dom.*;
import org.xml.sax.InputSource;

public class MakeFixtures {
  static final String ORIGINAL = "<approval ID=\"approval1\"><payee>Mina Chen</payee><amount currency=\"USD\">1200</amount><account>EXAMPLE-0001</account></approval>";
  static final String PROJECTED = "<approval ID=\"approval1\"><payee>Mina Chen</payee></approval>";
  static final String STYLE = "<xsl:stylesheet version=\"3.0\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\"><xsl:output method=\"xml\" omit-xml-declaration=\"yes\"/><xsl:template match=\"/\"><approval ID=\"approval1\"><payee><xsl:value-of select=\"/approval/payee\"/></payee></approval></xsl:template></xsl:stylesheet>";
  static Document parse(String s) throws Exception {
    var f=DocumentBuilderFactory.newInstance(); f.setNamespaceAware(true);
    f.setFeature("http://apache.org/xml/features/disallow-doctype-decl",true);
    return f.newDocumentBuilder().parse(new InputSource(new StringReader(s)));
  }
  static String serialize(Document d) throws Exception {
    var t=TransformerFactory.newInstance().newTransformer();
    t.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION,"yes");
    var w=new StringWriter(); t.transform(new DOMSource(d),new StreamResult(w)); return w.toString();
  }
  static String sign(String text, KeyPair key, boolean xslt) throws Exception {
    var d=parse(text); var root=d.getDocumentElement(); root.setIdAttribute("ID",true);
    var f=XMLSignatureFactory.getInstance("DOM"); var ts=new ArrayList<Transform>();
    ts.add(f.newTransform(Transform.ENVELOPED,(TransformParameterSpec)null));
    if(xslt) {
      // Intentionally outside the production profile, enabled ONLY for this oracle fixture.
      var style=parse(STYLE.replace("version=\"3.0\"","version=\"1.0\"").replace("<approval ID=\"approval1\">","<approval><xsl:attribute name=\"ID\">approval1</xsl:attribute>"));
      ts.add(f.newTransform(Transform.XSLT,new XSLTTransformParameterSpec(new DOMStructure(style.getDocumentElement()))));
    }
    ts.add(f.newTransform(CanonicalizationMethod.EXCLUSIVE,(TransformParameterSpec)null));
    var ref=f.newReference("#approval1",f.newDigestMethod(DigestMethod.SHA256,null),ts,null,null);
    var si=f.newSignedInfo(f.newCanonicalizationMethod(CanonicalizationMethod.EXCLUSIVE,(C14NMethodParameterSpec)null),
      f.newSignatureMethod(SignatureMethod.RSA_SHA256,null),List.of(ref));
    var sc=new DOMSignContext(key.getPrivate(),root); sc.setDefaultNamespacePrefix("ds");
    f.newXMLSignature(si,null).sign(sc);
    String wire=serialize(d);
    var parsed=parse(wire); parsed.getDocumentElement().setIdAttribute("ID",true);
    var sig=parsed.getElementsByTagNameNS(XMLSignature.XMLNS,"Signature").item(0);
    var vc=new DOMValidateContext(key.getPublic(),sig);
    if(xslt) vc.setProperty("org.jcp.xml.dsig.secureValidation",false);
    if(!f.unmarshalXMLSignature(vc).validate(vc)) throw new AssertionError("JDK fixture verification failed");
    return wire;
  }
  static String quote(String s) {return "\""+s.replace("\\","\\\\").replace("\"","\\\"").replace("\r","\\r").replace("\n","\\n").replace("\t","\\t")+"\"";}
  static String b64(java.math.BigInteger i) {var b=i.toByteArray();if(b[0]==0)b=Arrays.copyOfRange(b,1,b.length);return Base64.getUrlEncoder().withoutPadding().encodeToString(b);}
  public static void main(String[] args) throws Exception {
    if(args.length==4) {
      var decode=Base64.getUrlDecoder();
      var pk=KeyFactory.getInstance("RSA").generatePublic(new java.security.spec.RSAPublicKeySpec(
        new java.math.BigInteger(1,decode.decode(args[0])),new java.math.BigInteger(1,decode.decode(args[1]))));
      var d=parse(java.nio.file.Files.readString(java.nio.file.Path.of(args[2])));
      d.getDocumentElement().setIdAttribute("ID",true);
      var sig=d.getElementsByTagNameNS(XMLSignature.XMLNS,"Signature").item(0);
      var vc=new DOMValidateContext(pk,sig);
      if(args[3].equals("xslt-oracle-only")) vc.setProperty("org.jcp.xml.dsig.secureValidation",false);
      System.out.println(XMLSignatureFactory.getInstance("DOM").unmarshalXMLSignature(vc).validate(vc));
      return;
    }
    var g=KeyPairGenerator.getInstance("RSA");g.initialize(2048);var key=g.generateKeyPair();
    var pk=(RSAPublicKey)key.getPublic();
    System.out.println("{\"original\":"+quote(ORIGINAL)+",\"projected\":"+quote(PROJECTED)+",\"stylesheet\":"+quote(STYLE)+
      ",\"signedOriginal\":"+quote(sign(ORIGINAL,key,false))+",\"signedProjected\":"+quote(sign(PROJECTED,key,false))+
      ",\"embeddedXslt\":"+quote(sign(ORIGINAL,key,true))+",\"publicKey\":{\"kty\":\"RSA\",\"n\":"+quote(b64(pk.getModulus()))+",\"e\":"+quote(b64(pk.getPublicExponent()))+"},\"oracle\":{\"implementation\":\"OpenJDK JSR105\",\"version\":"+quote(System.getProperty("java.version"))+",\"allThreeVerify\":true,\"embeddedXsltSecureValidation\":false}}");
  }
}
