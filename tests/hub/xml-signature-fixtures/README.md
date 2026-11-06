# Frozen XML Signature coverage fixtures

These are fresh project-authored pedagogic examples, not production credentials
or W3C conformance vectors. `docs/web/hub/xml-signature/fixtures.mjs` contains only
public XML, RSA public JWK, and signatures. No private key was exported.

`MakeFixtures.java` uses the independent OpenJDK JSR105 XML Signature provider.
It generates a transient RSA-2048 key and signs three documents. Before emitting
each fixture it reparses the wire XML and verifies that signature with the public
key. The recorded producer was OpenJDK 25.0.5. Regeneration changes the key and
signatures; it is not a byte-reproducible private-key fixture.

- Original: one enveloped signature over the entire approval root (`ID`).
- Projected: the same profile over payee-only content. Amount and account are absent.
- Embedded XSLT: an independently valid transform signature, intentionally outside
  Factoidal's strict profile. **Only the independent oracle** disables JDK secure
  validation to generate/verify this case. Production Factoidal never enables it.

Generate a new JSON fixture set (then replace the corresponding `FIXTURES` data):

```sh
java tests/hub/xml-signature-fixtures/MakeFixtures.java > /tmp/xml-signature-fixtures.json
```

Verify the **committed** fixture wires independently, including covered tamper and
JDK's default secure-validation refusal of embedded XSLT:

```sh
node --test tests/hub/xml-signature-oracle.test.mjs
```

Run the actual Lean/HACL verifier and actual Lean XSLT controls with a freshly
built native `l4wasm-cli`:

```sh
node --test tests/hub/xml-signature-native.test.mjs
# Or set FACTOIDAL_SIGNATURE_NATIVE to a validated native dispatch binary.
```

Missing Java or native engine is a test failure, never zero tests or a synthetic
verification pass. Fresh WASM/browser verification is a separate required gate.

The adapter is deliberately narrow: XML 1.0 documents; no declaration markup
(DTD, comments, CDATA); no processing instructions; bounded input/depth; caller-
pinned public RSA key; RSA-SHA256/SHA-256; one root-ID reference; enveloped-signature
then Exclusive XML Canonicalization **1.0**, without comments. It adds no XMLDSig
XSLT execution, external references, key lookup, certificate validation, or signing.

References: [XMLDSig 1.1 Recommendation](https://www.w3.org/TR/xmldsig-core1/),
[Exclusive C14N 1.0](https://www.w3.org/TR/xml-exc-c14n/),
[XML Signature Best Practices](https://www.w3.org/TR/xmldsig-bestpractices/),
especially avoiding XSLT transforms and checking what was signed. The preprocessing
example is explicitly a different boundary from an embedded `ds:Transform`.
