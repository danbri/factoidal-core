# The Lean XML processor's conformance profile, widened (2026-10-10)

Task: the W3C XML Conformance Test Suite (`xmlconf`) put 24 + 55 + 65 + 59
cases out of the Lean processor's profile. This record says what was added,
how `lake exe l4xmlconf` now counts, the score of each line, the cases that
still fail, and the defects found on the way. Run the numbers again before
you quote them:

```
formal/lean4/.lake/build/bin/l4xmlconf            # from the repository root
formal/lean4/.lake/build/bin/l4xmlconf --verbose  # lists every failure
```

## Result (measured 2026-10-10)

| Line | Score | What it reads |
|---|---|---|
| plain XML | 1861 pass, 0 fail (out of 1861) | cases that are plain UTF-8 bytes; unchanged by this work |
| namespaces | 56 pass, 0 fail (out of 56) | `eduni/namespaces/*`: XML parse, then `Document.namespaceWellFormed` |
| encodings | 65 pass, 0 fail (out of 65) | cases whose document or named entity is not plain UTF-8, decoded by `decodeXmlBytes` |
| XML 1.1 | 257 pass, 1 fail (out of 258) | `VERSION="1.1"` cases and the three `ibm/xml-1.1` manifests |
| validating | 2183 pass, 1 fail (out of 2184) | parse, then the validity constraints |

Not scored, and printed: 24 `TYPE="error"` cases in the XML suites, 3 in the
Namespaces suites, 5 in the XML 1.1 suites, 313 cases for editions 1 to 4
only (the parser follows the Fifth Edition; owner instruction for this task:
leave that bucket as is), and 0 cases in an encoding the decoder does not
implement (the line exists and prints names; no scored case needs it).

The validating line splits as: valid 799 pass, 1 fail (out of 800); invalid
225 pass, 0 fail (out of 225); not-wf 1159 pass, 0 fail (out of 1159). The
Namespaces suites are not read in that mode.

Downstream users of the XML tree were measured before and after each step
and did not move: `l4w3c` on the rdf11 manifest 1041 pass, 0 fail (out of
1041) with RDF/XML 166 pass, 0 fail (out of 166); `l4rdfxml-probe` 132, 41
and 132 pass, 0 fail; `l4xslt` 84 exact and 87 canonical pass (out of 87
decided); `l4schematron` 8 pass, 0 fail (out of 8); `l4xpath` 100 pass, 0
fail (out of 100).

## Where each layer lives

| Layer | File | Spec |
|---|---|---|
| Bytes to text | `XML/Encoding.lean` | XML 1.0 section 4.3.3, Appendix F |
| Parser, both versions | `XML/Parser.lean` | XML 1.0 5e, XML 1.1 |
| Namespaces | `XML/Namespaces.lean` | Namespaces in XML 1.0 and 1.1 |
| Validity | `XML/Validity.lean` | XML 1.0 sections 2.8, 2.9, 3, 4.1, 4.2.2 |
| Runner | `Harness/XmlConfRun.lean` | reads the manifests |

### Encodings

`decodeXmlBytes : ByteArray -> Except String String` is total. It detects the
family from the first four bytes (Appendix F.1), reads the encoding
declaration, checks it against the family, and decodes UTF-8, UTF-16 (both
orders, with or without a byte order mark), ISO-8859-1 and US-ASCII.
`decodeXmlBytesE` returns a `DecodeError`: `unsupported name`, `invalid`,
or `conflict`, so a caller can tell an encoding it cannot read from an
entity that is broken. Rules, from section 4.3.3:

- UTF-16 with a byte order mark: no declaration, `UTF-16`, or the label for
  the same byte order. Another label is a conflict.
- UTF-16 without a mark (`00 3C 00 3F`, `3C 00 3F 00`): only a declaration
  that names the byte order (`UTF-16LE`, `UTF-16BE`). `UTF-16` alone, or no
  declaration, is the fatal error "in UTF-16 but does not begin with a byte
  order mark".
- A UTF-8 mark with another encoding declared, or an 8-bit entity that
  declares UTF-16: conflict.
- A name that is not an `[81] EncName` is left to the parser, which rejects
  the declaration; the decoder does not call it "unsupported".

`parseXMLWith` is `parseXMLCore` with a flag. Text from the decoder is
parsed with the byte-order-mark and encoding checks off, because the decoder
already applied section 4.3.3 against the bytes. A `String` given to
`parseXML` is still taken to have been UTF-8.

### XML 1.1

The version is read from the XML declaration on the RAW text, before line
ends are normalised, because the set of line ends depends on it. `[3] S`
contains #xD, so the declaration parses the same on raw text. Then:

- Section 2.11: NEL, LS, CR NEL and a lone CR become one LF
  (`normalizeLineEndings11`). CR LS is two LFs. External entities are
  normalised in both versions.
- Section 2.2: `[1] document` excludes `RestrictedChar`, so the normalised
  text of a 1.1 document is checked once for a literal restricted control,
  NUL or non-character. A restricted control gets in only through a
  character reference (section 4.1), in content, attribute values and
  entity values.
- Section 4.3.4: the document's version decides for its entities. A 1.1
  document may invoke a 1.0 entity; a 1.0 document may not invoke one that
  declares 1.1.
- `[77] TextDecl` is checked as the grammar writes it (`textDeclIsWellFormed`):
  each pseudo-attribute follows whitespace, and NEL or LS is not whitespace.
- Names (section 2.3) are the same ranges as the Fifth Edition's: checked
  against the text of the XML 1.1 Recommendation, no change was needed.

`Theorems.lean`: `Node.wellFormed`, `Attribute.wellFormed` and
`Document.wellFormed` take the document version, the lemmas gain a version
argument, and the serialiser writes CR, NEL, LS and the restricted controls
as character references so that a 1.1 document round-trips.

### The DTD model

The parser used to scan an ATTLIST for ID pairs and drop the rest. It now
records, in `Doctype`: every `[53] AttDef` (type with its token list, default,
and whether it came from the external subset), every `[45] elementdecl`
(content specification as text), the unparsed entities, the declared names,
a flag when part of the DTD could not be read, and the parameter-entity
nesting problems found while splicing the external subset. Three consequences:

- Section 3.3.3 and 5.1: a processor that reads an ATTLIST must collapse
  the value of an attribute whose declared type is not CDATA. It now does.
  The first declaration of an attribute is binding (section 3.3).
- Rule NE08 of Namespaces in XML 1.0 section 6: no colon in a PI target,
  an entity name or a notation name. `namespaceWellFormed` checks the prolog,
  epilog, content and DTD.
- White space in an attribute value that comes from an entity's replacement
  text is a space (section 3.3.3, step 3). Before, a TAB, LF or CR in
  replacement text reached the value unchanged.

### Validity

`validate`/`validateWithNotes` check, by constraint name: Root Element Type;
Element Valid (EMPTY, ANY, mixed, element content by Brzozowski derivatives);
Unique Element Type Declaration; No Duplicate Types; Attribute Value Type;
ID; IDREF; Entity Name; Name Token; Notation Attributes; Enumeration; One ID
per Element Type; ID Attribute Default; One Notation Per Element Type; No
Notation on Empty Element; No Duplicate Tokens; Required Attribute;
Attribute Default Legal; Fixed Attribute Default; Notation Declared;
Entity Declared (only the case section 4.1 makes a validity error); Standalone
Document Declaration; Proper Declaration/PE Nesting; Proper Group/PE Nesting;
Proper Conditional Section/PE Nesting. A document with no document type
declaration is not valid (section 2.8).

The parse tree has no node for a reference, so five constraints cannot be
decided from it. The parser records `Notes` (one `ElemNote` per element, in
reverse post-order, and a flag for undeclared entities) and
`parseXMLNotes` returns them with the tree. Nothing in `Document` changed
for that; `parseXML` ignores the notes. The notes carry: a reference in an
element's content (an EMPTY element with `&e;` for an empty `e`), a
character reference to white space in element content, attributes changed by
the tree-level normalisation (for the Standalone constraint), and a
reference to an undeclared entity under section 4.1's first clause.

## Cases that still fail

`ibm-1-1-valid-P03-ibm03v09` (TYPE `valid`, XML 1.1). Its entity,
`valid/P03/ibm03v09.ent`, is `<?xml version="1.1" U+2028?>`: a text
declaration with no encoding declaration, with a line separator inside it.
XML 1.1 `[77] TextDecl ::= '<?xml' VersionInfo? EncodingDecl S? '?>'` makes
the encoding declaration mandatory, and section 2.11 says: "it is a fatal
error to use them [NEL, #x2028] within the XML declaration or text
declaration". The manifest's own description says "(This test is
questionable)". The processor rejects the document. Fixing the score means
accepting what the Recommendation forbids; it needs an owner decision.

## Not checked (no failing test yet)

These are known gaps of the validity layer. Each needs an issue and an
expected-failure test before it is called a shortfall in the sense of
`CLAUDE.md`; none has been opened.

- Default attribute values are recorded but not supplied to elements
  (XML 1.0 section 5.1 asks a processor that reads the ATTLIST to supply
  them). The validity layer checks specified attributes only.
- Nesting constraints are checked on the external subset's parameter
  entities inside a markup declaration. A parameter entity included at
  declaration-separator position is parsed as whole declarations (a
  well-formedness constraint), and one included from the internal subset is
  not scanned.
- The check "Entity Declared" covers the case the parser let through; a
  document whose DTD could not be read in full is reported by
  `Doctype.incomplete`, and the runner counts such `valid` cases apart
  (0 occur).
- `xml:id`, `xml:base`, and the `xml:lang` value syntax are not checked.

## Defects found on the way

- `ByteArray.data` copies the array on every call. The first decoder used it
  per byte; a 200 KB UTF-16 document took over ten minutes in the runner.
  `byteAt` uses `get!`, which reads in constant time.
- The runner's list of manifests omitted `ibm/xml-1.1/ibm_*.xml`, which
  `xmlconf.xml` includes: 209 cases were outside every denominator.
- The runner read only the directories the document's own text named;
  `eduni/errata-2e/E18.xml` names `subdir1/`, whose entity names `../subdir2/`.
  The runner now follows names through the texts it loads (three rounds) and
  matches a `../` identifier against the end of a path it read.
- An entity whose replacement text contains a character reference to a
  restricted control used to fail only at use; in 1.1 that is legal
  (xmlconf `rmt-054`).

## Differences between the test suite and the Recommendation

- `rmt-034` and `rmt-035` (1.1 suite, 2003) call an NMTOKENS value valid when
  a carriage return comes from a character reference in an entity. They pass
  here for a different reason than the manifest gives: step 3 of section
  3.3.3 turns white space in replacement text into a space. `rmt-036`/`037`
  (NEL by character reference) stay invalid.
- Errata E20 and the 3.3.3 example say a tab or CR put in by a character
  reference directly in the attribute value stays a tab or CR and so breaks
  NMTOKENS; `rmt-e2e-20` pins that.
