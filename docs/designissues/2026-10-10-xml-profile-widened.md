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
| plain XML | 1861 pass, 0 fail, 0 local-override (out of 1861) | cases that are plain UTF-8 bytes; unchanged by this work |
| namespaces | 56 pass, 0 fail, 0 local-override (out of 56) | `eduni/namespaces/*`: XML parse, then `Document.namespaceWellFormed` |
| encodings | 65 pass, 0 fail, 0 local-override (out of 65) | cases whose document or named entity is not plain UTF-8, decoded by `decodeXmlBytes` |
| XML 1.1 | 258 pass, 0 fail, 0 local-override (out of 258) | `VERSION="1.1"` cases and the three `ibm/xml-1.1` manifests |
| validating | 2184 pass, 0 fail, 0 local-override (out of 2184) | parse, then the validity constraints |
| output | 46 pass, 0 fail, 0 local-override (out of 46) | `valid` and `invalid` cases in which the parser supplied a declared default, compared with the suite's OUTPUT file |
| xml-local | 51 pass, 0 fail, 1 expected-fail (out of 52) | `tests/xml-local/xml-local.xml`, repository-local fixtures (see "Issue 705") |

Not scored, and printed: 24 `TYPE="error"` cases in the XML suites, 3 in the
Namespaces suites, 5 in the XML 1.1 suites, 313 cases for editions 1 to 4
only (the parser follows the Fifth Edition; owner instruction for this task:
leave that bucket as is), and 0 cases in an encoding the decoder does not
implement (the line exists and prints names; no scored case needs it).

The validating line splits as: valid 800 pass, 0 fail (out of 800); invalid
225 pass, 0 fail (out of 225); not-wf 1159 pass, 0 fail (out of 1159). The
Namespaces suites are not read in that mode.

The run exits 1 if any line has a failure. A case named in
`tests/local-overrides/*.json` with `"suite": "xmlconf"` (key `test_id` is
the manifest `ID`) is counted in a `local-override` bucket on every line it
belongs to, never as a pass; if it passes, that line fails with a STALE
note, and an override that matches no scored case fails the run. At present
no xmlconf case is overridden (see "The case that failed").

Downstream users of the XML tree were measured before and after the work
on issue 705, on the same machine and the same fixtures; every log is
identical to its "before" log, apart from wall-clock times in the OWL probe:
`l4w3c` on the rdf11 manifest 1041 pass, 0 fail (out of 1041), with RDF/XML
166 pass, 0 fail (out of 166); `l4w3c` on the SPARQL 1.1 manifest-all 650
pass, 0 fail (out of 650); `l4sparql-probe` 428 pass, 0 fail (out of 428);
`l4rdfxml-probe` 132, 41 and 132 pass, 0 fail; `l4xslt` 84 exact and 87
canonical pass (out of 87 decided); `l4schematron` 8 pass, 0 fail (out of 8
decided); `l4xpath` 100 pass, 0 fail (out of 100); `l4grddl` 19 pass, 22
fail (out of 41 decided; the 22 are the same cases as before); `l4rif` 45
pass, 0 fail (out of 45 decided); `l4mathml` 81 pass, 0 fail (out of 81);
`l4xsd-datatypes` 18955 pass, 0 fail (out of 18955); `l4owl-probe --dir
third_party/testing/owl` unchanged. None of these suites has a document whose
DTD defaults an attribute, which is why they cannot move; the `output` line
and `xml-local` are the lines that do.

## Where each layer lives

| Layer | File | Spec |
|---|---|---|
| Bytes to text | `XML/Encoding.lean` | XML 1.0 section 4.3.3, Appendix F |
| Parser, both versions | `XML/Parser.lean` | XML 1.0 5e, XML 1.1 |
| Namespaces | `XML/Namespaces.lean` | Namespaces in XML 1.0 and 1.1 |
| Validity | `XML/Validity.lean` | XML 1.0 sections 2.8, 2.9, 3, 4.1, 4.2.2 |
| `xml:lang`, `xml:id`, `xml:base` | `XML/XmlAttributes.lean` | XML 1.0 section 2.12, RFC 5646, xml:id 1.0, XML Base 2e, LEIRI |
| Runner | `Harness/XmlConfRun.lean` | reads the manifests, `tests/xml-local/`, `tests/local-overrides/` |

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
  The first declaration of an attribute is binding (section 3.3). It also
  supplies the declared default (see "Issue 705").
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

The check "Entity Declared" covers the case the parser let through. A
document whose DTD could not be read in full is reported by
`Doctype.incomplete`, and the runner counts such `valid` cases apart (0
occur).

## The case that failed

`ibm-1-1-valid-P03-ibm03v09.xml` (TYPE `valid`, XML 1.1) was the one failure
of the XML 1.1 line and of the validating line. The first record of it, and
issue https://github.com/danbri/factoidal/issues/704 , said that its entity
`valid/P03/ibm03v09.ent`, `<?xml version="1.1" U+2028?>`, breaks XML 1.1
`[77] TextDecl` (the encoding declaration is mandatory) and section 2.11
(NEL and #x2028 in a text declaration are a fatal error), that the manifest
calls the case "questionable", and that passing it would mean accepting what
the Recommendation forbids. The diagnosis stopped there. The document is

```
<?xml version="1.1"?>
<!DOCTYPE doc [ <!ELEMENT doc (#PCDATA)> <!ENTITY e SYSTEM "ibm03v09.ent"> <!ATTLIST doc a CDATA #IMPLIED> ]>
<doc>Test</doc>
```

and it never references `&e;`. The parser read every external entity when
it met the declaration, and so refused a document for a fault in an entity
nothing names. XML 1.0 section 2.1 asks for the well-formedness of "each of
the parsed entities which is referenced directly or indirectly within the
document"; sections 4.4.1 and 4.4.3 let a processor leave an unreferenced
entity unread. The text declaration is as bad as the first record says, and
that does not matter here.

Repair: `EntityDef.unreadable` carries the fault of an entity whose text was
supplied and is not a well-formed external parsed entity; a reference in
content, in an attribute value or default, or (for a parameter entity) in the
DTD reports it. A first version of the work added a `local-override` for the
case (issue 704, as proposed); the runner then reported it STALE, which is how
the diagnosis was found to be wrong. The override file was removed in the same
series of commits. Both outcomes are guarded in `XML/Tests.lean`
(`unreferencedEnt`, `withEnt`, `pe`): the same bad text is accepted when no
reference names the entity and rejected when one does. This section is the record for closing
issue 704.

Method error, 2026-10-10: a failing conformance case was taken to be a fixture
that contradicts the Recommendation because the entity text was bad, without
checking that the document reaches the entity. The check that would have found
it is one `--verbose` run and a look at the document. Written into
`tests/local-overrides/README.md`, "Before adding an override".

## Issue 705

https://github.com/danbri/factoidal/issues/705 named three gaps. No xmlconf
case exercised them, so no line showed them. Each is now in the library, with
`#guard` cases (positive and negative) in `XML/Tests.lean`, and with
repository-local fixtures in `tests/xml-local/` that `l4xmlconf` scores on the
`xml-local` line.

### (a) Attribute defaults, XML 1.0 sections 3.3.2 and 5.1

`Parser.defaultedAttrs` adds, after the attributes a start tag specifies and
in the order of the declarations, one attribute for each name the element type
declares with a default value or `#FIXED` and the tag leaves out. The first
declaration of a name is binding (3.3). The value is the declared literal
normalised as 3.3.3 says for a specified value: literal tab, line feed and
carriage return to a space; references replaced; a character reference to
white space kept; for a type other than CDATA, runs of spaces collapsed
(`literalValue` and `defaultValue`, moved from `Validity.lean` into the
parser). A literal that is not an `[10] AttValue` (a `<`, a recursive or
external entity reference) is a well-formedness error when the default is
supplied; in the internal subset it was already refused at the declaration.

`ElemNote.defaulted` names the attributes supplied. The validity layer reads
it: Standalone Document Declaration (2.9) now asks whether a supplied
attribute's declaration is external, instead of looking for an attribute
missing from the tree (which the tree no longer shows). The value constraints
apply to a supplied value as to a specified one (an IDREF default that names
no ID breaks IDREF); one existing guard held only because defaults were not
supplied and is replaced by two that state both cases.

Section 5.1 limits what a non-validating processor processes: "Except when
standalone="yes", they must not process entity declarations or attribute-list
declarations encountered after a reference to a parameter entity that is not
read". Both kinds are now left out in that case (`AttDecl.afterUnreadPe`,
`EntityDef.afterUnreadPe`, `EntityTable.standalone`; `lookupEntityDef` does
not offer a marked entity). The attribute-list half also keeps such a
declaration out of the §3.3.3 normalisation. The validity layer still sees every
declaration in `Doctype.attDecls`.

Downstream, the tree now carries the defaulted attributes. Namespaces in XML
treats a defaulted `xmlns` or `xmlns:p` as a declaration, because the namespace
layer reads the tree; Canonical XML includes them (its §2.3 uses the data
model that has them), and the Recommendation's own example 3.3, with its DTD
(`attr="default"` on `e9`), is a guard in `XML/Canonical.lean`. RDF/XML, XSLT,
Schematron, XPath, GRDDL, RIF, MathML and the SPARQL results reader read the
tree and so see them; the measurements above show that no fixture of those
suites declares a default.

Evidence on the real W3C files: the `output` line. For each `valid` or
`invalid` case that has an OUTPUT file and in which the parser supplied a
default, it compares the canonical form (Canonical XML 1.0, comments omitted)
with the file, after removing the differences between the suite's "Second
Canonical Form" and Canonical XML 1.0 (`commonCanonicalForm` in the runner:
the notation list in a leading DOCTYPE, the XML 1.1 declaration, `&quot;` and
`&gt;`, decimal references for white space, a space before `?>` in a PI).
46 cases qualify and all 46 agree. A scratch program run first over the
documents that declare an ATTLIST in their own text (159 cases with an OUTPUT
file) gave 147 agreeing; the 12 others differed only by the formatting
differences above (a notation list or a processing instruction before the
DOCTYPE in the expected file, the XML 1.1 declaration, a NEL written as a
reference), none by an attribute. The line fails if it has no case.

Mutation checks, so that the fixtures are known to tell the behaviours apart:
with the defaults switched off the guards in `Canonical.lean` stop the
build; with the unread-parameter-entity rule switched off,
`xml-local-defaults-unread-pe-then-attlist` fails; with the external
parameter-entity scan switched off, seven `pe-nesting` fixtures fail.

### (b) `xml:lang`, `xml:id`, `xml:base`

`Document.xmlAttributeIssues` (`XML/XmlAttributes.lean`) reports, in document
order and then the declarations, what is wrong with these attributes. It does
not change what `parseXML` accepts; a document with bad values is accepted and
has issues. An attribute is in the XML namespace when its prefix is `xml`
(Namespaces in XML 1.0 section 3 binds that prefix to
`http://www.w3.org/XML/1998/namespace`, permanently and to nothing else).

- `xml:lang`: the empty string, or an RFC 5646 section 2.1 `Language-Tag`
  (`langtag`, `privateuse`, or an irregular grandfathered tag), compared
  without regard to case. XML 1.0 section 2.12 requires "language identifiers as
  defined by BCP 47" and no registry check, so the check is the syntax of
  RFC 5646 section 2.2.9 "well-formed".
- `xml:id` (xml:id 1.0 section 4): the value, normalised as for type ID, is an
  NCName; every declaration of `xml:id` has type ID; the values of all
  attributes of type ID (xml:id attributes and attributes the DTD declares as
  ID) are unique. Each xml:id attribute that has a non-unique value is
  reported. xml:id errors are not fatal (section 6) and are not here.
- `xml:base` (XML Base 2e section 3): a LEIRI reference, from the W3C Note
  "Legacy extended IRIs". `ucschar` in that syntax admits almost every
  character, so the check is structural: a `%` starts two hexadecimal digits,
  the scheme before a colon in the first segment is ALPHA followed by ALPHA,
  DIGIT, `+`, `-` or `.`, at most one `#`, and `[` and `]` only in an
  authority. The Note says generic software should not check LEIRIs against
  the syntax, so the list is short.
- Use for resolution: the RDF/XML parser resolves `rdf:about`, `rdf:resource`,
  `rdf:ID` and `rdf:datatype` against the `xml:base` in force on the element
  (`Syntax/RdfXml.lean`); GRDDL (`GRDDL/Discovery.lean`) uses `xml:base` on the
  root element only. Nothing was changed there.

### (c) Parameter-entity nesting in external parameter entities

Issue 705 says the nesting constraints (XML 1.0 sections 2.8, 3.2, 3.3) are
checked only for references inside declarations of the external subset. The
constraints are in sections 2.8 (Proper Declaration/PE Nesting), 3.2.1 and 3.2.2
(Proper Group/PE Nesting) and 3.4 (Proper Conditional Section/PE Nesting);
section 3.3 has none. In the internal subset a reference may not stand inside a
markup declaration at all (WFC PEs in Internal Subset), and a reference between
declarations must have whole declarations as its replacement text (WFC PE
Between Declarations), so in the Fifth Edition no nesting violation can occur
there. What was missing is the case in the sentence the WFC ends with: "(This
does not apply to references that occur in external parameter entities or to
the external subset.)". The text of an external parameter entity that the
internal subset references was parsed as declarations without the scan that
includes references inside its declarations: such an entity was rejected as
not well-formed, and its nesting violations were never recorded. The same held
for an external parameter entity referenced from the external subset, and for an
internal parameter entity included from an external context whose
replacement text holds a reference written as `&#37;`. `parseSubset` now scans
the text of every parameter entity it includes from an external context
(`peScan`, moved before `parseSubset`), as the external subset's own text is,
and records the violations in `Doctype.peNesting`.

Fixtures: `tests/xml-local/pe-nesting/` (eleven documents): a reference inside
a declaration of an external parameter entity that the internal subset
references (valid); the three nesting violations in that position (invalid, each
naming its constraint); a conditional section in such an entity (valid); the
same violation from the external subset; a character-reference `%` in the
external subset (valid) and in the internal subset (not well-formed); a
reference inside a declaration of the internal subset (not well-formed); a
reference between declarations with a partial declaration (not well-formed).

### Open

- A default that is not an `[10] AttValue`, declared in an external subset that
  the processor reads, is checked only when a start tag leaves the attribute
  out and the default is supplied. The well-formedness constraints on attribute
  values apply to the declaration. The case
  `xml-local-defaults-unreadable-default-unused` has `XFAIL` naming
  https://github.com/danbri/factoidal/issues/705 and is the expected failure on
  the `xml-local` line.

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

## Nested entities in constant stack (https://github.com/danbri/factoidal/issues/755, 2026-10-12)

Section 4.4.2 includes the replacement text of an internal entity at the
reference, and that text can reference another entity. The parser expanded
such a chain with one native stack frame per level, in three places:
`expandEntityValue` (a reference in text or in an attribute value),
`entityHasWsCharRef` (the note that a white-space character reference is in
the content) and `parseChildren` (an entity whose replacement text carries
markup, reparsed as `[43] content`). WFC: No Recursion makes a chain finite,
but the document chooses its length: a chain of 10,000 text entities
overflowed a 512 KB native stack and the wasm module in Node, and a chain of
3,000 markup entities overflowed the wasm module under
`node --stack-size=512`.

Each now runs as a worklist, with the readable definition kept as the
specification and an equality theorem between the two:

| readable definition | loop the compiler runs (`@[csimp]`) | theorem |
|---|---|---|
| `expandEntityValue` | `expandEntityLoop` (pending texts: `EntPending`) | `expandEntityLoop_eq`, `expandEntityValue_eq_fast` |
| `entityHasWsCharRef` | `entityWsLoop` (texts to scan: `WsPending`) | `entityWsLoop_eq`, `entityHasWsCharRef_eq_fast` |
| `parseChildren`, `parseElement` | `parseChildrenW`, `parseElementW` (waiting frames: `ChildFrame`) | `parseChildrenW_eq`, `parseElement_eq_parseElementW`, `parseChildren_eq_parseChildrenFromStart` (added 2026-10-15) |

The theorems state the same characters, nodes, flags, notes, positions and
errors, with no hypothesis. A recursive text entity is rejected by the
`visited` check as before; a recursive markup entity exhausts the fuel and is
rejected by WFC: Parsed Entity, as before. Element nesting still costs one
frame of `parseElementW` per level: that is the document's own nesting.

The guards are in `XML/Tests.lean` (chains of 2,000 text and 1,000 markup
levels, the white-space note at the bottom of a chain, No Recursion and
Parsed Entity at the end of a chain); the stack is checked by the
`xml-text-chain` and `xml-markup-chain` cases of `tests/stack/run.sh`. The
scored lines did not move: `l4xmlconf` 1861 pass, 0 fail (out of 1861
scored), and the RDF/XML, XSLT, Schematron, MathML and XSD rows of
`tools/lean-scoreboard.sh` equal those of the base build (core 24d5aab2).
Measured canary numbers: `skills/danbri-function-precrime-checkers/SKILL.md`.

Addendum, 2026-10-15 (https://github.com/danbri/factoidal/issues/871). The theorem
`parseElement_eq_parseElementW` reaches the document element. `Syntax/RdfXml.lean` also
calls `parseChildren` directly: `parseChildrenFold` reads the replacement text of a markup
entity that is referenced from the content of `rdf:RDF` with it, and that call kept the recursive
form. `xml-markup-chain` puts its reference inside a node element, so no case reached the call: a chain
of 6,000 markup entities under `rdf:RDF` overflowed 512 KB (3,000 ran). The theorem
`parseChildren_eq_parseChildrenFromStart` covers the call, and the case `xml-markup-chain-top` runs the
chain at 10,000 levels. Record: `docs/designissues/2026-10-15-csimp-reach.md`, section 6, item 3.

Addendum, 2026-10-18 (https://github.com/danbri/factoidal/issues/872). After issue 871 the chain of
markup entities under `rdf:RDF` ran in bounded stack, but its time grew faster than the number of
levels. Measurement (`l4wasm-cli call parseToDatasetJson` on `xml-markup-chain-top`, one triple for each
level; callgrind at 5,000 levels, 2.90 G instructions) found three costs that each grow with the square
of the number of declarations or levels:

1. `lookupEntityDef` scanned the list of declarations: 967 M instructions, half from `declareEntity`
   (the check for an earlier declaration of the same name, a full scan for a new name) and half from
   `generalEntityRaw` (each reference).
2. The `mark` step of `parseSubset` measured `defs.length` twice for each declaration: 325 M.
3. `parseChildrenW` gave each waiting frame its own accumulator. The frame that continued after a
   replacement text appended the nodes of that text, which held the nodes of all deeper texts, to it
   (`acc ++ fr.acc`): 275 M in `List.appendTR`, and the frees of the copies.

Repair:

1. `EntityTable` (`XML/Document.lean`) keeps, beside `defs`, `index` (a hash map from a name to its
   declarations, newest first) and `count`, with the fields `index_eq : index = entityIndexOf defs` and
   `count_eq : count = defs.length`. `EntityTable.cons` adds a declaration to the three.
   `@[csimp] lookupEntityDef_eq_fast` (`XML/Parser.lean`) runs the lookup through the index; the proof is
   `find_defs_eq_find_index` by induction on the declarations. Equality of tables compares `defs` and
   the flags (a hand-written `DecidableEq`, lawful because `index` and `count` are functions of `defs`).
   The fuel bounds that were `ents.defs.length + 1` are `ents.count + 1`.
2. `parseEntityDecl` takes `unreadPe` (the `dtd.incomplete` of the caller) and sets `afterUnreadPe` on
   the declaration that it adds. The `mark` step that compared lengths and changed the newest
   declaration afterwards is removed; the table that results is the same.
3. `parseChildrenW` keeps one accumulator for the replacement text and the waiting frames, and
   `ChildFrame` has no accumulator. `resumeC` takes the part of the accumulator that the frames read
   before the replacement text (`base`), and `parseChildrenW_eq` now states
   `parseChildrenW frames s pos (acc ++ base) … = resumeC frames base (parseChildren s pos acc …)`,
   proved by the same mutual functional induction.

| levels | before | after |
|---:|---:|---:|
| 2,500 | 0.29 s | 0.14 s |
| 5,000 | 0.55 s | 0.17 s |
| 10,000 | 2.28 s | 0.39 s |
| 20,000 | 12.39 s | 0.51 s |
| 30,000 | 35.07 s | 1.06 s |
| 40,000 | 76.31 s | 1.04 s |

Callgrind: 5,000 levels 2.90 G to 1.34 G instructions, 10,000 levels 9.44 G to 2.64 G (ratio 1.97 for
twice the levels). The row `rdfxml-markup-chain` of `tests/stack/lean_scaling.sh` (`l4factoidal parse
--format rdfxml`, 5,000 against 20,000 levels) failed the bound with the build before (0.470 s to
10.770 s, ratio 22.9) and passes after.
