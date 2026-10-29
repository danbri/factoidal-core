# QT4: optional and environment features in qt4tests (agent qt4-K)

Tracking: https://github.com/danbri/factoidal/issues/1101 (QT4CG
specifications and qt4tests). Owner, 2026-10-28 22:25Z, verbatim: "if it is
within our reach to zero these counts, let's just be better at those pieces
of the spec landscape." Target: 0 fail and 0 unsupported in qt4tests, XPath
and XQuery modes.

## 1. Why a test is unsupported

The runner `formal/lean4/Harness/Qt4Run.lean` (`lake exe l4qt4`) marks a
test case unsupported when one of its dependencies (catalog element
`dependency`) is not satisfied, when its environment needs something the
runner does not build, or when an assertion needs something the evaluator
does not have. The script `tools/qt4/why-unsupported.py` counts the first
kind from the catalog files only (it runs no test):

    python3 tools/qt4/why-unsupported.py [ROOT] [--features a,b,...]

It copies `depOk` and `featureSupported` of the runner; pass `--features`
when the runner's list changes. The meaning of each dependency type is in
`dependency_meanings.xml` of https://github.com/qt4cg/qt4tests.

## 2. Settings of the dynamic context, set for each test

Some dependencies name a setting of the processor, not a capability:

| dependency | setting | where |
|---|---|---|
| `feature=xpath-1.0-compatibility` | XPath 1.0 compatibility mode (XPath 4.0 §2.2.1.1) | `Env.compat10` |
| `default-language=V` | the default language (XPath 4.0 §B.2) | `Env.defaultLanguage` |
| `xml-version=1.1` | XML 1.1 and XML Names 1.1 (XPath 4.0 §A.2, constraint xml-version) | `Env.xml11` |
| `feature=dtd-validation-option` (satisfied or not) | the `dtd-validation` option of `fn:doc` and `fn:parse-xml` | `Env.dtdValidation` |

`configureFor` in the runner sets these from the dependencies of each test.
`dependency_meanings.xml` says of `xpath-1.0-compatibility`: "requires the
expression to be evaluated in XPath 1.0 compatibility mode".

### XML version

XDM 4.0 §4.1.6: "Implementations are now required to accept all characters
allowed by XML 1.1, even if they do not support an XML 1.1 parser." So
strings hold every XML 1.1 character in both settings (`XPath4.isXmlCp`).
The setting changes only:

* XQuery end-of-line handling (XQuery 4.0 §A.3.3): CR LF and CR become LF
  always; with XML 1.1 also CR NEL, NEL and LINE SEPARATOR
  (`XQuery4.normalizeLineEnds`). XPath 4.0 does no end-of-line handling
  (the host language does): qt4tests `line-ending-P002`.
* character references in XQuery (XQST0090): XML 1.1 admits references to
  C0 and C1 control characters (`XQuery4.isXmlCharV`).
* namespace undeclarations in direct element constructors: `xmlns:p=""` is
  XQST0085 with XML Names 1.0; with XML Names 1.1 it undeclares `p`, and a
  use of `p` after that is XPST0081.
* the serializer writes a prefix undeclaration of an XML 1.1 source only
  with `undeclare-prefixes` and version 1.1.

The tests that need XML 1.0 before the fifth edition (`1.0:4-`) stay
unsupported: this processor never uses those name rules.

## 3. Features turned on

* The namespace axis, XPath mode only (XPath 4.0 §4.7.2.1; XQuery 4.0 says
  "XQuery does not support the namespace axis", XQST0134). The axis and
  namespace nodes were already in `XPath4.Core` (`nsNodesOf`).
* Collations other than the codepoint collation
  (`non_unicode_codepoint_collation`): `XPath4.Collation`.
* `arbitraryPrecisionDecimal`: a cast from `xs:double` or `xs:float` to
  `xs:decimal` keeps every digit (`XPath4.decOfFloat`).
* `limits=big_integer` and `limits=year_lt_0`. A year before 1 is shown
  with the AD calendar as `1 - year` BC (XSD 1.1 year 0 is 1 BC; F&O 4.0
  §9.8.4: "the year before 1 CE is thus 1 BCE").
* `unicode-normalization-form`: NFC, NFD, NFKC, NFKD and
  `FULLY-NORMALIZED` (`XPath4.Unicode.fullyNormalize`: a space before a
  first composing character, then NFC, as F&O 4.0 §5.4.9 defines it).
* The `dtd-validation` option: it was implemented (`XmlParse.parseDocument`
  calls `XML.validate`) but `fn:system-properties` reported false. It is
  now a setting (`Env.dtdValidation`, on by default). `fn:doc` resolves the
  external DTD subset and external entities against the document's URI,
  and the runner reads the files that an XML resource names. After DTD
  validation, whitespace text in element content is dropped (XDM 4.0
  §7.6.3).
* The `xinclude` option: XInclude 1.1 (`XPath4.XInclude`): `parse="xml"`
  and `parse="text"`, `xi:fallback`, loop detection, base URI fixup
  (`xml:base`) and default-namespace fixup; `xpointer` is not evaluated (a
  resource error, so the fallback applies). A setting (`Env.xinclude`), as
  the DTD option. Included resources need `trust-external`.
* `fn:doc` with other parsing options (`strip-space`, `dtd-validation`,
  `xinclude`, `xsd-validation`) gives another document node (option
  `stable`, F&O 4.0 §14.6.1).
* `l4qt4 --list-fails` writes the reason of every unsupported case: the
  first dependency that is not satisfied, or the environment.

## 4. Static typing: dropped by the 4.0 specifications

XPath 4.0 and XQuery 4.0, changes in 4.0: "The static typing feature has
been dropped. [Issue 1343 PR 1344 3 September 2024]". XPST0005 is not
defined in the 4.0 texts. The 77 test cases with `feature=staticTyping`
(48 apply to XPath 4.0) test the pessimistic static typing of XQuery 1.0 to
3.1 (`dependency_meanings.xml`: "Requires 'pessimistic' static typing").
Example: `fn:filter((), if (current-dateTime() eq ...) then fn:exists#1
else 1)` must raise XPTY0004 although the evaluation that runs never sees
the integer.

A 4.0 processor cannot claim a feature that 4.0 does not define. These
cases stay unsupported until the owner decides between: (a) report them
apart, as "not applicable to 4.0 (feature dropped)", the way the XQuery-only
cases are not counted in XPath mode; (b) implement the 3.1 pessimistic
static typing as an opt-in mode of the runner.

## 5. Dependencies that cannot all be satisfied by one processor

* `unicode-version=V` (5 cases): the expected results hold for Unicode
  version V. `fn-normalize-unicode-11*` list the characters that version V
  leaves unassigned; Unicode 16.0 assigns some of them. Unsupported.
* `!feature=F` for a feature this processor has (`satisfied="false"`):
  the test is for processors that lack F. Unsupported, unless F is a
  setting (section 2).

## 6. Measured

From `formal/lean4/`, `ulimit -s 65520`, `lake build l4qt4`,
`.lake/build/bin/l4qt4 --isolate 60 [--lang xquery]`, qt4tests `b39c4bc0`
(the vendored copy on `main`), each run with its own `TMPDIR`:

| mode | `main` 08ef339d | this work |
|---|---|---|
| XPath | 28250 pass, 705 fail, 9704 unsupported | 28331 pass, 695 fail, 9633 unsupported |
| XQuery | 42244 pass, 1746 fail, 1956 unsupported | 42305 pass, 1735 fail, 1906 unsupported |

(out of 38659 and 45946). No test set has fewer passes. FULLY-NORMALIZED
came after these runs: `fn-normalize-unicode` 41 pass, 9 unsupported before,
44 pass, 6 unsupported after, in both modes.

## 7. Theorems

No `sorry`, no new axioms (`#print axioms`: propext, Classical.choice,
Quot.sound).

`formal/lean4/L4Factoidal/XPath4/OptionalTheorems.lean`:

* `nsNodesOf_sound`, `nsNodesOf_complete`: the namespace nodes of an
  element are the in-scope bindings of the `XML.Namespaces` scope the
  record was made from (`XML.lookupPrefix`), plus `xml`.
* `firstBinds_mem`: the first binding of a prefix is the one in force.
* `isXmlCp_eq_xml11`, `isXmlCp_of_xml10`, `xml11_agrees_xml10`: XPath 4.0
  strings hold XML 1.1 `Char` (`XML.isXml11CharCode`); on XML 1.0
  characters the two versions agree.
* `#guard`s: `Doc.ofDocument` against `XML.applyDeclarations` on sample
  documents.

`formal/lean4/L4Factoidal/XQuery4/XmlVersionTheorems.lean`:

* `normalizeLineEnds_agree`: the XML 1.1 and XML 1.0 end-of-line handling
  give the same text when the query has no NEL and no LINE SEPARATOR.
* `normalizeLineEnds_no_cr`: after either, the text has no CR.
* `isXmlCharV_of_xml10`, `isXmlCharV_true_eq`: a character reference that
  the XML 1.0 grammar reads is read the same with XML 1.1; the XML 1.1
  class is `XML.isXml11CharCode`.

`formal/lean4/L4Factoidal/XPath4/XIncludeTheorems.lean`:

* `expand_noXi`: `XInclude.expand` gives back the node itself when no
  element of the subtree is in the XInclude namespace. So the `xinclude`
  option changes nothing for such a document. `#guard`s in
  `XPath4/XInclude.lean` test text and XML inclusion, the fallback, a
  resource error and a loop.

Open: that `XPath4.buildNode` sets `inscope` to `convScope` of the scope
that `XML.applyDeclarations` computes for the same element (tested by the
`#guard`s, not proved).

## 8. A measurement error and its repair

2026-10-28: two `l4qt4 --isolate` runs at the same time (XPath mode and
XQuery mode) wrote the same progress files `$TMPDIR/l4qt4-progress-<set>`.
Whole test sets were read from the other run's file and scored as all
fail: XPath mode showed 28013 pass, 1046 fail, against 28319 pass, 705 fail
for the same binary run alone. The progress file name now holds the mode
and the process id. Until a runner with that fix is built, give each run its
own `TMPDIR`.
