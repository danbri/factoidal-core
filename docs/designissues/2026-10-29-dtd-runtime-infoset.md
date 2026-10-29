# Runtime DTD information and XInclude configuration

Date: 2026-10-29

The XML parser already applies DTD attribute defaults, normalizes tokenized
attribute values, and retains declarations. `XPath4.Doc.ofDocument` already
copies ID and IDREF declarations. The runtime `parse-xml` and resource-backed
`doc` paths previously called `Doc.ofNodes` and lost those declaration tables.
`XPath4.DtdInfoset` now supplies `Doc.withDtdInfoset` for those paths. It retains
the existing tree, including defaulted attributes, and copies the same tables
as `Doc.ofDocument`. The `dtdInfoset` processor setting controls that copy.
It adds no XSD type annotations.

The bridge theorems establish that the adapter leaves all node records intact,
that disabling it is the identity, and that its ID and IDREF tables agree with
`Doc.ofDocument` when the input table is initially empty. The attribute token
theorems connect declared ID and IDREFS values to `XML.Validity.checkAttributes`.
These statements do not establish complete DTD validation or XDM conformance.

DTD validation already existed as a parse option. Its processor setting can
now disable it. The reader keeps `XML.Parser.Notes` and calls
`XML.Validity.validateWithNotes`, so validity constraints involving standalone
processing or reference provenance can use the facts recorded by the parser.
The old `validate` call reconstructed empty notes after discarding those facts.

XInclude is disabled by default. When enabled, the parse option expands
namespace-qualified include elements through caller-supplied resources. XML
and text inclusions, nested references, and fallback are implemented without
I/O. An inclusion cycle, missing resource, unsupported XPointer, malformed XML,
or excessive nesting produces an error. A no-namespace included document root
gets a default namespace reset, to prevent adoption of the including element's
namespace. Included roots also carry resolved xml:base and xml:lang, and fallback
roots retain namespace, base URI and language context from their removed parents.
XPointer selection and DTD declaration merging across included documents are not
implemented.

The parent session runs the build and regression sets. No measurements have
been recorded in this note before that verification.
