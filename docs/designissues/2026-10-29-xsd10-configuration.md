# Selectable XML Schema 1.0 processing

Date: 2026-10-29.

The processor configuration carries `FeatureSettings.xsdVersion` and
`FeatureSettings.schemaLocationHints`. The default is XSD 1.1 with location
hints off. A caller can select XSD 1.0 independently of location hints.
The qt4tests runner selects the version from `xsd-version` dependencies.
Its XSD 1.0 profile enables schema location hints, since schema-aware
modules can import their schema documents. An explicit negative dependency
turns location hints off.

The runner chooses the configuration before it builds the environment.
Thus source validation, schema loading, expression evaluation and result
assertions use the same version. The schema cache key includes the version.

## Reuse and execution

`XSD.Version` adapts the existing `XSD.Lexical` edition policy. Calendar
values use the shared astronomical calendar internally. The 1.0 lexical
adapter rejects year zero and translates negative lexical years. The
existing XSD parsers and value facets remain the datatype implementation.
XPath constructors, casts and function conversion use the selected policy.
The XPath type library keeps the F&O duration extensions in 1.0 mode, but
does not expose `xs:dateTimeStamp`.

The regex engine shares compilation and execution. In 1.0 mode the shared
character-class parser also checks the stricter placement of an unescaped
hyphen. The literal `q` flag bypasses regex grammar, as before. Matching,
replacement, tokenization, analysis, compiled regex records and collection
filters use the same setting.

The schema reader retains component indices across editions and controls
which built-in declarations are visible. It checks original schema
documents for 1.1 constructs before conditional inclusion can remove them.
The validator and the XPath schema hooks share those components.

Schema location hints are handled in the Lean XQuery library. A preparatory
parse collects imports, then the existing XSD reader assembles the schema
from host-supplied documents. The final parse checks schema references
against those components. Imported library modules and modules supplied to
`fn:load-xquery-module` use this path too. Schema hooks retain source
documents so another import can rebuild a combined schema without losing
existing components. Resource reading stays in the host; the evaluator
performs no network or filesystem access.

`FnItem.scoped` retains the complete schema hook and feature settings for
functions returned by a dynamically loaded module. Application restores
that context. This also supports nested inline functions. Named simple
types use the existing primitive cast and schema facet checks when called
as constructors.

Schema-aware function type comparisons use the existing recursive subtype
operation with a schema parameter. The hook supplies type derivation,
declarations, substitution affiliation and abstract-element information.
Instance matching excludes abstract elements; type comparison retains the
declaration relationship.

Two shared defects were exposed by the newly enabled targets. Regex
matching must clear nested captures when it enters their enclosing group
again, so an internal back-reference cannot read a previous iteration's
capture. Element construction distinguishes directly nested literal
children from nodes inserted through enclosed expressions. Direct literal
children inherit explicit namespace declarations; copied nodes inherit
the full parent scope, including bindings added for name fixup. Validation then
preserves the original XDM namespace properties while adding type
annotations and bindings needed by defaulted attributes.

## Assurance boundary

Default-path equalities are definitional. Common-datatype lemmas connect
the versioned lexical mapping and facets to the existing XSD operations.
Regex agreement is conditional on acceptance by the 1.0 grammar. These
proofs establish implementation agreement, not complete conformance to
either XML Schema specification.

The common atomic theorem excludes calendar and floating-point lexical
differences and requires pattern facets accepted by the 1.0 grammar.
Particle restriction, unique particle attribution and element declaration
consistency still use the shared 1.1 algorithms. There is no general
schema-structure equivalence theorem. General BCE serialization still uses
the shared 1.1 year spelling, although lexical input and the date component
functions use the selected edition. The qt4tests measurements do not
establish full XSD 1.0 conformance.

The final theorem names, measured scores and remaining target failures are
recorded in [the report](../../REPORT.md). The target tests are the actual
qt4tests cases; none is reclassified by this change.
