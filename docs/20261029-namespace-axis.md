# Namespace axis configuration work

Date: 2026-10-29.

The namespace axis and namespace records were already implemented in the
XPath 4 engine. The runner did not admit the `namespace-axis` feature.
Configuration selection is handled in the accompanying processor change.

The document model now reuses `XML.visibleBindings` for namespace enumeration.
The ordered enumeration bridge and guards are in `XPath4/Doc.lean`.
See the [design record](designissues/2026-10-29-xpath-namespace-view.md) for
the exact theorem hypotheses and the existing index capacity limit.

`lake env lean L4Factoidal/XPath4/Doc.lean`, run with `formal/lean4/` as
the explicit working directory, exits 0. This checks the theorem and guards.
The coordinated `l4qt4` build and target-set runs supply integration validation.
No conformance score is claimed in this note.
