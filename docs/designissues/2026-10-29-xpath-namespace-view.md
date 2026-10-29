# XPath namespace nodes and the XML namespace view

Date: 2026-10-29.

The XPath 4 document model already supplies namespace nodes. It stores the
in-scope declarations on each element and makes namespace records on demand.
A namespace record has its element as parent. Its expanded name has an empty
namespace URI and the declared prefix as local name. Its string value is the
bound URI. Namespace declarations are excluded from the attribute axis.

`XPath4.NRec.namespaceScope` converts this string-valued scope to
`XML.NsScope`. An empty URI becomes `none`, so an undeclaration hides an
inherited binding. `XPath4.nsNodesOf` now calls `XML.visibleBindings` from
`XML/NamespaceView.lean` to remove shadowed bindings and undeclarations.
This replaces the separate XPath deduplication algorithm.

`nsNodesOf_eq_visibleBindings` states ordered list equality with that shared
view for element records whose visible scope fits the index encoding and
already contains the mandatory `xml` binding. The proof is in `Doc.lean`,
so every build that uses the document model checks it. Build-time guards
check shadowing, default namespace undeclaration, non-element nodes, and
the fallback XML binding for manually constructed records.

The existing namespace node index encoding reserves 4096 positions per
element and retains at most 4094 visible bindings before the fallback XML
binding. This change preserves that limit. The theorem states its size
hypothesis explicitly. It does not establish correspondence for larger
scopes, or prove that document flattening supplies the correct scope at
every element. These remain separate proof obligations.

The qt4tests runner must admit `feature=namespace-axis` for these existing
operations to be tested. The processor setting and runner selection are
part of the accompanying configuration change. The namespace view change
itself does not select configurations.
