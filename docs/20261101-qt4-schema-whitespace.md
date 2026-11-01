# Schema-aware XML parsing whitespace

F&O 4.0 `strip-space: all` preserves whitespace-only text when XSD
validation identifies simple or complex-with-simple content, as well as
within inherited `xml:space="preserve"`. See the option table in
https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-parse-xml
(same cached normative snapshot as `20261101-qt4-parse-schema-errors.md`).

Previously parsing stripped whitespace before schema validation, destroying
the lexical value in official QT4CG parse-xml-436. Parsing now defers this
stripping when XSD validation is requested. The validator sees the lexical
content and applies its normal whitespace facets/typed-value computation.
The resulting typed XDM is then filtered using its annotations. Existing
PSVI construction already removes element-only whitespace. Simple-content
exemptions are local; `xml:space` inheritance and `default` resets are separate.

`stripValidatedWs` removes only eligible text leaves and compacts the
preorder array. Parent, child, attribute, subtree-end and origin indices
are remapped, preventing orphan whitespace from appearing in range-based
axes or string values. Node annotations, typed values, namespace bindings,
document/base URIs, ID/IDREF metadata and source origin are retained. Its
input contract is a freshly constructed preorder XDM (parents precede
children); it does not repair arbitrary malformed host-supplied documents.
The traversal uses two linear array passes plus existing attribute scans.

The new `parsedDocOfKids` wrapper applies this parsing policy. Raw
`docOfKids` and shared XQuery/XProc validators retain their contracts.
The kernel proves `parsedDocOfKids_no_strip` equals the previous document
step when stripping is disabled. Axiom audit: propext, Classical.choice,
Quot.sound only. This is an identity theorem, not a general proof of
compaction topology or full SVG/XML conformance.

## Validation

Lean 4.33.1 checks the changed XmlParse module and 23 executable guards in
`XSD11/XmlParseWhitespaceTests.lean`: real schema parsing/validation,
public `parseXmlFn` and `parseFragmentFn`, simple/complex simple content,
normalized token typed values, lax untyped content, xml:space inheritance
and reset, compacted sibling/parent/attribute/subtree indices, string
values and metadata. No mutation-testing claim is made.

Targeted native runner `/private/tmp/l4qt4-xsd-whitespace` replaces current
XmlParse and Load objects in the existing October 30 native object graph;
it is not a whole-current-HEAD or npm/WASM build. SHA256:
`8e27b71f999521b13278d70af82ee6462c86a2dfa8132ce9899edbdf2d67d88f`.
Unmodified QT4CG fixtures at `18728a6943589f8341d67f94af154e3c68917bbb`:

| Set | Before pass/fail/unsupported | After |
|---|---|---|
| fn-parse-xml | 53 / 1 / 3 | 54 / 0 / 3 |
| fn-parse-xml-fragment | 40 / 0 / 1 | 40 / 0 / 1 |
| fn-doc | 75 / 1 / 3 | 75 / 1 / 3 |

The three parse-xml unsupported entries remain older-language dependency
cases; none were removed or newly skipped. fn-doc-40-065 remains a visible
failure. Run from `formal/lean4`:

```sh
/private/tmp/l4qt4-xsd-whitespace \
  --root ../../../factoidal-qt4/third_party/testing/qt4tests \
  --family fn --set fn-parse-xml --lang xquery --list-fails
```
