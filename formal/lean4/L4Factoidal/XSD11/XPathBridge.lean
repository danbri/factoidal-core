/-
L4Factoidal.XSD11.XPathBridge — theorems that tie the schema-aware paths of
XPath 4.0 and F&O 4.0 (`L4Factoidal.XPath4`) to XML Schema 1.1 validation
(`L4Factoidal.XSD11`), so that the two trees have one validation path.

* `docOfKids_skip`: with `xsd-validation` `skip`, the document that
  `fn:parse-xml`, `fn:parse-xml-fragment` and `fn:doc` make is the parsed
  tree (`Doc.ofNodes`).
* `docOfKids_validate`: with the in-scope schema definitions of
  `schemaHookOf s` and another `xsd-validation` mode, that document is the
  result of `validateFor s` on the document element of the parsed tree
  (`XML.Parser`): XPath 4.0 has no validation of its own.
* `validateFor_ok`: a document that `validateFor` gives is the XDM
  document (`psviDoc`) of the PSVI that `validateElement` makes from that
  element, and the PSVI erases to the element (`validateElement_erase`):
  validation adds annotations and does not change the parsed tree.
* `parseXml_validate`: the two together for one call of `fn:parse-xml`'s
  document step.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Load
import L4Factoidal.XSD11.Theorems

namespace L4Factoidal.XSD11

open L4Factoidal.XML

theorem docOfKids_skip (e : XPath4.Env) (o : XPath4.ParseOpts) (kids : List Node) (uri : String)
    (h : o.xsd = "skip") : XPath4.docOfKids e o kids uri = .ok (XPath4.Doc.ofNodes kids uri) := by
  simp [XPath4.docOfKids, h]
  rfl

theorem docOfKids_validate (s : Schema) (e : XPath4.Env) (o : XPath4.ParseOpts)
    (kids : List Node) (uri : String) (root : Node)
    (hs : e.schema = schemaHookOf s) (hx : o.xsd ≠ "skip")
    (hr : kids.find? XPath4.isElemKid = some root) :
    XPath4.docOfKids e o kids uri = validateFor s o.xsd root uri := by
  unfold XPath4.docOfKids
  simp only [hs, schemaHookOf, hr, beq_iff_eq, hx, if_false]
  cases validateFor s o.xsd root uri <;> rfl

theorem validateFor_ok (s : Schema) (mode : String) (root : Node) (uri : String) (d : XPath4.Doc)
    (h : validateFor s mode root uri = .ok d) :
    ∃ how, d = psviDoc s (validateElement s xpathHooks 10000 [] how root {}).1 uri ∧
      (validateElement s xpathHooks 10000 [] how root {}).1.erase = root := by
  unfold validateFor at h
  cases hw : howFor s mode root with
  | none => simp [hw] at h
  | some how =>
    simp only [hw] at h
    refine ⟨how, ?_, validateElement_erase s xpathHooks 10000 [] how root {}⟩
    unfold validateHow at h
    simp only at h
    split at h
    · cases h
    · cases h; rfl

/-- `fn:parse-xml` with `xsd-validation` (not `skip`) under the in-scope
schema of `schemaHookOf s`: when the document step succeeds, its document
is the XDM document of the PSVI of the parsed document element, and that
PSVI erases to the parsed element. -/
theorem parseXml_validate (s : Schema) (e : XPath4.Env) (o : XPath4.ParseOpts)
    (kids : List Node) (uri : String) (root : Node) (d : XPath4.Doc)
    (hs : e.schema = schemaHookOf s) (hx : o.xsd ≠ "skip")
    (hr : kids.find? XPath4.isElemKid = some root)
    (hd : XPath4.docOfKids e o kids uri = .ok d) :
    ∃ how, d = psviDoc s (validateElement s xpathHooks 10000 [] how root {}).1 uri ∧
      (validateElement s xpathHooks 10000 [] how root {}).1.erase = root := by
  rw [docOfKids_validate s e o kids uri root hs hx hr] at hd
  exact validateFor_ok s o.xsd root uri d hd

end L4Factoidal.XSD11
