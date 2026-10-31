/- Necessary XML character admission at the RDF/result-to-XML boundary.
These are counterexample facts about the actual XML predicate and SRX escape
function, not a complete serializer or parser correctness theorem. -/
import L4Factoidal.SPARQL.ResultsXml

namespace L4Factoidal.SPARQL.ResultsXmlAdmission

/-- XML 1.0 Char excludes U+0001, including as a referenced code point. -/
theorem soh_not_xml10 : XML.isXmlCharCode 1 = false := rfl

theorem soh_not_xml10_reference : XML.XmlVersion.isCharCode .v10 1 = false := rfl

/-- Any literal U+0001 defeats XML 1.0's necessary character-stream admission. -/
theorem containing_soh_not_admitted (before after : List Char) :
    (before ++ Char.ofNat 1 :: after).all XML.isXmlChar = false := by
  simp [List.all_append, List.all_cons, XML.isXmlChar, XML.isXmlCharCode]

/-- The actual SRX escaping operation does not remove or represent this code point. -/
theorem srxEscape_soh :
    srxEscape (String.singleton (Char.ofNat 1)) = String.singleton (Char.ofNat 1) := rfl

theorem srxEscape_soh_not_admitted :
    (srxEscape (String.singleton (Char.ofNat 1))).toList.all XML.isXmlChar = false := rfl

/-- Escaping markup is not a universal XML-character admission guarantee. -/
theorem srxEscape_not_universally_admitted :
    ¬ ∀ s : String, (srxEscape s).toList.all XML.isXmlChar = true := by
  intro h
  have bad := h (String.singleton (Char.ofNat 1))
  rw [srxEscape_soh_not_admitted] at bad
  cases bad

private def sohLiteral : RDF.WfLiteral :=
  ⟨{ lexicalForm := String.singleton (Char.ofNat 1), datatype := RDF.xsdString, langTag := none, direction := none }, by decide⟩

/-- A term accepted by the RDF foundation type can have an SRX encoding that
fails XML 1.0 character admission. This concerns the actual termToXml producer. -/
theorem rdf_term_counterexample :
    ∃ t : RDF.Term, (termToXml t).toList.all XML.isXmlChar = false := by
  exact ⟨.literal sohLiteral, rfl⟩

-- Actual parser controls: XML 1.0 cannot solve this by a numeric reference;
-- XML 1.1 admits a reference, but still forbids the literal restricted char.
#guard !(XML.parseXML ("<r>" ++ String.singleton (Char.ofNat 1) ++ "</r>")).isOk
#guard !(XML.parseXML "<r>&#1;</r>").isOk
#guard (XML.parseXML "<?xml version=\"1.1\"?><r>&#1;</r>").isOk
#guard !(XML.parseXML ("<?xml version=\"1.1\"?><r>" ++ String.singleton (Char.ofNat 1) ++ "</r>")).isOk

#print axioms soh_not_xml10
#print axioms containing_soh_not_admitted
#print axioms srxEscape_soh
#print axioms srxEscape_not_universally_admitted
#print axioms rdf_term_counterexample
end L4Factoidal.SPARQL.ResultsXmlAdmission
