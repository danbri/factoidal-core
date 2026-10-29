/-
DTD information carried from the XML parser into runtime XDM documents.
Attribute defaults and normalization are performed by XML.Parser, before
this adapter. DTD validation reuses XML.Validity, including parser notes.
-/
import L4Factoidal.XPath4.Doc
import L4Factoidal.XML.Validity

namespace L4Factoidal.XPath4

open L4Factoidal.XML

/-- Preserve the parser's DTD attribute declarations when the XDM tree is
    rebuilt after whitespace processing. No schema type annotations are added. -/
def Doc.withDtdInfoset (base : Doc) (d : Document) (enabled : Bool := true) : Doc :=
  if enabled then
    match d.doctype with
    | none => base
    | some dt =>
      { base with
        idAttrs := dt.idAttrs
        idrefAttrs := (dt.attDecls.filter (fun a =>
            a.type == AttType.IDREF || a.type == AttType.IDREFS)).map
            (fun a => (a.element, a.name)) }
  else base

@[simp] theorem Doc.withDtdInfoset_disabled (base : Doc) (d : Document) :
    base.withDtdInfoset d false = base := rfl

/-- DTD typing does not rebuild, remove, or replace any attribute node.
    Thus the normalized defaults supplied by XML.Parser are retained. -/
@[simp] theorem Doc.withDtdInfoset_nodes (base : Doc) (d : Document) (enabled : Bool) :
    (base.withDtdInfoset d enabled).nodes = base.nodes := by
  cases enabled <;> cases h : d.doctype <;> simp [Doc.withDtdInfoset, h]

/-- Runtime readers and the existing document reader use the identical
    XML DTD ID declaration table. -/
theorem Doc.withDtdInfoset_ids (base : Doc) (d : Document) (dt : Doctype)
    (h : d.doctype = some dt) :
    (base.withDtdInfoset d).idAttrs = (Doc.ofDocument d).idAttrs := by
  simp [Doc.withDtdInfoset, Doc.ofDocument, h]

/-- Runtime readers and the existing document reader use the identical
    IDREF and IDREFS declaration table. -/
theorem Doc.withDtdInfoset_idrefs (base : Doc) (d : Document) (dt : Doctype)
    (h : d.doctype = some dt) :
    (base.withDtdInfoset d).idrefAttrs = (Doc.ofDocument d).idrefAttrs := by
  simp [Doc.withDtdInfoset, Doc.ofDocument, h]

/-- A declared ID attribute contributes the same ID value used by fn:id,
    regardless of separate lexical or fixed-value violations. -/
theorem validity_id_value (dt : Doctype) (tag : String) (a : Attribute)
    (decl : AttDecl) (hdecl : attDeclOf dt.attDecls tag a.name = some decl)
    (htype : decl.type = .ID) :
    (checkAttributes dt tag [a]).2.1 = [a.value] := by
  simp [checkAttributes, hdecl, htype]

/-- IDREFS values use the XML validity layer's whitespace tokenization. -/
theorem validity_idrefs_tokens (dt : Doctype) (tag : String) (a : Attribute)
    (decl : AttDecl) (hdecl : attDeclOf dt.attDecls tag a.name = some decl)
    (htype : decl.type = .IDREFS) :
    (checkAttributes dt tag [a]).2.2 = tokens a.value := by
  simp [checkAttributes, hdecl, htype]

/-- The parser's default-attribute producer uses exactly the normalized
    value consulted by the XML validity layer for the same declaration. -/
theorem parser_default_attribute (ents : EntityTable) (decl : AttDecl)
    (tag lit value : String) (htag : decl.element = tag)
    (hdefault : decl.defaultDecl = .value lit)
    (hvalue : defaultValue ents decl = some value) :
    defaultedAttrs ents [decl] tag [] =
      .ok [{ name := decl.name, value }] := by
  simp [defaultedAttrs, defaultedAttrs.go, htag, hdefault, hvalue]

end L4Factoidal.XPath4
