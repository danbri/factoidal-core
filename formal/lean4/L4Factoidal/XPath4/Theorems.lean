/-
L4Factoidal.XPath4.Theorems — what binds the XPath 4.0 tree to the rest
of the project: proved statements, and build-time checks (`#guard`) where
a statement is only tested.

Proved here (no `sorry`, no new axioms):

* `nodeLt_irrefl`, `nodeLt_trans`, `nodeLt_total` — document order on
  node references is a strict total order (XDM 4.0 §2.4: a total order
  over all nodes; within a document, the node table index, which
  `XPath4.Doc` assigns in preorder).
* `nodeRef_at_doc`, `nodeRef_at_rt` — moving to another node of the
  same document keeps the document (the axes stay in one tree, also for
  a document built at run time).
* `Env.doc_rt` — a node built at run time reads its own tree, never
  the caller's documents.
* `parseXml_eq` — `fn:parse-xml` (no options) builds its tree from
  `XML.Document.children` of the project's XML parser, nothing else, and
  raises no error, when the parser accepts the text, the text is
  namespace-well-formed and needs no external resource.
* `matchAt_eq` — the matching segments of `fn:analyze-string`,
  `fn:matching-segments` and `fn:replace` are found by
  `Regex.cmatch`, the ordered matcher of `Regex.XPath` (the same one
  SPARQL `REPLACE` uses).
* `upperCase_shared` and seven more, `matches_shared` — the `fn:`
  string functions are the `L4Factoidal.Fn.String` functions that SPARQL,
  RIF and RML call; `fn:matches` is `Regex.isMatch`.
* In `XPath4.Json`: `parseJsonText_eq` (`fn:parse-json` is
  `JSON.parseJson` on a text with no unpaired surrogate escape) and
  `x2jEscChar_eq_escapeChar` (`fn:xml-to-json` escapes a string
  character as the project serializer `JSON.escapeChar` does, outside
  the characters the XPath rules treat specially).

Tested here (`#guard`), not proved:

* XPath 1.0 / 4.0 agreement on a sample of XPath 1.0 expressions over one
  document: `L4Factoidal.XPath.Full.evalText` (the engine of the XSLT 1.0
  and GRDDL paths) and `XPath4.evalString` give the same string, for
  location paths over the 1.0 axes, predicates, and core functions.
* `xml-to-json(json-to-xml($j))` gives back `$j` for JSON texts in the
  normal form xml-to-json writes (F&O 4.0 §17.5: the round trip holds
  up to insignificant whitespace and number form).
* `parse-json($j)` and `JSON.parseJson $j` agree on samples.

Open (recorded in the Stage 2 worknote): a proof that `Doc.ofNodes`
assigns indices in preorder with parent links that agree with the
children of `XML.Node`; a proof of the 1.0/4.0 agreement over the whole
1.0 fragment; a proof of the JSON round trip.
-/
import L4Factoidal.XPath4.Eval
import L4Factoidal.XPath4.CastTheorems
import L4Factoidal.XPath.Eval
import L4Factoidal.JSON.Parser
import L4Factoidal.XPath4.DocTheorems2
import L4Factoidal.XPath4.PathTheorems

namespace L4Factoidal.XPath4

/-! ## Document order -/

theorem nodeLt_irrefl (a : NodeRef) : nodeLt a a = false := by
  simp [nodeLt]

theorem nodeLt_trans (a b c : NodeRef) (h1 : nodeLt a b = true) (h2 : nodeLt b c = true) :
    nodeLt a c = true := by
  simp only [nodeLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  omega

theorem nodeLt_total (a b : NodeRef) :
    (a.doc = b.doc ∧ a.idx = b.idx) ∨ nodeLt a b = true ∨ nodeLt b a = true := by
  simp only [nodeLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem nodeRef_at_doc (n : NodeRef) (i : Nat) : (n.at i).doc = n.doc := rfl
theorem nodeRef_at_rt (n : NodeRef) (i : Nat) : (n.at i).rt = n.rt := rfl
theorem nodeRef_at_idx (n : NodeRef) (i : Nat) : (n.at i).idx = i := rfl

theorem Env.doc_rt (e : Env) (n : NodeRef) (d : Doc) (h : n.rt = some d) : e.doc n = d := by
  simp [Env.doc, h]

/-! ## Regular expressions -/

theorem matchAt_eq (r : Regex.Compiled) (p : Regex.Re) (input suffix : List Nat) (pos : Nat) :
    matchAt r p input suffix pos =
      if Regex.Exec.acceptsNorm p suffix then
        Regex.cmatch input r.multiline (Regex.cmatchFuel r.capt suffix) r.capt suffix pos some
      else none := rfl

/-! ## XPath 1.0 and XPath 4.0 on the 1.0 fragment (tested) -/

/-- XPath 1.0 (`XPath.Full`): the string form of the value; a node-set
    gives the string values of its nodes, joined by `|`. -/
def xp1 (xml expr : String) : Option String := do
  let d ← (L4Factoidal.XML.parseXML xml).toOption
  let kids := d.children
  let v ← XPath.Full.evalText { doc := kids, item := .doc kids 0 } expr
  match v with
  | .nodes ns => some (String.intercalate "|" ((XPath.Full.normalize ns).map XPath.Full.Item.stringValue))
  | other => some other.toStr

/-- XPath 4.0, the same form. -/
def xp4 (xml expr : String) : Option String := do
  let d ← (Doc.ofString xml).toOption
  let env : Env := { docs := #[d], ctx := some [.node (NodeRef.mk' 0 0)], pos := 1, size := 1 }
  let s ← (evalString expr env).toOption
  match s with
  | [.atom a] => some a.str
  | items =>
    if items.all Item.isNode then
      some (String.intercalate "|" (items.filterMap (fun i => match i with
        | .node n => some (env.nodeString n) | _ => none)))
    else none

def sampleXml : String :=
  "<doc a='1'><p id='x'>one<b>bold</b></p><p>two</p><!--c--><q n='3'>three</q><p n='5'>four</p></doc>"

def sample1 : List String := [
  "/doc/p", "//p", "//p[2]", "//p[last()]", "//p[@n]", "//*[@n > 2]",
  "/doc/p[1]/b", "//b/ancestor::*", "//b/ancestor-or-self::node()", "//q/preceding-sibling::p",
  "//q/following-sibling::*", "//b/parent::p", "//p[1]/descendant::text()", "//p/following::q",
  "//q/preceding::text()", "/doc/@a", "//@n", "//p/self::p", "count(//p)", "string(//p[2])",
  "concat(//p[1], '-', //q)", "contains(//q, 'hr')", "starts-with(name(/doc), 'd')",
  "string-length(//p[3])", "normalize-space('  a  b ')", "translate('abc', 'ab', 'AB')",
  "substring-before('a-b', '-')", "substring-after('a-b', '-')", "substring('abcdef', 2, 3)",
  "boolean(//p[4])", "not(//q)", "sum(//@n)", "floor(number(//q/@n) div 2)", "round(2.5)",
  "local-name(//*[@id])", "count(//node())", "count(//text())", "//p[. = 'two']",
  "//*[position() = 2]", "name(//q/..)", "string(//comment())", "count(//p | //q)",
  "//p[@n][1]", "true() and not(false())", "number('12') + 1", "lang('en')"
]

/-- The sample expressions on which the two engines agree (all of them,
    when this guard holds). -/
def agree1 : List String := sample1.filter (fun x => xp1 sampleXml x == xp4 sampleXml x)

#guard agree1.length == sample1.length
-- and neither engine refused any of them
#guard sample1.all (fun x => (xp1 sampleXml x).isSome && (xp4 sampleXml x).isSome)
#guard xp4 sampleXml "//p[last()]" == some "four"

/-! ## JSON (tested) -/

def rtJson (j : String) : String :=
  evalShow ("xml-to-json(json-to-xml('" ++ j ++ "'))")

#guard rtJson "{\"a\":[1,true,null,\"x\"],\"b\":{}}" == "{\"a\":[1,true,null,\"x\"],\"b\":{}}"
#guard rtJson "[\"a/b\",-0.5e3,[]]" == "[\"a\\/b\",-0.5e3,[]]"
#guard rtJson "\"line\\nbreak\"" == "\"line\\nbreak\""

/-- `parse-json` against `JSON.parseJson`: the XPath view of the
    library's tree (`JV.ofJson`) is what `parseJsonText` returns. -/
def jvShape : JV → String
  | .null => "n" | .bool _ => "b" | .num _ => "#" | .str _ => "s"
  | .arr xs => "[" ++ toString xs.length ++ "]"
  | .obj kvs => "{" ++ toString kvs.length ++ "}"

#guard (match JSON.parseJson "{\"a\":[1,\"x\",{\"b\":null}]}", parseJsonText "{\"a\":[1,\"x\",{\"b\":null}]}" with
  | .ok j, .ok v => jvShape (JV.ofJson [] j) == jvShape v && jvShape v == "{1}"
  | _, _ => false)
#guard evalShow "parse-json('{\"a\":[1,\"x\",{\"b\":null}]}')?a?3 => map:size()" == "1"

/-! ## fn:parse-xml is the project's XML parser -/

open L4Factoidal.XML in
/-- With no options, `fn:parse-xml` on a string that the XML parser
    (`XML.Parser`, the well-formedness decision) accepts, that is
    namespace-well-formed and that needs no external resource, returns the
    document node of `Doc.ofNodes` over the parser's document children
    (prolog, element, epilog) after xml:id processing (`normXmlId`, which
    only normalizes the value of `xml:id` attributes): the node table is
    built from `XML.Document.children` and nothing else. -/
theorem parseXml_eq (h : Hooks) (e : Env) (s : String) (d : Document)
    (hp : parseDecodedXMLWith (fun _ => none) s = .ok d)
    (hns : d.namespaceWellFormed = true)
    (hsys : d.doctype.bind (·.systemId) = none)
    (hext : refsExternalEntity d s = false) :
    parseXmlFn h e [sStr s, []] =
      .ok [({ Doc.ofNodes (d.children.map (normXmlId 100000)) with baseUri := e.baseUri }).rootItem
        (runtimeDocId "parse-xml" s)] := by
  simp [parseXmlFn, parseOpts, parseDocument, docKids, checkOptionKeys, optLookup, optBool, optionStr,
    bytesOfAtomic, sStr, single, optAtom, argN, Atomic.ofStr, Atomic.str, hp, hns, hsys, hext]
  cases d.doctype <;> rfl

/-! ## One function library with SPARQL, RIF and RML

These `fn:` functions are, by definition, the functions of
`L4Factoidal.Fn.String` that `SPARQL/Expr.lean` (UCASE, LCASE,
ENCODE_FOR_URI, CONTAINS, STRBEFORE, STRAFTER), `RIF/Builtins.lean` and
`RML/Functions.lean` call, so a theorem about one is a theorem about the
other. Each lemma is the table entry applied to a string argument. -/

section FnShared
variable (h : Hooks) (e : Env) (s t : String)

def fnQ (l : String) : QN := { uri := nsFN, loc := l }

theorem upperCase_shared :
    (libLookupAll (fnQ "upper-case")).map (fun f => f h e [sStr s]) =
      some (pure (sStr (Fn.String.upperCase s))) := rfl
theorem lowerCase_shared :
    (libLookupAll (fnQ "lower-case")).map (fun f => f h e [sStr s]) =
      some (pure (sStr (Fn.String.lowerCase s))) := rfl
theorem encodeForUri_shared :
    (libLookupAll (fnQ "encode-for-uri")).map (fun f => f h e [sStr s]) =
      some (pure (sStr (Fn.String.encodeForUri s))) := rfl
theorem iriToUri_shared :
    (libLookupAll (fnQ "iri-to-uri")).map (fun f => f h e [sStr s]) =
      some (pure (sStr (Fn.String.iriToUri s))) := rfl
theorem escapeHtmlUri_shared :
    (libLookupAll (fnQ "escape-html-uri")).map (fun f => f h e [sStr s]) =
      some (pure (sStr (Fn.String.escapeHtmlUri s))) := rfl
/-- Under the codepoint default collation, `fn:contains`,
    `fn:substring-before` and `fn:substring-after` are the shared
    `Fn.String` functions. -/
theorem contains_shared (he : e.defaultCollation = codepointCollation) :
    (libLookupAll (fnQ "contains")).map (fun f => f h e [sStr s, sStr t]) =
      some (pure (sBool (Fn.String.contains s t))) := by
  cases e; simp only at he; subst he; rfl
theorem substringBefore_shared (he : e.defaultCollation = codepointCollation) :
    (libLookupAll (fnQ "substring-before")).map (fun f => f h e [sStr s, sStr t]) =
      some (pure (sStr (Fn.String.substringBefore s t))) := by
  cases e; simp only at he; subst he; rfl
theorem substringAfter_shared (he : e.defaultCollation = codepointCollation) :
    (libLookupAll (fnQ "substring-after")).map (fun f => f h e [sStr s, sStr t]) =
      some (pure (sStr (Fn.String.substringAfter s t))) := by
  cases e; simp only at he; subst he; rfl

/-- `fn:matches` is `Regex.isMatch` (the engine of SPARQL `REGEX`) on the
    compiled pattern. -/
theorem matches_shared (p f : String) :
    (libLookupAll (fnQ "matches")).map (fun g => g h e [sStr s, sStr p, sStr f]) =
      some (do let re ← compileRe4 p f; pure (sBool (Regex.isMatch re.r s))) := rfl

end FnShared

/-! ## Bridge: fn:resolve-uri and the RDF parsers' RFC 3986 resolver

`fn:resolve-uri` and the readers resolve with `L4Factoidal.Syntax.resolveIri`,
the resolver of the Turtle, TriG, RDF/XML and SPARQL parsers (RFC 3986 §5.2,
checked there against all 44 examples of RFC 3986 §5.4). -/

/-- For a relative reference against an absolute base without a fragment,
    the readers' resolution is the RDF parsers' resolution. -/
theorem resolveUri_eq_resolveIri (base href : String)
    (hb : isAbsIri base = true) (hh : isAbsIri href = false) :
    resolveUri base href = L4Factoidal.Syntax.resolveIri ((base.splitOn "#").headD base) href := by
  simp [resolveUri, hb, hh]

/-- An absolute reference is returned unchanged (F&O 4.0 §6.1). -/
theorem resolveUri_abs (base href : String) (hh : isAbsIri href = true) :
    resolveUri base href = href := by
  simp [resolveUri, hh]

/-! ## Bridge: date and time arithmetic is `L4Factoidal.Fn.DateTime`

The subtraction of two xs:dateTime values and the addition of a duration
to a date are the functions SPARQL's date arithmetic uses
(`Fn.DateTime.subtractValues`, `Fn.DateTime.plusDuration`). -/

theorem sub_dateTime_shared (tz : Int) (x y : XSD.DTValue) :
    arith0 tz .sub ⟨.b .dateTime, .x (.dt .dateTime x)⟩ ⟨.b .dateTime, .x (.dt .dateTime y)⟩ =
      .ok (mkDur .dayTimeDuration 0 (Fn.DateTime.subtractValues tz x y).seconds) := by
  rfl

theorem add_date_duration_shared (tz : Int) (x : XSD.DTValue) (d : XSD.DurValue) :
    arith0 tz .add ⟨.b .date, .x (.dt .date x)⟩ ⟨.b .dayTimeDuration, .x (.dur d)⟩ =
      .ok ⟨.b .date, .x (.dt .date (dtProject .date (Fn.DateTime.plusDuration x d)))⟩ := by
  rfl

end L4Factoidal.XPath4
