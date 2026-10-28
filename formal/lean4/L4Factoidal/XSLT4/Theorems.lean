/-
L4Factoidal.XSLT4.Theorems — what is proved and what is tested of the
XSLT 4.0 processor, bound to the code it states things about.

Proved (no `sorry`; `#print axioms` below):

* `parse_eq_parseXPath`: with no `xpath-default-namespace` and no named
  item types, an XPath
  expression of a stylesheet is the expression that `XPath4.parseXPath`
  reads, in the stylesheet's namespace bindings — XSLT adds nothing to
  the XPath 4.0 grammar (XSLT 4.0 §5.3);
* `materialize_item`: an existing item is
  delivered as itself — the result of `xsl:sequence` is the value of its
  expression, with the identity of its nodes (§10.4.1);
* `patMatch_ctx`, `patMatch_type`: the pattern `.` matches every item,
  and the type pattern `~T` matches exactly the items of type `T`
  (§6.3.3; XPath 4.0 §3.2 sequence type matching through
  `Env.itemMatches`);
* `stripDoc_noRules`: with no `xsl:strip-space`, whitespace stripping
  is the identity on source documents (§4.3);
* `findRule_empty`: with no template rules, no rule matches, so the
  built-in rules of the mode apply (§6.10);
* `defaultPriority_*`: the default priorities of the basic pattern
  forms are the values of §6.4.

Tested (`#guard`, checked at build time):

* the identity transform (`xsl:copy` with `xsl:apply-templates` over
  `@* | node()`, and `xsl:mode on-no-match="shallow-copy"`) gives a
  document deep-equal to its source (`Env.nodeDeepEq`);
* the serialized result of a transformation is well-formed XML under the
  project's XML parser (`L4Factoidal.XML.isWellFormed`);
* on XSLT 1.0 stylesheets, XSLT4 gives the same serialized result as
  the XSLT 1.0 engine `L4Factoidal.XSLT.transform` (the full comparison
  over the vendored XSLT 1.0 corpora is `l4xslt4 --xslt10 DIR`).

Open (https://github.com/danbri/factoidal/issues/1149): a theorem that
XSLT4 agrees with `L4Factoidal.XSLT` on the XSLT 1.0 fragment, and a
theorem that the identity transform is the identity on every document.
Both need a semantics of `run` over its fuel and state that this file
does not yet have.
-/
import L4Factoidal.XSLT4.Transform
import L4Factoidal.XSLT.Transform

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-! ## XPath expressions of a stylesheet -/

theorem expandTypes_nil (ns : List (String × String)) (f : Nat) (s : String) : expandTypes [] ns f s = s := by
  cases f <;> simp [expandTypes]

theorem parse_eq_parseXPath (c : SCx) (src : String) (e : Expr)
    (hns : c.xpathNs = "") (hty : c.types = []) (h : parseXPath src c.xpNs = .ok e) : c.parse src = .ok e := by
  simp [SCx.parse, hty, expandTypes_nil, h, hns]
  rfl

/-! ## Items are delivered as themselves -/

theorem materialize_item (env : Env) (id : Nat) (i : Item) : materialize env id (.item i) = .ok i := rfl

/-! ## Patterns -/

theorem patMatch_ctx (env : Env) (f : Nat) (it : Item) : patMatch env (f + 1) .ctx it = .ok true := by
  simp [patMatch]; rfl

theorem patMatch_type (env : Env) (f : Nat) (ty : IType) (it : Item) :
    patMatch env (f + 1) (.instOf .ctx ty) it = .ok (env.itemMatches it ty) := by
  simp [patMatch]; rfl

theorem defaultPriority_name (q : QN) : defaultPriority (.step .child (.name (.name q)) []) = 0 := rfl
theorem defaultPriority_attrName (q : QN) : defaultPriority (.step .attribute (.name (.name q)) []) = 0 := rfl
theorem defaultPriority_nsWild (u : String) : defaultPriority (.step .child (.name (.ns u)) []) = -0.25 := rfl
theorem defaultPriority_wild : defaultPriority (.step .child (.name .any) []) = -0.5 := rfl
theorem defaultPriority_node : defaultPriority (.step .child (.kind .anyNode) []) = -0.5 := rfl
theorem defaultPriority_root : defaultPriority .root = -0.5 := rfl
theorem defaultPriority_dot : defaultPriority .ctx = -1 := rfl

/-! ## Whitespace stripping and rule selection -/

theorem stripDoc_noRules (S : Sheet) (d : Doc) (h : S.space = []) : stripDoc S d = d := by
  simp [stripDoc, h]

#print axioms parse_eq_parseXPath
#print axioms patMatch_type
#print axioms stripDoc_noRules

theorem findRule_empty (S : Sheet) (env : Env) (mode : String) (it : Item) (ok : Tmpl → Bool)
    (h : S.templates = #[]) : findRule S env mode it ok = .ok none := by
  simp [findRule, h]
  rfl

/-! ## Tested properties (`#guard`) -/

/-- Compile and run a stylesheet text on a source text; the serialized
    principal result. -/
def runText (style src : String) : Except String String :=
  match compileStylesheet "file:///t.xsl" [("file:///t.xsl", style)] with
  | .error e => .error ("compile " ++ e.code ++ " " ++ e.msg)
  | .ok S =>
    match Doc.ofString src "file:///s.xml" with
    | .error e => .error e
    | .ok d =>
      let env : Env := { docs := #[d] }
      match transform S { globalCtx := some (.node (NodeRef.mk' 0 0)), env } with
      | .error e => .error ("run " ++ e.code ++ " " ++ e.msg)
      | .ok r =>
        let v : M Seq := match r.raw with
          | [.node n] => if (env.nrec n).kind == .document then pure r.raw
              else do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq r.raw) "")]
          | _ => do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq r.raw) "")]
        match v with
        | .error e => .error e.code
        | .ok v =>
          match serializeResult S env [("omit-xml-declaration", "yes")] v with
          | .ok t => .ok t
          | .error e => .error ("serialize " ++ e.code)

/-- Is the result of transforming `src` deep-equal to `src`? -/
def resultIsSource (style src : String) : Bool :=
  match compileStylesheet "file:///t.xsl" [("file:///t.xsl", style)], Doc.ofString src "file:///s.xml" with
  | .ok S, .ok d =>
    let env : Env := { docs := #[d] }
    match transform S { globalCtx := some (.node (NodeRef.mk' 0 0)), env } with
    | .ok r =>
      -- the delivered result is the raw result in a document node: its
      -- children against the children of the source document
      let kidsOf (m : NodeRef) := ((env.nrec m).children.toList.map (m.at ·))
      let a : List NodeRef := match r.raw with
        | [.node n] => if (env.nrec n).kind == .document then kidsOf n else [n]
        | s => s.filterMap (fun i => match i with | .node n => some n | _ => none)
      let b := kidsOf (NodeRef.mk' 0 0)
      a.length == b.length && (a.zip b).all (fun (x, y) => env.nodeDeepEq 100000 x y)
    | .error _ => false
  | _, _ => false

def identityXsl : String :=
  "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
  "<xsl:template match='@*|node()'><xsl:copy><xsl:apply-templates select='@*|node()'/></xsl:copy></xsl:template>" ++
  "</xsl:stylesheet>"

def shallowCopyXsl : String :=
  "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
  "<xsl:mode on-no-match='shallow-copy'/></xsl:stylesheet>"

def sampleDocs : List String :=
  ["<a/>", "<a x='1' y='2'><b>text</b><c/><!--note--><?pi data?>tail</a>",
   "<p:r xmlns:p='urn:p' xmlns='urn:d'><e p:a='v'>x<f/>y</e></p:r>",
   "<doc><list><item n='1'>one</item><item n='2'>two</item></list></doc>"]

#guard sampleDocs.all (resultIsSource identityXsl)
#guard sampleDocs.all (resultIsSource shallowCopyXsl)

/-- The serialized result parses as well-formed XML. -/
def wellFormedResult (style src : String) : Bool :=
  match runText style src with
  | .ok t => L4Factoidal.XML.isWellFormed t
  | .error _ => false

def sampleStyles : List String :=
  [identityXsl,
   "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
   "<xsl:template match='/'><out><xsl:for-each select='//*'><n name='{name()}'><xsl:value-of select='count(*)'/></n></xsl:for-each></out></xsl:template></xsl:stylesheet>",
   "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
   "<xsl:template match='/'><r><xsl:attribute name='a'>&lt;&amp;&quot;</xsl:attribute><xsl:text>&lt;&amp;]]&gt;</xsl:text><xsl:comment>c--d</xsl:comment></r></xsl:template></xsl:stylesheet>"]

#guard sampleStyles.all (fun st => sampleDocs.all (wellFormedResult st))

/-! ## Agreement with the XSLT 1.0 engine on XSLT 1.0 stylesheets -/

/-- The result of the XSLT 1.0 engine, without its XML declaration. -/
def run10 (style src : String) : Option String :=
  match L4Factoidal.XML.parseXML style, L4Factoidal.XML.parseXML src with
  | .ok s1, .ok s2 =>
    match L4Factoidal.XSLT.transform s1 s2 with
    | .produced t =>
      let t := t.trimAscii.toString
      if t.startsWith "<?xml" then
        match t.splitOn "?>" with
        | _ :: rest => some (String.intercalate "?>" rest).trimAscii.toString
        | [] => some t
      else some t
    | .refused _ => none
  | _, _ => none

def agrees (style src : String) : Bool :=
  match run10 style src, runText style src with
  | some a, .ok b => a == b.trimAscii.toString
  | _, _ => false

def styles10 : List String :=
  ["<xsl:stylesheet version='1.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
   "<xsl:template match='/'><out><xsl:apply-templates/></out></xsl:template>" ++
   "<xsl:template match='item'><i><xsl:value-of select='@n'/>:<xsl:value-of select='.'/></i></xsl:template>" ++
   "</xsl:stylesheet>",
   "<xsl:stylesheet version='1.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
   "<xsl:template match='/'><out><xsl:for-each select='//item'><xsl:sort select='.' order='descending'/>" ++
   "<xsl:if test='position() &gt; 0'><x><xsl:value-of select='.'/></x></xsl:if></xsl:for-each></out></xsl:template>" ++
   "</xsl:stylesheet>",
   "<xsl:stylesheet version='1.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
   "<xsl:variable name='v' select='count(//item)'/>" ++
   "<xsl:template match='/'><out total='{$v}'><xsl:call-template name='t'><xsl:with-param name='p' select='2'/></xsl:call-template></out></xsl:template>" ++
   "<xsl:template name='t'><xsl:param name='p'/><xsl:choose><xsl:when test='$p = 2'>two</xsl:when><xsl:otherwise>other</xsl:otherwise></xsl:choose></xsl:template>" ++
   "</xsl:stylesheet>"]

#guard styles10.all (fun st => agrees st "<doc><list><item n='1'>one</item><item n='2'>two</item></list></doc>")

end L4Factoidal.XSLT4
