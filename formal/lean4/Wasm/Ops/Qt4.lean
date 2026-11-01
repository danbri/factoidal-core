/-
Wasm.Ops.Qt4 — XPath 4.0, XQuery 4.0 and XSLT 4.0 over the dispatch ABI.
Every decision is in `L4Factoidal.XPath4`, `L4Factoidal.XQuery4` and
`L4Factoidal.XSLT4` (the engines that `lake exe l4qt4` and `lake exe l4xslt4`
score against the QT4 CG test suites); this module reads strings and writes
JSON. The XPath 1.0 and XSLT 1.0 ops (`xpathEval`, `xsltTransform` in
`Wasm/Ops/Formats.lean`) are separate and unchanged.

  xpath4Eval(xml, expr)
    xml: the context document ("" for no context item); expr: XPath 4.0.
  xqueryEval(query, contextXml?)
    query: an XQuery 4.0 main module; contextXml: the context document
    ("" or absent for no context item).
    -> {"ok":true,"count":N,"items":[{"type":T,"value":S}…],
        "adaptive":S,"xml":S|null}
       `items`: each item of the result, with its type (`xs:integer`,
       `element()`, `map(*)`, ...) and its Serialization 4.0 adaptive
       serialization. `adaptive`: the whole sequence with the adaptive
       method. `xml`: the whole sequence with the xml method (no XML
       declaration), or null when that method cannot serialize it (for
       example a map: SENR0001).

  xslt4Transform(stylesheet, source)
    source: the source document ("" for no global context item).
    -> {"ok":true,"output":S,"method":M,"secondary":[{"href":H,"output":S}…],
        "messages":[S…]}
       `output`: the principal result serialized with the stylesheet's
       unnamed output definition (Serialization 4.0; XSLT 4.0 §26).
       `secondary`: the results of `xsl:result-document`, each serialized
       with its own output definition. `messages`: the `xsl:message` texts.

An error is the envelope of `Wasm/Ops/ErrorModel.lean` with code
`xml.failed`, and the member `qtError`:
    {"ok":false,"error":"err:XPST0003: …","code":"xml.failed","spec":…,
     "qtError":{"code":"XPST0003","namespace":"http://www.w3.org/2005/xqt-errors",
                "message":"…"}}
`qtError.code` is the error code the specification names (local part of the
error QName); `namespace` is the QName's namespace.

No I/O. The evaluators are pure functions (`XPath4.M` is `Except`): the
dynamic context holds only the documents given as arguments, no resources,
no collections and no file system. So:
  * `fn:doc`, `fn:doc-available` and `fn:collection` find no document other
    than the arguments (FODC0002 and the like);
  * `fn:unparsed-text` and `fn:json-doc` find no resource (FOUT1170);
  * `file:` functions (EXPath File) have no file system (`file:io-error`);
  * `import module` finds no library module (XQST0059);
  * `xsl:import`, `xsl:include` and `xsl:use-package` find no module
    (XTSE0165), because the stylesheet is the only module text given;
  * `fn:transform` uses the same pure inline stylesheet adapter as the QT4
    harness. It receives only the supplied documents/resources; there is no
    host fetch, stylesheet resolver, schema provider, or file system.
Execution is bounded by the evaluator's fuel (`qt4Fuel`): each nested
evaluation step uses one unit, and an exhausted fuel is the error FOER0000.
The fuel does not bound the stack: parts of the engines take one stack frame
per item (`tools/lean-tail-recursion-allow.txt`, PENDING
https://github.com/danbri/factoidal/issues/1110), and in the wasm module the
host's call stack ends before the fuel for large documents, deep recursion
and deeply nested expressions (expected failures in
`npm/factoidal/test/qt4.test.mjs`).
-/
import Wasm.Ops.Support
import Wasm.Ops.ErrorModel
import L4Factoidal.XPath4.Eval
import L4Factoidal.XPath4.Serialize
import L4Factoidal.XQuery4.Module
import L4Factoidal.XSLT4.Transform
import L4Factoidal.XSLT4.QtFnTransform

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XPath4

/-- The fuel of one evaluation: the depth of nested evaluation steps
(`XPath4.eval`'s first argument; XQuery `evalModule`). A deeper evaluation
fails with FOER0000. -/
def qt4Fuel : Nat := 4000

/-- The error envelope of a QT4 error. -/
def qtErrJson (op : String) (e : Err) : String :=
  -- a code already written as `Q{uri}local` (EXPath File and Binary)
  let (ns, code) : String × String :=
    if e.code.startsWith "Q{" then
      match (e.code.drop 2).toString.splitOn "}" with
      | [u, l] => (u, l)
      | _ => (nsERR, e.code)
    else if e.uri == "" then (nsERR, e.code)
    else if e.uri == "#none" then ("", e.code)
    else (e.uri, e.code)
  let shown := if ns == nsERR then "err:" ++ code else "Q{" ++ ns ++ "}" ++ code
  errCoded "xml.failed" s!"{op}: {shown}: {e.msg}"
    [("qtError", .object [("code", .string code), ("namespace", .string ns),
                          ("message", .string e.msg)])]

/-- The sequence type name of one item (XPath 4.0 §3.1). -/
def qt4ItemType (env : Env) : Item → String
  | .atom a => "xs:" ++ a.ty.name
  | .node n =>
    match (env.nrec n).kind with
    | .document => "document-node()"
    | .element => "element()"
    | .attribute => "attribute()"
    | .text => "text()"
    | .comment => "comment()"
    | .pi => "processing-instruction()"
    | .namespace => "namespace-node()"
  | .map _ => "map(*)"
  | .arr _ => "array(*)"
  | .fn _ => "function(*)"
  | .jnode .. => "jnode()"

/-- The success envelope of a sequence. -/
def qt4SeqJson (op : String) (env : Env) (s : Seq) : String :=
  match env.serializeWith { method := "adaptive" } s with
  | .error e => qtErrJson op e
  | .ok whole =>
    let item (i : Item) : Json :=
      .object [("type", .string (qt4ItemType env i)),
               ("value", .string ((env.serializeWith { method := "adaptive" } [i]).toOption.getD ""))]
    let xml : Json := match env.serializeWith { method := "xml" } s with
      | .ok t => .string t
      | .error _ => .null
    okWith [("count", .number (toString s.length)),
            ("items", .array (s.map item)),
            ("adaptive", .string whole),
            ("xml", xml)]

/-- The dynamic context of `xpath4Eval` and `xqueryEval`: the document as
context item, or no context item for `""`. -/
def qt4Env (xml : String) : Except Err Env :=
  if xml == "" then .ok {}
  else match Doc.ofString xml with
    | .ok d => .ok { docs := #[d], ctx := some [.node (NodeRef.mk' 0 0)], pos := 1, size := 1 }
    | .error m => .error { code := "FODC0002", msg := "the context document is not well-formed XML: " ++ m }

/-- Attach the existing pure fn:transform adapter without introducing resource
I/O or changing evaluator fuel. Function-item callbacks use the same fuel as
the public evaluation entry; full callback/fuel semantics are not proved here. -/
def qt4TransformEnv (env : Env) : Env :=
  { env with host := L4Factoidal.XSLT4.Qt.transformHost env (fun f args => apply qt4Fuel env f args) env.host }

/-- `xpath4Eval(xml, expr)`. -/
def xpath4Eval (xml expr : String) : String :=
  match qt4Env xml with
  | .error e => qtErrJson "xpath4Eval" e
  | .ok initial =>
    let env := qt4TransformEnv initial
    match parseXPath expr env.ns >>= eval qt4Fuel env with
    | .ok s => qt4SeqJson "xpath4Eval" env s
    | .error e => qtErrJson "xpath4Eval" e

/-- `xqueryEval(query, contextXml)`. -/
def xqueryEval (query contextXml : String) : String :=
  match qt4Env contextXml with
  | .error e => qtErrJson "xqueryEval" e
  | .ok initial =>
    let env := qt4TransformEnv initial
    match L4Factoidal.XQuery4.evalQuery query env qt4Fuel with
    | .ok s => qt4SeqJson "xqueryEval" env s
    | .error e => qtErrJson "xqueryEval" e

/-- The URI of the stylesheet module (its static base URI). The module
text is the only one given, so a relative `xsl:import` or `xsl:include`
resolves against it and finds nothing. -/
def xslt4StylesheetUri : String := "urn:x-factoidal:xslt4:stylesheet"

open L4Factoidal.XSLT4 in
/-- A result as the transformation delivers it: a document node, unless it
is one already (XSLT 4.0 §26.1). -/
def xslt4AsDocument (env : Env) (raw : Seq) : M Seq :=
  match raw with
  | [.node n] =>
    if (env.nrec n).kind == .document then pure raw
    else do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq raw) "")]
  | _ => do pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq raw) "")]

open L4Factoidal.XSLT4 in
/-- Compile, run and serialize. -/
def xslt4Run (stylesheet source : String) :
    M (String × String × List (String × String) × List String) := do
  let S ← compileStylesheet xslt4StylesheetUri [(xslt4StylesheetUri, stylesheet)]
  let (env, ctx) ← if source == "" then pure (({} : Env), (none : Option Item)) else
    match Doc.ofString source with
    | .ok d => pure ({ docs := #[d] }, some (.node (NodeRef.mk' 0 0)))
    | .error m => throw { code := "FODC0002", msg := "the source document is not well-formed XML: " ++ m }
  let r ← transform S { globalCtx := ctx, env }
  let props ← S.outputProps r.principalFormat.1 r.principalFormat.2
  let props := if props.any (·.1 == "method") then props
    else [("method", defaultMethod env r.raw)] ++ props
  let raw ← if r.principalFormat.1 != "" || !r.principalFormat.2.isEmpty then pure r.raw
    else match props.lookup "method" with
      | some "json" | some "adaptive" | some "csv" => pure r.raw
      | _ => xslt4AsDocument env r.raw
  let out ← serializeResult S env props raw
  let method := (props.lookup "method").getD "xml"
  let mut secondary : List (String × String) := []
  for (href, v, f, sp) in r.secondary do
    let p ← S.outputProps f sp
    let v ← if (sp.lookup "method").isSome || f != "" then pure v else xslt4AsDocument env v
    secondary := secondary ++ [(href, ← serializeResult S env p v)]
  pure (out, method, secondary, r.msgs)

/-- `xslt4Transform(stylesheet, source)`. -/
def xslt4Transform (stylesheet source : String) : String :=
  match xslt4Run stylesheet source with
  | .error e => qtErrJson "xslt4Transform" e
  | .ok (out, method, secondary, msgs) =>
    okWith [("output", .string out), ("method", .string method),
            ("secondary", .array (secondary.map fun (h, o) =>
              .object [("href", .string h), ("output", .string o)])),
            ("messages", .array (msgs.map Json.string))]

def qt4OpNames : List String := ["xpath4Eval", "xqueryEval", "xslt4Transform"]

/-- Serve one of `qt4OpNames`, or `none` for any other op. -/
def callQt4 (op : String) (args : List String) : Option String :=
  match op, args with
  | "xpath4Eval", [x, e] => some (xpath4Eval x e)
  | "xqueryEval", [q] => some (xqueryEval q "")
  | "xqueryEval", [q, c] => some (xqueryEval q c)
  | "xslt4Transform", [s, x] => some (xslt4Transform s x)
  | "xpath4Eval", xs => some (errJson s!"xpath4Eval expects 2 arguments, got {xs.length}")
  | "xqueryEval", xs => some (errJson s!"xqueryEval expects 1 or 2 arguments, got {xs.length}")
  | "xslt4Transform", xs => some (errJson s!"xslt4Transform expects 2 arguments, got {xs.length}")
  | _, _ => none

#guard (xpath4Eval "<r><a>1</a><a>2</a></r>" "sum(//a)") ==
  "{\"ok\":true,\"count\":1,\"items\":[{\"type\":\"xs:double\",\"value\":\"3\"}],\"adaptive\":\"3\",\"xml\":\"3\"}"
#guard (xpath4Eval "" "map { 'a': 1 }").endsWith "\"xml\":null}"
#guard (xpath4Eval "" "1 +").startsWith "{\"ok\":false,\"error\":\"xpath4Eval: err:XPST0003: "
#guard ((xpath4Eval "" "unparsed-text('file:///etc/passwd')").splitOn "\"code\":\"FOUT1170\"").length == 2
#guard ((xpath4Eval "" "Q{http://expath.org/ns/file}read-text('/etc/passwd')").splitOn
  "\"code\":\"io-error\",\"namespace\":\"http://expath.org/ns/file\"").length == 2
#guard ((xqueryEval "declare function local:f($n) { if ($n le 0) then 0 else 1 + local:f($n - 1) }; local:f(100000)" "").splitOn
  "\"code\":\"FOER0000\"").length == 2
#guard (xslt4Transform "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'><xsl:output method='text'/><xsl:template match='/'><xsl:value-of select='count(//a)'/></xsl:template></xsl:stylesheet>" "<r><a/><a/></r>") ==
  "{\"ok\":true,\"output\":\"2\",\"method\":\"text\",\"secondary\":[],\"messages\":[]}"
#guard ((xslt4Transform "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'><xsl:include href='b.xsl'/></xsl:stylesheet>" "<r/>").splitOn
  "\"code\":\"XTSE0165\"").length == 2

-- Public inline fn:transform reaches the same assertion toggle as the harness.
private def publicAssertSheet (test : String) : String :=
  "<xsl:stylesheet xmlns:xsl='http://www.w3.org/1999/XSL/Transform' version='3.0'>" ++
  "<xsl:template name='main'><out>ok<xsl:assert test='" ++ test ++
  "'/></out></xsl:template></xsl:stylesheet>"
private def publicAssertCall (test option : String) : String :=
  "transform(map{'stylesheet-text':\"" ++ publicAssertSheet test ++
  "\",'initial-template':QName('','main')" ++ option ++ "})?output ! string()"

#guard (xpath4Eval "" (publicAssertCall "false()" "")).endsWith "\"xml\":\"ok\"}"
#guard ((xqueryEval (publicAssertCall "false()" ",'enable-assertions':true()") "").splitOn
  "\"code\":\"XTMM9001\"").length == 2
#guard (xpath4Eval "" (publicAssertCall "1 idiv 0 = 1" ",'enable-assertions':false()")).endsWith "\"xml\":\"ok\"}"
#guard ((xpath4Eval "" "transform(map{'stylesheet-location':'https://example.org/not-fetched.xsl'})").splitOn
  "\"ok\":false").length == 2
#guard ((xqueryEval "element-to-map(<a>bad</a>, {'plan':{'a':{'layout':'simple','type':'boolean'}}})" "").splitOn
  "\"code\":\"FOJS0010\"").length == 2

end L4Wasm.Ops
