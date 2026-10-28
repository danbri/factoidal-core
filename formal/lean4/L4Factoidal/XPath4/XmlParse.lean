/-
L4Factoidal.XPath4.XmlParse — documents built at run time: `fn:parse-xml`,
`fn:parse-xml-fragment` (F&O 4.0 §14.6), and the text resources of the
dynamic context: `fn:unparsed-text`, `fn:unparsed-text-lines`,
`fn:unparsed-text-available` (§14.7), `fn:doc` and `fn:doc-available` for
a resource the caller read in advance, and `fn:base-uri` with `xml:base`.

Spec: F&O 4.0 editor's draft, qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c, `function-catalog.xml`.

The parser is the project's XML 1.0 parser (`L4Factoidal.XML.Parser`, the
well-formedness decision) with namespace well-formedness
(`L4Factoidal.XML.Namespaces`) and DTD validity (`L4Factoidal.XML.Validity`)
on top. A new document is not added to the dynamic context (which is
read-only): its nodes carry it (`NodeRef.rt`), and its document number is
derived from the input, so the same input gives the same node (the function
is nondeterministic, so this is allowed).

The evaluator does no I/O. An external DTD or entity, and the text of
`fn:unparsed-text`, come from `Env.resources`, which the caller fills.

Options of `fn:parse-xml`: `base-uri`, `dtd-validation`, `strip-space`
(`all`, `none`, `conditional` = `none`), `trust-external`, `xinclude`
(`true` is `FODC0013`: there is no XInclude processor), `xsd-validation`
(anything but `skip` is `FODC0009`: not schema-aware), `use-xsi-schema-location`,
`line-numbers` (ignored, as the spec allows).
-/
import L4Factoidal.XPath4.Lib
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.Namespaces
import L4Factoidal.XML.Validity

namespace L4Factoidal.XPath4

open L4Factoidal.XML

/-! ## Runtime documents -/

/-- The document number of a document built at run time from `src`
    (`tag` keeps the functions apart). Outside the range of the caller's
    documents. -/
def runtimeDocId (tag src : String) : Nat :=
  (2 : Nat) ^ 40 + (hash (tag ++ "\x00" ++ src)).toNat

/-- The document node of a runtime document. -/
def Doc.rootItem (d : Doc) (id : Nat) : Item := .node { doc := id, idx := 0, rt := some d }

/-! ## Resources -/

/-- The text of a resource, by the reference as written or resolved
    against the static base URI. -/
def Env.resource (e : Env) (href : String) : Option String :=
  match e.resources.lookup href with
  | some t => some t
  | none => e.resources.lookup (resolveUri e.baseUri href)

/-! ## Whitespace stripping (`strip-space: all`) -/

def isXmlWs (s : String) : Bool := s.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')

def stripWs : Nat → Bool → Node → Node
  | 0, _, n => n
  | f + 1, keep, n =>
    match n with
    | .element tag attrs kids =>
      let keep := match attrs.find? (fun a => a.name == "xml:space") with
        | some a => if a.value == "preserve" then true else if a.value == "default" then false else keep
        | none => keep
      let kids := kids.filter (fun k => match k with
        | .text t => keep || !isXmlWs t
        | _ => true)
      .element tag attrs (kids.map (stripWs f keep))
    | other => other

/-- Remove the whitespace-only text that DTD validation marks as
    ignorable: the text children of an element whose declared content is
    element-only (`[47] children`) or `EMPTY` (XML 1.0 §2.10). -/
def stripIgnorable (dt : Doctype) : Nat → Node → Node
  | 0, n => n
  | f + 1, n =>
    match n with
    | .element tag attrs kids =>
      let elemOnly := match elementDeclOf dt.elementDecls tag with
        | some ed => match parseContentSpecText ed.spec with
          | some (.children _) | some .empty => true
          | _ => false
        | none => false
      let kids := if elemOnly then kids.filter (fun k => match k with
          | .text t => !isXmlWs t
          | _ => true) else kids
      .element tag attrs (kids.map (stripIgnorable dt f))
    | other => other

/-! ## Options -/

def optLookup (opts : Seq) (key : String) : Option Seq :=
  match opts with
  | [.map kvs] => mapGet kvs (Atomic.ofStr key)
  | _ => none

def optBool (opts : Seq) (key : String) (dflt : Bool) : M Bool :=
  match optLookup opts key with
  | none => pure dflt
  | some [.atom ⟨_, .bool b⟩] => pure b
  | some _ => err "XPTY0004" ("option " ++ key ++ " must be an xs:boolean")

def bytesOfAtomic (a : Atomic) : Option ByteArray :=
  match a.v with
  | .x (.bin _ bs) => some (ByteArray.mk (bs.map (fun b => b.toUInt8)).toArray)
  | _ => none

/-- Is a declared external general entity referenced (`&name;`) in `src`? -/
def refsExternalEntity (d : Document) (src : String) : Bool :=
  match d.doctype with
  | none => false
  | some dt => dt.entities.defs.any (fun (n, ed) => ed.external && (src.splitOn ("&" ++ n ++ ";")).length > 1)

/-- The option parameter conventions (F&O 4.0 §1.7.4): an option whose
    name is not defined, and is not a QName in a namespace, is a type
    error. -/
def checkOptionKeys (opts : Seq) (known : List String) : M Unit := do
  match opts with
  | [.map kvs] =>
    for (k, _) in kvs do
      match k.v with
      | .qn q => if q.uri == "" then err "XPTY0004" ("unknown option " ++ q.loc)
      | _ => if !known.contains k.str then err "XPTY0004" ("unknown option " ++ k.str)
  | _ => pure ()

def parseXmlOptionNames : List String := ["base-uri", "dtd-validation", "strip-space", "trust-external",
  "xinclude", "xsd-validation", "use-xsi-schema-location", "line-numbers", "stable"]

/-! ## fn:parse-xml -/

structure ParseOpts where
  baseUri : String
  dtdValidation : Bool := false
  stripAll : Bool := false
  trustExternal : Bool := false
  /-- `xsd-validation`: `skip`, or a mode for `SchemaHook.validate`. -/
  xsd : String := "skip"

def parseOpts (e : Env) (opts : Seq) : M ParseOpts := do
  checkOptionKeys opts parseXmlOptionNames
  let base := match optLookup opts "base-uri" with
    | some s => strOf s
    | none => e.baseUri
  let dtd ← optBool opts "dtd-validation" false
  let strip := optionStr opts "strip-space" "none"
  if !["all", "none", "conditional"].contains strip then
    err "XPTY0004" ("strip-space must be all, none or conditional, not " ++ strip)
  let trust ← optBool opts "trust-external" false
  if ← optBool opts "xinclude" false then
    err "FODC0013" "no XInclude processor is available"
  let xsd := optionStr opts "xsd-validation" "skip"
  pure { baseUri := base, dtdValidation := dtd, stripAll := strip == "all", trustExternal := trust, xsd }

/-- The document of `kids`, validated when `xsd-validation` asks for it. -/
def docOfKids (e : Env) (o : ParseOpts) (kids : List Node) (uri : String) : M Doc :=
  if o.xsd == "skip" then pure (Doc.ofNodes kids uri)
  else match e.schema.validate, kids.find? (fun k => match k with | .element .. => true | _ => false) with
    | some f, some root => match f o.xsd root uri with
      | .ok d => pure d
      | .error x => throw x
    | _, _ => err "FODC0009" "no schema to validate with"

/-- The children of a parsed document after the whitespace rules of the
    options (`strip-space`, and ignorable whitespace under DTD
    validation) and xml:id processing. -/
def docKids (o : ParseOpts) (d : Document) : List Node :=
  let ks := if o.stripAll then d.children.map (stripWs 100000 false) else d.children
  let ks := match d.doctype with
    | some dt => if o.dtdValidation then ks.map (stripIgnorable dt 100000) else ks
    | none => ks
  ks.map (normXmlId 100000)

/-- A system identifier relative to the reference of the document that
    names it (`../docs/a.xml` and `b.dtd` give `../docs/b.dtd`). -/
def siblingRef (docHref sys : String) : String :=
  if sys.startsWith "/" || (sys.splitOn ":").length > 1 then sys else
  match (docHref.splitOn "/").dropLast with
  | [] => sys
  | ds => String.intercalate "/" ds ++ "/" ++ sys

/-- Parse a whole document (string or bytes) under the options;
    `docHref` is the reference the document was read from, against which
    its external DTD subset and external entities are resolved. -/
def parseDocument (e : Env) (o : ParseOpts) (src : Atomic) (docHref : String := "") : M Document := do
  let resolve : Resolver := if o.trustExternal then
      (fun h => match e.resource h with
        | some t => some t
        | none => if docHref == "" then none else e.resource (siblingRef docHref h))
    else (fun _ => none)
  let run (r : Resolver) : Except XmlError Document :=
    match bytesOfAtomic src with
    | some bs => parseXMLBytesWith r bs
    | none => parseDecodedXMLWith r src.str
  match run resolve with
  | .error ex =>
    -- an unread external resource: FODC0016 when trust-external is false
    if !o.trustExternal && (run (fun _ => some "")).isOk then
      err "FODC0016" "the document needs an external resource and trust-external is false"
    else err "FODC0006" ("not well-formed: " ++ ex.message)
  | .ok d =>
    if !d.namespaceWellFormed then err "FODC0006" "not namespace-well-formed"
    if !o.trustExternal then
      if (d.doctype.bind (·.systemId)).isSome || refsExternalEntity d src.str then
        err "FODC0016" "the document needs an external resource and trust-external is false"
    if o.dtdValidation then
      if d.doctype.isNone then err "FODC0007" "DTD validation requested, and there is no DOCTYPE"
      if !(validate d).isEmpty then err "FODC0007" "the document is not valid against its DTD"
    pure d

def parseXmlFn : LibFn := fun _ e a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some src =>
    let o ← parseOpts e (argN a 1)
    let d ← parseDocument e o src
    let kids := docKids o d
    let doc := { (← docOfKids e o kids "") with baseUri := o.baseUri }
    pure [doc.rootItem (runtimeDocId "parse-xml" src.str)]

/-! ## fn:parse-xml-fragment -/

/-- Split off a text declaration (XML 1.0 §4.3.1 `[77] TextDecl`): it
    must have an encoding declaration and no standalone declaration. -/
def splitTextDecl (s : String) : M String := do
  if !s.startsWith "<?xml" then return s
  let rest := (s.drop 5).toString
  if !(rest.startsWith " " || rest.startsWith "\t" || rest.startsWith "\n" || rest.startsWith "\r" || rest.startsWith "?") then
    return s
  match rest.splitOn "?>" with
  | decl :: _ :: _ =>
    if (decl.splitOn "encoding").length < 2 then err "FODC0006" "a text declaration needs an encoding declaration"
    if (decl.splitOn "standalone").length > 1 then err "FODC0006" "a text declaration has no standalone declaration"
    pure (rest.drop (decl.length + 2)).toString
  | _ => err "FODC0006" "unterminated text declaration"

def parseFragmentFn : LibFn := fun _ e a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some src =>
    let o ← parseOpts e (argN a 1)
    let text ← match bytesOfAtomic src with
      | some bs => match decodeXmlBytesE bs with
        | .ok t => pure t
        | .error ex => err "FODC0006" ex.message
      | none => pure src.str
    let text := if text.startsWith "\uFEFF" then (text.drop 1).toString else text
    let body ← splitTextDecl text
    let resolve : Resolver := if o.trustExternal then (fun h => e.resource h) else (fun _ => none)
    match parseDecodedXMLWith resolve ("<w>" ++ body ++ "</w>") with
    | .error ex => err "FODC0006" ("not a well-formed external entity: " ++ ex.message)
    | .ok d =>
      if !d.namespaceWellFormed then err "FODC0006" "not namespace-well-formed"
      let kids := match d.root with
        | .element _ _ ks => ks
        | _ => []
      let kids := if o.stripAll then (kids.filter (fun k => match k with
          | .text t => !isXmlWs t | _ => true)).map (stripWs 100000 false) else kids
      let doc := { (← docOfKids e o kids "") with baseUri := o.baseUri }
      pure [doc.rootItem (runtimeDocId "parse-xml-fragment" src.str)]

/-! ## Text resources -/

def checkEncoding (enc : Seq) : M Unit := do
  match optAtom enc with
  | none => pure ()
  | some x =>
    let n := x.str.toLower
    if !["utf-8", "utf8", "utf-16", "us-ascii", "ascii", "iso-8859-1", "latin1", "utf-16le", "utf-16be"].contains n then
      err "FOUT1190" ("unsupported encoding " ++ x.str)

def Env.resourceBin (e : Env) (href : String) : Option ByteArray :=
  match e.resourceBytes.lookup href with
  | some t => some t
  | none => e.resourceBytes.lookup (resolveUri e.baseUri href)

def supportedEncodings : List String :=
  ["UTF-8", "UTF8", "UTF-16", "UTF-16LE", "UTF-16BE", "US-ASCII", "ASCII", "ISO-8859-1", "LATIN1"]

/-- `bin:infer-encoding` (EXPath Binary 4.0): the effective encoding and
    the offset after a byte order mark. -/
def inferEncoding (bs : ByteArray) (cand : Option String) : String × Nat :=
  let b (i : Nat) : Nat := if i < bs.size then (bs.get! i).toNat else 256
  let e := cand.map String.toUpper
  if (e.isNone || e == some "UTF-8") && b 0 == 0xEF && b 1 == 0xBB && b 2 == 0xBF then ("UTF-8", 3)
  else if (e.isNone || e == some "UTF-16" || e == some "UTF-16LE") && b 0 == 0xFF && b 1 == 0xFE then ("UTF-16LE", 2)
  else if (e.isNone || e == some "UTF-16" || e == some "UTF-16BE") && b 0 == 0xFE && b 1 == 0xFF then ("UTF-16BE", 2)
  else if e == some "UTF-16" then ("UTF-16BE", 0)
  else match e with
    | some x => (x, 0)
    | none => ("UTF-8", 0)

def decodeUtf16 (bs : ByteArray) (off : Nat) (be : Bool) : Option String := Id.run do
  if (bs.size - off) % 2 != 0 then return none
  let mut out : String := ""
  let mut hi : Option Nat := none
  let n := (bs.size - off) / 2
  for k in [0:n] do
    let i := off + 2 * k
    let a := (bs.get! i).toNat
    let c := (bs.get! (i + 1)).toNat
    let u := if be then a * 256 + c else c * 256 + a
    match hi with
    | some h =>
      if 0xDC00 ≤ u && u ≤ 0xDFFF then
        out := out.push (Char.ofNat (0x10000 + (h - 0xD800) * 0x400 + (u - 0xDC00)))
        hi := none
      else return none
    | none =>
      if 0xD800 ≤ u && u ≤ 0xDBFF then hi := some u
      else if 0xDC00 ≤ u && u ≤ 0xDFFF then return none
      else out := out.push (Char.ofNat u)
  if hi.isSome then return none
  return some out

/-- UTF-8 decoding in which each maximal invalid subsequence becomes
    U+FFFD (the `fallback` option). -/
def utf8Lossy (bs : ByteArray) : String := Id.run do
  let mut out : String := ""
  let mut i := 0
  let n := bs.size
  for _ in [0:n] do
    if i ≥ n then break
    let b0 := (bs.get! i).toNat
    let len := if b0 < 0x80 then 1 else if b0 &&& 0xE0 == 0xC0 then 2
      else if b0 &&& 0xF0 == 0xE0 then 3 else if b0 &&& 0xF8 == 0xF0 then 4 else 0
    if len == 0 || i + len > n then
      out := out.push '\uFFFD'; i := i + 1
    else
      match String.fromUTF8? (bs.extract i (i + len)) with
      | some t => out := out ++ t; i := i + len
      | none => out := out.push '\uFFFD'; i := i + 1
  return out

/-- Decode the octets of a resource (F&O 4.0 §17.1.5): FOUT1190 for an
    encoding that is not supported or octets that it cannot decode, when
    an encoding was given; FOUT1200 when none was given and the inferred
    one cannot decode them. With `fallback`, a character that cannot be
    decoded or is not permitted becomes U+FFFD. -/
def decodeResource (bs : ByteArray) (cand : Option String) (fallback : Bool) : M String := do
  if let some c := cand then
    if !supportedEncodings.contains c.toUpper then err "FOUT1190" ("unsupported encoding " ++ c)
  let (enc, off) := inferEncoding bs cand
  let body := bs.extract off bs.size
  let fail {α} : M α := if cand.isNone then err "FOUT1200" "cannot infer the encoding of the resource"
    else err "FOUT1190" ("the resource cannot be decoded as " ++ enc)
  let text ← match enc.toUpper with
    | "UTF-8" | "UTF8" =>
      match String.fromUTF8? body with
      | some t => pure t
      | none => if fallback then pure (utf8Lossy body) else fail
    | "UTF-16LE" => match decodeUtf16 bs off false with | some t => pure t | none => fail
    | "UTF-16BE" | "UTF-16" => match decodeUtf16 bs off true with | some t => pure t | none => fail
    | "US-ASCII" | "ASCII" =>
      if body.toList.all (· < 128) then pure (String.ofList (body.toList.map (fun x => Char.ofNat x.toNat)))
      else if fallback then pure (String.ofList (body.toList.map (fun x => if x < 128 then Char.ofNat x.toNat else '\uFFFD')))
      else fail
    | _ => pure (String.ofList (body.toList.map (fun x => Char.ofNat x.toNat)))
  if text.toList.any (fun c => !isXmlCp c.toNat) then
    if fallback then pure (String.ofList (text.toList.map (fun c => if isXmlCp c.toNat then c else '\uFFFD')))
    else err "FOUT1190" "the resource contains a character that is not allowed in XML"
  else pure text

def textResourceWith (e : Env) (href : String) (cand : Option String) (fallback : Bool) : M String := do
  if (href.splitOn "#").length > 1 then err "FOUT1170" "a fragment identifier is not allowed"
  match e.resourceBin href with
  | some bs =>
    -- with no $encoding, external encoding information is used first
    let ext := (e.resourceEncodings.lookup href).orElse (fun _ => e.resourceEncodings.lookup (resolveUri e.baseUri href))
    decodeResource bs (cand.orElse (fun _ => ext)) fallback
  | none =>
  match e.resource href with
  | some t =>
    if let some c := cand then
      if !supportedEncodings.contains c.toUpper then err "FOUT1190" ("unsupported encoding " ++ c)
    let bad : Bool := t.toList.any (fun c => !isXmlCp c.toNat)
    if bad && !fallback then err "FOUT1190" "the resource contains a character that is not allowed in XML"
    let t' : String := if t.startsWith "\uFEFF" then (t.drop 1).toString else t
    pure t'
  | none => err "FOUT1170" ("resource not available: " ++ href)

def textResource (e : Env) (href : String) : M String := textResourceWith e href none false

/-- The options of `fn:unparsed-text` and its relatives: a string (the
    encoding) or a map (`encoding`, `normalize-newlines`, `fallback`;
    `fn:unparsed-text-lines` has no `normalize-newlines`). Another key is
    XPTY0004 (the option parameter conventions, F&O 4.0 §1.7.4). -/
def unparsedOpts (e : Env) (o : Seq)
    (keys : List String := ["encoding", "normalize-newlines", "fallback"]) :
    M (Option String × Bool × Bool) := do
  match o with
  | [] => pure (none, false, false)
  | [.map _] =>
    checkOptionKeys o keys
    let enc ← match optLookup o "encoding" with
      | none | some [] => pure none
      | some v => match ← e.coerce (parseTy "xs:string") v "encoding" with
        | [.atom x] => pure (some x.str)
        | _ => err "XPTY0004" "encoding must be xs:string"
    let nl ← optBool o "normalize-newlines" false
    let fb ← optBool o "fallback" false
    pure (enc, nl, fb)
  | [.atom x] => pure (some x.str, false, false)
  | _ => err "XPTY0004" "the options must be a string or a map"

def readUnparsed (e : Env) (href : String) (o : Seq)
    (keys : List String := ["encoding", "normalize-newlines", "fallback"]) : M String := do
  let (enc, nl, fb) ← unparsedOpts e o keys
  let t ← textResourceWith e href enc fb
  pure (if nl then (t.replace "\r\n" "\n").replace "\r" "\n" else t)

/-- Split text into lines (`\n`, `\r\n`, `\r`); a final empty line is
    dropped. -/
def textLines (t : String) : List String :=
  let t := (t.replace "\r\n" "\n").replace "\r" "\n"
  let ls := t.splitOn "\n"
  if ls.getLast? == some "" then ls.dropLast else ls

/-- `fn:doc` for a document the caller registered, or a resource it read
    in advance (parsed with the `fn:parse-xml` options). -/
def docFn (e : Env) (a : List Seq) : M Seq := do
  match optAtom (argN a 0) with
  | none => pure []
  | some u =>
    if (u.str.splitOn "#").length > 1 then err "FODC0005" "a fragment identifier is not allowed"
    if !iriRefOk u.str then err "FODC0005" ("not a valid URI reference: " ++ u.str)
    let o ← parseOpts e (argN a 1)
    -- a relative reference is resolved against the static base URI
    match e.docUris.lookup u.str |>.orElse (fun _ => e.docUris.lookup (resolveUri e.baseUri u.str)) with
    | some d =>
      if o.dtdValidation then err "FODC0007" "DTD validation of a registered document" else
      pure [.node (NodeRef.mk' d 0)]
    | none =>
      match e.resource u.str with
      | some t =>
        let d ← match parseDocument e o (Atomic.ofStr t) u.str with
          | .ok d => pure d
          | .error x => if x.code == "FODC0006" then err "FODC0002" x.msg else throw x
        let uri := resolveUri e.baseUri u.str
        let kids := docKids o d
        -- documents read with different options are different documents
        let oSig := toString o.stripAll ++ toString o.dtdValidation ++ toString o.trustExternal ++ o.xsd
        -- fn:doc: a document that cannot be validated is not available (FODC0002)
        let doc ← match docOfKids e o kids uri with
          | .ok d => pure d
          | .error x => err "FODC0002" x.msg
        pure [doc.rootItem (runtimeDocId "doc" (uri ++ "|" ++ oSig))]
      | none => err "FODC0002" ("document not available: " ++ u.str)

def xmlParseTable : List (String × LibFn) := [
  ent "parse-xml" parseXmlFn,
  ent "parse-xml-fragment" parseFragmentFn,
  ent "unparsed-text" (fun _ e a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some h => pure (sStr (← readUnparsed e h.str (argN a 1)))),
  ent "unparsed-text-lines" (fun _ e a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some h => pure ((textLines (← readUnparsed e h.str (argN a 1) ["encoding", "fallback"])).map (fun l => .atom (Atomic.ofStr l)))),
  ent "unparsed-text-available" (fun _ e a => do
    match optAtom (argN a 0) with
    | none => pure (sBool false)
    | some h =>
      let _ ← unparsedOpts e (argN a 1)
      pure (sBool (match readUnparsed e h.str (argN a 1) with | .ok _ => true | .error _ => false))),
  ent "doc" (fun _ e a => docFn e a),
  ent "doc-available" (fun _ e a => do
    match optAtom (argN a 0) with
    | none => pure (sBool false)
    | some _ =>
      -- a type error in the options is raised, not turned into false
      match parseOpts e (argN a 1) with
      | .error x => if x.code == "XPTY0004" then throw x
      | .ok _ => pure ()
      pure (sBool (match docFn e a with | .ok _ => true | .error _ => false))),
  ent "base-uri" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | none => pure []
    | some n =>
      let d := e.doc n
      let docBase := if d.baseUri != "" then d.baseUri else d.uri
      -- the xml:base attributes on the element ancestors, outermost first
      let chain := ((n :: e.ancestors n).filter (fun m => (e.nrec m).kind == .element)).reverse
      let bases := chain.filterMap (fun m =>
        (e.nrec m).attrs.toList.findSome? (fun x =>
          let r := e.nrec (m.at x)
          if r.name.uri == nsXML && r.name.loc == "base" then some r.value else none))
      let b := bases.foldl resolveUri docBase
      let k := (e.nrec n).kind
      if k == .text || k == .comment || k == .pi || k == .attribute then
        match (e.nrec n).parent with
        | none => pure []
        | some _ => pure (if b == "" then [] else single (Atomic.ofUri b))
      else if k == .namespace then pure []
      else pure (if b == "" then [] else single (Atomic.ofUri b)))
]

end L4Factoidal.XPath4
