/-
L4Factoidal.XPath4.Serialize — XSLT and XQuery Serialization 4.0 and
`fn:serialize` (F&O 4.0 §17.2.3).

Spec: XSLT and XQuery Serialization 4.0, editor's draft
(https://qt4cg.org/specifications/xslt-xquery-serialization-40/Overview.html,
read 2026-10-28): §2 sequence normalization, §3 serialization parameters
(and §3.1 the parameter document), §5 the XML output method, §6 XHTML,
§7 HTML, §8 text, §9 JSON (with JSON Lines and `canonical`, RFC 8785),
§10 CSV, §11 adaptive, §12 character maps.

The serializer is a function from an XDM sequence and a parameter record
to a string: `fn:serialize` skips the encoding phase (F&O 4.0 §17.2.3),
so `encoding` only decides which characters are written as character
references (XML, HTML) or `\u` escapes (JSON).

Implementation-defined choices (Serialization 4.0 §13): the indent unit
is two spaces; the line ending is U+000A; an anonymous function item is
written `(anonymous-function)#N` by the adaptive method; the parameter
defaults of the element form are those of the map form; the supported
encodings are UTF-8, UTF-16, UTF-32, US-ASCII and ISO-8859-1.

`normalization-form` (NFC, NFD, NFKC, NFKD by `XPath4.Unicode`) is
applied to the text and attribute values before escaping; characters a
character map replaces are not normalized.

Not implemented: `byte-order-mark` (the result is a string), the `record` rule of the JSON method (the item model has no
record annotation).
-/
import L4Factoidal.XPath4.Json
import L4Factoidal.XPath4.Unicode

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

def nsOUTPUT : String := "http://www.w3.org/2010/xslt-xquery-serialization"
def nsXHTML : String := "http://www.w3.org/1999/xhtml"

/-! ## Parameters (§3) -/

structure SerParams where
  method : String := "xml"
  indent : Bool := false
  omitDecl : Bool := true
  standalone : Option Bool := none
  version : Option String := none
  htmlVersion : Option String := none
  doctypeSystem : Option String := none
  doctypePublic : Option String := none
  cdata : List QN := []
  suppress : List QN := []
  itemSep : Option String := none
  charMap : List (Char × String) := []
  escapeSolidus : Bool := true
  allowDup : Bool := false
  jsonNodeMethod : String := "xml"
  jsonLines : Bool := false
  canonical : Bool := false
  undeclare : Bool := false
  encoding : String := "UTF-8"
  normForm : String := "none"
  includeContentType : Bool := true
  escapeUriAttrs : Bool := true
  mediaType : Option String := none
  indentUnit : String := "  "
  lineEnding : Option String := none
  csvHeader : Bool := false
  csvQuote : String := "\""
  csvSep : String := ","
deriving Inhabited

/-- The kinds of parameter value (the required types of the F&O 4.0
    §17.2.3 table). -/
inductive PKind where
  | bool | boolOpt | str | qnames | method | dec | charmap
deriving DecidableEq

def paramKinds : List (String × PKind) := [
  ("allow-duplicate-names", .bool), ("byte-order-mark", .bool), ("canonical", .bool),
  ("cdata-section-elements", .qnames), ("csv-header", .bool), ("csv-quote-character", .str),
  ("csv-separator", .str), ("doctype-public", .str), ("doctype-system", .str),
  ("encoding", .str), ("escape-solidus", .bool), ("escape-uri-attributes", .bool),
  ("html-version", .dec), ("include-content-type", .bool), ("indent", .bool),
  ("indent-attributes", .bool), ("indent-unit", .str), ("item-separator", .str),
  ("json-lines", .bool), ("json-node-output-method", .method), ("line-ending", .str),
  ("media-type", .str), ("method", .method), ("normalization-form", .str),
  ("omit-xml-declaration", .bool), ("standalone", .boolOpt),
  ("suppress-indentation", .qnames), ("undeclare-prefixes", .bool),
  ("use-character-maps", .charmap), ("version", .str)]

def serMethods : List String := ["xml", "xhtml", "html", "text", "json", "adaptive", "csv"]

/-- One parameter value, after the type checks of either form. -/
inductive PVal where
  | b (v : Bool)
  | ob (v : Option Bool)
  | s (v : String)
  | qs (v : List QN)
  | cm (v : List (Char × String))

def SerParams.set (p : SerParams) (name : String) (v : PVal) : M SerParams := do
  let sepm {α} (m : String) : M α := err "SEPM0016" m
  match name, v with
  | "allow-duplicate-names", .b x => pure { p with allowDup := x }
  | "canonical", .b x => pure { p with canonical := x }
  | "cdata-section-elements", .qs x => pure { p with cdata := p.cdata ++ x }
  | "csv-header", .b x => pure { p with csvHeader := x }
  | "csv-quote-character", .s x =>
      if x.length != 1 then sepm "csv-quote-character must be one character" else pure { p with csvQuote := x }
  | "csv-separator", .s x =>
      if x.length != 1 then sepm "csv-separator must be one character" else pure { p with csvSep := x }
  | "doctype-public", .s x => pure { p with doctypePublic := if x == "" then none else some x }
  | "doctype-system", .s x => pure { p with doctypeSystem := if x == "" then none else some x }
  | "encoding", .s x => pure { p with encoding := x }
  | "escape-solidus", .b x => pure { p with escapeSolidus := x }
  | "escape-uri-attributes", .b x => pure { p with escapeUriAttrs := x }
  | "html-version", .s x => pure { p with htmlVersion := some x }
  | "include-content-type", .b x => pure { p with includeContentType := x }
  | "indent", .b x => pure { p with indent := x }
  | "indent-unit", .s x =>
      let x := x.replace "\\t" "\t"
      if x.toList.all (· == ' ') || x.toList.all (· == '\t') then pure { p with indentUnit := x }
      else sepm "indent-unit must be spaces or tabs"
  | "item-separator", .s x => pure { p with itemSep := some x }
  | "json-lines", .b x => pure { p with jsonLines := x }
  | "json-node-output-method", .s x => pure { p with jsonNodeMethod := x }
  | "line-ending", .s x =>
      let y := ((((x.replace "\\r" "\r").replace "\\n" "\n").replace "&#xD;" "\r").replace "&#x0D;" "\r")
        |>.replace "&#xA;" "\n" |>.replace "&#x0A;" "\n"
      if ["\n", "\r", "\r\n"].contains y then pure { p with lineEnding := some y }
      else sepm "line-ending must be a line feed, a carriage return, or both"
  | "media-type", .s x => pure { p with mediaType := some x }
  | "method", .s x => pure { p with method := x }
  | "normalization-form", .s x => pure { p with normForm := x }
  | "omit-xml-declaration", .b x => pure { p with omitDecl := x }
  | "standalone", .ob x => pure { p with standalone := x }
  | "suppress-indentation", .qs x => pure { p with suppress := p.suppress ++ x }
  | "undeclare-prefixes", .b x => pure { p with undeclare := x }
  | "use-character-maps", .cm x => pure { p with charMap := x }
  | "version", .s x => pure { p with version := some x }
  | _, _ => pure p

/-- Check the values that both forms share (§3: SEPM0016, and
    the encoding and normalization form a serializer supports). -/
def SerParams.check (p : SerParams) : M SerParams := do
  if !serMethods.contains p.method && !p.method.startsWith "Q{" then
    err "SEPM0016" ("unknown output method " ++ p.method)
  if !(serMethods.contains p.jsonNodeMethod || p.jsonNodeMethod.startsWith "Q{") then
    err "SEPM0016" ("unknown json-node-output-method " ++ p.jsonNodeMethod)
  let enc := p.encoding.toLower
  if !["utf-8", "utf8", "utf-16", "utf-16le", "utf-16be", "utf-32", "us-ascii", "ascii",
       "iso-8859-1", "latin1", "iso-latin-1"].contains enc then
    err "SESU0007" ("unsupported encoding " ++ p.encoding)
  if p.method == "csv" && p.csvSep == p.csvQuote then
    err "SEPM0016" "csv-separator and csv-quote-character must differ"
  -- Serialization 4.0 §11.2, §11.3: one character, not U+000A or U+000D
  for (nm, v) in [("csv-separator", p.csvSep), ("csv-quote-character", p.csvQuote)] do
    if v.length != 1 || v == "\n" || v == "\r" then
      err "SEPM0016" (nm ++ " must be one character other than U+000A and U+000D")
  if (p.method == "xml" || p.method == "xhtml") && p.omitDecl &&
      (p.standalone.isSome || (p.version.getD "1.0" != "1.0" && p.doctypeSystem.isSome)) then
    err "SEPM0009" "omit-xml-declaration is inconsistent with standalone, or with version and doctype-system"
  let nf := p.normForm.toUpper
  if !["NONE", "NFC", "NFD", "NFKC", "NFKD"].contains nf then
    err "SESU0011" ("unsupported normalization form " ++ p.normForm)
  pure p

/-! ### The map form (option parameter conventions, F&O 4.0 §1.7) -/

def Env.coerceTo (e : Env) (ty : String) (v : Seq) (what : String) : M Seq :=
  e.coerce (parseTy ty) v what

def mapParamValue (e : Env) (name : String) (k : PKind) (v : Seq) : M (Option PVal) := do
  if v.isEmpty && k != .boolOpt then return none
  match k with
  | .bool =>
    match ← e.coerceTo "xs:boolean" v name with
    | [.atom ⟨_, .bool b⟩] => pure (some (.b b))
    | _ => err "XPTY0004" (name ++ " must be xs:boolean")
  | .boolOpt =>
    match ← e.coerceTo "xs:boolean?" v name with
    | [.atom ⟨_, .bool b⟩] => pure (some (.ob (some b)))
    | _ => pure (some (.ob none))
  | .str =>
    match ← e.coerceTo "xs:string" v name with
    | [.atom a] => pure (some (.s a.str))
    | _ => err "XPTY0004" (name ++ " must be xs:string")
  | .dec =>
    match ← e.coerceTo "xs:decimal" v name with
    | [.atom a] => pure (some (.s a.str))
    | _ => err "XPTY0004" (name ++ " must be xs:decimal")
  | .qnames =>
    let r ← e.coerceTo "xs:QName*" v name
    pure (some (.qs (r.filterMap (fun i => match i with
      | .atom ⟨_, .qn q⟩ => some q
      | _ => none))))
  | .method =>
    match v with
    | [.atom ⟨_, .qn q⟩] =>
        if q.uri == "" then err "XPTY0004" (name ++ ": a QName must have a namespace")
        else pure (some (.s q.eqn))
    | _ =>
      match ← e.coerceTo "xs:string" v name with
      | [.atom a] => pure (some (.s a.str))
      | _ => err "XPTY0004" (name ++ " must be xs:string or xs:QName")
  | .charmap =>
    match ← e.coerceTo "map(xs:string, xs:string)" v name with
    | [.map kvs] =>
      let mut out : List (Char × String) := []
      for (key, val) in kvs do
        match key.str.toList, val with
        | [c], [.atom a] => out := out ++ [(c, a.str)]
        | [_], _ => err "XPTY0004" "use-character-maps: value must be xs:string"
        | _, _ => err "SEPM0016" ("use-character-maps: key '" ++ key.str ++ "' is not one character")
      pure (some (.cm out))
    | _ => err "XPTY0004" "use-character-maps must be a map(xs:string, xs:string)"

def mapParams (e : Env) (kvs : List (Atomic × Seq)) : M SerParams := do
  let mut p : SerParams := {}
  for (k, v) in kvs do
    match k.v with
    | .qn q =>
        if q.uri == "" then err "XPTY0004" ("serialization parameter " ++ q.loc ++ " must be a string, not a QName in no namespace")
    | _ =>
      if !k.isStringLike then err "XPTY0004" "serialization parameter names are strings"
      let name := k.str
      match paramKinds.lookup name with
      | none => err "XPTY0004" ("unknown serialization parameter " ++ name)
      | some kind =>
        match ← mapParamValue e name kind v with
        | some pv => p ← p.set name pv
        | none => pure ()
  p.check

/-! ### The element form (§3.1, the serialization parameter document) -/


def Env.elemKids (e : Env) (n : NodeRef) : List NodeRef :=
  ((e.nrec n).children.toList.map n.at).filter (fun c => (e.nrec c).kind == .element)

def Env.attrNodes (e : Env) (n : NodeRef) : List NodeRef := (e.nrec n).attrs.toList.map n.at

def parseYesNo (name v : String) : M Bool :=
  match trimWs v with
  | "yes" | "true" | "1" => pure true
  | "no" | "false" | "0" => pure false
  | x => err "SEPM0017" (name ++ ": '" ++ x ++ "' is not yes or no")

/-- A lexical QName in a parameter document, with the element's
    in-scope namespaces; an unprefixed name is in no namespace. -/
def resolveLexQN (scope : List (String × String)) (s : String) : M QN :=
  if s.startsWith "Q{" then
    match (s.drop 2).toString.splitOn "}" with
    | [u, l] => pure { uri := u, loc := l }
    | _ => err "SEPM0017" ("bad EQName " ++ s)
  else match s.splitOn ":" with
    | [l] => pure { uri := "", loc := l }
    | [p, l] => match scope.lookup p with
      | some u => pure { uri := u, loc := l, pfx := p }
      | none => err "SEPM0017" ("undeclared prefix " ++ p)
    | _ => err "SEPM0017" ("bad QName " ++ s)

def elemParams (e : Env) (root : NodeRef) : M SerParams := do
  let r := e.nrec root
  if r.kind != .element || r.name.uri != nsOUTPUT || r.name.loc != "serialization-parameters" then
    err "XPTY0004" "the options must be an output:serialization-parameters element"
  for a in e.attrNodes root do
    if (e.nrec a).name.uri == "" then err "SEPM0017" "attribute on output:serialization-parameters"
  let mut p : SerParams := {}
  let mut seen : List String := []
  for c in e.elemKids root do
    let cr := e.nrec c
    let key := cr.name.eqn
    if seen.contains key then err "SEPM0019" ("duplicate parameter " ++ cr.name.loc)
    seen := key :: seen
    if cr.name.uri == "" then err "SEPM0017" ("parameter " ++ cr.name.loc ++ " is not in the output namespace")
    if cr.name.uri != nsOUTPUT then continue
    let name := cr.name.loc
    let some kind := paramKinds.lookup name | err "SEPM0017" ("unknown serialization parameter " ++ name)
    if kind == .charmap then
      for a in e.attrNodes c do
        if (e.nrec a).name.uri == "" then err "SEPM0017" "attribute on use-character-maps"
      let mut cm : List (Char × String) := []
      for m in e.elemKids c do
        let mr := e.nrec m
        if mr.name.uri != nsOUTPUT || mr.name.loc != "character-map" then
          err "SEPM0017" "use-character-maps may contain only output:character-map"
        let mut ch : Option String := none
        let mut ms : Option String := none
        for a in e.attrNodes m do
          let ar := e.nrec a
          if ar.name.uri != "" then continue
          if ar.name.loc == "character" then ch := some ar.value
          else if ar.name.loc == "map-string" then ms := some ar.value
          else err "SEPM0017" ("attribute " ++ ar.name.loc ++ " on output:character-map")
        match ch, ms with
        | some cs, some s =>
          match cs.toList with
          | [x] =>
            if cm.any (·.1 == x) then err "SEPM0018" ("character " ++ cs ++ " is mapped twice")
            cm := cm ++ [(x, s)]
          | _ => err "SEPM0017" "character-map/@character must be one character"
        | _, _ => err "SEPM0017" "character-map needs character and map-string"
      p ← p.set name (.cm cm)
      continue
    let mut value : Option String := none
    for a in e.attrNodes c do
      let ar := e.nrec a
      if ar.name.uri != "" then continue
      if ar.name.loc == "value" then value := some ar.value
      else err "SEPM0017" ("attribute " ++ ar.name.loc ++ " on output:" ++ name)
    let some v := value | err "SEPM0017" ("output:" ++ name ++ " has no value attribute")
    let pv ← match kind with
      | .bool => pure (PVal.b (← parseYesNo name v))
      | .boolOpt =>
        match trimWs v with
        | "omit" => pure (PVal.ob none)
        | x => pure (PVal.ob (some (← parseYesNo name x)))
      | .qnames =>
        let toks := (trimWs v).splitOn " " |>.filter (· != "")
        pure (PVal.qs (← toks.mapM (resolveLexQN cr.inscope)))
      | .method =>
        let x := trimWs v
        if x.contains ':' then pure (PVal.s (← resolveLexQN cr.inscope x).eqn)
        else if serMethods.contains x then pure (PVal.s x)
        else err "SEPM0017" ("unknown method " ++ x)
      | _ => pure (PVal.s v)
    p ← p.set name pv
  p.check

/-- The serialization parameters of XQuery output declarations
    (`declare option output:name "value";`, XQuery 4.0 §5.20.2): local
    name and string value, in order. The values have the lexical forms of
    the parameter document (Serialization 4.0 §3.1); a value that is not
    valid for its parameter is SEPM0016. `scope` resolves the QName values
    (`method`, `cdata-section-elements`, `suppress-indentation`). -/
def declParams (scope : List (String × String)) (decls : List (String × String))
    (init : SerParams := {}) : M SerParams := do
  let sepm {α} (m : String) : M α := err "SEPM0016" m
  let yesNo (name v : String) : M Bool :=
    match trimWs v with
    | "yes" | "true" | "1" => pure true
    | "no" | "false" | "0" => pure false
    | x => sepm (name ++ ": '" ++ x ++ "' is not yes or no")
  let lexQN (v : String) : M QN :=
    match resolveLexQN scope v with
    | .ok q => pure q
    | .error ex => sepm ex.msg
  let mut p : SerParams := init
  for (name, v) in decls do
    if name == "parameter-document" then continue
    let some kind := paramKinds.lookup name | err "XQST0109" ("unknown serialization parameter " ++ name)
    let pv ← match kind with
      | .bool => pure (PVal.b (← yesNo name v))
      | .boolOpt =>
        match trimWs v with
        | "omit" => pure (PVal.ob none)
        | x => pure (PVal.ob (some (← yesNo name x)))
      | .qnames =>
        let toks := (trimWs v).splitOn " " |>.filter (· != "")
        pure (PVal.qs (← toks.mapM lexQN))
      | .method =>
        let x := trimWs v
        -- Q{}local is a name in no namespace: a method of this specification
        let x := if x.startsWith "Q{}" then (x.drop 3).toString else x
        if x.contains ':' || x.startsWith "Q{" then pure (PVal.s (← lexQN x).eqn)
        else if serMethods.contains x then pure (PVal.s x)
        else sepm ("unknown method " ++ x)
      | .charmap => err "XQST0109" "use-character-maps is not an output declaration"
      | _ => pure (PVal.s v)
    p ← p.set name pv
  p.check

/-- The parameters of an `output:parameter-document` (XQuery 4.0
    §5.20.2): the text of a serialization parameter document. A document
    that does not parse is XQST0119; its parameter errors are those of the
    parameter document (SEPM0017, SEPM0018, SEPM0019). -/
def paramDocParams (e : Env) (txt : String) : M SerParams := do
  match Doc.ofString txt with
  | .error m => err "XQST0119" ("the parameter document does not parse: " ++ m)
  | .ok d =>
    let n0 : NodeRef := { doc := 0, idx := 0, rt := some d }
    let some root := ((e.nrec n0).children.toList.map n0.at).find? (fun c => (e.nrec c).kind == .element)
      | err "XQST0119" "the parameter document has no element"
    elemParams e root

def serParamsOf (e : Env) (opts : Seq) : M SerParams :=
  match opts with
  | [] => pure {}
  | [.map kvs] => mapParams e kvs
  | [.node n] => elemParams e n
  | _ => err "XPTY0004" "the options of fn:serialize must be a map or an output:serialization-parameters element"

/-! ## Output -/

abbrev W := StateT String M

def emit (s : String) : W Unit := modify (· ++ s)

def hexU (n : Nat) : String :=
  String.ofList ((Nat.toDigits 16 n).map Char.toUpper)

def charRef (c : Char) : String := "&#x" ++ hexU c.toNat ++ ";"

def SerParams.encodable (p : SerParams) (c : Char) : Bool :=
  if p.encoding == "UTF-8" then true else
  match p.encoding.toLower with
  | "us-ascii" | "ascii" => c.toNat < 128
  | "iso-8859-1" | "latin1" | "iso-latin-1" => c.toNat < 256
  | _ => true

def SerParams.mapped (p : SerParams) (c : Char) : Option String := p.charMap.lookup c

/-- Escape one character of a text node (XML and XHTML, §5). -/
def SerParams.escTextChar (p : SerParams) (c : Char) : String :=
  match p.mapped c with
  | some r => r
  | none =>
    let n := c.toNat
    if c == '&' then "&amp;"
    else if c == '<' then "&lt;"
    else if c == '>' then "&gt;"
    else if c == '\r' then "&#xD;"
    else if !p.canonical && ((0x7F ≤ n && n ≤ 0x9F) || n == 0x2028 || (n < 0x20 && n != 9 && n != 10)) then charRef c
    else if p.encodable c then String.singleton c else charRef c

def SerParams.escAttrChar (p : SerParams) (html : Bool) (next : Option Char) (c : Char) : String :=
  match p.mapped c with
  | some r => r
  | none =>
    match c with
    | '&' => if html && next == some '{' then "&" else "&amp;"
    | '<' => if html then "<" else "&lt;"
    | '>' => if html || p.canonical then ">" else "&gt;"
    | '"' => "&quot;"
    | '\n' => "&#xA;"
    | '\t' => "&#x9;"
    | '\r' => "&#xD;"
    | c =>
      let n := c.toNat
      if !p.canonical && ((0x7F ≤ n && n ≤ 0x9F) || n == 0x2028 || n < 0x20) then charRef c
      else if p.encodable c then String.singleton c else charRef c

/-- Unicode normalization of a string by `normalization-form`. -/
def SerParams.norm (p : SerParams) (s : String) : String :=
  let f := p.normForm.toUpper
  if f == "NONE" then s else (Unicode.normalize f s).getD s

def SerParams.escText (p : SerParams) (s : String) : String :=
  (p.norm s).toList.foldl (fun acc c => acc ++ p.escTextChar c) ""

def SerParams.escAttr (p : SerParams) (html : Bool) (s : String) : String := Id.run do
  let cs := (p.norm s).toList.toArray
  let mut out := ""
  for i in [0:cs.size] do
    out := out ++ p.escAttrChar html cs[i + 1]? (cs.getD i ' ')
  return out

/-- Text where markup is not recognised (HTML `script`, `style`): only
    the character map and the encoding apply. -/
def SerParams.rawText (p : SerParams) (s : String) : String :=
  (p.norm s).toList.foldl (fun acc c => acc ++ match p.mapped c with
    | some r => r
    | none => if p.encodable c then String.singleton c else charRef c) ""

/-! ### Sequence normalization (§2) -/

/-- An item of the normalized sequence: a node, or a text node built
    from strings. -/
inductive NItem where
  | node (n : NodeRef)
  | text (s : String)

def flattenArrays : Nat → Seq → Seq
  | 0, s => s
  | f + 1, s => s.flatMap (fun i => match i with
      | .arr ms => flattenArrays f ms.flatten
      | x => [x])

def Env.normalizeSeq (e : Env) (p : SerParams) (s : Seq) : M (List NItem) := do
  let s2 := flattenArrays 1000 s
  let s2 := if s2.isEmpty then [Item.atom (Atomic.ofStr "")] else s2
  -- S3, S4: atomic values to strings, with the item separator
  let mut s4 : List NItem := []
  let mut prevStr := false
  let mut first := true
  for i in s2 do
    match p.itemSep with
    | some sep =>
      if !first then s4 := s4 ++ [.text sep]
      match i with
      | .atom a => s4 := s4 ++ [.text a.str]
      | .node n => s4 := s4 ++ [.node n]
      | _ => err "SENR0001" "a function item cannot be serialized by this method"
    | none =>
      match i with
      | .atom a =>
        s4 := s4 ++ [.text ((if prevStr then " " else "") ++ a.str)]
        prevStr := true
      | .node n => s4 := s4 ++ [.node n]; prevStr := false
      | _ => err "SENR0001" "a function item cannot be serialized by this method"
    first := false
  -- S6: a document node is replaced by its children; S7: merge texts
  let mut out : List NItem := []
  let mut acc : Option String := none
  for i in s4 do
    let parts : List NItem := match i with
      | .node n =>
        let r := e.nrec n
        if r.kind == .document then r.children.toList.map (fun c => .node (n.at c)) else [.node n]
      | t => [t]
    for x in parts do
      let txt : Option String := match x with
        | .text t => some t
        | .node n => if (e.nrec n).kind == .text then some (e.nrec n).value else none
      match txt with
      | some t => acc := some ((acc.getD "") ++ t)
      | none =>
        if let some t := acc then
          if t != "" then out := out ++ [.text t]
        acc := none
        match x with
        | .node n =>
          let k := (e.nrec n).kind
          if k == .attribute || k == .namespace then
            err "SENR0001" "an attribute or namespace node cannot be serialized by this method"
          out := out ++ [x]
        | _ => pure ()
  if let some t := acc then
    if t != "" then out := out ++ [.text t]
  pure out

/-! ### The XML, XHTML and HTML methods (§5, §6, §7) -/

def htmlVoid : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param",
   "source", "track", "wbr", "basefont", "frame", "isindex", "keygen", "command"]

def htmlBoolAttrs : List String :=
  ["checked", "compact", "declare", "defer", "disabled", "ismap", "multiple", "nohref",
   "noresize", "noshade", "nowrap", "readonly", "selected"]

def uriAttrs : List String :=
  ["href", "src", "action", "cite", "data", "longdesc", "usemap", "codebase", "classid",
   "profile", "datasrc", "for", "background", "archive", "formaction", "poster", "manifest"]

structure XCtx where
  p : SerParams
  /-- `xml`, `xhtml` or `html`. -/
  m : String
  html5 : Bool

/-- The element names of HTML5 (the HTML Living Standard element index),
    for the XHTML method's recognition of no-namespace elements (§7.1). -/
def html5Elems : List String :=
  ["a", "abbr", "address", "area", "article", "aside", "audio", "b", "base", "bdi", "bdo",
   "blockquote", "body", "br", "button", "canvas", "caption", "cite", "code", "col", "colgroup",
   "data", "datalist", "dd", "del", "details", "dfn", "dialog", "div", "dl", "dt", "em", "embed",
   "fieldset", "figcaption", "figure", "footer", "form", "h1", "h2", "h3", "h4", "h5", "h6",
   "head", "header", "hgroup", "hr", "html", "i", "iframe", "img", "input", "ins", "kbd", "keygen",
   "label", "legend", "li", "link", "main", "map", "mark", "math", "menu", "meta", "meter", "nav",
   "noscript", "object", "ol", "optgroup", "option", "output", "p", "param", "picture", "pre",
   "progress", "q", "rp", "rt", "ruby", "s", "samp", "script", "search", "section", "select",
   "slot", "small", "source", "span", "strong", "style", "sub", "summary", "sup", "svg", "table",
   "tbody", "td", "template", "textarea", "tfoot", "th", "thead", "time", "title", "tr", "track",
   "u", "ul", "var", "video", "wbr"]

/-- The XHTML elements whose content model is EMPTY (§7.1, prior to HTML5). -/
def xhtmlEmpty : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "basefont",
   "frame", "isindex", "param"]

/-- The void elements of HTML5 (§7.1). -/
def html5Void : List String :=
  ["area", "base", "br", "col", "embed", "hr", "img", "input", "keygen", "link", "meta",
   "param", "source", "track", "wbr"]

def XCtx.isHtmlElem (x : XCtx) (q : QN) : Bool :=
  if x.m == "html" then q.uri == "" || (x.html5 && q.uri == nsXHTML)
  -- §7.1: in the XHTML namespace, or (HTML5) an HTML5 element name in no namespace
  else if x.m == "xhtml" then q.uri == nsXHTML || (x.html5 && q.uri == "" && html5Elems.contains q.loc.toLower)
  else false

def lower (s : String) : String := s.toLower

def qnIn (q : QN) (qs : List QN) : Bool := qs.any (fun x => x.uri == q.uri && x.loc == q.loc)

def Env.isWsText (e : Env) (n : NodeRef) : Bool :=
  let r := e.nrec n
  r.kind == .text && r.value.toList.all isWs

/-- Dedupe an in-scope list (newest first) to its effective bindings. -/
def effectiveScope (sc : List (String × String)) : List (String × String) :=
  sc.foldl (fun acc (p, u) => if acc.any (·.1 == p) then acc else acc ++ [(p, u)]) []

def cdataSection (s : String) : String :=
  "<![CDATA[" ++ s.replace "]]>" "]]]]><![CDATA[>" ++ "]]>"

/-- A CDATA section in an encoding: a character that the encoding cannot
    represent ends the section and is written as a character reference
    (Serialization 4.0 §5.1.4, `cdata-section-elements`). -/
def SerParams.cdataIn (p : SerParams) (s : String) : String := Id.run do
  let mut out := ""
  let mut cur := ""
  for c in s.toList do
    if p.encodable c then cur := cur.push c
    else
      if cur != "" then out := out ++ cdataSection cur
      cur := ""
      out := out ++ charRef c
  if cur != "" || out == "" then out := out ++ cdataSection cur
  out

def XCtx.nl (x : XCtx) (depth : Nat) : String :=
  "\n" ++ String.join (List.replicate depth x.p.indentUnit)

/-- Whether the content of an element is indented: indentation is on,
    the element is not listed in `suppress-indentation`, it has no
    non-whitespace text child, and no `xml:space="preserve"`. -/
def XCtx.indentsIn (x : XCtx) (e : Env) (n : NodeRef) : Bool :=
  let r := e.nrec n
  x.p.indent && !x.p.canonical && !qnIn r.name x.p.suppress &&
  !(r.children.toList.any (fun c => (e.nrec (n.at c)).kind == .text && !e.isWsText (n.at c))) &&
  !(r.attrs.toList.any (fun a => let ar := e.nrec (n.at a); ar.name.uri == nsXML && ar.name.loc == "space" && ar.value == "preserve")) &&
  !(x.m == "html" && x.isHtmlElem r.name && ["pre", "script", "style", "textarea", "title"].contains (lower r.name.loc))

/-- The namespace declarations an element needs, given the bindings the
    output has in scope. -/
def Env.nsDecls (e : Env) (x : XCtx) (n : NodeRef) (scope : List (String × String)) :
    List (String × String) :=
  let r := e.nrec n
  let own := effectiveScope r.inscope |>.filter (fun (pf, _) => pf != "xml")
  let needed := own ++ [(r.name.pfx, r.name.uri)] ++
    (e.attrNodes n).filterMap (fun a =>
      let ar := e.nrec a
      if ar.name.uri != "" && ar.name.pfx != "" && ar.name.pfx != "xml" then some (ar.name.pfx, ar.name.uri) else none)
  let needed := effectiveScope needed.reverse |>.reverse
  let needed := effectiveScope needed
  let decls := needed.filter (fun (pf, u) =>
    match scope.lookup pf with
    | some v => v != u
    | none => !(pf == "" && u == ""))
  -- undeclarations of prefixes (XML 1.1 with undeclare-prefixes)
  let undecl := if x.p.undeclare && x.p.version == some "1.1" then
    scope.filter (fun (pf, u) => pf != "" && u != "" && !own.any (·.1 == pf) && pf != r.name.pfx) |>.map (fun (pf, _) => (pf, ""))
    else []
  let all := decls ++ undecl
  if x.p.canonical then all.mergeSort (fun a b => a.1 ≤ b.1) else all

/-- Is `n` inside (a strict descendant of) an HTML `script` or `style`
    element, under the HTML method? Its text and the attributes of its
    descendants are not escaped (§7.4). -/
def Env.inRawHtml (e : Env) (x : XCtx) (n : NodeRef) : Bool :=
  x.m == "html" && (e.ancestors n).any (fun a =>
    let r := e.nrec a
    r.kind == .element && x.isHtmlElem r.name && ["script", "style"].contains (lower r.name.loc))

def Env.writeAttr (e : Env) (x : XCtx) (elemHtml : Bool) (a : NodeRef) : W Unit := do
  let ar := e.nrec a
  -- an attribute of an element inside script or style: not escaped
  let rawHere := match ar.parent with
    | some p => e.inRawHtml x (a.at p)
    | none => false
  let nm := if ar.name.pfx == "" then ar.name.loc else ar.name.pfx ++ ":" ++ ar.name.loc
  let v := ar.value
  if elemHtml && x.m == "html" && ar.name.uri == "" && htmlBoolAttrs.contains (lower nm) && lower v == lower nm then
    emit (" " ++ nm)
  else
    let v := if elemHtml && x.p.escapeUriAttrs && ar.name.uri == "" && uriAttrs.contains (lower nm)
      then Fn.String.escapeHtmlUri v else v
    emit (" " ++ nm ++ "=\"" ++ (if rawHere then x.p.rawText v else x.p.escAttr (elemHtml && x.m == "html") v) ++ "\"")

def Env.sortedAttrs (e : Env) (x : XCtx) (n : NodeRef) : List NodeRef :=
  let as := e.attrNodes n
  if x.p.canonical then
    as.mergeSort (fun a b =>
      let ra := e.nrec a
      let rb := e.nrec b
      ra.name.uri < rb.name.uri || (ra.name.uri == rb.name.uri && ra.name.loc ≤ rb.name.loc))
  else as

def metaTag (x : XCtx) : String :=
  let ct := (x.p.mediaType.getD "text/html") ++ "; charset=" ++ x.p.encoding
  let close := if x.m == "html" then ">" else " />"
  -- with HTML5, both the HTML and the XHTML method write meta charset (§6, §7)
  if x.html5 then "<meta charset=\"" ++ x.p.encoding ++ "\"" ++ (if x.m == "html" then ">" else "/>")
  else "<meta http-equiv=\"Content-Type\" content=\"" ++
    (if x.m == "xhtml" then (x.p.mediaType.getD "text/html") ++ "; charset=" ++ x.p.encoding else ct) ++ "\"" ++ close

def Env.isContentTypeMeta (e : Env) (x : XCtx) (n : NodeRef) : Bool :=
  let r := e.nrec n
  r.kind == .element && x.isHtmlElem r.name && lower r.name.loc == "meta" &&
  -- a charset attribute, or http-equiv Content-Type (case-insensitive, trimmed)
  (e.attrNodes n).any (fun a => let ar := e.nrec a;
    ar.name.uri == "" && (lower ar.name.loc == "charset" ||
      (lower ar.name.loc == "http-equiv" && lower (trimWs ar.value) == "content-type")))

/-- XML 1.0 `Char` (§2.2 of XML 1.0): what an XML 1.0 output may hold;
    XML 1.1 also allows the C0 and C1 controls, as character
    references. -/
def xml10Char (c : Char) : Bool :=
  let n := c.toNat
  n == 9 || n == 10 || n == 13 || (0x20 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) || n ≥ 0x10000

def XCtx.checkChars (x : XCtx) (s : String) : M Unit :=
  if x.m != "html" && x.p.version.getD "1.0" == "1.0" && !s.toList.all (fun c => xml10Char c || (x.p.mapped c).isSome) then
    err "SERE0006" "a character that XML 1.0 does not allow"
  else pure ()

/-- An absolute URI (RFC 3986 §4.3: it has a scheme). -/
def hasScheme (u : String) : Bool :=
  match u.toList with
  | c :: rest =>
    c.isAlpha && (match rest.span (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.') with
      | (_, ':' :: _) => true
      | _ => false)
  | [] => false

def Env.writeNode (e : Env) (x : XCtx) : Nat → NodeRef → List (String × String) → Nat → Bool → Option QN → W Unit
  | 0, _, _, _, _, _ => pure ()
  | f + 1, n, scope, depth, ind, parent => do
    let r := e.nrec n
    match r.kind with
    | .document =>
      for c in r.children.toList do
        e.writeNode x f (n.at c) scope depth ind none
    | .text =>
      x.checkChars r.value
      let inCdata := match parent with
        | some q => qnIn q x.p.cdata && !(x.m == "html" && x.isHtmlElem q)
        | none => false
      let raw := (match parent with
        | some q => x.m == "html" && x.isHtmlElem q && ["script", "style"].contains (lower q.loc)
        | none => false) || e.inRawHtml x n
      if inCdata && !x.p.canonical then emit (x.p.cdataIn r.value)
      else if raw then emit (x.p.rawText r.value)
      else emit (x.p.escText r.value)
    | .comment => emit ("<!--" ++ r.value ++ "-->")
    | .pi =>
      if x.m == "html" then emit ("<?" ++ r.name.loc ++ (if r.value == "" then "" else " " ++ r.value) ++ ">")
      else emit ("<?" ++ r.name.loc ++ (if r.value == "" then "" else " " ++ r.value) ++ "?>")
    | .attribute =>
      emit ((if r.name.pfx == "" then r.name.loc else r.name.pfx ++ ":" ++ r.name.loc) ++ "=\"" ++ x.p.escAttr false r.value ++ "\"")
    | .namespace =>
      emit ("xmlns" ++ (if r.name.loc == "" then "" else ":" ++ r.name.loc) ++ "=\"" ++ x.p.escAttr false r.value ++ "\"")
    | .element =>
      let isH := x.isHtmlElem r.name
      -- §7.1 prefix normalization (XHTML method, HTML5): an element in the
      -- XHTML, SVG or MathML namespace loses its prefix and gets a default
      -- namespace; prefixes bound to those namespaces are dropped unless an
      -- attribute of the element uses them
      let normNs := ["http://www.w3.org/1999/xhtml", "http://www.w3.org/2000/svg",
        "http://www.w3.org/1998/Math/MathML"]
      let pnorm := x.m == "xhtml" && x.html5 && normNs.contains r.name.uri
      let nm := if r.name.pfx == "" || pnorm then r.name.loc else r.name.pfx ++ ":" ++ r.name.loc
      let decls := if x.m == "html" && isH && r.name.uri == "" then
          (e.nsDecls x n scope).filter (fun (pf, _) => pf != "")
        else e.nsDecls x n scope
      let decls := if !(x.m == "xhtml" && x.html5) then decls else
        let attrPfx := (e.attrNodes n).map (fun a => (e.nrec a).name.pfx)
        let kept := decls.filter (fun (pf, u) => pf == "" || !normNs.contains u || attrPfx.contains pf)
        if pnorm then
          let kept := kept.filter (fun (pf, _) => pf != "")
          if scope.lookup "" == some r.name.uri then kept else ("", r.name.uri) :: kept
        else kept
      if x.p.canonical && decls.any (fun (_, u) => u != "" && !hasScheme u) then
        err "SERE0024" "canonical serialization: a namespace URI is not absolute"
      for a in e.attrNodes n do x.checkChars (e.nrec a).value
      emit ("<" ++ nm)
      for (pf, u) in decls do
        emit (" xmlns" ++ (if pf == "" then "" else ":" ++ pf) ++ "=\"" ++ x.p.escAttr false u ++ "\"")
      for a in e.sortedAttrs x n do
        e.writeAttr x isH a
      let scope' := decls ++ scope
      let kidsAll := r.children.toList.map n.at
      let indentHere := ind && x.indentsIn e n
      let kids := if indentHere then kidsAll.filter (fun c => !e.isWsText c) else kidsAll
      let isHead := isH && lower r.name.loc == "head" && x.p.includeContentType && x.m != "xml"
      let kids := if isHead then kids.filter (fun c => !e.isContentTypeMeta x c) else kids
      if kids.isEmpty && !isHead then
        if x.m == "html" && isH then
          emit ">"
          if !htmlVoid.contains (lower r.name.loc) then emit ("</" ++ nm ++ ">")
        else if x.m == "xhtml" then
          -- §7.1: the minimized form only for an element expected to be empty
          let empty := isH && (if x.html5 then html5Void else xhtmlEmpty).contains (lower r.name.loc)
          if empty then emit " />" else emit ("></" ++ nm ++ ">")
        else if x.p.canonical then emit ("></" ++ nm ++ ">")
        else emit "/>"
      else
        emit ">"
        if isHead then
          if indentHere then emit (x.nl (depth + 1))
          emit (metaTag x)
        for c in kids do
          if indentHere then emit (x.nl (depth + 1))
          e.writeNode x f c scope' (depth + 1) (ind && indentHere) (some r.name)
        if indentHere then emit (x.nl depth)
        emit ("</" ++ nm ++ ">")

/-- The first element of the normalized sequence (for the DOCTYPE). -/
def Env.firstElem (e : Env) (items : List NItem) : Option NodeRef :=
  items.findSome? (fun i => match i with
    | .node n => if (e.nrec n).kind == .element then some n else none
    | _ => none)

def Env.writeMarkup (e : Env) (p : SerParams) (s : Seq) : M String := do
  let items ← e.normalizeSeq p s
  let m := p.method
  let html5 := match p.htmlVersion with
    | some v => (v.toList.headD '5') ≥ '5'
    | none => m != "html" || (match p.version with | some v => (v.toList.headD '5') ≥ '5' | none => true)
  let x : XCtx := { p, m, html5 }
  let act : W Unit := do
    if m != "html" && !p.omitDecl && !p.canonical then
      emit ("<?xml version=\"" ++ (p.version.getD "1.0") ++ "\" encoding=\"" ++ p.encoding ++ "\"" ++
        (match p.standalone with
          | some b => " standalone=\"" ++ (if b then "yes" else "no") ++ "\""
          | none => "") ++ "?>")
      if p.indent then emit "\n"
    match e.firstElem items with
    | some fe =>
      let r := e.nrec fe
      let root := if r.name.pfx == "" then r.name.loc else r.name.pfx ++ ":" ++ r.name.loc
      if !p.canonical then
        match p.doctypeSystem, p.doctypePublic with
        | some sys, some pub => emit ("<!DOCTYPE " ++ root ++ " PUBLIC \"" ++ pub ++ "\" \"" ++ sys ++ "\">")
        | some sys, none => emit ("<!DOCTYPE " ++ root ++ " SYSTEM \"" ++ sys ++ "\">")
        | none, some pub =>
            -- XHTML method, HTML5, no doctype-system: <!DOCTYPE html> (§7.1);
            -- the HTML method keeps the public identifier
            if m == "xhtml" && html5 && lower r.name.loc == "html" && x.isHtmlElem r.name then
              emit "<!DOCTYPE html>"
              if p.indent then emit "\n"
            else if m != "xml" then emit ("<!DOCTYPE " ++ root ++ " PUBLIC \"" ++ pub ++ "\">")
        | none, none =>
            if m != "xml" && html5 && lower r.name.loc == "html" && x.isHtmlElem r.name then
              emit "<!DOCTYPE html>"
              if p.indent then emit "\n"
    | none => pure ()
    let mut first := true
    let mut seenElem := false
    for i in items do
      match i with
      | .text t =>
        x.checkChars t
        emit (p.escText t)
      | .node n =>
        let k := (e.nrec n).kind
        if p.canonical && !first then
          if seenElem || k == .element then emit "\n"
        else if p.indent && !first then emit "\n"
        e.writeNode x 100000 n [("", ""), ("xml", nsXML)] 0 true none
        if k == .element then seenElem := true
      first := false
  let ((), out) ← act.run ""
  pure out

/-! ### The text method (§8) -/

def Env.writeText (e : Env) (p : SerParams) (s : Seq) : M String := do
  let items ← e.normalizeSeq p s
  let mut out := ""
  for i in items do
    match i with
    | .text t => out := out ++ p.rawText t
    | .node n => out := out ++ p.rawText (e.nodeString n)
  pure out

/-! ### The JSON method (§9) -/

/-- ECMAScript `Number::toString` (RFC 8785 §3.2.2.3) of a finite
    double, from its shortest round-trip digits. -/
def esNumber (f : Float) : String :=
  if f == 0 then "0"
  else
    let neg := f < 0
    let (d, q) := shortestDigits false (if neg then -f else f)
    let ds := (toString d).toList
    let k : Int := ds.length
    let n : Int := q + 1
    let digits := String.ofList ds
    let body :=
      if k ≤ n && n ≤ 21 then digits ++ String.ofList (List.replicate (n - k).toNat '0')
      else if 0 < n && n ≤ 21 then
        String.ofList (ds.take n.toNat) ++ "." ++ String.ofList (ds.drop n.toNat)
      else if -6 < n && n ≤ 0 then
        "0." ++ String.ofList (List.replicate (-n).toNat '0') ++ digits
      else
        let e := n - 1
        let mant := match ds with
          | [c] => String.singleton c
          | c :: rest => String.singleton c ++ "." ++ String.ofList rest
          | [] => "0"
        mant ++ "e" ++ (if e < 0 then "-" else "+") ++ toString e.natAbs
    (if neg then "-" else "") ++ body

def hex4l (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (4 - s.length) '0') ++ s

def hex4u (n : Nat) : String := (hex4l n).toUpper

def SerParams.jsonEscChar (p : SerParams) (c : Char) : String :=
  let n := c.toNat
  let short : Option String :=
    if c == '"' then some "\\\"" else if c == '\\' then some "\\\\"
    else if c == '\x08' then some "\\b" else if c == '\x0C' then some "\\f"
    else if c == '\n' then some "\\n" else if c == '\r' then some "\\r"
    else if c == '\t' then some "\\t" else none
  if p.canonical then
    match short with
    | some e => e
    | none => if n < 0x20 then "\\u" ++ hex4l n else String.singleton c
  else
    match p.mapped c with
    | some r => r
    | none =>
      match short with
      | some e => e
      | none =>
        if c == '/' then (if p.escapeSolidus then "\\/" else "/")
        else if n < 0x20 || (0x7F ≤ n && n ≤ 0x9F) then "\\u" ++ hex4u n
        else if p.encodable c then String.singleton c
        else if n ≥ 0x10000 then
          let v := n - 0x10000
          "\\u" ++ hex4u (0xD800 + v / 0x400) ++ "\\u" ++ hex4u (0xDC00 + v % 0x400)
        else "\\u" ++ hex4u n

def SerParams.jsonString (p : SerParams) (s : String) : String :=
  "\"" ++ (p.norm s).toList.foldl (fun acc c => acc ++ p.jsonEscChar c) "" ++ "\""

/-- The UTF-16 code units of a string (RFC 8785 §3.2.3 key order). -/
def utf16Units (s : String) : List Nat :=
  s.toList.flatMap (fun c =>
    let n := c.toNat
    if n ≥ 0x10000 then
      let v := n - 0x10000
      [0xD800 + v / 0x400, 0xDC00 + v % 0x400]
    else [n])

def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

def Env.jsonNumber (p : SerParams) (a : Atomic) : M String :=
  match a.num? with
  | some (.i i) => pure (toString i)
  | some (.d d) =>
    if p.canonical then pure (esNumber (floatOfDec d)) else pure (Dec.canonical d)
  | some (.f f) | some (.g f) =>
    if f.isNaN then (if p.canonical then err "SERE0020" "NaN in canonical JSON" else pure "null")
    else if f.isInf then
      (if p.canonical then err "SERE0020" "infinity in canonical JSON"
       else pure (if f > 0 then "1e9999" else "-1e9999"))
    else if f == 0 && !p.canonical && (1.0 / f) < 0 then pure "-0"
    else pure (esNumber f)
  | none => pure a.str

mutual
def Env.jsonItem (e : Env) (p : SerParams) : Nat → Nat → Item → W Unit
  | 0, _, _ => pure ()
  | f + 1, depth, i => do
    let nl (d : Nat) : String :=
      if p.indent && !p.jsonLines then (p.lineEnding.getD "\n") ++ String.join (List.replicate d p.indentUnit) else ""
    let sp := if p.indent then " " else ""
    match i with
    | .atom a =>
      if a.isNumeric then emit (← Env.jsonNumber p a)
      else match a.v with
        | .bool b => emit (if b then "true" else "false")
        | .qn q => if q.uri == nsFN && q.loc == "null" then emit "null" else emit (p.jsonString a.str)
        | _ => emit (p.jsonString a.str)
    | .node n =>
      let sub : SerParams :=
        if p.canonical then { p with method := p.jsonNodeMethod, omitDecl := true }
        else { method := p.jsonNodeMethod, omitDecl := true }
      let s ← (if sub.method == "text" then e.writeText sub [.node n] else e.writeMarkup sub [.node n])
      emit (p.jsonString s)
    | .jnode _ _ v _ => e.jsonSeq p f depth v
    | .arr ms =>
      emit "["
      let mut first := true
      for m in ms do
        if !first then emit ","
        emit (nl (depth + 1))
        e.jsonSeq p f (depth + 1) m
        first := false
      if !ms.isEmpty then emit (nl depth)
      emit "]"
    | .map kvs =>
      let keyed := kvs.map (fun (k, v) => (k.str, v))
      if !p.allowDup || p.canonical then
        let ks := keyed.map (·.1)
        let rec dup : List String → Bool
          | [] => false
          | k :: rest => rest.contains k || dup rest
        if dup ks then err "SERE0022" "two keys of a map have the same string value"
      let keyed := if p.canonical then keyed.mergeSort (fun a b => !lexLt (utf16Units b.1) (utf16Units a.1)) else keyed
      emit "{"
      let mut first := true
      for (k, v) in keyed do
        if !first then emit ","
        emit (nl (depth + 1))
        emit (p.jsonString k ++ ":" ++ sp)
        e.jsonSeq p f (depth + 1) v
        first := false
      if !keyed.isEmpty then emit (nl depth)
      emit "}"
    | .fn _ => err "SERE0021" "a function item cannot be serialized as JSON"
def Env.jsonSeq (e : Env) (p : SerParams) : Nat → Nat → Seq → W Unit
  | 0, _, _ => pure ()
  | f + 1, depth, s =>
    match s with
    | [] => emit "null"
    | [i] => e.jsonItem p f depth i
    | _ => err "SERE0023" "a sequence of more than one item cannot be serialized as JSON"
end

def Env.writeJson (e : Env) (p : SerParams) (s : Seq) : M String := do
  if p.jsonLines then
    let mut parts : List String := []
    for i in s do
      let ((), out) ← (e.jsonItem { p with indent := false } 100000 0 i).run ""
      parts := parts ++ [out]
    pure (String.intercalate "\n" parts)
  else
    let ((), out) ← (e.jsonSeq p 100000 0 s).run ""
    pure out

/-! ### The adaptive method (§11) -/

def conventionalPrefix (u : String) : Option String :=
  if u == nsFN then some "fn" else if u == nsXS then some "xs"
  else if u == nsMAP then some "map" else if u == nsARR then some "array"
  else if u == nsMATH then some "math" else none

def adaptiveName (q : QN) : String :=
  if q.uri == "" then q.loc
  else match conventionalPrefix q.uri with
    | some pf => pf ++ ":" ++ q.loc
    | none => q.eqn

def SerParams.adaptiveStr (p : SerParams) (s : String) : String :=
  "\"" ++ p.rawText (s.replace "\"" "\"\"") ++ "\""

def primitiveName (a : Atomic) : String :=
  match a.ty with
  | .b b => match b.primitive with
    | some pb => pb.localName
    | none => b.localName
  | .untyped => "untypedAtomic"

def SerParams.adaptiveAtom (p : SerParams) (a : Atomic) : String :=
  match a.v with
  | .bool b => if b then "true()" else "false()"
  | .qn q =>
    if a.is .notation then q.eqn else "#" ++ adaptiveName q
  | _ =>
    if a.ty == .untyped || a.is .string || a.is .anyURI then p.adaptiveStr a.str
    else if a.is .integer || a.is .decimal then a.str
    else if a.is .double then
      (match a.v with
        | .dbl f => if f.isNaN then "NaN" else if f.isInf then (if f > 0 then "INF" else "-INF") else a.str
        | _ => a.str)
    else if a.is .float then "xs:float(\"" ++ a.str ++ "\")"
    else "xs:" ++ primitiveName a ++ "(\"" ++ p.rawText a.str ++ "\")"

mutual
def Env.adaptiveItem (e : Env) (p : SerParams) : Nat → Item → W Unit
  | 0, _ => pure ()
  | f + 1, i => do
    match i with
    | .atom a => emit (p.adaptiveAtom a)
    | .node n =>
      let k := (e.nrec n).kind
      if k == .attribute || k == .namespace then
        e.writeNode { p, m := "xml", html5 := true } 10 n [] 0 false none
      else
        let s ← (e.writeMarkup { p with method := "xml", itemSep := none, omitDecl := true } [.node n] : M String)
        emit s
    -- Serialization 4.0 §11: jtree(V) for a parentless JNode, else jnode(K:V)
    | .jnode _ steps v _ =>
      match steps with
      | [] => emit "jtree(" *> e.adaptiveMember p f v *> emit ")"
      | st :: _ => emit ("jnode(" ++ p.adaptiveAtom st.key ++ ":") *> e.adaptiveMember p f v *> emit ")"
    | .arr ms =>
      emit "["
      let mut first := true
      for m in ms do
        if !first then emit ","
        e.adaptiveMember p f m
        first := false
      emit "]"
    | .map kvs =>
      emit "{"
      let mut first := true
      for (k, v) in kvs do
        if !first then emit ","
        emit (p.adaptiveAtom k ++ ":")
        e.adaptiveMember p f v
        first := false
      emit "}"
    | .fn fi =>
      match fi with
      | .builtin q n => emit (adaptiveName q ++ "#" ++ toString n)
      | other => emit ("(anonymous-function)#" ++ toString other.arity)
def Env.adaptiveMember (e : Env) (p : SerParams) : Nat → Seq → W Unit
  | 0, _ => pure ()
  | f + 1, s =>
    match s with
    | [i] => e.adaptiveItem p f i
    | _ => do
      emit "("
      let mut first := true
      for i in s do
        if !first then emit ","
        e.adaptiveItem p f i
        first := false
      emit ")"
end

def Env.writeAdaptive (e : Env) (p : SerParams) (s : Seq) : M String := do
  let sep := p.itemSep.getD "\n"
  let mut parts : List String := []
  for i in s do
    let ((), out) ← (e.adaptiveItem p 100000 i).run ""
    parts := parts ++ [out]
  pure (String.intercalate sep parts)

/-! ### The CSV method (§10) -/

def SerParams.csvField (p : SerParams) (s : String) : String :=
  let s := s.toList.foldl (fun acc c => acc ++ (p.mapped c).getD (String.singleton c)) ""
  let q := p.csvQuote
  let le := p.lineEnding.getD "\n"
  let needs := s.contains p.csvSep.front || s.contains q.front || s.contains '\n' || s.contains '\r'
  let s := if needs then q ++ s.replace q (q ++ q) ++ q else s
  (s.replace "\r\n" "\n").replace "\r" "\n" |>.replace "\n" le

def Env.writeCsv (e : Env) (p : SerParams) (s : Seq) : M String := do
  let le := p.lineEnding.getD "\n"
  let rowsOf (xs : Seq) : M (List (List String)) := xs.mapM (fun i => match i with
    | .arr ms => ms.mapM (fun m => do
        let as ← e.atomize m
        pure (String.intercalate " " (as.map Atomic.str)))
    | _ => err "SERE0025" "CSV rows must be arrays of atomic values")
  let (header, rows) ← match s with
    | [.map kvs] =>
      let rows ← rowsOf ((mapGet kvs (Atomic.ofStr "rows")).getD [])
      let cols := ((mapGet kvs (Atomic.ofStr "columns")).getD []).map (fun i => match i with
        | .atom a => a.str | _ => "")
      pure ((if p.csvHeader && !cols.isEmpty then some cols else none), rows)
    | _ => pure (none, ← rowsOf s)
  let line (fs : List String) : String := String.intercalate p.csvSep (fs.map p.csvField) ++ le
  pure (String.join ((header.toList ++ rows).map line))

/-! ## `fn:serialize` -/

def Env.serializeWith (e : Env) (p : SerParams) (s : Seq) : M String := do
  let out ← match p.method with
    | "json" => e.writeJson p s
    | "adaptive" => e.writeAdaptive p s
    | "text" => e.writeText p s
    | "csv" => e.writeCsv p s
    | "xml" | "xhtml" | "html" => e.writeMarkup p s
    | _ => e.writeMarkup { p with method := "xml" } s
  match p.lineEnding with
  | some le => if p.method == "json" || p.method == "csv" then pure out else pure (out.replace "\n" le)
  | none => pure out

def serializeFn : LibFn := fun _ e a => do
  let p ← serParamsOf e (argN a 1)
  pure (sStr (← e.serializeWith p (argN a 0)))

/-! ## `fn:normalize-unicode` (F&O 4.0 §5.4.9) -/

def normalizeUnicodeFn : LibFn := fun _ _ a => do
  let s := strOf (argN a 0)
  let f := if (argN a 1).isEmpty then "NFC" else (trimWs (strOf (argN a 1))).toUpper
  if f == "" then pure (sStr s)
  else match Unicode.normalize f s with
    | some r => pure (sStr r)
    | none => err "FOCH0003" ("unsupported normalization form " ++ f)

def serializeTable : List (String × LibFn) :=
  [("serialize", serializeFn), ("normalize-unicode", normalizeUnicodeFn)]

end L4Factoidal.XPath4
