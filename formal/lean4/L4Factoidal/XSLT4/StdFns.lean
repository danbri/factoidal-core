/-
L4Factoidal.XSLT4.StdFns — the XSLT 4.0 functions that need no
transformation state: `fn:system-property`, `fn:function-available`,
`fn:element-available`, `fn:type-available`,
`fn:available-system-properties` (XSLT 4.0 §20.5, §20.6). They are
available in static expressions (`use-when`, shadow attributes, static
variables, §9.7) as well as at run time.
-/
import L4Factoidal.XSLT4.Static

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-- The XSLT instructions this processor implements (for
    `fn:element-available`). -/
def xslInstructions : List String :=
  ["analyze-string", "apply-imports", "apply-templates", "array", "array-member", "assert",
   "attribute", "break", "call-template", "choose", "comment", "copy", "copy-of", "document",
   "element", "evaluate", "fallback", "for-each", "for-each-group", "fork", "if", "iterate",
   "map", "map-entry", "merge", "message", "namespace", "next-iteration", "next-match", "number",
   "on-empty", "on-non-empty", "perform-sort", "processing-instruction", "result-document",
   "select", "sequence", "source-document", "switch", "text", "try", "value-of", "variable",
   "where-populated"]

/-- The XSLT elements that are not instructions: declarations and the
    elements that occur only inside other elements. -/
def xslOtherElements : List String :=
  ["accept", "accumulator", "accumulator-rule", "attribute-set", "catch", "character-map",
   "context-item", "decimal-format", "expose", "function", "global-context-item", "import",
   "import-schema", "include", "item-type", "key", "matching-substring", "merge-action",
   "merge-key", "merge-source", "mode", "namespace-alias", "non-matching-substring",
   "otherwise", "output", "output-character", "override", "package", "param", "preserve-space",
   "record", "sort", "strip-space", "stylesheet", "template", "transform", "use-package", "when",
   "with-param"]

/-- The XSLT 4.0 functions (namespace `fn`) that the host provides. -/
def xslFunctions : List (String × List Nat) :=
  [("current", [0]), ("current-group", [0]), ("current-grouping-key", [0]),
   ("current-merge-group", [0, 1]), ("current-merge-key", [0]), ("current-merge-key-array", [0]),
   ("current-output-uri", [0]), ("character-map", [1]),
   ("document", [1, 2]), ("element-available", [1]), ("function-available", [1, 2]),
   ("key", [2, 3]), ("regex-group", [1]), ("regex-groups", [0]), ("stream-available", [1]), ("system-property", [1]),
   ("type-available", [1]), ("unparsed-entity-public-id", [1, 2]), ("unparsed-entity-uri", [1, 2]),
   ("accumulator-before", [1]), ("accumulator-after", [1]), ("copy-of", [0, 1]), ("snapshot", [0, 1]),
   ("available-system-properties", [0]), ("apply-templates", [1, 2]), ("map-for-key", [1, 2]), ("transform", [1])]

def systemProperty (l : String) : String :=
  match l with
  | "version" => "4.0"
  | "vendor" => "Factoidal"
  | "vendor-url" => "https://github.com/danbri/factoidal-core"
  | "product-name" => "Factoidal"
  | "product-version" => "0.21"
  | "is-schema-aware" => "yes"
  | "supports-serialization" => "yes"
  | "supports-backwards-compatibility" => "yes"
  | "supports-namespace-axis" => "yes"
  | "supports-streaming" => "no"
  | "supports-dynamic-evaluation" => "yes"
  | "supports-higher-order-functions" => "yes"
  | "xpath-version" => "4.0"
  | "xsd-version" => "1.1"
  | _ => ""

def systemPropertyNames : List String :=
  ["version", "vendor", "vendor-url", "product-name", "product-version", "is-schema-aware",
   "supports-serialization", "supports-backwards-compatibility", "supports-namespace-axis",
   "supports-streaming", "supports-dynamic-evaluation", "supports-higher-order-functions",
   "xpath-version", "xsd-version"]

/-- Resolve a lexical QName argument (`p:local`, `local`, `Q{uri}local`)
    with the namespace bindings of the call. -/
def lexQName (ns : List (String × String)) (s : String) (useDefault : Bool) (code : String) : M QN := do
  let s := s.trimAscii.toString
  if s.startsWith "Q{" then
    match (s.drop 2).toString.splitOn "}" with
    | [u, l] => pure { uri := u, loc := l }
    | _ => err code ("invalid EQName '" ++ s ++ "'")
  else match s.splitOn ":" with
    | [l] =>
        if !(isNCName l) then err code ("invalid QName '" ++ s ++ "'") else
        pure { uri := if useDefault then nsFN else "", loc := l }
    | [p, l] =>
        if !(isNCName p && isNCName l) then err code ("invalid QName '" ++ s ++ "'") else
        if p == "xml" then pure { uri := nsXML, loc := l, pfx := p } else
        match ns.lookup p with
        | some u => pure { uri := u, loc := l, pfx := p }
        | none => match defaultNs.lookup p with
          | some u => pure { uri := u, loc := l, pfx := p }
          | none => err code ("undeclared prefix '" ++ p ++ "'")
    | _ => err code ("invalid QName '" ++ s ++ "'")
where
  isNCName (x : String) : Bool :=
    match x.toList with
    | c :: cs => isNameStart c && cs.all (fun d => isNameCh d && d != ':')
    | [] => false

/-- A string argument (`xs:string`, or an untyped or URI value). -/
def strArg (a : Seq) : String := match a with
  | [.atom x] => x.str
  | _ => ""

/-- Does the stylesheet-independent function table define `q#k`? -/
def builtinAvailable (q : QN) (k : Option Nat) : Bool :=
  let xsl := q.uri == nsFN && ((xslFunctions.lookup q.loc).map (fun ks => match k with
    | some n => ks.contains n | none => true)).getD false
  let cat := match k with
    | some n => (findSig q n).isSome || (q.uri == nsFN && q.loc == "concat" && n ≥ 2)
    | none => (findSigAny q).isSome
  let xs := q.uri == nsXS && (atypeOfName? q.loc).isSome && q.loc != "NOTATION"
            && q.loc != "anyAtomicType" && (k.isNone || k == some 1)
  let impl := (libLookupAll q).isSome || q.uri == nsXS
  xsl || (cat && impl) || xs

/-- The host functions of this module. `userFn q k` says whether the
    stylesheet declares `q#k` (`none` arity: any). -/
def stdHostT (typeKnown : QN → Bool) (userFn : QN → Option Nat → Bool) (q : QN) (k : Nat) : Option HostFn :=
  if q.uri != nsFN then none else
  match q.loc, k with
  | "system-property", 1 => some fun c a => do
      let n ← lexQName c.ns (strArg (a.getD 0 [])) false "XTDE1390"
      if n.uri == nsXSL then pure (sStr (systemProperty n.loc)) else pure (sStr "")
  | "available-system-properties", 0 => some fun _ _ =>
      pure (systemPropertyNames.map (fun l => Item.atom ⟨.b .qname, .qn { uri := nsXSL, loc := l, pfx := "xsl" }⟩))
  | "function-available", 1 | "function-available", 2 => some fun c a => do
      let n ← lexQName c.ns (strArg (a.getD 0 [])) true "XTDE1400"
      let ar : Option Nat := match a.getD 1 [] with
        | [.atom x] => x.str.toNat?
        | _ => none
      pure (sBool (builtinAvailable n ar || userFn n ar))
  | "element-available", 1 => some fun c a => do
      -- a QName, or an EQName string; an unprefixed name is in the
      -- default namespace (§24.3.2)
      let n ← match a.getD 0 [] with
        | [.atom ⟨_, .qn q⟩] => pure q
        | v => do
          let n ← lexQName c.ns (strArg v) false "XTDE1440"
          let s := (strArg v).trimAscii.toString
          if n.uri == "" && !s.contains ':' && !s.startsWith "Q{" then
            pure { n with uri := (c.ns.lookup "#type").getD ((c.ns.lookup "").getD "") }
          else pure n
      -- any XSLT element this processor implements (§24.3.2)
      pure (sBool (n.uri == nsXSL && (xslInstructions.contains n.loc || xslOtherElements.contains n.loc)))
  | "type-available", 1 => some fun c a => do
      let n ← lexQName c.ns (strArg (a.getD 0 [])) false "XTDE1428"
      -- a built-in type, or a type of the in-scope schema (§3.15)
      let s := (strArg (a.getD 0 [])).trimAscii.toString
      let n := if n.uri == "" && !s.contains ':' && !s.startsWith "Q{" then
          { n with uri := (c.ns.lookup "#type").getD ((c.ns.lookup "").getD "") } else n
      pure (sBool ((n.uri == nsXS && ((atypeOfName? n.loc).isSome ||
        ["anyType", "untyped", "anySimpleType", "untypedAtomic"].contains n.loc)) || typeKnown n))
  | _, _ => none

/-- `stdHostT` with no schema types beyond the built-in ones. -/
def stdHost (userFn : QN → Option Nat → Bool) (q : QN) (k : Nat) : Option HostFn :=
  stdHostT (fun _ => false) userFn q k

end L4Factoidal.XSLT4
