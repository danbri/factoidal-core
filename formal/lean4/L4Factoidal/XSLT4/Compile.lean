/-
L4Factoidal.XSLT4.Compile — read stylesheet modules into a `Sheet`.

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28): §3 (stylesheet structure: modules, `xsl:include`,
`xsl:import` and import precedence §3.11, simplified stylesheets §3.8,
forwards-compatible processing §3.10, `use-when` §3.13.1, shadow
attributes §3.13.2), §5 (static context, value templates), §6
(template rules, modes), §9 (variables), §10 (named templates,
attribute sets, functions) and the declarations of §§16–26.

The module texts are supplied by the caller (`texts`, by absolute
URI): the compiler does no I/O. `moduleRefs` lists the modules a text
refers to, so a caller can fetch them first.

Packages (§3.4): `processModule` compiles the declarations of one
package; `XSLT4.Package` compiles the used packages and merges their
components. `compileUsePackage` compiles the `xsl:override` and
`xsl:with-param` children of an `xsl:use-package` declaration.

Not implemented: schema import. It raises a static error that names the
construct.
-/
import L4Factoidal.XSLT4.StdFns
import L4Factoidal.XSLT4.Rename

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-- A stylesheet module: its node table and URI. -/
structure Mod where
  d : Doc
  uri : String
deriving Inhabited

/-- A component of a used package that an `xsl:override` declaration
    replaces (§3.4.5.3): kind, name, highest arity (functions), the new
    name of the original (the target of `xsl:original`), its visibility
    in the used package. -/
structure OvRec where
  kind : String
  name : QN
  hi : Nat := 0
  orig : QN
  vis : String
deriving Inhabited

/-- A named component of a package (§3.4.5): kind (`function`,
    `template`, `variable`, `attribute-set`, `mode`), expanded name,
    arity range (functions), visibility in the containing package, the
    `visibility` attribute of its declaration (`""` when absent), and
    whether it is a stylesheet parameter. -/
structure Comp where
  kind : String
  name : QN
  lo : Nat := 0
  hi : Nat := 0
  vis : String := "private"
  declared : String := ""
  isParam : Bool := false
deriving Inhabited

/-- The symbolic identifier of a component (§3.4.5). -/
def Comp.sym (c : Comp) : String :=
  c.kind ++ " " ++ c.name.eqn ++ (if c.kind == "function" then "#" ++ toString c.hi else "")

structure CSt where
  sheet : Sheet := {}
  prec : Nat := 0
  order : Nat := 0
  tid : Nat := 0
  /-- Static variables and parameters evaluated so far. -/
  statics : List (QN × Seq) := []
  /-- Values the caller gives for static parameters. -/
  staticParams : List (QN × Seq) := []
  /-- Module texts by absolute URI. -/
  texts : List (String × String) := []
  /-- The include/import chain (to refuse cycles, XTSE0180). -/
  stack : List String := []
  /-- Names of the stylesheet functions seen so far (for
      `function-available` in later static expressions). -/
  fnNames : List (QN × Nat) := []
  /-- The named item types of all modules (§5.4). -/
  types : List (QN × String) := []
  /-- Packages (§3.4). The number of package instances made so far (for
      fresh component names). -/
  pkgCounter : Nat := 0
  /-- Per `xsl:use-package` element (module URI, node index): the
      overridden components. -/
  ovRecs : List ((String × Nat) × List OvRec) := []
  /-- Per `xsl:use-package` element: the stylesheet parameters of the
      used package (name, name in the merged sheet, static). -/
  usedParams : List ((String × Nat) × List (QN × QN × Bool)) := []
  /-- Per `xsl:use-package` element: the modes of the used package
      that are not hidden here (key, visibility). -/
  usedModes : List ((String × Nat) × List (String × String)) := []
  /-- Components declared inside `xsl:override`: kind, name, highest
      arity, visibility. -/
  ovComps : List (String × QN × Nat × String) := []
  /-- The template ids of the template rules declared inside
      `xsl:override`. -/
  ovTids : List Nat := []
  /-- The number of templates, functions, globals, attribute sets and
      modes that came from used packages (they come first). -/
  ownStart : Nat × Nat × Nat × Nat × Nat := (0, 0, 0, 0, 0)
  /-- The components accepted from used packages, with their visibility
      here (hidden ones are left out). -/
  acq : List Comp := []
  /-- The modes declared (`xsl:mode`) in this package: key, visibility. -/
  declModes : List (String × String) := []
deriving Inhabited

abbrev CM := StateT CSt M

def cerr {α} (code msg : String) : CM α := throw { code, msg }

def liftM {α} (x : M α) : CM α := fun s => do let v ← x; pure (v, s)

/-! ## Node access -/

def Mod.r (m : Mod) (i : Nat) : NRec := m.d.get i
def Mod.name (m : Mod) (i : Nat) : QN := (m.r i).name
def Mod.isElem (m : Mod) (i : Nat) : Bool := (m.r i).kind == .element
def Mod.isXsl (m : Mod) (i : Nat) (l : String) : Bool :=
  let r := m.r i
  r.kind == .element && r.name.uri == nsXSL && r.name.loc == l
def Mod.kids (m : Mod) (i : Nat) : List Nat := (m.r i).children.toList
def Mod.elemKids (m : Mod) (i : Nat) : List Nat := (m.kids i).filter m.isElem
def Mod.rawAttrs (m : Mod) (i : Nat) : List (QN × String) :=
  (m.r i).attrs.toList.map (fun a => let r := m.r a; (r.name, r.value))
def Mod.text (m : Mod) (i : Nat) : String := m.d.stringValue i

/-- An element's attributes, as (name, value). -/
abbrev Attrs := List (QN × String)

def Attrs.get (as : Attrs) (l : String) : Option String :=
  (as.find? (fun (q, _) => q.uri == "" && q.loc == l)).map (·.2)

def Attrs.xsl (as : Attrs) (l : String) : Option String :=
  (as.find? (fun (q, _) => q.uri == nsXSL && q.loc == l)).map (·.2)

def parseBool (v : String) : Option Bool :=
  match v.trimAscii.toString with
  | "yes" | "true" | "1" => some true
  | "no" | "false" | "0" => some false
  | _ => none

def Attrs.bool (as : Attrs) (l : String) (dflt : Bool) : CM Bool :=
  match as.get l with
  | none => pure dflt
  | some v => match parseBool v with
    | some b => pure b
    | none => cerr "XTSE0020" ("invalid boolean '" ++ v ++ "' for attribute " ++ l)

def tokens (s : String) : List String :=
  (s.split (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')).toList.map (·.toString) |>.filter (· != "")

/-! ## Static evaluation (§9.7) -/

def CSt.userFn (s : CSt) (q : QN) (k : Option Nat) : Bool :=
  s.fnNames.any (fun (n, a) => n == q && (k.isNone || k == some a))

def staticEnv (c : SCx) : CM Env := do
  let s ← get
  let st := s.statics
  let host := stdHost (fun q k => s.userFn q k)
  pure { vars := st, ns := c.xpNs, baseUri := c.baseUri, host }

def staticEval (c : SCx) (src : String) : CM Seq := do
  let e ← liftM (c.parse src)
  let env ← staticEnv c
  match eval 100000 env e with
  | .ok v => pure v
  | .error er =>
      if er.code == "XPST0008" then cerr "XPST0008" (er.msg ++ " (in a static expression)")
      else throw er

def staticBool (c : SCx) (src : String) : CM Bool := do
  let v ← staticEval c src
  match ebv v with
  | .ok b => pure b
  | .error e => throw e

def staticAvt (c : SCx) (src : String) : CM String := do
  let parts ← liftM (splitTemplate src)
  let env ← staticEnv c
  let mut out := ""
  for (isE, t) in parts do
    if isE then
      if t.trimAscii.toString == "" then continue
      let e ← liftM (c.parse t)
      let v ← liftM (eval 100000 env e)
      let as ← liftM (env.atomize v)
      out := out ++ String.intercalate " " (as.map Atomic.str)
    else out := out ++ t
  pure out

/-- The attributes of an XSLT element with shadow attributes (§3.13.2)
    expanded: `_name="{avt}"` replaces `name`. -/
def effAttrs (c : SCx) (m : Mod) (i : Nat) : CM Attrs := do
  let raw := m.rawAttrs i
  if !(m.name i).uri.isEmpty && (m.name i).uri != nsXSL then return raw
  let mut out : Attrs := raw.filter (fun (q, _) => !(q.uri == "" && q.loc.startsWith "_"))
  for (q, v) in raw do
    if q.uri == "" && q.loc.startsWith "_" && q.loc.length > 1 then
      let nm := (q.loc.drop 1).toString
      let val ← staticAvt c v
      out := (out.filter (fun (x, _) => !(x.uri == "" && x.loc == nm))) ++ [({ uri := "", loc := nm }, val)]
  pure out

/-! ## The static context of an element -/

def effScope (sc : List (String × String)) : List (String × String) :=
  sc.foldl (fun acc (p, u) => if acc.any (·.1 == p) then acc else acc ++ [(p, u)]) []

/-- The URIs named by an `exclude-result-prefixes` value. -/
def exclUris (ns : List (String × String)) (v : String) : CM (List String) := do
  let mut out : List String := []
  for t in tokens v do
    if t == "#all" then out := out ++ ns.map (·.2)
    else if t == "#default" then
      match ns.lookup "" with
      | some u => out := out ++ [u]
      | none => cerr "XTSE0809" "#default used where there is no default namespace"
    else match ns.lookup t with
      | some u => out := out ++ [u]
      | none => cerr "XTSE0808" ("exclude-result-prefixes names undeclared prefix '" ++ t ++ "'")
  pure out

/-- Enter element `i`: its namespaces and the standard attributes
    (§3.5: unprefixed on XSLT elements, `xsl:`-prefixed on others). -/
def SCx.enter (c : SCx) (m : Mod) (i : Nat) (as : Attrs) : CM SCx := do
  let r := m.r i
  let isX := r.name.uri == nsXSL
  let g := fun (l : String) => if isX then as.get l else as.xsl l
  let nat := effScope r.inscope
  let mut c := { c with ns := c.fixedNs.getD nat, nat }
  let ns := c.ns
  if let some v := g "xpath-default-namespace" then c := { c with xpathNs := v.trimAscii.toString }
  if let some v := g "expand-text" then
    match parseBool v with
    | some b => c := { c with expandText := b }
    | none => cerr "XTSE0020" ("invalid expand-text value '" ++ v ++ "'")
  if let some v := g "version" then c := { c with version := v.trimAscii.toString }
  if let some v := g "exclude-result-prefixes" then
    c := { c with excl := c.excl ++ (← exclUris ns v) }
  if let some v := g "extension-element-prefixes" then
    c := { c with ext := c.ext ++ (← exclUris ns v) }
  if let some v := g "default-mode" then
    let v := v.trimAscii.toString
    let dm ← if v == "#unnamed" then pure "#unnamed" else do pure (← liftM (c.qname v)).eqn
    c := { c with defaultMode := dm }
  if let some v := g "default-collation" then c := { c with defaultCollation := v }
  match (as.find? (fun (q, _) => q.uri == nsXML && q.loc == "space")).map (·.2) with
  | some "preserve" => c := { c with preserveWs := true }
  | some "default" => c := { c with preserveWs := false }
  | _ => pure ()
  pure c

/-- `use-when` (§3.13.1): is the element included? -/
def useWhenOk (c : SCx) (m : Mod) (i : Nat) (as : Attrs) : CM Bool := do
  let isX := (m.name i).uri == nsXSL
  match (if isX then as.get "use-when" else as.xsl "use-when") with
  | none => pure true
  | some src => staticBool c src

/-! ## Compiling sequence constructors -/

def qnOf (c : SCx) (as : Attrs) (l : String) (code := "XTSE0280") : CM (Option QN) :=
  match as.get l with
  | none => pure none
  | some v => some <$> liftM (c.qname v false code)

def reqAttr (as : Attrs) (l : String) (inst : String) : CM String :=
  match as.get l with
  | some v => pure v
  | none => cerr "XTSE0010" ("xsl:" ++ inst ++ " requires attribute " ++ l)

def optExpr (c : SCx) (as : Attrs) (l : String) : CM (Option Expr) :=
  match as.get l with
  | none => pure none
  | some v => some <$> liftM (c.parse v)

def optAvt (c : SCx) (as : Attrs) (l : String) : CM (Option Avt) :=
  match as.get l with
  | none => pure none
  | some v => some <$> liftM (c.avt v)

def optType (c : SCx) (as : Attrs) (l : String := "as") : CM (Option IType) :=
  match as.get l with
  | none => pure none
  | some v => some <$> liftM (c.parseType v)

def modeKey (c : SCx) (v : String) : CM String := do
  let v := v.trimAscii.toString
  if v == "#default" then pure c.defaultMode
  else if v == "#unnamed" then pure "#unnamed"
  else if v == "#current" then pure "#current"
  else if v == "#all" then pure "#all"
  else pure (← liftM (c.qname v)).eqn

/-- The attributes each instruction allows (§2.3: XTSE0090 for any
    other attribute in no namespace, except in forwards-compatible
    mode). -/
def allowedAttrs : List (String × List String) := [
  ("apply-templates", ["select", "mode", "separator"]),
  ("call-template", ["name"]), ("apply-imports", []), ("next-match", []),
  ("for-each", ["select", "separator"]), ("value-of", ["select", "separator", "disable-output-escaping", "cdata"]),
  ("text", ["disable-output-escaping", "select", "separator", "cdata"]),
  ("sequence", ["select", "as"]), ("if", ["test", "then", "else"]), ("choose", []),
  ("when", ["test"]), ("otherwise", []), ("switch", ["select"]),
  ("variable", ["name", "select", "as", "static", "visibility"]),
  ("param", ["name", "select", "as", "required", "tunnel", "static"]),
  ("with-param", ["name", "select", "as", "tunnel"]),
  ("copy", ["select", "copy-namespaces", "inherit-namespaces", "use-attribute-sets", "type", "validation"]),
  ("copy-of", ["select", "copy-accumulators", "copy-namespaces", "type", "validation"]),
  ("element", ["name", "namespace", "inherit-namespaces", "use-attribute-sets", "type", "validation"]),
  ("attribute", ["name", "namespace", "select", "separator", "type", "validation"]),
  ("comment", ["select"]), ("processing-instruction", ["name", "select"]),
  ("namespace", ["name", "select"]), ("document", ["validation", "type"]),
  ("sort", ["select", "lang", "order", "collation", "stable", "case-order", "data-type"]),
  ("message", ["select", "terminate", "error-code"]), ("assert", ["test", "select", "error-code"]),
  ("for-each-group", ["select", "group-by", "group-adjacent", "group-starting-with", "group-ending-with",
     "split-when", "merge-when", "composite", "collation"]),
  ("iterate", ["select"]), ("break", ["select"]), ("next-iteration", []), ("on-completion", ["select"]),
  ("try", ["select", "rollback-output"]), ("catch", ["errors", "select"]),
  ("analyze-string", ["select", "regex", "flags", "compiled-regex"]),
  ("matching-substring", []), ("non-matching-substring", []),
  ("map", ["select", "duplicates"]), ("map-entry", ["key", "select"]),
  ("array", ["for-each", "select"]), ("array-member", ["select"]),
  ("number", ["value", "select", "level", "count", "from", "format", "lang", "letter-value", "ordinal",
     "start-at", "grouping-separator", "grouping-size"]),
  ("where-populated", []), ("on-empty", ["select"]), ("on-non-empty", ["select"]),
  ("perform-sort", ["select"]), ("fallback", []), ("fork", []), ("select", ["as"]),
  ("evaluate", ["xpath", "as", "base-uri", "with-params", "context-item", "namespace-context",
     "schema-aware", "trusted"]),
  ("result-document", ["format", "href", "select", "validation", "type", "method", "allow-duplicate-names",
     "build-tree", "byte-order-mark", "canonical", "cdata-section-elements", "csv-header",
     "csv-quote-character", "csv-separator", "doctype-public", "doctype-system", "encoding",
     "escape-solidus", "escape-uri-attributes", "html-version", "include-content-type", "indent",
     "indent-attributes", "indent-unit", "item-separator", "json-lines", "json-node-output-method",
     "line-ending", "media-type", "normalization-form", "omit-xml-declaration", "parameter-document",
     "standalone", "suppress-indentation", "undeclare-prefixes", "use-character-maps", "output-version"]),
  ("source-document", ["href", "streamable", "use-accumulators", "validation", "type"]),
  ("merge", []), ("merge-source", ["name", "for-each-item", "for-each-source", "select", "streamable",
     "use-accumulators", "sort-before-merge", "validation", "type"]),
  ("merge-key", ["select", "lang", "order", "collation", "case-order", "data-type"]),
  ("merge-action", []),
  ("template", ["match", "name", "priority", "mode", "as", "visibility"]),
  ("function", ["name", "as", "visibility", "streamability", "override-extension-function", "override",
     "new-each-time", "cache"]),
  ("key", ["name", "match", "use", "composite", "collation"]),
  ("mode", ["name", "as", "streamable", "use-accumulators", "on-no-match", "on-multiple-match",
     "warning-on-no-match", "warning-on-multiple-match", "typed", "copy-namespaces", "visibility"]),
  ("include", ["href"]), ("import", ["href"]),
  ("use-package", ["name", "package-version"]), ("expose", ["component", "names", "visibility"]),
  ("accept", ["component", "names", "visibility"]), ("override", []),
  ("package-location", ["href", "path-in-archive", "archive-type", "is-priority", "format"]),
  ("attribute-set", ["name", "use-attribute-sets", "visibility", "streamable"]),
  ("decimal-format", ["name", "decimal-separator", "grouping-separator", "infinity", "minus-sign",
     "exponent-separator", "NaN", "percent", "per-mille", "zero-digit", "digit", "pattern-separator"]),
  ("strip-space", ["elements"]), ("preserve-space", ["elements"]),
  ("namespace-alias", ["stylesheet-prefix", "result-prefix"]),
  ("character-map", ["name", "use-character-maps"]), ("output-character", ["character", "string"]),
  ("accumulator", ["name", "initial-value", "as", "streamable"]),
  ("accumulator-rule", ["match", "phase", "select", "capture"]),
  ("global-context-item", ["as", "use"]), ("context-item", ["as", "use"]),
  ("stylesheet", ["id", "version", "default-mode", "default-validation", "input-type-annotations",
     "default-collation", "extension-element-prefixes", "exclude-result-prefixes", "expand-text",
     "fixed-namespaces", "main-module", "schema-role", "use-when", "xpath-default-namespace"]),
  ("transform", ["id", "version", "default-mode", "default-validation", "input-type-annotations",
     "default-collation", "extension-element-prefixes", "exclude-result-prefixes", "expand-text",
     "fixed-namespaces", "main-module", "schema-role", "use-when", "xpath-default-namespace"]),
  ("package", ["id", "name", "package-version", "version", "input-type-annotations", "declared-modes",
     "default-mode", "default-validation", "default-collation", "extension-element-prefixes",
     "exclude-result-prefixes", "expand-text", "fixed-namespaces", "schema-role", "use-when",
     "xpath-default-namespace"]),
  ("output", ["name", "method", "allow-duplicate-names", "build-tree", "byte-order-mark", "canonical",
     "cdata-section-elements", "csv-header", "csv-quote-character", "csv-separator", "doctype-public",
     "doctype-system", "encoding", "escape-solidus", "escape-uri-attributes", "html-version",
     "include-content-type", "indent", "indent-attributes", "indent-unit", "item-separator", "json-lines",
     "json-node-output-method", "line-ending", "media-type", "normalization-form", "omit-xml-declaration",
     "parameter-document", "standalone", "suppress-indentation", "undeclare-prefixes", "use-character-maps",
     "version"])]

/-- Attributes whose value must be one of a fixed set (XTSE0020). -/
def enumAttrs : List (String × List String) := [
  ("level", ["single", "multiple", "any"]),
  ("visibility", ["public", "private", "final", "abstract"]),
  ("on-multiple-match", ["use-last", "fail"]),
  ("on-no-match", ["deep-copy", "shallow-copy", "deep-skip", "shallow-skip", "text-only-copy", "fail"]),
  ("validation", ["strict", "lax", "preserve", "strip"]),
  ("default-validation", ["preserve", "strip"]),
  ("use", ["required", "optional", "absent"]),
  ("phase", ["start", "end"]),
  ("input-type-annotations", ["preserve", "strip", "unspecified"])]

/-- Attributes whose value must be a boolean (XTSE0020); the attributes
    that are attribute value templates are checked when evaluated. -/
def boolAttrs : List String :=
  ["copy-namespaces", "inherit-namespaces", "tunnel", "required", "static", "composite", "streamable",
   "cache", "override", "override-extension-function", "declared-modes", "copy-accumulators",
   "rollback-output", "sort-before-merge", "capture", "warning-on-no-match", "warning-on-multiple-match",
   "expand-text"]

/-- The standard attributes every XSLT element may have (§3.5). -/
def standardAttrs : List String :=
  ["default-collation", "default-mode", "default-validation", "exclude-result-prefixes",
   "expand-text", "extension-element-prefixes", "use-when", "version", "xpath-default-namespace"]

def checkAttrs (c : SCx) (l : String) (as : Attrs) : CM Unit := do
  for (q, v) in as do
    if q.uri == nsXSL then cerr "XTSE0090" ("an XSLT element cannot have the attribute xsl:" ++ q.loc)
    -- a processor that is not schema-aware (§3.14)
    if q.uri == "" && q.loc == "type" && l != "output" then
      cerr "XTSE1660" "the type attribute needs a schema-aware processor"
    if q.uri == "" && (q.loc == "validation" || q.loc == "default-validation") && v.trimAscii.toString == "strict" then
      cerr "XTSE1660" "validation=\"strict\" needs a schema-aware processor"
  if c.forwardsCompat then return
  match allowedAttrs.lookup l with
  | none => pure ()
  | some ok =>
    for (q, v) in as do
      if q.uri == "" && !ok.contains q.loc && !standardAttrs.contains q.loc then
        cerr "XTSE0090" ("attribute " ++ q.loc ++ " is not allowed on xsl:" ++ l)
      if q.uri == "" then
        let v' := v.trimAscii.toString
        let applies := q.loc != "use" || l == "context-item" || l == "global-context-item"
        if let some vals := enumAttrs.lookup q.loc then
          if applies && !vals.contains v' then
            cerr "XTSE0020" ("invalid value '" ++ v ++ "' for attribute " ++ q.loc ++ " of xsl:" ++ l)
        if boolAttrs.contains q.loc && (parseBool v').isNone then
          cerr "XTSE0020" ("invalid boolean '" ++ v ++ "' for attribute " ++ q.loc ++ " of xsl:" ++ l)

/-- The namespace bindings a literal result element copies (§11.1.3):
    all in scope except the XSLT namespace, excluded and extension
    namespaces. -/
def lreDecls (c : SCx) : List (String × String) :=
  c.nat.filter (fun (p, u) => p != "xml" && u != nsXSL && !c.excl.contains u && !c.ext.contains u)

def nextTid : CM Nat := do
  let s ← get
  set { s with tid := s.tid + 1 }
  pure s.tid

mutual

/-- Compile the nodes `ids` (children of one element) as a sequence
    constructor. -/
def compileNodes : Nat → SCx → Mod → List Nat → CM (List Instr)
  | 0, _, _, _ => cerr "XTSE0010" "stylesheet too deeply nested"
  | f + 1, c, m, ids => do
    let mut out : Array Instr := #[]
    for i in ids do
      let r := m.r i
      match r.kind with
      | .text =>
          let t := r.value
          if t.toList.all (fun ch => ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') && !c.preserveWs then
            continue
          if c.expandText then out := out.push (.tvt (← liftM (c.avt t)))
          else out := out.push (.lit t)
      | .element =>
          for x in ← compileElem f c m i do out := out.push x
      | _ => pure ()
    pure out.toList

/-- Compile one element of a sequence constructor. -/
def compileElem : Nat → SCx → Mod → Nat → CM (List Instr)
  | 0, _, _, _ => cerr "XTSE0010" "stylesheet too deeply nested"
  | f + 1, c0, m, i => do
    let as ← effAttrs c0 m i
    let c ← c0.enter m i as
    if !(← useWhenOk c m i as) then return []
    let q := m.name i
    if q.uri == nsXSL then
      return [← compileXsl f c m i as]
    if c.ext.contains q.uri then
      -- an extension instruction: this processor has none (§24.2)
      let fbs ← (m.elemKids i).filterM (fun k => pure (m.isXsl k "fallback"))
      let bodies ← fbs.mapM (fun k => do compileNodes f c m (m.kids k))
      let ats := (m.rawAttrs i).filter (fun (aq, _) => aq.uri != nsXSL)
      let ats := ats.map (fun (aq, v) => (aq, (c.avt v).toOption, (c.parse v).toOption))
      return [.extCall q ats bodies]
    -- a literal result element (§11.1)
    if (as.xsl "type").isSome || (as.xsl "validation") == some "strict" then
      cerr "XTSE1660" "xsl:type and xsl:validation=\"strict\" need a schema-aware processor"
    let mut ats : List (QN × Avt) := []
    for (aq, v) in m.rawAttrs i do
      if aq.uri == nsXSL then continue
      ats := ats ++ [(aq, ← liftM (c.avt v))]
    let useSets ← match as.xsl "use-attribute-sets" with
      | some v => (tokens v).mapM (fun t => liftM (c.qname t))
      | none => pure []
    let body ← compileNodes f c m (m.kids i)
    pure [.lre q (lreDecls c) ats useSets body]

def compileSorts : Nat → SCx → Mod → List Nat → CM (List SortK)
  | 0, _, _, _ => pure []
  | f + 1, c, m, ids => ids.filterMapM (fun k => do
      if !m.isXsl k "sort" && !m.isXsl k "merge-key" then return none
      let as ← effAttrs c m k
      let c' ← c.enter m k as
      let sel ← optExpr c' as "select"
      let body ← compileNodes f c' m (m.kids k)
      if sel.isSome && !body.isEmpty then cerr "XTSE1015" "xsl:sort has both a select attribute and content"
      pure (some (.mk sel body (← optAvt c' as "order") (← optAvt c' as "lang") (← optAvt c' as "data-type")
        (← optAvt c' as "case-order") (← optAvt c' as "collation") (← optAvt c' as "stable"))))

def compileParams : Nat → SCx → Mod → List Nat → String → CM (List WParam)
  | 0, _, _, _, _ => pure []
  | f + 1, c, m, ids, tag => do
   let ps ← compileParams1 f c m ids tag
   let names := ps.map (·.name)
   if tag == "param" then
     for (p, i) in names.zipIdx do
       if (names.take i).any (· == p) then
         cerr "XTSE0580" ("two parameters named $" ++ p.show)
   pure ps

def compileParams1 : Nat → SCx → Mod → List Nat → String → CM (List WParam)
  | 0, _, _, _, _ => pure []
  | f + 1, c, m, ids, tag => ids.filterMapM (fun k => do
      if !m.isXsl k tag then return none
      let as ← effAttrs c m k
      let c' ← c.enter m k as
      if !(← useWhenOk c' m k as) then return none
      let some nm ← qnOf c' as "name" | cerr "XTSE0010" ("xsl:" ++ tag ++ " requires a name")
      let sel ← optExpr c' as "select"
      let body ← compileNodes f c' m (m.kids k)
      if sel.isSome && !body.isEmpty then
        cerr (if tag == "param" then "XTSE0620" else "XTSE0620") ("xsl:" ++ tag ++ " has both select and content")
      let required ← as.bool "required" false
      let tunnel ← as.bool "tunnel" false
      pure (some (.mk nm sel body (← optType c' as) tunnel required)))

def compileXsl : Nat → SCx → Mod → Nat → Attrs → CM Instr
  | 0, _, _, _, _ => cerr "XTSE0010" "stylesheet too deeply nested"
  | f + 1, c, m, i, as => do
    let l := (m.name i).loc
    checkAttrs c l as
    let kids := m.kids i
    let ekids := m.elemKids i
    let body (ids : List Nat := kids) : CM (List Instr) := compileNodes f c m ids
    let notTag (ts : List String) : List Nat := kids.filter (fun k => !(ts.any (m.isXsl k ·)))
    match l with
    | "text" =>
        let t := m.text i
        match ← optExpr c as "select" with
        | some e => pure (.valueOf (some e) (← optAvt c as "separator") [] false)
        | none =>
          if !ekids.isEmpty then
            -- 4.0: the content is a sequence constructor (§11.4.2)
            let b ← compileNodes f { c with preserveWs := true } m kids
            pure (.valueOf none (← optAvt c as "separator") b false)
          else if c.expandText then pure (.tvt (← liftM (c.avt t))) else pure (.lit t)
    | "value-of" =>
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE0870" "xsl:value-of has both select and content"
        let sep ← optAvt c as "separator"
        pure (.valueOf sel sep b (c.backCompat && sep.isNone))
    | "sequence" =>
        let sel ← optExpr c as "select"
        let b ← body (notTag ["fallback"])
        if sel.isSome && !b.isEmpty then cerr "XTSE3185" "xsl:sequence has both select and content"
        pure (.seq sel b (← optType c as))
    | "select" =>
        let src := m.text i
        if src.trimAscii.toString == "" then pure (.seq none [] (← optType c as))
        else pure (.seq (some (← liftM (c.parse src))) [] (← optType c as))
    | "element" =>
        let nm ← liftM (c.avt (← reqAttr as "name" l))
        let useSets ← match as.get "use-attribute-sets" with
          | some v => (tokens v).mapM (fun t => liftM (c.qname t))
          | none => pure []
        pure (.elem nm (← optAvt c as "namespace") c.ns useSets (← body))
    | "attribute" =>
        let nm ← liftM (c.avt (← reqAttr as "name" l))
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE0840" "xsl:attribute has both select and content"
        pure (.attr nm (← optAvt c as "namespace") c.ns sel (← optAvt c as "separator") b)
    | "comment" =>
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE0940" "xsl:comment has both select and content"
        pure (.comment sel b)
    | "processing-instruction" =>
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE0880" "xsl:processing-instruction has both select and content"
        pure (.pi (← liftM (c.avt (← reqAttr as "name" l))) sel b)
    | "namespace" =>
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE0910" "xsl:namespace has both select and content"
        pure (.nsI (← liftM (c.avt (← reqAttr as "name" l))) sel b)
    | "document" => pure (.docI (← body))
    | "apply-templates" =>
        let sel ← optExpr c as "select"
        let mode ← match as.get "mode" with
          | some v => modeKey c v
          | none => pure c.defaultMode
        for k in ekids do
          if !(m.isXsl k "sort" || m.isXsl k "with-param") then
            cerr "XTSE0010" "xsl:apply-templates may contain only xsl:sort and xsl:with-param"
        pure (.applyT sel mode (← compileSorts f c m ekids) (← compileParams f c m ekids "with-param")
          (← optAvt c as "separator"))
    | "call-template" =>
        let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:call-template requires a name"
        pure (.callT nm (← compileParams f c m ekids "with-param"))
    | "apply-imports" => pure (.applyImports (← compileParams f c m ekids "with-param"))
    | "next-match" => pure (.nextMatch (← compileParams f c m ekids "with-param"))
    | "for-each" =>
        let sel ← liftM (c.parse (← reqAttr as "select" l))
        pure (.forEach sel (← compileSorts f c m ekids) (← body (notTag ["sort"])) (← optAvt c as "separator"))
    | "for-each-group" =>
        let sel ← liftM (c.parse (← reqAttr as "select" l))
        let opts := ["group-by", "group-adjacent", "group-starting-with", "group-ending-with", "split-when", "merge-when"]
        let given := opts.filter (fun o => (as.get o).isSome)
        if given.length != 1 then cerr "XTSE1080" "xsl:for-each-group needs exactly one grouping attribute"
        let g := given.headD ""
        let kind : GroupKind := match g with
          | "group-by" => .by | "group-adjacent" => .adjacent | "group-starting-with" => .startingWith
          | "group-ending-with" => .endingWith | "split-when" => .splitWhen | _ => .mergeWhen
        let v := (as.get g).getD ""
        let (key, pat) ← if kind == .startingWith || kind == .endingWith then
            do pure (none, some (← liftM (c.pattern v)))
          else do pure (some (← liftM (c.parse v)), none)
        let composite ← as.bool "composite" false
        if (as.get "collation").isSome && !(kind == .by || kind == .adjacent) then
          cerr "XTSE1090" "collation is allowed only with group-by or group-adjacent"
        pure (.forEachGroup sel kind key pat composite (← optAvt c as "collation")
          (← compileSorts f c m ekids) (← body (notTag ["sort"])))
    | "if" =>
        let test ← liftM (c.parse (← reqAttr as "test" l))
        let th ← optExpr c as "then"
        let b ← body
        if th.isSome && !b.isEmpty then cerr "XTSE3185" "xsl:if has both a then attribute and content"
        pure (.ifI test th (← optExpr c as "else") b)
    | "choose" | "switch" =>
        let mut whens : List (Expr × List Instr) := []
        let mut other : Option (List Instr) := none
        for k in ekids do
          let kas ← effAttrs c m k
          let ck ← c.enter m k kas
          if !(← useWhenOk ck m k kas) then continue
          if m.isXsl k "when" then
            if other.isSome then cerr "XTSE0010" "xsl:when after xsl:otherwise"
            let t ← liftM (ck.parse (← reqAttr kas "test" "when"))
            let sel ← optExpr ck kas "select"
            let b ← compileNodes f ck m (m.kids k)
            let b := match sel with | some e => [Instr.seq (some e) [] none] | none => b
            whens := whens ++ [(t, b)]
          else if m.isXsl k "otherwise" then
            if other.isSome then cerr "XTSE0010" "two xsl:otherwise elements"
            let sel ← optExpr ck kas "select"
            let b ← compileNodes f ck m (m.kids k)
            other := some (match sel with | some e => [Instr.seq (some e) [] none] | none => b)
          else if m.isXsl k "fallback" then pure ()
          else cerr "XTSE0010" ("xsl:" ++ l ++ " may contain only xsl:when and xsl:otherwise")
        for k in kids do
          if (m.r k).kind == .text && !((m.r k).value.toList.all Char.isWhitespace) then
            cerr "XTSE0010" ("text is not allowed in xsl:" ++ l)
        if whens.isEmpty then cerr "XTSE0010" ("xsl:" ++ l ++ " needs at least one xsl:when")
        if l == "choose" then pure (.choose whens other)
        else pure (.switch (← liftM (c.parse (← reqAttr as "select" l))) whens other)
    | "variable" =>
        let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:variable requires a name"
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE0620" "xsl:variable has both select and content"
        pure (.var nm (← optType c as) sel b)
    | "copy" =>
        let useSets ← match as.get "use-attribute-sets" with
          | some v => (tokens v).mapM (fun t => liftM (c.qname t))
          | none => pure []
        pure (.copy (← optExpr c as "select") (← as.bool "copy-namespaces" true)
          (← as.bool "inherit-namespaces" true) useSets (← body))
    | "copy-of" =>
        pure (.copyOf (← liftM (c.parse (← reqAttr as "select" l))) (← as.bool "copy-namespaces" true))
    | "message" =>
        pure (.message (← optExpr c as "select") (← body)
          ((← optAvt c as "terminate").getD [.lit "no"]) (← optAvt c as "error-code"))
    | "assert" =>
        pure (.assertI (← liftM (c.parse (← reqAttr as "test" l))) (← optExpr c as "select") (← body)
          (← optAvt c as "error-code"))
    | "number" =>
        let level := (as.get "level").getD "single"
        let cnt ← match as.get "count" with
          | some v => some <$> liftM (c.pattern v) | none => pure none
        let frm ← match as.get "from" with
          | some v => some <$> liftM (c.pattern v) | none => pure none
        if (as.get "value").isSome && ((as.get "select").isSome || (as.get "level").isSome || cnt.isSome || frm.isSome) then
          cerr "XTSE0975" "xsl:number with value cannot have select, level, count or from"
        pure (.number (← optExpr c as "value") (← optExpr c as "select") level cnt frm
          ((← optAvt c as "format").getD [.lit "1"]) (← optAvt c as "lang") (← optAvt c as "ordinal")
          (← optAvt c as "start-at") (← optAvt c as "grouping-separator") (← optAvt c as "grouping-size"))
    | "iterate" =>
        let sel ← liftM (c.parse (← reqAttr as "select" l))
        let ps ← compileParams f c m ekids "param"
        let oc ← match ekids.find? (m.isXsl · "on-completion") with
          | some k => do
              let kas ← effAttrs c m k
              let ck ← c.enter m k kas
              pure (some (← optExpr ck kas "select", ← compileNodes f ck m (m.kids k)))
          | none => pure none
        pure (.iterate sel ps oc (← body (notTag ["param", "on-completion"])))
    | "break" =>
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE3125" "xsl:break has both select and content"
        pure (.breakI sel b)
    | "next-iteration" => pure (.nextIteration (← compileParams f c m ekids "with-param"))
    | "try" =>
        let sel ← optExpr c as "select"
        let mut catches : List (List String × Option Expr × List Instr) := []
        for k in ekids do
          if m.isXsl k "catch" then
            let kas ← effAttrs c m k
            let ck ← c.enter m k kas
            let errs := tokens ((kas.get "errors").getD "*")
            let errs ← errs.mapM (fun t => do
              if t == "*" then pure "*"
              else if t.startsWith "*:" then pure ("*:" ++ (t.drop 2).toString)
              else if t.endsWith ":*" then
                let p := (t.dropEnd 2).toString
                match ck.ns.lookup p with
                | some u => pure ("Q{" ++ u ++ "}*")
                | none => cerr "XTSE0280" ("undeclared prefix '" ++ p ++ "' in xsl:catch")
              else if t.startsWith "Q{" && t.endsWith "*" then pure t
              else pure (← liftM (ck.qname t)).eqn)
            catches := catches ++ [(errs, ← optExpr ck kas "select", ← compileNodes f ck m (m.kids k))]
        if catches.isEmpty then cerr "XTSE0010" "xsl:try needs an xsl:catch"
        let b ← body (notTag ["catch", "fallback"])
        if sel.isSome && !b.isEmpty then cerr "XTSE3140" "xsl:try has both select and content"
        pure (.tryI sel b catches)
    | "analyze-string" =>
        let sel ← liftM (c.parse (← reqAttr as "select" l))
        let rx ← liftM (c.avt (← reqAttr as "regex" l))
        let fl ← liftM (c.avt ((as.get "flags").getD ""))
        let ms ← match ekids.find? (m.isXsl · "matching-substring") with
          | some k => some <$> compileNodes f c m (m.kids k) | none => pure none
        let ns ← match ekids.find? (m.isXsl · "non-matching-substring") with
          | some k => some <$> compileNodes f c m (m.kids k) | none => pure none
        if ms.isNone && ns.isNone then cerr "XTSE1130" "xsl:analyze-string needs matching or non-matching content"
        pure (.analyzeString sel rx fl ms ns)
    | "map" => pure (.mapI (← optExpr c as "select") (← body) (← optExpr c as "duplicates"))
    | "record" =>
        -- 4.0 (§21): each attribute in no namespace is a field
        let mut ents : List Instr := []
        for (aq, v) in as do
          if aq.uri != "" || standardAttrs.contains aq.loc then continue
          ents := ents ++ [.mapEntry (.lit (Atomic.ofStr aq.loc)) (some (← liftM (c.parse v))) []]
        pure (.mapI none (ents ++ (← body)) none)
    | "map-entry" =>
        let key ← liftM (c.parse (← reqAttr as "key" l))
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE3280" "xsl:map-entry has both select and content"
        pure (.mapEntry key sel b)
    | "array" => pure (.arrayI (← optExpr c as "for-each") (← optExpr c as "select") (← body))
    | "array-member" => pure (.arrayMember (← optExpr c as "select") (← body))
    | "evaluate" =>
        let xp ← liftM (c.parse (← reqAttr as "xpath" l))
        pure (.evaluate xp (← optExpr c as "context-item") (← optExpr c as "with-params")
          (← optExpr c as "namespace-context") (← optType c as)
          (← compileParams f c m ekids "with-param") c.xpNs c.baseUri)
    | "result-document" =>
        let ser ← (as.filter (fun (q, _) => q.uri == "" && q.loc != "href" && q.loc != "format" && q.loc != "select"
            && q.loc != "validation" && q.loc != "type" && !standardAttrs.contains q.loc)).mapM
          (fun (q, v) => do pure (q.loc, ← liftM (c.avt v)))
        let sel ← optExpr c as "select"
        let b ← body
        if sel.isSome && !b.isEmpty then cerr "XTSE3185" "xsl:result-document has both select and content"
        let b := match sel with
          | some e => [Instr.seq (some e) [] none]
          | none => b
        pure (.resultDoc (← optAvt c as "href") (← optAvt c as "format") ser b)
    | "where-populated" => pure (.wherePopulated (← body))
    | "on-empty" => pure (.onEmpty (← optExpr c as "select") (← body))
    | "on-non-empty" => pure (.onNonEmpty (← optExpr c as "select") (← body))
    | "perform-sort" =>
        pure (.performSort (← optExpr c as "select") (← compileSorts f c m ekids) (← body (notTag ["sort"])))
    | "fork" => pure (.seq none (← body (notTag ["fallback"])) none)
    | "note" => pure (.seq none [] none)
    | "fallback" => pure (.seq none [] none)
    | "source-document" =>
        pure (.sourceDoc (← liftM (c.avt (← reqAttr as "href" l))) (← body))
    | "merge" =>
        let mut srcs : List MSource := []
        for k in ekids do
          if m.isXsl k "merge-source" then
            let kas ← effAttrs c m k
            let ck ← c.enter m k kas
            let sel ← liftM (ck.parse (← reqAttr kas "select" "merge-source"))
            let keys ← compileSorts f ck m (m.elemKids k)
            srcs := srcs ++ [.mk ((kas.get "name").getD "") (← optExpr ck kas "for-each-item")
              (← optExpr ck kas "for-each-source") sel (← kas.bool "sort-before-merge" false) keys]
        let act ← match ekids.find? (m.isXsl · "merge-action") with
          | some k => compileNodes f c m (m.kids k)
          | none => cerr "XTSE0010" "xsl:merge needs xsl:merge-action"
        pure (.merge srcs act)
    | "param" => cerr "XTSE0010" "xsl:param is not allowed here"
    | "with-param" | "sort" | "when" | "otherwise" | "catch" | "matching-substring"
    | "non-matching-substring" | "on-completion" | "merge-source" | "merge-action" | "merge-key"
    | "context-item" =>
        cerr "XTSE0010" ("xsl:" ++ l ++ " is not allowed here")
    | _ =>
      let fbs := ekids.filter (m.isXsl · "fallback")
      let bodies ← fbs.mapM (fun k => compileNodes f c m (m.kids k))
      if c.forwardsCompat then pure (.unknown (m.name i) bodies "XTDE1450")
      else if ["template", "function", "include", "import", "output", "key", "mode", "stylesheet",
               "transform", "package", "decimal-format", "attribute-set", "namespace-alias",
               "strip-space", "preserve-space", "character-map", "accumulator", "global-context-item",
               "import-schema", "use-package", "expose", "accept", "override", "item-type", "record-type"].contains l then
        cerr "XTSE0010" ("xsl:" ++ l ++ " is a declaration, not an instruction")
      else cerr "XTSE0010" ("unknown XSLT instruction xsl:" ++ l)

end

/-! ## Declarations -/

/-- A top-level element of a module, after includes are expanded:
    its module, index and static context. -/
structure Decl where
  m : Mod
  i : Nat
  c : SCx
deriving Inhabited

/-- Parse a module text. -/
def openModule (uri : String) : CM Mod := do
  let s ← get
  match s.texts.lookup uri with
  | none => cerr "XTSE0165" ("cannot read stylesheet module " ++ uri)
  | some txt =>
    match Doc.ofString txt uri with
    | .ok d => pure { d, uri }
    | .error e => cerr "XTSE0165" ("stylesheet module " ++ uri ++ " is not well-formed: " ++ e)

def Mod.rootElem (m : Mod) : Option Nat :=
  (m.kids 0).find? m.isElem

def resolveHref (base href : String) : String := resolveUri base href

/-- The module-level static context of the root element. -/
def standardNs : List (String × String) :=
  [("xsl", nsXSL), ("xml", nsXML), ("xs", nsXS), ("xsi", "http://www.w3.org/2001/XMLSchema-instance"),
   ("fn", nsFN), ("math", nsMATH), ("map", nsMAP), ("array", nsARR), ("err", nsERR)]

def rootCx (m : Mod) (i : Nat) (as : Attrs) : CM SCx := do
  let c : SCx := { baseUri := m.uri, types := (← get).types }
  let c ← c.enter m i as
  match as.get "fixed-namespaces" with
  | none => pure c
  | some v =>
    let mut fx : List (String × String) := []
    let add (fx : List (String × String)) (p u : String) := (fx.filter (·.1 != p)) ++ [(p, u)]
    for t in tokens v do
      if t == "#standard" then
        for (p, u) in standardNs do fx := add fx p u
      else if let some u := c.nat.lookup t then fx := add fx t u
      else if let some u := standardNs.lookup t then fx := add fx t u
      else match t.splitOn "=" with
        | [p, u] =>
            if p == "xmlns" || (p == "xml") != (u == nsXML) then cerr "XTSE0122" ("cannot bind prefix " ++ p)
            fx := add fx p u
        | _ =>
          -- a URI of a document whose outermost element gives the bindings
          let uri := resolveHref m.uri t
          match (← get).texts.lookup uri with
          | some txt =>
            match Doc.ofString txt uri with
            | .ok d =>
              let some r := (d.get 0).children.toList.find? (fun k => (d.get k).kind == .element)
                | cerr "XTSE0122" ("no element in " ++ t)
              for (p, u) in effScope (d.get r).inscope do
                if p != "xml" && p != "" then fx := add fx p u
            | .error _ => cerr "XTSE0122" ("cannot read " ++ t)
          | none => cerr "XTSE0122" ("invalid fixed-namespaces token '" ++ t ++ "'")
    let c := { c with fixedNs := some fx }
    pure { c with ns := fx }

/-- Evaluate a static variable or parameter (§9.6) and record it. -/
def addStatic (c : SCx) (m : Mod) (i : Nat) (as : Attrs) : CM Unit := do
  let some nmS := as.get "name" | cerr "XTSE0010" "a static variable requires a name"
  let nm ← liftM (c.qname nmS)
  let s ← get
  let isParam := m.isXsl i "param"
  let given := if isParam then s.staticParams.find? (fun (q, _) => q == nm) else none
  let v ← match given with
    | some (_, v) => pure v
    | none =>
      if !(m.kids i).isEmpty && (as.get "select").isNone then
        cerr "XTSE0010" "a static variable must not have content"
      else match as.get "select" with
      | some src => staticEval c src
      | none =>
        if isParam && (← as.bool "required" false) then
          cerr "XTDE0050" ("no value given for the required static parameter $" ++ nmS)
        else pure (if (as.get "as").isSome then [] else sStr "")
  let v ← match as.get "as" with
    | some t => do
        let ty ← liftM (c.parseType t)
        let env ← staticEnv c
        liftM (env.coerce ty v ("$" ++ nmS))
    | none => pure v
  modify (fun s => { s with statics := (nm, v) :: s.statics })

/-- Expand the top-level children of a module root, following
    `xsl:include` (same precedence), evaluating static variables and
    `use-when` in document order. -/
def expandModule : Nat → Mod → Nat → SCx → CM (List Decl)
  | 0, _, _, _ => cerr "XTSE0180" "includes nested too deeply"
  | f + 1, m, root, c => do
    let mut out : List Decl := []
    for i in m.elemKids root do
      let as ← effAttrs c m i
      let ci ← c.enter m i as
      if !(← useWhenOk ci m i as) then continue
      if m.isXsl i "include" then
        let some href := as.get "href" | cerr "XTSE0010" "xsl:include requires href"
        let uri := resolveHref m.uri href
        if (← get).stack.contains uri then cerr "XTSE0180" ("stylesheet module " ++ uri ++ " includes itself")
        let m' ← openModule uri
        let some r' := m'.rootElem | cerr "XTSE0165" ("empty module " ++ uri)
        let as' ← effAttrs {} m' r'
        let c' ← rootCx m' r' as'
        if !(← useWhenOk c' m' r' as') then continue
        if m'.isXsl r' "package" then cerr "XTSE0165" "an xsl:package cannot be included"
        modify (fun s => { s with stack := uri :: s.stack })
        let sub ← if (m'.name r').uri == nsXSL then expandModule f m' r' c'
          else pure [{ m := m', i := r', c := c' }]  -- an included simplified stylesheet
        modify (fun s => { s with stack := s.stack.drop 1 })
        out := out ++ sub
      else
        if (m.isXsl i "variable" || m.isXsl i "param") && (← as.bool "static" false) then
          addStatic ci m i as
        if m.isXsl i "item-type" then
          -- the type text after shadow attributes (static values)
          if let some n := as.get "name" then
            if let .ok q := ci.qname n then
              let t := (as.get "as").getD "item()*"
              modify (fun s => { s with types := (q, t) :: s.types.filter (fun (x, _) => !(x == q)) })
        if m.isXsl i "function" then
          if let some n := as.get "name" then
            if let .ok q := ci.qname n then
              let ar := ((m.elemKids i).filter (m.isXsl · "param")).length
              modify (fun s => { s with fnNames := (q, ar) :: s.fnNames })
        out := out ++ [{ m, i, c := ci }]
    pure out

/-- The body of an abstract component (§3.4.5.2): invoking it is the
    dynamic error XTDE3052. -/
def abstractErr (kind : String) (q : QN) : Instr :=
  .staticErr "XTDE3052" ("the abstract " ++ kind ++ " " ++ q.show ++ " is invoked and has no implementation")

def addTemplate (t : Tmpl) : CM Unit :=
  modify (fun s => { s with sheet := { s.sheet with templates := s.sheet.templates.push t } })

def nextOrder : CM Nat := do
  let s ← get
  set { s with order := s.order + 1 }
  pure s.order

/-- Compile one template (§6.1, §10.1). -/
def compileTemplate (prec : Nat) (d : Decl) (as : Attrs) (inMode : Option String := none) : CM Unit := do
  let c := d.c
  let m := d.m
  let i := d.i
  checkAttrs c "template" as
  let ekids := m.elemKids i
  let name ← qnOf c as "name"
  let pat ← match as.get "match" with
    | some v => some <$> liftM (c.pattern v)
    | none => pure none
  if name.isNone && pat.isNone then cerr "XTSE0500" "xsl:template needs a match or a name attribute"
  if pat.isNone && ((as.get "mode").isSome || (as.get "priority").isSome) then
    cerr "XTSE0500" "a template with no match attribute cannot have mode or priority"
  let modes ← match as.get "mode", inMode with
    | some v, _ => do
        let ts := tokens v
        if ts.isEmpty then cerr "XTSE0550" "empty mode attribute" else
        if ts.contains "#all" && ts.length > 1 then cerr "XTSE0550" "#all with other modes" else
        if ts.eraseDups.length != ts.length then cerr "XTSE0550" "a mode is listed twice" else
        ts.mapM (modeKey c)
    | none, some md => pure [md]
    | none, none => pure [c.defaultMode]
  let ps ← compileParams 100000 c m ekids "param"
  let ctxEl := ekids.find? (m.isXsl · "context-item")
  let (ctxAbsent, ctxAs, ctxUse) ← match ctxEl with
    | some k => do
        let kas ← effAttrs c m k
        let u := ((kas.get "use").getD "optional").trimAscii.toString
        pure (u == "absent", ← optType c kas, u)
    | none => pure (false, none, "optional")
  let vis := ((as.get "visibility").getD "").trimAscii.toString
  if vis != "" && name.isNone then cerr "XTSE0500" "a template with no name cannot have a visibility attribute"
  let bodyIds := (m.kids i).filter (fun k => !(m.isXsl k "param" || m.isXsl k "context-item"))
  let body ← compileNodes 100000 c m bodyIds
  if vis == "abstract" && bodyIds.any (fun k => m.isElem k || !(m.text k).trimAscii.isEmpty) then
    cerr "XTSE0010" "an abstract template must have no content"
  let body := if vis == "abstract" then [abstractErr "template" (name.getD default)]
    else [Instr.seq none body none]
  let as' ← optType c as
  let tid ← nextTid
  let order ← nextOrder
  let prio? : Option Float ← match as.get "priority" with
    | some v =>
      match (castFromString v.trimAscii.toString (.b .decimal)) with
      | .ok a => match a.num? with
        | some n => pure (some n.toFloat)
        | none => cerr "XTSE0530" "invalid priority"
      | .error _ => cerr "XTSE0530" ("invalid priority '" ++ v ++ "'")
    | none => pure none
  match pat with
  | some p =>
    let alts := exprAlternatives 1000 p.e
    for a in alts do
      addTemplate { id := tid, pat := some { e := a, src := p.src }, name, modes, prec, order, prio := prio?.getD (defaultPriority a), params := ps, ty := as', body, ctxAbsent, ctxAs, ctxUse, vis }
  | none =>
    addTemplate { id := tid, pat := none, name, modes, prec, order, params := ps, ty := as', body, ctxAbsent, ctxAs, ctxUse, vis }

/-- Compile the declarations of one module (at precedence `prec`). -/
def compileDecl (prec : Nat) (d : Decl) : CM Unit := do
  let c := { d.c with types := (← get).types }
  let m := d.m
  let i := d.i
  let as ← effAttrs c m i
  let q := m.name i
  if q.uri != nsXSL then
    if q.uri == "" then cerr "XTSE0130" ("top-level element " ++ q.loc ++ " has no namespace")
    return  -- user-defined data elements are ignored (§3.7.3)
  let ekids := m.elemKids i
  let upd (f : Sheet → Sheet) : CM Unit := modify (fun s => { s with sheet := f s.sheet })
  checkAttrs c q.loc as
  match q.loc with
  | "template" => compileTemplate prec { d with c } as
  | "function" =>
      let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:function requires a name"
      if [nsFN, nsXS, nsMATH, nsMAP, nsARR, nsXSL, nsXML].contains nm.uri then
        cerr "XTSE0080" ("a stylesheet function cannot be in namespace " ++ nm.uri)
      let ps ← compileParams 100000 c m ekids "param"
      -- 4.0 (§10.3.2): optional parameters, with default values, follow
      -- the required ones
      let mut seenOpt := false
      for p in ps do
        let opt := p.sel.isSome || !p.body.isEmpty
        if opt then seenOpt := true
        else if seenOpt then cerr "XTSE0761" "a required function parameter follows an optional one"
      let bodyIds := (m.kids i).filter (fun k => !(m.isXsl k "param"))
      let body ← compileNodes 100000 c m bodyIds
      let s ← get
      if s.sheet.functions.any (fun g => g.name == nm && g.params.length == ps.length && g.prec == prec) then
        cerr "XTSE0770" ("two functions " ++ nm.show ++ "#" ++ toString ps.length)
      let fty ← optType c as
      let vis := ((as.get "visibility").getD "").trimAscii.toString
      let body := if vis == "abstract" then [abstractErr "function" nm] else body
      let net := ((as.get "new-each-time").getD "maybe").trimAscii.toString
      let net := if net == "yes" || net == "true" || net == "1" then "yes"
        else if net == "no" || net == "false" || net == "0" then "no" else net
      upd (fun sh => { sh with functions := sh.functions ++ [{ name := nm, params := ps, ty := fty, body, prec, vis, newEachTime := net }] })
  | "variable" | "param" =>
      let some nm ← qnOf c as "name" | cerr "XTSE0010" ("xsl:" ++ q.loc ++ " requires a name")
      let isStatic ← as.bool "static" false
      let sel ← optExpr c as "select"
      let body ← compileNodes 100000 c m (m.kids i)
      if sel.isSome && !body.isEmpty then cerr "XTSE0620" "a global variable has both select and content"
      let s ← get
      if s.sheet.globals.any (fun g => g.name == nm && g.prec == prec) then
        cerr "XTSE0630" ("two global variables named $" ++ nm.show)
      let gty ← optType c as
      let req ← as.bool "required" false
      let vis := ((as.get "visibility").getD "").trimAscii.toString
      if vis == "abstract" && (sel.isSome || !body.isEmpty) then
        cerr "XTSE0010" "an abstract variable must have no select attribute and no content"
      let g : Global := { name := nm, isParam := q.loc == "param", sel, body, ty := gty, required := req, isStatic, prec, vis }
      upd (fun sh => { sh with globals := sh.globals ++ [g] })
  | "key" =>
      let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:key requires a name"
      let pat ← liftM (c.pattern (← reqAttr as "match" "key"))
      let use ← optExpr c as "use"
      let body ← compileNodes 100000 c m (m.kids i)
      if use.isSome && !body.isEmpty then cerr "XTSE1205" "xsl:key has both use and content"
      if use.isNone && body.isEmpty then cerr "XTSE1205" "xsl:key needs use or content"
      let comp ← as.bool "composite" false
      upd (fun sh => { sh with keys := sh.keys ++ [{ name := nm, pat, use, body, composite := comp }] })
  | "mode" =>
      let key ← match as.get "name" with
        | some v =>
          if v.trimAscii.toString.startsWith "#" then cerr "XTSE0020" ("invalid mode name '" ++ v ++ "'")
          else modeKey c v
        | none => pure "#unnamed"
      let onm : NoMatch ← match ((as.get "on-no-match").getD "text-only-copy").trimAscii.toString with
        | "text-only-copy" => pure .textOnlyCopy | "deep-copy" => pure .deepCopy
        | "shallow-copy" => pure .shallowCopy | "deep-skip" => pure .deepSkip
        | "shallow-skip" => pure .shallowSkip | "fail" => pure .fail
        | v => cerr "XTSE0020" ("invalid on-no-match '" ++ v ++ "'")
      let mty ← optType c as
      let mcn ← as.bool "copy-namespaces" true
      let vis := ((as.get "visibility").getD "").trimAscii.toString
      if key == "#unnamed" && vis != "" && vis != "private" then
        cerr "XTSE0020" "the unnamed mode is always private"
      if vis == "abstract" then cerr "XTSE0020" "a mode cannot be abstract"
      let md : ModeDef := { name := key, onNoMatch := onm, onMultiple := (as.get "on-multiple-match").getD "use-last", typed := (as.get "typed").getD "unspecified", ty := mty, copyNs := mcn, vis }
      upd (fun sh => { sh with modes := (sh.modes.filter (·.name != key)) ++ [md] })
      modify (fun s => { s with declModes := s.declModes ++ [(key, vis)] })
      -- 4.0 enclosing modes (§6.9.6): templates inside xsl:mode
      for k in ekids do
        if m.isXsl k "template" then
          let kas ← effAttrs c m k
          let ck ← c.enter m k kas
          if (kas.get "mode").isSome then cerr "XTSE3555" "a template inside xsl:mode cannot have a mode attribute"
          compileTemplate prec { m, i := k, c := ck } kas (some key)
  | "attribute-set" =>
      let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:attribute-set requires a name"
      let useSets ← match as.get "use-attribute-sets" with
        | some v => (tokens v).mapM (fun t => liftM (c.qname t))
        | none => pure []
      for k in ekids do
        if !m.isXsl k "attribute" then cerr "XTSE0010" "xsl:attribute-set may contain only xsl:attribute"
      let body ← compileNodes 100000 c m (m.kids i)
      let vis := ((as.get "visibility").getD "").trimAscii.toString
      let body := if vis == "abstract" then [abstractErr "attribute set" nm] else body
      upd (fun sh => { sh with attrSets := sh.attrSets ++ [{ name := nm, useSets, body, vis }] })
  | "output" =>
      let key ← match as.get "name" with
        | some v => do pure (← liftM (c.qname v)).eqn
        | none => pure ""
      let mut props : List (String × String) := []
      for (aq, v) in as do
        if aq.uri == "" && aq.loc != "name" && !standardAttrs.contains aq.loc then
          let v' ← if aq.loc == "cdata-section-elements" || aq.loc == "suppress-indentation" then
              do pure (String.intercalate " " ((← (tokens v).mapM (fun t => liftM (c.qname t true))).map QN.eqn))
            else if aq.loc == "method" && v.contains ':' then do pure (← liftM (c.qname v)).eqn
            else pure v
          props := props ++ [(aq.loc, v')]
      let s ← get
      let old := (s.sheet.outputs.lookup key).getD []
      let merged := (old.filter (fun (k, _) => !(props.any (·.1 == k)))) ++ props
      upd (fun sh => { sh with outputs := (sh.outputs.filter (·.1 != key)) ++ [(key, merged)] })
  | "decimal-format" =>
      let key ← match as.get "name" with
        | some v => do pure (← liftM (c.qname v)).eqn
        | none => pure ""
      let props := (as.filter (fun (aq, _) => aq.uri == "" && aq.loc != "name" && !standardAttrs.contains aq.loc)).map
        (fun (aq, v) => (aq.loc, v))
      upd (fun sh => { sh with decimalFormats := sh.decimalFormats ++ [(key, props)] })
  | "strip-space" | "preserve-space" =>
      let strip := q.loc == "strip-space"
      let ts ← (tokens (← reqAttr as "elements" q.loc)).mapM (fun t => do
        if t == "*" then pure NameTest.any
        else if t.startsWith "*:" then pure (NameTest.loc (t.drop 2).toString)
        else if t.endsWith ":*" then
          match c.ns.lookup (t.dropEnd 2).toString with
          | some u => pure (NameTest.ns u)
          | none => cerr "XTSE0280" ("undeclared prefix in " ++ t)
        else pure (NameTest.name (← liftM (c.qname t (c.xpathNs != "")))))
      let ts := if c.xpathNs != "" then ts.map (fun t => match t with
          | .name n => if n.uri == "" && n.pfx == "" then NameTest.name { n with uri := c.xpathNs } else t
          | t => t) else ts
      upd (fun sh => { sh with space := sh.space ++ ts.map (fun t => (t, strip, prec)) })
  | "namespace-alias" =>
      let sp ← reqAttr as "stylesheet-prefix" "namespace-alias"
      let rp ← reqAttr as "result-prefix" "namespace-alias"
      let look (p : String) : CM String :=
        if p == "#default" then pure ((c.ns.lookup "").getD "")
        else match c.ns.lookup p with
          | some u => pure u
          | none => cerr "XTSE0812" ("undeclared prefix '" ++ p ++ "' in xsl:namespace-alias")
      let su ← look sp
      let ru ← look rp
      let rpx := if rp == "#default" then "" else rp
      upd (fun sh => { sh with nsAliases := (su, rpx, ru) :: sh.nsAliases })
  | "character-map" =>
      let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:character-map requires a name"
      let mut cs : List (Char × String) := []
      for k in ekids do
        if m.isXsl k "output-character" then
          let kas := m.rawAttrs k
          let ch := (Attrs.get kas "character").getD ""
          match ch.toList with
          | [x] => cs := cs ++ [(x, (Attrs.get kas "string").getD "")]
          | _ => cerr "XTSE0020" "xsl:output-character needs a single character"
      -- use-character-maps: resolved when the map is used, since the
      -- other maps may be declared later
      let mut uses : List String := []
      if let some v := as.get "use-character-maps" then
        for t in tokens v do
          uses := uses ++ [(← liftM (c.qname t)).eqn]
      upd (fun sh => { sh with charMaps := sh.charMaps ++ [(nm.eqn, uses, cs)] })
  | "accumulator" =>
      let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:accumulator requires a name"
      let init ← liftM (c.parse (← reqAttr as "initial-value" "accumulator"))
      let mut rules : List AccRule := []
      for k in ekids do
        if m.isXsl k "accumulator-rule" then
          let kas ← effAttrs c m k
          let ck ← c.enter m k kas
          let pat ← liftM (ck.pattern (← reqAttr kas "match" "accumulator-rule"))
          let sel ← optExpr ck kas "select"
          let b ← compileNodes 100000 ck m (m.kids k)
          rules := rules ++ [{ pat, isEnd := (kas.get "phase") == some "end", sel, body := b }]
      let aty ← optType c as
      upd (fun sh => { sh with accumulators := sh.accumulators ++ [{ name := nm, init, ty := aty, rules }] })
  | "global-context-item" =>
      let use := (as.get "use").getD "optional"
      let t ← optType c as
      upd (fun sh => { sh with globalCtxUse := use, globalCtxAs := t })
  | "import" => pure ()
  | "include" => pure ()
  | "import-schema" => cerr "XTSE1650" "xsl:import-schema: this processor is not schema-aware"
  | "use-package" => pure ()  -- `compileUsePackage`
  | "item-type" => pure ()
  | "record-type" =>
      -- the constructor function (§5.4.2.2): one parameter per field
      let some nm ← qnOf c as "name" | cerr "XTSE0010" "xsl:record-type requires a name"
      let mut ps : List WParam := []
      let mut ents : List Instr := []
      for k in ekids do
        if !m.isXsl k "field" then continue
        let kas ← effAttrs c m k
        let ck ← c.enter m k kas
        let some fnm := kas.get "name" | cerr "XTSE0010" "xsl:field requires a name"
        let fq : QN := { uri := "", loc := fnm }
        let sel ← optExpr ck kas "select"
        let b ← compileNodes 100000 ck m (m.kids k)
        ps := ps ++ [.mk fq sel b (← optType ck kas) false false]
        ents := ents ++ [.mapEntry (.lit (Atomic.ofStr fnm)) (some (.var fq)) []]
      upd (fun sh => { sh with functions := sh.functions ++ [{ name := nm, params := ps, body := [.mapI none ents none], prec }] })
  | "expose" =>
      -- only as a child of xsl:package (§3.4.5.1)
      let ok := match (m.r i).parent with
        | some p => m.isXsl p "package" && (m.r p).parent == some 0
        | none => false
      if !ok then cerr "XTSE0010" "xsl:expose is allowed only as a child of xsl:package"
  | "accept" | "override" | "package-location" =>
      cerr "XTSE0010" ("xsl:" ++ q.loc ++ " is allowed only as a child of xsl:use-package")
  | "note" => pure ()
  | l =>
      if d.c.forwardsCompat then pure ()
      else cerr "XTSE0010" ("unknown XSLT declaration xsl:" ++ l)

/-! ## `xsl:use-package`: overriding declarations (§3.4.5.3) -/

def qnOriginal : QN := { uri := nsXSL, loc := "original" }

def itemStar : IType := .seq .item .star

/-- Types are identical when each is a subtype of the other (§3.4.5.3). -/
def tyIdentical (a b : IType) : Bool := subtype a b && subtype b a

/-- The declared type of a global variable (§3.4.5.3). -/
def Global.declType (g : Global) : IType :=
  match g.ty with
  | some t => t
  | none => if g.sel.isSome then itemStar else if !g.body.isEmpty then .doc none else .atomic (.b .string)

/-- XTSE3070: the signature of an overriding function is compatible
    with the overridden one. -/
def fnCompatible (o n : XFunction) : Bool :=
  let req (f : XFunction) := (f.params.filter (fun p => p.sel.isNone && p.body.isEmpty)).length
  o.params.length == n.params.length && req o == req n &&
  (o.params.zip n.params).all (fun (a, b) => tyIdentical (a.ty.getD itemStar) (b.ty.getD itemStar)) &&
  tyIdentical (o.ty.getD itemStar) (n.ty.getD itemStar) && o.newEachTime == n.newEachTime

/-- XTSE3070 for named templates. -/
def tmplCompatible (o n : Tmpl) : Bool :=
  tyIdentical (o.ty.getD itemStar) (n.ty.getD itemStar) &&
  o.params.all (fun p =>
    if p.tunnel then
      match n.params.find? (·.name == p.name) with
      | some q => q.tunnel && tyIdentical (p.ty.getD itemStar) (q.ty.getD itemStar)
      | none => true
    else
      n.params.any (fun q => q.name == p.name && !q.tunnel && q.required == p.required &&
        tyIdentical (p.ty.getD itemStar) (q.ty.getD itemStar))) &&
  n.params.all (fun q => o.params.any (·.name == q.name) || !q.required) &&
  o.ctxUse == n.ctxUse && tyIdentical (o.ctxAs.getD .item) (n.ctxAs.getD .item)

/-- The error for a reference to `xsl:original` where it names nothing
    (§3.4.5.4). -/
def origMisuse (k : Char) : CM Unit :=
  match k with
  | 'f' => cerr "XPST0017" "xsl:original is not a function here"
  | 'v' => cerr "XPST0008" "$xsl:original is not a variable here"
  | 't' => cerr "XTSE0650" "xsl:original is not a named template here"
  | 'a' => cerr "XTSE0710" "xsl:original is not an attribute set here"
  | _ => pure ()

def isWsText (s : String) : Bool := s.all (fun ch => ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r')

/-- Compile one declaration inside `xsl:override`: compile it as a
    declaration of this package, bind `xsl:original` in it to the
    overridden component, and check the override rules. -/
def compileOverride (prec : Nat) (recs : List OvRec) (pmods : List (String × String)) (d : Decl) : CM Unit := do
  let m := d.m
  let i := d.i
  let l := (m.name i).loc
  if !(["template", "function", "variable", "param", "attribute-set"].contains l) || (m.name i).uri != nsXSL then
    cerr "XTSE0010" ("xsl:override cannot contain " ++ (m.name i).show)
  let s0 ← get
  let nT := s0.sheet.templates.size
  let nF := s0.sheet.functions.length
  let nG := s0.sheet.globals.length
  let nA := s0.sheet.attrSets.length
  compileDecl prec d
  let s1 ← get
  let newT := s1.sheet.templates.toList.drop nT
  let newF := s1.sheet.functions.drop nF
  let newG := s1.sheet.globals.drop nG
  let newA := s1.sheet.attrSets.drop nA
  let find (k : String) (q : QN) (hi : Nat) : CM OvRec :=
    match recs.find? (fun r => r.kind == k && r.name == q && (k != "function" || r.hi == hi)) with
    | some r => pure r
    | none => cerr "XTSE3058" ("xsl:override: " ++ k ++ " " ++ q.show ++ " is not a component of the used package")
  let mut ren : Ren := {}
  let mut abstractOrig := false
  let mut bad : Option String := none
  let mut comps : List (String × QN × Nat × String) := []
  -- template rules: only in modes the used package makes public (§3.4.6)
  for t in newT do
    if t.pat.isSome then
      for md in t.modes do
        match pmods.lookup md with
        | some "public" => pure ()
        | some _ => cerr "XTSE3060" ("cannot add template rules to the mode " ++ md ++ " of a used package")
        | none =>
          if md == "#unnamed" then cerr "XTSE3440" "a template rule in xsl:override must be in a public mode of the used package"
          else cerr "XTSE3060" ("the mode " ++ md ++ " is not a public mode of the used package")
      modify (fun s => { s with ovTids := t.id :: s.ovTids })
  match newT.find? (·.name.isSome) with
  | some t =>
    let nm := t.name.getD default
    let r ← find "template" nm 0
    ren := { ren with tmpls := [(qnOriginal, r.orig)] }
    abstractOrig := r.vis == "abstract"
    match s1.sheet.templates.toList.find? (fun x => x.name == some r.orig) with
    | some o => if !tmplCompatible o t then bad := some ("the override of template " ++ nm.show ++ " has an incompatible signature")
    | none => pure ()
    comps := comps ++ [("template", nm, 0, if t.vis == "" then "private" else t.vis)]
  | none => pure ()
  for g in newF do
    let r ← find "function" g.name g.params.length
    ren := { ren with fns := [(qnOriginal, 0, 100000, r.orig)] }
    abstractOrig := r.vis == "abstract"
    match s1.sheet.functions.find? (fun x => x.name == r.orig) with
    | some o => if !fnCompatible o g then bad := some ("the override of function " ++ g.name.show ++ " has an incompatible signature")
    | none => pure ()
    comps := comps ++ [("function", g.name, g.params.length, if g.vis == "" then "private" else g.vis)]
  for g in newG do
    let r ← find "variable" g.name 0
    ren := { ren with vars := [(qnOriginal, r.orig)] }
    abstractOrig := r.vis == "abstract"
    match s1.sheet.globals.find? (fun x => x.name == r.orig) with
    | some o => if !tyIdentical o.declType g.declType then
        bad := some ("the override of variable $" ++ g.name.show ++ " has a different type")
    | none => pure ()
    comps := comps ++ [("variable", g.name, 0, if g.isParam then "public" else if g.vis == "" then "private" else g.vis)]
  for a in newA do
    let r ← find "attribute-set" a.name 0
    ren := { ren with sets := [(qnOriginal, r.orig)] }
    abstractOrig := r.vis == "abstract"
    comps := comps ++ [("attribute-set", a.name, 0, if a.vis == "" then "private" else a.vis)]
  -- bind xsl:original
  let act : RM (Array Tmpl × List XFunction × List Global × List AttrSet) := do
    let ts ← s1.sheet.templates.toList.mapIdxM (fun k t => if k < nT then pure t else renTmpl ren t)
    let fs ← s1.sheet.functions.mapIdxM (fun k g => if k < nF then pure g else renFn ren g)
    let gs ← s1.sheet.globals.mapIdxM (fun k g => if k < nG then pure g else renGlobal ren g)
    let as ← s1.sheet.attrSets.mapIdxM (fun k a => if k < nA then pure a else renAttrSet ren a)
    pure (ts.toArray, fs, gs, as)
  let ((ts, fs, gs, ats), refs) := act.run #[]
  let origRefs := refs.toList.filter (fun (_, n) => n == qnOriginal.eqn || n.startsWith (qnOriginal.eqn ++ "#"))
  if !origRefs.isEmpty && abstractOrig then cerr "XTSE3075" "xsl:original refers to an abstract component"
  -- xsl:original names only the overridden component (§3.4.5.4)
  let myKind : Char := if !newF.isEmpty then 'f' else if !newG.isEmpty then 'v'
    else if newT.any (·.name.isSome) then 't' else 'a'
  for (k, _) in origRefs do
    if k != myKind then origMisuse k
  if let some msg := bad then cerr "XTSE3070" msg
  modify (fun s => { s with sheet := { s.sheet with templates := ts, functions := fs, globals := gs, attrSets := ats },
                            ovComps := s.ovComps ++ comps })

/-- Compile the children of an `xsl:use-package` declaration that
    belong to this package: the `xsl:override` declarations and the
    `xsl:with-param` values for the used package's parameters (§3.4.4).
    The used package itself was merged before (`XSLT4.Package`). -/
def compileUsePackage (prec : Nat) (d : Decl) : CM Unit := do
  let m := d.m
  let i := d.i
  let c := d.c
  let key := (m.uri, i)
  let recs := ((← get).ovRecs.lookup key).getD []
  let pmods := ((← get).usedModes.lookup key).getD []
  for k in m.kids i do
    let r := m.r k
    if r.kind == .text then
      if !isWsText r.value then cerr "XTSE0010" "xsl:use-package cannot contain text"
      continue
    if r.kind != .element then continue
    let kas ← effAttrs c m k
    let ck ← c.enter m k kas
    if !(← useWhenOk ck m k kas) then continue
    if m.isXsl k "override" then
      for o in m.kids k do
        let ro := m.r o
        if ro.kind == .text then
          if !isWsText ro.value then cerr "XTSE0010" "xsl:override cannot contain text"
          continue
        if ro.kind != .element then continue
        let oas ← effAttrs ck m o
        let co ← ck.enter m o oas
        if !(← useWhenOk co m o oas) then continue
        compileOverride prec recs pmods { m, i := o, c := co }
    else if m.isXsl k "accept" || m.isXsl k "package-location" || m.isXsl k "with-param" then pure ()
    else cerr "XTSE0010" ("xsl:use-package cannot contain " ++ (m.name k).show)
  -- parameter values for the used package (non-static ones; static ones
  -- were given when it was compiled)
  let wps ← compileParams 100000 c m (m.elemKids i) "with-param"
  let pm := ((← get).usedParams.lookup key).getD []
  for p in wps do
    match pm.find? (·.1 == p.name) with
    | some (_, gq, false) =>
      modify (fun s => { s with sheet := { s.sheet with globals := s.sheet.globals.map (fun g =>
        if g.name == gq then { g with sel := p.sel, body := p.body, isParam := false, required := false } else g) } })
    | _ => pure ()

/-- Process one module and its imports (§3.11): imports first (lower
    precedence), then the module's own declarations. `onUse` merges
    the package that an `xsl:use-package` declaration of the principal
    module names (§3.4.2); it runs before any precedence is given. -/
def processModule (onUse : Decl → CM Unit) : Nat → Mod → CM Unit
  | 0, _ => cerr "XTSE0210" "imports nested too deeply"
  | f + 1, m => do
    let some root := m.rootElem | cerr "XTSE0165" "the stylesheet module has no element"
    let ras ← effAttrs {} m root
    let c ← rootCx m root ras
    let rq := m.name root
    if rq.uri != nsXSL || !["stylesheet", "transform", "package"].contains rq.loc then
      -- a simplified stylesheet (§3.8): one template rule for "."
      -- 4.0: xsl:version may be omitted; it defaults to 4.0, and then
      -- text value templates are on (§3.8)
      let ver := (if rq.uri == nsXSL then ras.get "version" else ras.xsl "version").getD "4.0"
      let et := match (ver.splitOn ".").head?.bind String.toNat? with
        | some k => k ≥ 4
        | none => true
      let c := { c with version := ver, expandText := if (ras.xsl "expand-text").isSome then c.expandText else et }
      let body ← compileElem 100000 c m root
      let prec := (← get).prec
      modify (fun s => { s with prec := s.prec + 1 })
      let tid ← nextTid
      addTemplate { id := tid, pat := some { e := .ctx, src := "." }, prio := -1, prec, body }
      modify (fun s => { s with sheet := { s.sheet with version := ver } })
      return
    if rq.loc != "stylesheet" && rq.loc != "transform" && rq.loc != "package" then
      cerr "XTSE0150" ("xsl:" ++ rq.loc ++ " is not a stylesheet root element")
    if (ras.get "version").isNone then cerr "XTSE0110" "xsl:stylesheet requires a version attribute"
    checkAttrs c rq.loc ras
    if !(← useWhenOk c m root ras) then return
    if rq.loc == "package" && (← get).stack.length > 1 then
      cerr "XTSE0165" "an xsl:package cannot be included or imported"
    let decls ← expandModule 100 m root c
    -- used packages (§3.4.2): only at the level of the principal module
    if (← get).stack.length == 1 then
      for d in decls do
        if d.m.isXsl d.i "use-package" then onUse d
      let sh := (← get).sheet
      modify (fun s => { s with ownStart := (sh.templates.size, sh.functions.length, sh.globals.length,
        sh.attrSets.length, sh.modes.length) })
    else if decls.any (fun d => d.m.isXsl d.i "use-package") then
      cerr "XTSE3008" "xsl:use-package in a module that is not at the level of the principal module"
    -- imports, in order, before this module's precedence is fixed
    let mut seenOther := false
    for d in decls do
      if d.m.isXsl d.i "import" then
        let as ← effAttrs d.c d.m d.i
        let some href := as.get "href" | cerr "XTSE0010" "xsl:import requires href"
        let uri := resolveHref d.m.uri href
        if (← get).stack.contains uri then cerr "XTSE0210" ("stylesheet module " ++ uri ++ " imports itself")
        let m' ← openModule uri
        modify (fun s => { s with stack := uri :: s.stack })
        processModule onUse f m'
        modify (fun s => { s with stack := s.stack.drop 1 })
      else seenOther := true
    let prec := (← get).prec
    modify (fun s => { s with prec := s.prec + 1 })
    if m.uri == (← get).stack.getLast?.getD m.uri then
      modify (fun s => { s with sheet := { s.sheet with
        version := (ras.get "version").getD "4.0", defaultMode := c.defaultMode, ns := c.ns } })
    for d in decls do
      if d.m.isXsl d.i "use-package" then compileUsePackage prec d
      else if !d.m.isXsl d.i "import" then compileDecl prec d

/-- The named item types declared in a module text (`xsl:item-type`,
    `xsl:record-type` children of the root): expanded name, item type. -/
def typeDecls (uri txt : String) : List (QN × String) :=
  match Doc.ofString txt uri with
  | .error _ => []
  | .ok d =>
    let m : Mod := { d, uri }
    match m.rootElem with
    | none => []
    | some r =>
      (m.elemKids r).filterMap (fun i =>
        let as := m.rawAttrs i
        let sc := effScope (m.r i).inscope
        let resolve (s : String) : Option QN := match s.splitOn ":" with
          | [l] => some { uri := "", loc := l }
          | [p, l] => (sc.lookup p).map (fun u => { uri := u, loc := l })
          | _ => none
        if m.isXsl i "item-type" then
          match (Attrs.get as "name").bind resolve with
          | some q => some (q, (Attrs.get as "as").getD "item()*")
          | none => none
        else if m.isXsl i "record-type" then
          match (Attrs.get as "name").bind resolve with
          | some q =>
            let fields := ((m.elemKids i).filter (m.isXsl · "field")).map (fun k =>
              let fa := m.rawAttrs k
              let opt := (Attrs.get fa "select").isSome || !(m.kids k).isEmpty
              let ty := (Attrs.get fa "as").getD "item()*"
              let ty := if ty.trimAscii.toString.endsWith "?" || ty.trimAscii.toString.endsWith "*" then ty else ty
              (Attrs.get fa "name").getD "" ++ (if opt then "?" else "") ++ " as " ++ ty)
            some (q, "record(" ++ String.intercalate ", " fields ++ ")")
          | none => none
        else none)

/-- The static checks over a whole compiled package: XTSE0660 (two
    named templates of one name and precedence) and XTSE0720 (attribute
    sets that use themselves). -/
def checkSheet : CM Unit := do
    let s ← get
    let named := s.sheet.templates.toList.filterMap (fun t => t.name.map (fun n => (n, t.prec, t.id)))
    for (n, p, i) in named do
      let top := (named.filter (fun (n2, _, _) => n2 == n)).foldl (fun a (_, p2, _) => max a p2) 0
      if p == top && named.any (fun (n2, p2, i2) => n2 == n && p2 == p && i2 != i) then
        cerr "XTSE0660" ("two templates named " ++ n.show)
    let sets := s.sheet.attrSets
    for a in sets do
      if a.name.uri.startsWith "#pkg" then continue
      let mut seen : List QN := []
      let mut todo : List QN := a.useSets
      for _ in [0:1000] do
        match todo with
        | [] => break
        | x :: rest =>
          todo := rest
          if x == a.name then cerr "XTSE0720" ("attribute set " ++ a.name.show ++ " uses itself")
          -- a cycle through a used package is found when it is evaluated
          -- (XTDE0640)
          if seen.contains x || x.uri.startsWith "#pkg" then continue
          seen := x :: seen
          for b in sets do
            if b.name == x then todo := todo ++ b.useSets

/-- The modules a module text refers to (`xsl:include`, `xsl:import`),
    as absolute URIs. -/
def moduleRefs (uri txt : String) : List String :=
  match Doc.ofString txt uri with
  | .error _ => []
  | .ok d =>
    let m : Mod := { d, uri }
    (List.range d.nodes.size).filterMap (fun i =>
      if m.isXsl i "include" || m.isXsl i "import" then
        (Attrs.get (m.rawAttrs i) "href").map (resolveHref uri)
      else none)

end L4Factoidal.XSLT4
