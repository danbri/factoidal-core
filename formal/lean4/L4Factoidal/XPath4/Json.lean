/-
L4Factoidal.XPath4.Json — JSON in XPath 4.0: `fn:parse-json`,
`fn:json-doc`, `fn:json-to-xml`, `fn:xml-to-json` (F&O 4.0 §17.4, §17.5).

Spec: F&O 4.0 editor's draft, qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c (`function-catalog.xml`,
`xpath-functions.xml` §17.5 "XML representation of JSON").

The JSON text is parsed by RFC 8259 (`liberal: true` accepts the same
grammar: the spec lets an implementation decide which deviations it
accepts). A string is kept as a list of PIECES: a character, or a
codepoint that is not a permitted character (`U+0000`, an unpaired
surrogate, `U+FFFE`, `U+FFFF`) with the escape sequence that wrote it.
The permitted characters are those of XML 1.1 (`U+0001` to `U+D7FF`,
`U+E000` to `U+FFFD`, `U+10000` to `U+10FFFF`), as the tests expect. The
pieces are then rendered by the `escape` and `fallback` options.

`json-doc` reads a resource that the caller read in advance
(`Env.resources`); the evaluator does no I/O.
-/
import L4Factoidal.XPath4.XmlParse

namespace L4Factoidal.XPath4

open L4Factoidal.XML

/-! ## The JSON tree -/

inductive JPiece where
  | ch (c : Char)
  /-- A codepoint that is not a permitted character, and its escape. -/
  | bad (code : Nat) (esc : String)
deriving Inhabited, BEq

inductive JV where
  | obj (kvs : List (List JPiece × JV))
  | arr (xs : List JV)
  | str (ps : List JPiece)
  | num (lex : String)
  | bool (b : Bool)
  | null
deriving Inhabited

def jsErr {α} (msg : String) : M α := err "FOJS0001" msg

/-! ## The parser -/

def isJsonWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def skipJWs (cs : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:cs.size] do
    if j < cs.size && isJsonWs cs[j]! then j := j + 1 else break
  return j

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hex4 (cs : Array Char) (i : Nat) : Option Nat := do
  if i + 4 > cs.size then none
  let a ← hexVal? cs[i]!
  let b ← hexVal? cs[i+1]!
  let c ← hexVal? cs[i+2]!
  let d ← hexVal? cs[i+3]!
  pure (((a * 16 + b) * 16 + c) * 16 + d)

def permittedCp (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- A JSON string body from `i` (after the opening quote). -/
def parseJStr (cs : Array Char) (i : Nat) : M (List JPiece × Nat) := do
  let mut out : Array JPiece := #[]
  let mut j := i
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then jsErr "unterminated string"
    let c := cs[j]!
    if c == '"' then return (out.toList, j + 1)
    if c.toNat < 0x20 then jsErr "an unescaped control character in a string"
    if c != '\\' then
      out := out.push (.ch c); j := j + 1
    else
      if j + 1 ≥ cs.size then jsErr "unterminated escape"
      let e := cs[j+1]!
      match e with
      | '"' => out := out.push (.ch '"'); j := j + 2
      | '\\' => out := out.push (.ch '\\'); j := j + 2
      | '/' => out := out.push (.ch '/'); j := j + 2
      | 'b' => out := out.push (.ch (Char.ofNat 8)); j := j + 2
      | 'f' => out := out.push (.ch (Char.ofNat 12)); j := j + 2
      | 'n' => out := out.push (.ch '\n'); j := j + 2
      | 'r' => out := out.push (.ch '\r'); j := j + 2
      | 't' => out := out.push (.ch '\t'); j := j + 2
      | 'u' =>
        match hex4 cs (j + 2) with
        | none => jsErr "bad \\u escape"
        | some u =>
          let esc := String.ofList ((cs.extract j (j + 6)).toList)
          if 0xD800 ≤ u && u ≤ 0xDBFF then
            -- a high surrogate: paired with a following low surrogate?
            let lo := if j + 7 < cs.size && cs[j+6]! == '\\' && cs[j+7]! == 'u' then hex4 cs (j + 8) else none
            match lo with
            | some l =>
              if 0xDC00 ≤ l && l ≤ 0xDFFF then
                out := out.push (.ch (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00))))
                j := j + 12
              else out := out.push (.bad u esc); j := j + 6
            | none => out := out.push (.bad u esc); j := j + 6
          else if permittedCp u then out := out.push (.ch (Char.ofNat u)); j := j + 6
          else out := out.push (.bad u esc); j := j + 6
      | _ => jsErr ("invalid escape \\" ++ String.singleton e)
  jsErr "unterminated string"

def parseJNum (cs : Array Char) (i : Nat) : M (String × Nat) := do
  let mut j := i
  let chAt (k : Nat) : Char := if k < cs.size then cs[k]! else ' '
  if chAt j == '-' then j := j + 1
  if chAt j == '0' then j := j + 1
  else if chAt j ≥ '1' && chAt j ≤ '9' then
    for _ in [0:cs.size] do
      if chAt j ≥ '0' && chAt j ≤ '9' then j := j + 1 else break
  else jsErr "bad number"
  if chAt j == '.' then
    j := j + 1
    if !(chAt j ≥ '0' && chAt j ≤ '9') then jsErr "bad number: no digit after the point"
    for _ in [0:cs.size] do
      if chAt j ≥ '0' && chAt j ≤ '9' then j := j + 1 else break
  if chAt j == 'e' || chAt j == 'E' then
    j := j + 1
    if chAt j == '+' || chAt j == '-' then j := j + 1
    if !(chAt j ≥ '0' && chAt j ≤ '9') then jsErr "bad number: no digit in the exponent"
    for _ in [0:cs.size] do
      if chAt j ≥ '0' && chAt j ≤ '9' then j := j + 1 else break
  pure (String.ofList ((cs.extract i j).toList), j)

def litAt (cs : Array Char) (i : Nat) (s : String) : Bool :=
  s.toList.zipIdx.all (fun (c, k) => i + k < cs.size && cs[i + k]! == c)

def parseJV : Nat → Array Char → Nat → M (JV × Nat)
  | 0, _, _ => jsErr "JSON nested too deeply"
  | f + 1, cs, i => do
    let i := skipJWs cs i
    if i ≥ cs.size then jsErr "unexpected end of input"
    match cs[i]! with
    | '{' =>
      let mut j := skipJWs cs (i + 1)
      let mut kvs : Array (List JPiece × JV) := #[]
      if j < cs.size && cs[j]! == '}' then return (.obj [], j + 1)
      for _ in [0:cs.size] do
        j := skipJWs cs j
        if j ≥ cs.size || cs[j]! != '"' then jsErr "expected a string key"
        let (k, j2) ← parseJStr cs (j + 1)
        let j3 := skipJWs cs j2
        if j3 ≥ cs.size || cs[j3]! != ':' then jsErr "expected ':'"
        let (v, j4) ← parseJV f cs (j3 + 1)
        kvs := kvs.push (k, v)
        let j5 := skipJWs cs j4
        if j5 < cs.size && cs[j5]! == ',' then j := j5 + 1
        else if j5 < cs.size && cs[j5]! == '}' then return (.obj kvs.toList, j5 + 1)
        else jsErr "expected ',' or '}'"
      jsErr "unterminated object"
    | '[' =>
      let mut j := skipJWs cs (i + 1)
      let mut xs : Array JV := #[]
      if j < cs.size && cs[j]! == ']' then return (.arr [], j + 1)
      for _ in [0:cs.size] do
        let (v, j2) ← parseJV f cs j
        xs := xs.push v
        let j3 := skipJWs cs j2
        if j3 < cs.size && cs[j3]! == ',' then j := j3 + 1
        else if j3 < cs.size && cs[j3]! == ']' then return (.arr xs.toList, j3 + 1)
        else jsErr "expected ',' or ']'"
      jsErr "unterminated array"
    | '"' => let (s, j) ← parseJStr cs (i + 1); pure (.str s, j)
    | 't' => if litAt cs i "true" then pure (.bool true, i + 4) else jsErr "bad literal"
    | 'f' => if litAt cs i "false" then pure (.bool false, i + 5) else jsErr "bad literal"
    | 'n' => if litAt cs i "null" then pure (.null, i + 4) else jsErr "bad literal"
    | c =>
      if c == '-' || c.isDigit then let (n, j) ← parseJNum cs i; pure (.num n, j)
      else jsErr ("unexpected character " ++ String.singleton c)

def parseJsonText (s : String) : M JV := do
  let s := if s.startsWith "﻿" then (s.drop 1).toString else s
  let cs := s.toList.toArray
  let (v, j) ← parseJV 10000 cs 0
  if skipJWs cs j < cs.size then jsErr "text after the JSON value"
  pure v

/-! ## Options and rendering of strings -/

def hexUpper4 (n : Nat) : String :=
  let ds := "0123456789ABCDEF".toList
  String.ofList ((List.range 4).reverse.map (fun k => ds.getD ((n / 16 ^ k) % 16) '0'))

/-- The escaped form of a special character (§17.4.4 `escape: true`). -/
def escChar (c : Char) : String :=
  let n := c.toNat
  if c == '\\' then "\\\\"
  else if n == 8 then "\\b" else if n == 12 then "\\f" else if n == 10 then "\\n"
  else if n == 13 then "\\r" else if n == 9 then "\\t"
  else if n < 0x20 || (0x7F ≤ n && n ≤ 0x9F) then "\\u" ++ hexUpper4 n
  else String.singleton c

structure JOpts where
  escape : Bool := false
  fallback : Option Item := none
  dups : String := "use-first"
  numFmt : String := "double"
  null : Seq := []
  numParser : Option Item := none
  ordered : Bool := true

def optBoolT (opts : Seq) (key : String) (dflt : Bool) : M Bool :=
  match optLookup opts key with
  | none => pure dflt
  | some [.atom ⟨_, .bool b⟩] => pure b
  | some _ => err "XPTY0004" ("option " ++ key ++ " must be a single xs:boolean")

def optFn (opts : Seq) (key : String) : M (Option Item) :=
  match optLookup opts key with
  | none => pure none
  | some [] => pure none
  | some [f@(.fn fi)] => if fi.arity == 1 then pure (some f) else err "XPTY0004" ("option " ++ key ++ " must be a function of arity 1")
  | some [f@(.map _)] => pure (some f)
  | some [f@(.arr _)] => pure (some f)
  | some _ => err "XPTY0004" ("option " ++ key ++ " must be a function")

def jsonOpts (opts : Seq) (dupDefault : String) (dupsAllowed : List String) : M JOpts := do
  match opts with
  | [] | [.map _] => pure ()
  | _ => err "XPTY0004" "options must be a map"
  let _ ← optBoolT opts "liberal" false
  let escape ← optBoolT opts "escape" false
  let fallback ← optFn opts "fallback"
  if escape && fallback.isSome then err "FOJS0005" "fallback is not allowed with escape: true"
  let dups ← match optLookup opts "duplicates" with
    | none => pure dupDefault
    | some [.atom a] =>
      if a.isStringLike then
        if dupsAllowed.contains a.str then pure a.str else err "FOJS0005" ("invalid duplicates option " ++ a.str)
      else err "XPTY0004" "duplicates must be a string"
    | some _ => err "XPTY0004" "duplicates must be a string"
  let numFmt ← match optLookup opts "number-format" with
    | none => pure "double"
    | some [.atom a] =>
      if ["double", "decimal", "adaptive"].contains a.str then pure a.str
      else err "XPTY0004" ("invalid number-format " ++ a.str)
    | some _ => err "XPTY0004" "number-format must be a string"
  let null := (optLookup opts "null").getD []
  if null.length > 1 then err "XPTY0004" "the null option must be at most one item"
  let numParser ← optFn opts "number-parser"
  let ordered ← optBoolT opts "retain-order" true
  pure { escape, fallback, dups, numFmt, null, numParser, ordered }

/-- Render string pieces. -/
def renderPieces (h : Hooks) (e : Env) (o : JOpts) (ps : List JPiece) : M String := do
  let mut out := ""
  for p in ps do
    match p with
    | .ch c => out := out ++ (if o.escape then escChar c else String.singleton c)
    | .bad code esc =>
      if o.escape then out := out ++ "\\u" ++ hexUpper4 code
      else
        match o.fallback with
        | none => out := out.push (Char.ofNat 0xFFFD)
        | some f =>
          let r ← h.call f [sStr esc]
          match ← e.atomize r with
          | [a] => out := out ++ a.str
          | _ => err "XPTY0004" "the fallback function must return one atomic value"
  pure out

/-! ## fn:parse-json -/

def jsonNumber (o : JOpts) (lex : String) : M Atomic := do
  let hasExp := lex.any (fun c => c == 'e' || c == 'E')
  let toDecOrInt : M Atomic := do
    let d ← castFromString lex (.b .decimal)
    match d.v with
    | .dec x => if (L4Factoidal.XSD.Dec.norm x).scale == 0 then pure (Atomic.ofInt (L4Factoidal.XSD.Dec.norm x).mantissa) else pure d
    | _ => pure d
  match o.numFmt with
  | "decimal" =>
    if hasExp then
      let x ← castFromString lex (.b .double)
      castAtomic x (.b .decimal)
    else toDecOrInt
  | "adaptive" => if hasExp then castFromString lex (.b .double) else toDecOrInt
  | _ => castFromString lex (.b .double)

def jvToXdm (h : Hooks) (e : Env) (o : JOpts) : Nat → JV → M Seq
  | 0, _ => err "FOJS0001" "JSON nested too deeply"
  | f + 1, v =>
    match v with
    | .null => pure o.null
    | .bool b => pure (sBool b)
    | .num lex => do pure (single (← jsonNumber o lex))
    | .str ps => do pure (sStr (← renderPieces h e o ps))
    | .arr xs => do
      let ms ← xs.mapM (jvToXdm h e o f)
      pure [.arr ms]
    | .obj kvs => do
      let mut acc : Array (Atomic × Seq) := #[]
      let mut seen : Std.HashSet String := {}
      for (k, v) in kvs do
        let ks ← renderPieces h e o k
        if seen.contains ks then
          match o.dups with
          | "reject" => err "FOJS0003" ("duplicate key " ++ ks)
          | "use-last" =>
            let val ← jvToXdm h e o f v
            acc := acc.map (fun (a, s) => if a.str == ks then (a, val) else (a, s))
          | _ => pure ()
        else
          seen := seen.insert ks
          acc := acc.push (Atomic.ofStr ks, ← jvToXdm h e o f v)
      pure [.map acc.toList]

def parseJsonFn (h : Hooks) (e : Env) (src : String) (opts : Seq) : M Seq := do
  checkOptionKeys opts ["liberal", "duplicates", "escape", "fallback", "null", "number-format"]
  let o ← jsonOpts opts "use-first" ["reject", "use-first", "use-last"]
  let v ← parseJsonText src
  jvToXdm h e o 100000 v

/-! ## fn:json-to-xml -/

def jattr (n v : String) : Attribute := { name := n, value := v }

def jvToXml (h : Hooks) (e : Env) (o : JOpts) (key : Option (String × Bool)) : Nat → JV → M Node
  | 0, _ => err "FOJS0001" "JSON nested too deeply"
  | f + 1, v => do
    let keyAts : List Attribute := match key with
      | some (k, esc) => [jattr "key" k] ++ (if esc then [jattr "escaped-key" "true"] else [])
      | none => []
    match v with
    | .null => pure (.element "null" keyAts [])
    | .bool b => pure (.element "boolean" keyAts [.text (if b then "true" else "false")])
    | .num lex =>
      let txt ← match o.numParser with
        | none => pure lex
        | some p => do
          let r ← h.call p [single (Atomic.untypedOf lex)]
          pure (String.intercalate " " ((← e.atomize r).map (·.str)))
      pure (.element "number" keyAts [.text txt])
    | .str ps =>
      let s ← renderPieces h e o ps
      let ats := keyAts ++ (if o.escape && (s.splitOn "\\").length > 1 then [jattr "escaped" "true"] else [])
      pure (.element "string" ats (if s == "" then [] else [.text s]))
    | .arr xs =>
      let kids ← xs.mapM (jvToXml h e o none f)
      pure (.element "array" keyAts kids)
    | .obj kvs =>
      let mut kids : Array Node := #[]
      let mut seen : Std.HashSet String := {}
      for (k, v) in kvs do
        let ks ← renderPieces h e o k
        let plain ← renderPieces h e { o with escape := false, fallback := none } k
        if seen.contains plain then
          match o.dups with
          | "reject" => err "FOJS0003" ("duplicate key " ++ ks)
          | "use-first" => continue
          | _ => pure ()
        seen := seen.insert plain
        kids := kids.push (← jvToXml h e o (some (ks, o.escape && (ks.splitOn "\\").length > 1)) f v)
      pure (.element "map" keyAts kids.toList)

def addFnNs : Node → Node
  | .element t ats kids => .element t (jattr "xmlns" nsFN :: ats) kids
  | n => n

def jsonToXmlFn (h : Hooks) (e : Env) (src : String) (opts : Seq) : M Seq := do
  checkOptionKeys opts ["liberal", "duplicates", "validate", "escape", "fallback", "number-parser"]
  if (← optBoolT opts "validate" false) then err "FOJS0004" "this processor is not schema-aware"
  let o ← jsonOpts opts "retain" ["reject", "use-first", "retain"]
  let v ← parseJsonText src
  let root ← jvToXml h e o none 100000 v
  let doc := { Doc.ofNodes [addFnNs root] with baseUri := e.baseUri }
  pure [doc.rootItem (runtimeDocId "json-to-xml" (src ++ toString o.escape ++ o.dups))]

/-! ## fn:xml-to-json -/

def x2jErr {α} (msg : String) : M α := err "FOJS0006" msg

def jsonEscPlain (solidus : Bool) (s : String) : String :=
  String.join (s.toList.map (fun c =>
    let n := c.toNat
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if n == 8 then "\\b"
    else if n == 12 then "\\f" else if n == 10 then "\\n" else if n == 13 then "\\r"
    else if n == 9 then "\\t" else if c == '/' && solidus then "\\/"
    else if (1 ≤ n && n ≤ 31) || (127 ≤ n && n ≤ 159) then "\\u" ++ hexUpper4 n
    else String.singleton c))

/-- A string already escaped (`escaped="true"`): check the escapes, escape
    the rest. -/
def jsonEscEscaped (solidus : Bool) (s : String) : M String := do
  let cs := s.toList.toArray
  let mut out := ""
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '\\' then
      if i + 1 ≥ cs.size then err "FOJS0007" "a backslash at the end of an escaped string"
      let d := cs[i+1]!
      if "\"\\/bfnrt".toList.contains d then out := out ++ String.ofList [c, d]; i := i + 2
      else if d == 'u' then
        match hex4 cs (i + 2) with
        | some _ => out := out ++ String.ofList ((cs.extract i (i + 6)).toList); i := i + 6
        | none => err "FOJS0007" "invalid \\u escape"
      else err "FOJS0007" ("invalid escape \\" ++ String.singleton d)
    else
      out := out ++ (if c == '\\' then "\\\\" else jsonEscPlain solidus (String.singleton c))
      i := i + 1
  pure out

/-- Unescape a JSON-escaped key (for the duplicate check). -/
def jsonUnescape (s : String) : String :=
  match parseJsonText ("\"" ++ s ++ "\"") with
  | .ok (.str ps) => String.ofList (ps.map (fun p => match p with | .ch c => c | .bad _ _ => '�'))
  | _ => s

def isXmlWsStr (s : String) : Bool := s.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')

/-- The JSON form of an `xs:double` lexical value (§17.5.?? rules for
    `number`). -/
def jsonNumberOut (s : String) : M String := do
  let t := s.trim
  match castFromString t (.b .double) with
  | .ok a =>
    match a.v with
    | .dbl f => if f.isNaN || f.isInf then x2jErr ("not a JSON number: " ++ t) else pure ()
    | _ => pure ()
  | .error _ => x2jErr ("not a number: " ++ t)
  if t.toList.any Char.isAlpha && !(t.toList.all (fun c => c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-')) then
    x2jErr ("not a JSON number: " ++ t)
  let cs := t.toList
  let (sign, cs) := match cs with
    | '+' :: r => ("", r)
    | '-' :: r => ("-", r)
    | r => ("", r)
  let mant := cs.takeWhile (fun c => c != 'e' && c != 'E')
  let expo := cs.drop mant.length
  let ip := mant.takeWhile (· != '.')
  let fp := mant.drop ip.length
  let ip := let z := ip.dropWhile (· == '0'); if z.isEmpty then ['0'] else z
  let fp := if fp == ['.'] then ['.', '0'] else fp
  pure (sign ++ String.ofList ip ++ String.ofList fp ++ String.ofList expo)

def x2j (e : Env) (solidus indent : Bool) : Nat → Nat → NodeRef → Bool → M String
  | 0, _, _, _ => x2jErr "too deep"
  | f + 1, depth, n, inMap => do
    let r := e.nrec n
    if r.kind != .element then x2jErr "expected an element"
    if r.name.uri != nsFN then x2jErr ("element not in the fn namespace: " ++ r.name.loc)
    let ats := r.attrs.toList.map (fun a => e.nrec (n.at a))
    let attrV (l : String) := (ats.find? (fun a => a.name.uri == "" && a.name.loc == l)).map (·.value)
    -- allowed attributes
    for a in ats do
      if a.name.uri == "" || a.name.uri == nsFN then
        let ok := (a.name.uri == "" && ((inMap && (a.name.loc == "key" || a.name.loc == "escaped-key")) ||
          (r.name.loc == "string" && a.name.loc == "escaped")))
        if !ok then x2jErr ("attribute not allowed: " ++ a.name.loc)
        if a.name.loc == "escaped" || a.name.loc == "escaped-key" then
          let v := a.value.trim
          if !["true", "false", "1", "0"].contains v then x2jErr "escaped must be a boolean"
    if inMap && (attrV "key").isNone then x2jErr "a child of map needs a key"
    let kids := r.children.toList.map (fun c => n.at c)
    let elems := kids.filter (fun c => (e.nrec c).kind == .element)
    let texts := kids.filter (fun c => (e.nrec c).kind == .text)
    let nl (d : Nat) := if indent then "\n" ++ String.ofList (List.replicate (2 * d) ' ') else ""
    match r.name.loc with
    | "null" =>
      if !elems.isEmpty || texts.any (fun t => !isXmlWsStr (e.nrec t).value) then x2jErr "null must be empty"
      pure "null"
    | "boolean" =>
      if !elems.isEmpty then x2jErr "boolean has element content"
      let v := (e.nodeString n).trim
      if v == "true" || v == "1" then pure "true"
      else if v == "false" || v == "0" then pure "false"
      else x2jErr ("not a boolean: " ++ v)
    | "number" =>
      if !elems.isEmpty then x2jErr "number has element content"
      jsonNumberOut (e.nodeString n)
    | "string" =>
      if !elems.isEmpty then x2jErr "string has element content"
      let s := e.nodeString n
      let esc := match attrV "escaped" with | some v => v.trim == "true" || v.trim == "1" | none => false
      let body ← if esc then jsonEscEscaped solidus s else pure (jsonEscPlain solidus s)
      pure ("\"" ++ body ++ "\"")
    | "array" =>
      if texts.any (fun t => !isXmlWsStr (e.nrec t).value) then x2jErr "text in an array"
      let parts ← elems.mapM (fun c => x2j e solidus indent f (depth + 1) c false)
      if parts.isEmpty then pure "[]" else
      pure ("[" ++ String.intercalate "," (parts.map (fun p => nl (depth + 1) ++ p)) ++ nl depth ++ "]")
    | "map" =>
      if texts.any (fun t => !isXmlWsStr (e.nrec t).value) then x2jErr "text in a map"
      let mut seen : Std.HashSet String := {}
      let mut parts : Array String := #[]
      for c in elems do
        let cr := e.nrec c
        let cats := cr.attrs.toList.map (fun a => e.nrec (c.at a))
        let keyV := ((cats.find? (fun a => a.name.uri == "" && a.name.loc == "key")).map (·.value)).getD ""
        let escK := match (cats.find? (fun a => a.name.uri == "" && a.name.loc == "escaped-key")).map (·.value) with
          | some v => v.trim == "true" || v.trim == "1"
          | none => false
        let norm := if escK then jsonUnescape keyV else keyV
        if seen.contains norm then x2jErr ("duplicate key " ++ norm)
        seen := seen.insert norm
        let kOut ← if escK then jsonEscEscaped solidus keyV else pure (jsonEscPlain solidus keyV)
        let v ← x2j e solidus indent f (depth + 1) c true
        parts := parts.push (nl (depth + 1) ++ "\"" ++ kOut ++ "\":" ++ (if indent then " " else "") ++ v)
      if parts.isEmpty then pure "{}" else
      pure ("{" ++ String.intercalate "," parts.toList ++ nl depth ++ "}")
    | other => x2jErr ("unknown element " ++ other)

def xmlToJsonFn (e : Env) (n : NodeRef) (opts : Seq) : M Seq := do
  checkOptionKeys opts ["indent", "escape-solidus"]
  let indent ← optBoolT opts "indent" false
  let solidus ← optBoolT opts "escape-solidus" true
  let r := e.nrec n
  let top ← match r.kind with
    | .element => pure n
    | .document =>
      let kids := r.children.toList.map (fun c => n.at c)
      let elems := kids.filter (fun c => (e.nrec c).kind == .element)
      if kids.any (fun c => (e.nrec c).kind == .text) then x2jErr "text in the document node"
      match elems with
      | [x] => pure x
      | _ => x2jErr "a document node must have exactly one element child"
    | _ => x2jErr "expected a document or element node"
  -- the outermost element may have a key attribute (ignored)
  let ats := (e.nrec top).attrs.toList.map (fun a => e.nrec (top.at a))
  let hasKey := ats.any (fun a => a.name.uri == "" && (a.name.loc == "key" || a.name.loc == "escaped-key"))
  pure (sStr (← x2j e solidus indent 100000 0 top hasKey))

/-! ## The table -/

def jsonTable : List (String × LibFn) := [
  ent "parse-json" (fun h e a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some s => parseJsonFn h e s.str (argN a 1)),
  ent "json-doc" (fun h e a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some u =>
      let txt ← textResource e u.str
      parseJsonFn h e txt (argN a 1)),
  ent "json-to-xml" (fun h e a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some s => jsonToXmlFn h e s.str (argN a 1)),
  ent "xml-to-json" (fun _ e a => do
    match argN a 0 with
    | [] => pure []
    | [.node n] => xmlToJsonFn e n (argN a 1)
    | _ => x2jErr "expected a node")
]

#guard (match parseJsonText "{\"a\": [1, true, null, \"x\\u0041\"]}" with | .ok _ => true | .error _ => false)
#guard (match parseJsonText "[1,]" with | .ok _ => false | .error e => e.code == "FOJS0001")

end L4Factoidal.XPath4
