/-
L4Factoidal.XPath4.Uri — `fn:parse-uri` and `fn:build-uri` (F&O 4.0
§7.6), with the record `fn:uri-structure-record` (§7.6.1).

Spec: F&O 4.0 editor's draft, qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c, `function-catalog.xml`.

`fn:parse-uri` is the series of string transformations of the
specification, in the order given there: backslashes to slashes, the
fragment, the query, the scheme, the `file:` and drive-letter rules, the
hierarchical test, the authority, and the decoded path segments and query
parameters. The regular expressions of the text are written as direct
string operations. `fn:build-uri` is the inverse, with the three
encoding sets of the text (path segment, query parameter, fragment).
A plus sign is decoded as a space in query parameters only.
-/
import L4Factoidal.XPath4.XmlParse

namespace L4Factoidal.XPath4

/-! ## Decoding and encoding -/

/-- Percent-decoding (`fn:decode-from-uri`); `plus` also turns `+` into a space. -/
def uriDecode (plus : Bool) (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let n := cs.size
  let mut bytes : Array Nat := #[]
  let mut i := 0
  while i < n do
    let c := cs[i]!
    if c == '%' then
      match (cs[i + 1]?).bind hexDigitVal?, (cs[i + 2]?).bind hexDigitVal? with
      | some x, some y => bytes := bytes.push (x * 16 + y); i := i + 3
      | _, _ => bytes := bytes.push 0xFF; i := i + 1
    else if c == '+' && plus then
      bytes := bytes.push 32; i := i + 1
    else
      for b in Fn.String.utf8Bytes c do bytes := bytes.push b
      i := i + 1
  let l := bytes.toList
  pure (String.ofList (utf8Decode (l.length + 1) l))

/-- Percent-encode control characters and the characters of `set`. -/
def uriEncodeSet (set : String) (s : String) : String :=
  Fn.String.pctEncodeWith (fun c => !(c.toNat < 0x20 || set.contains c)) s

def pathSegSet : String := " %/?#[]"
def queryParamSet : String := " %=&#+[]"
def fragmentSet : String := " %#[]"

/-! ## Scheme knowledge -/

def nonHierarchicalSchemes : List String := ["jar", "mailto", "news", "tag", "tel", "urn"]
def hierarchicalSchemes : List String := ["http", "https", "ftp", "file", "ssh", "ldap", "ldaps", "telnet", "sftp", "ws", "wss"]

def defaultPort : String → Option Nat
  | "http" => some 80
  | "https" => some 443
  | "ftp" => some 21
  | "ssh" => some 22
  | _ => none

/-! ## Splitting helpers -/

def dropS (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- Split at the first occurrence of `c`: the text before, and the text after. -/
def splitFirst (c : Char) (s : String) : String × Option String :=
  let cs := s.toList
  let pre := cs.takeWhile (· != c)
  if pre.length == cs.length then (s, none)
  else (String.ofList pre, some (String.ofList (cs.drop (pre.length + 1))))

def isSchemeStart (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def isSchemeChar (c : Char) : Bool :=
  isSchemeStart c || ('0' ≤ c && c ≤ '9') || c == '+' || c == '-' || c == '.'

/-- `^([a-zA-Z][A-Za-z0-9+\-.]+):(.*)$` -/
def splitScheme (s : String) : Option String × String :=
  let cs := s.toList
  let pre := cs.takeWhile (· != ':')
  if pre.length < cs.length && pre.length ≥ 2 && isSchemeStart pre.head! && pre.all isSchemeChar then
    (some (String.ofList pre), String.ofList (cs.drop (pre.length + 1)))
  else (none, s)

def nonEmpty (s : String) : Option String := if s == "" then none else some s

def isDigits (s : String) : Bool := s != "" && s.toList.all Char.isDigit

/-- The authority: userinfo, host, port (not decoded). -/
def splitAuthority (auth : String) (allowDep omitPorts : Bool) (scheme : Option String) :
    M (Option String × Option String × Option Int) := do
  let (userinfo, hostport) :=
    match splitFirst '@' auth with
    | (u, some rest) =>
      let (_, pw) := splitFirst ':' u
      let u' := if (pw.getD "") != "" && !allowDep then none else nonEmpty u
      (u', rest)
    | (_, none) => (none, auth)
  let (host, portS) ← do
    if hostport.startsWith "[" then
      let cs := hostport.toList
      let pre := cs.takeWhile (· != ']')
      if pre.length == cs.length then err "FOUR0001" "unmatched [ in the authority"
      else
        let host := String.ofList (pre ++ [']'])
        let rest := String.ofList (cs.drop (pre.length + 1))
        if rest == "" then pure (some host, none)
        else if rest.startsWith ":" then pure (some host, nonEmpty (dropS rest 1))
        else err "FOUR0001" "junk after the IPv6 address"
    else
      match hostport.splitOn ":" with
      | [h] => pure (nonEmpty h, none)
      | [h, p] => if h == "" then pure (none, none) else pure (some h, nonEmpty p)
      | _ => pure (none, none)
  let port : Option Int := match portS with
    | some p => if isDigits p then some (Int.ofNat p.toNat!) else none
    | none => none
  let port := if omitPorts then
      match scheme, port with
      | some sc, some p => if (defaultPort sc.toLower) == some p.toNat then none else port
      | _, _ => port
    else port
  pure (userinfo, host, port)

/-! ## fn:parse-uri -/

def parseUriOptionNames : List String := ["allow-deprecated-features", "omit-default-ports", "unc-path"]

def strSeq (o : Option String) : Seq := match o with | some s => sStr s | none => []

def uriRecord (uri : String) (scheme : Option String) (absolute hier : Option Bool)
    (authority userinfo host : Option String) (port : Option Int)
    (path query fragment : Option String)
    (segs : Option (List String)) (params : Option (List (String × List String)))
    (filepath : Option String) : Seq :=
  let b (o : Option Bool) : Seq := match o with | some v => sBool v | none => []
  [.map [
    (Atomic.ofStr "uri", sStr uri),
    (Atomic.ofStr "scheme", strSeq scheme),
    (Atomic.ofStr "absolute", b absolute),
    (Atomic.ofStr "hierarchical", b hier),
    (Atomic.ofStr "authority", strSeq authority),
    (Atomic.ofStr "userinfo", strSeq userinfo),
    (Atomic.ofStr "host", strSeq host),
    (Atomic.ofStr "port", match port with | some p => sInt p | none => []),
    (Atomic.ofStr "path", strSeq path),
    (Atomic.ofStr "query", strSeq query),
    (Atomic.ofStr "fragment", strSeq fragment),
    (Atomic.ofStr "path-segments", match segs with
      | some l => l.map (fun x => Item.atom (Atomic.ofStr x))
      | none => []),
    (Atomic.ofStr "query-parameters", match params with
      | some ps => [.map (ps.map (fun (k, vs) => (Atomic.ofStr k, vs.map (fun x => Item.atom (Atomic.ofStr x)))))]
      | none => []),
    (Atomic.ofStr "filepath", strSeq filepath)]]

/-- Query parameters: tokens on `&`, key and value form-decoded; a repeated
    key collects its values in order. -/
def queryParams (q : String) : List (String × List String) :=
  q.splitOn "&" |>.foldl (fun acc tok =>
    let (k, v) := match splitFirst '=' tok with
      | (k, some v) => (uriDecode true k, uriDecode true v)
      | (_, none) => ("", uriDecode true tok)
    if acc.any (·.1 == k) then acc.map (fun (k2, vs) => if k2 == k then (k2, vs ++ [v]) else (k2, vs))
    else acc ++ [(k, [v])]) []

/-- Leading slashes of a character list. -/
def slashCount (s : String) : Nat := (s.toList.takeWhile (· == '/')).length

def parseUri (value : String) (allowDep omitPorts unc : Bool) : M Seq := do
  let s0 := value.replace "\\" "/"
  let (s1, frag) := splitFirst '#' s0
  let fragment := frag.bind (fun f => nonEmpty (uriDecode false f))
  let (s2, q) := splitFirst '?' s1
  let query := q.bind nonEmpty
  let (scheme0, s3) := splitScheme s2
  let absolute0 := scheme0.isSome && fragment.isNone
  -- file and drive-letter rules
  let isFileOrNone := match scheme0 with | none => true | some sc => sc.toLower == "file"
  let k3 := slashCount s3
  let rest3 := dropS s3 k3
  let driveRest : Option String :=
    match rest3.toList with
    | a :: b :: tl => if isSchemeStart a && (b == ':' || b == '|') then some (String.ofList (a :: ':' :: tl)) else none
    | _ => none
  let (scheme, s4) : Option String × String :=
    if !isFileOrNone then (scheme0, s3)
    else match driveRest with
      | some d => (some "file", "/" ++ d)
      | none => if scheme0.isNone && unc then (some "file", s3) else (scheme0, s3)
  let lower := scheme.map String.toLower
  let hier : Option Bool :=
    match lower with
    | some l =>
      if nonHierarchicalSchemes.contains l then some false
      else if hierarchicalSchemes.contains l then some true
      else if s4 == "" then none else some (s4.startsWith "/")
    | none => if s4 == "" then none else some (s4.startsWith "/")
  let absolute := if hier == some false then none else if absolute0 then some true else none
  -- the remaining components
  let (authority, str, filepath0) : Option String × String × Option String :=
    if lower == some "file" then
      let k := slashCount s4
      let r := dropS s4 k
      if unc && k ≥ 2 && r != "" then
        let g := "//" ++ r
        (none, g, some g)
      else
        let isDrive := match r.toList with
          | a :: ':' :: '/' :: _ => isSchemeStart a
          | _ => false
        if isDrive then (none, "/" ++ r, some r)
        else
          let t := if k > 0 then "/" ++ r else r
          (none, t, some t)
    else if hier == some true && s4.startsWith "//" then
      let r := dropS s4 2
      let pre := r.toList.takeWhile (· != '/')
      if pre.length == r.length then
        if r == "" then (none, s4, none) else (some r, "", none)
      else (nonEmpty (String.ofList pre), String.ofList (r.toList.drop pre.length), none)
    else (none, s4, none)
  let (userinfo, host, port) ← match authority with
    | some a => splitAuthority a allowDep omitPorts scheme
    | none => pure (none, none, none)
  let path := nonEmpty str
  let filepathRaw : Option String :=
    if lower == some "file" then filepath0
    else if scheme.isNone then path
    else none
  let filepath := filepathRaw.bind (fun f => nonEmpty (uriDecode false f))
  let segs := path.map (fun p => (p.splitOn "/").map (uriDecode false))
  let params := query.map queryParams
  pure (uriRecord value scheme absolute hier authority userinfo host port path query fragment segs params filepath)

def parseUriFn : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    let opts := argN a 1
    checkOptionKeys opts parseUriOptionNames
    let dep ← optBool opts "allow-deprecated-features" false
    let omitP ← optBool opts "omit-default-ports" false
    let unc ← optBool opts "unc-path" false
    parseUri v.str dep omitP unc

/-! ## fn:build-uri -/

def buildUri (parts : List (Atomic × Seq)) (allowDep omitPorts unc : Bool) : M String := do
  let fld (k : String) : Option Seq := match mapGet parts (Atomic.ofStr k) with
    | some [] => none
    | r => r
  let fstr (k : String) : Option String :=
    (fld k).bind (fun s => match optAtom s with | some x => nonEmpty x.str | none => none)
  let scheme := fstr "scheme"
  let lower := scheme.map String.toLower
  let hierFalse := match fld "hierarchical" with
    | some [.atom ⟨_, .bool false⟩] => true
    | _ => false
  let nonHier := hierFalse || (match lower with | some l => nonHierarchicalSchemes.contains l | none => false)
  let mut out := ""
  if let some sc := scheme then
    out := sc ++ (if nonHier then ":" else if lower == some "file" && unc then ":////" else "://")
  let mut userinfo := fstr "userinfo"
  let host := fstr "host"
  let mut port : Option String := (fld "port").bind (fun s => match optAtom s with | some x => some x.str | none => none)
  if let some u := userinfo then
    let (_, pw) := splitFirst ':' u
    if (pw.getD "") != "" && !allowDep then userinfo := none
  if omitPorts then
    match lower.bind defaultPort, port with
    | some d, some p => if p == toString d then port := none
    | _, _ => pure ()
  if userinfo.isSome || host.isSome || port.isSome then
    out := out ++ (match userinfo with | some u => u ++ "@" | none => "") ++ host.getD ""
      ++ (match port with | some p => ":" ++ p | none => "")
  else if let some a := fstr "authority" then
    out := out ++ a
  -- the path
  match fld "path-segments" with
  | some segs =>
    let ss := segs.filterMap (fun i => match i with | .atom x => some x.str | _ => none)
    let ss := if nonHier then ss else ss.map (uriEncodeSet pathSegSet)
    out := out ++ String.intercalate "/" ss
  | none => out := out ++ (fstr "path").getD ""
  -- the query
  let mut query : Option String := none
  match fld "query-parameters" with
  | some [.map kvs] =>
    let toks := kvs.flatMap (fun (k, vs) =>
      vs.filterMap (fun i => match i with
        | .atom x => some (if k.str == "" then uriEncodeSet queryParamSet x.str
                           else uriEncodeSet queryParamSet k.str ++ "=" ++ uriEncodeSet queryParamSet x.str)
        | _ => none))
    query := nonEmpty (String.intercalate "&" toks)
  | _ => query := fstr "query"
  if let some q := query then out := out ++ "?" ++ q
  if let some f := fstr "fragment" then out := out ++ "#" ++ uriEncodeSet fragmentSet f
  pure out

def buildUriFn : LibFn := fun _ _ a => do
  let parts ← asMap (argN a 0)
  let opts := argN a 1
  checkOptionKeys opts parseUriOptionNames
  let dep ← optBool opts "allow-deprecated-features" false
  let omitP ← optBool opts "omit-default-ports" false
  let unc ← optBool opts "unc-path" false
  pure (sStr (← buildUri parts dep omitP unc))

def uriTable : List (String × LibFn) := [
  ent "parse-uri" parseUriFn,
  ent "build-uri" buildUriFn
]

end L4Factoidal.XPath4
