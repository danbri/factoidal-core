import L4Factoidal.JSON.Parser
import L4Factoidal.WHATWG.URL.Parser

/-! Inline document import maps (HTML §8.1.5.2). The resolver returns a URL or a refusal.
The module loader still applies its fetch, CORS and response checks to every URL. -/
namespace L4Factoidal.WasmVM.Hosts.ImportMap

open L4Factoidal.WHATWG

abbrev Specifiers := List (String × Option String)

structure Map where
  imports : Specifiers := []
  scopes : List (String × Specifiers) := []
  integrity : List (String × String) := []
  deriving Inhabited

/-- Resolve a URL-like specifier. A bare name is left for import-map lookup. -/
def urlLike (specifier base : String) : Option URL.Url :=
  if specifier.startsWith "/" || specifier.startsWith "./" || specifier.startsWith "../" then
    URL.parseUrl specifier (some base)
  else URL.parseUrl specifier none

private def jsonObject : JSON.Json → Option (List (String × JSON.Json))
  | .object fields => some fields
  | _ => none

private def objectSection (fields : List (String × JSON.Json)) (name : String) :
    Option (List (String × JSON.Json)) :=
  match fields.reverse.find? (·.1 == name) with
  | none => some []
  | some (_, value) => jsonObject value

/-- The last JSON member that normalises to a key takes precedence within one map. -/
private def specifiers (base : String) (fields : List (String × JSON.Json)) : Specifiers :=
  fields.foldl (fun out (key, json) =>
    if key.isEmpty then out else
      let key := ((urlLike key base).map (·.serialize)).getD key
      let value := json.asString?.bind (fun text => (urlLike text base).map (·.serialize))
      let value := value.filter (fun target => !key.endsWith "/" || target.endsWith "/")
      (key, value) :: out) []

/-- Input limits keep nested JSON and the normalisation work bounded on wasm32.
The JSON fuel also limits the number of siblings. A map beyond either limit is refused. -/
def maxBytes : Nat := 65536
def jsonFuel : Nat := 512

private def parseFields (base : String) (root : JSON.Json) : Option Map := do
  let fields ← jsonObject root
  let imports ← objectSection fields "imports"
  let scopes ← objectSection fields "scopes"
  let scopes ← scopes.foldlM (fun out (scope, value) => do
    let rules ← jsonObject value
    match URL.parseUrl scope (some base) with
    | none => return out
    | some url =>
      let key := url.serialize
      return (key, specifiers base rules) :: out.filter (·.1 != key)) []
  let integrity ← objectSection fields "integrity"
  let integrity := integrity.reverse.filterMap fun (key, value) => do
    let url ← urlLike key base
    let metadata ← value.asString?
    return (url.serialize, metadata)
  return { imports := specifiers base imports, scopes, integrity }

/-- Registration accepts a complete JSON object. A malformed map has no effect. -/
def parse (source base : String) : Option Map := do
  if source.utf8ByteSize > maxBytes then none else do
    let chars := JSON.charsOfString source
    let (root, pos) ← (JSON.parseValueR chars 0 jsonFuel).toOption
    if JSON.skipWs chars pos (chars.size + 1) < chars.size then none
    else parseFields base root

/-- New maps may add keys to a scope. Entries from an earlier map win on duplicate keys.
Lookup visits rules in order when two matches have the same key. -/
def Map.merge (old new : Map) : Map :=
  { imports := old.imports ++ new.imports, scopes := old.scopes ++ new.scopes,
    integrity := old.integrity ++ new.integrity }

private def keyMatches (specifier key : String) (prefixes : Bool) : Bool :=
  specifier == key || (prefixes && key.endsWith "/" && specifier.startsWith key)

private def bestRule (rules : Specifiers) (key : String) (prefixes : Bool) :
    Option (String × Option String) :=
  rules.foldl (fun best rule =>
    if keyMatches key rule.1 prefixes && (best.all fun current => current.1.utf8ByteSize < rule.1.utf8ByteSize)
    then some rule else best) none

private def applyRule (specifier : String) (rule : String × Option String) : Option String :=
  rule.2.bind fun target =>
    if specifier == rule.1 then some target else
      let suffix := (specifier.drop rule.1.length).toString
      (URL.parseUrl suffix (some target)).map (·.serialize) |>.filter (·.startsWith target)

private def scopeMatches (base scope : String) : Bool :=
  base == scope || (scope.endsWith "/" && base.startsWith scope)

private def scopedRule (scopes : List (String × Specifiers)) (base key : String) (prefixes : Bool) :
    Option (String × Option String) :=
  let best := scopes.foldl (fun best (scope, rules) =>
    if !scopeMatches base scope then best else
    match bestRule rules key prefixes with
    | none => best
    | some rule =>
      if best.all (fun current : String × (String × Option String) =>
          current.1.utf8ByteSize < scope.utf8ByteSize ||
          (current.1 == scope && current.2.1.utf8ByteSize < rule.1.utf8ByteSize))
      then some (scope, rule) else best) none
  best.map Prod.snd

/-- Drop rules from a late map which could change an earlier successful resolution.
Each record is the referring module's base URL and the normalised specifier. -/
def Map.withoutResolved (map : Map) (resolved : Array (String × String)) : Map :=
  if resolved.isEmpty then map else
    let imports := map.imports.filter fun (key, _) =>
      !resolved.any (fun (_, specifier) => specifier.startsWith key)
    let scopes := map.scopes.map fun (scope, rules) =>
      (scope, rules.filter fun (key, _) =>
        !resolved.any (fun (base, specifier) => scopeMatches base scope && specifier.startsWith key))
    { map with imports, scopes }

/-- Apply the most specific scope that has a match, then the global map.
Null and escaping package addresses are terminal refusals. -/
def resolve (map : Map) (specifier base : String) : Option String :=
  let parsed := urlLike specifier base
  let key := (parsed.map (·.serialize)).getD specifier
  let prefixes := parsed.all (·.isSpecial)
  let rule := (scopedRule map.scopes base key prefixes).orElse fun _ => bestRule map.imports key prefixes
  match rule with
  | some hit => applyRule key hit
  | none => parsed.map (·.serialize)

/-- Kind: equivalence. Says: an empty map preserves URL-like module resolution.
Does not say: whether the resulting URL is eligible for a network fetch. -/
theorem resolve_empty (specifier base : String) :
    resolve {} specifier base = (urlLike specifier base).map (·.serialize) := rfl

/-- Kind: refusal. Says: an exact blocked key in the only global rule terminates resolution,
including when the specifier would otherwise resolve as a URL.
Does not say: which rule wins in an arbitrary scope. -/
theorem resolve_blocked (specifier base : String) :
    let key := ((urlLike specifier base).map (·.serialize)).getD specifier
    resolve { imports := [(key, none)] } specifier base = none := by
  simp [resolve, scopedRule, bestRule, keyMatches, applyRule]

/-- Kind: resource bound. Says: input larger than the byte cap cannot be registered.
Does not say: every smaller input parses successfully. -/
theorem parse_refuses_oversize (source base : String) (h : maxBytes < source.utf8ByteSize) :
    parse source base = none := by
  simp [parse, h]

private def exampleBase := "https://example.test/app/index.html"
private def exampleMap := (parse
  "{\"imports\":{\"@factoidal/core\":\"./vendor/browser.mjs\",\"./studio.js\":\"./studio.js?v=1\",\"pkg/\":\"./vendor/\",\"pkg/sub/\":\"./other/\",\"deny\":null},\"scopes\":{\"./sub/\":{\"pkg/\":\"./scoped/\"}}}"
  exampleBase).getD {}

#guard resolve exampleMap "@factoidal/core" exampleBase == some "https://example.test/app/vendor/browser.mjs"
#guard resolve exampleMap "./studio.js" exampleBase == some "https://example.test/app/studio.js?v=1"
#guard resolve exampleMap "pkg/sub/x" exampleBase == some "https://example.test/app/other/x"
#guard resolve exampleMap "pkg/sub/x" "https://example.test/app/sub/module.js" ==
  some "https://example.test/app/scoped/sub/x"
#guard resolve exampleMap "pkg/../escape.js" exampleBase == none
#guard resolve exampleMap "pkg/%2e%2e/escape.js" exampleBase == none
#guard resolve exampleMap "deny" exampleBase == none
#guard resolve exampleMap "./plain.js" exampleBase == some "https://example.test/app/plain.js"
#guard (parse "{} trailing" exampleBase).isNone
#guard resolve (({ imports := [("entry", some "first")] } : Map).merge
  { imports := [("entry", some "second")] }) "entry" exampleBase == some "first"
#guard (({ imports := [("pkg/", none), ("unrelated", none)] } : Map).withoutResolved
  #[(exampleBase, "pkg/file.js")]).imports == [("unrelated", none)]

#print axioms resolve_empty
#print axioms resolve_blocked
#print axioms parse_refuses_oversize

end L4Factoidal.WasmVM.Hosts.ImportMap
