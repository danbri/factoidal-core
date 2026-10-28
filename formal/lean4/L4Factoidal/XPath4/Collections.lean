/-
L4Factoidal.XPath4.Collections — `fn:collection` and `fn:uri-collection`
(F&O 4.0 §14.6.6 and §14.6.7). The available collections and URI
collections are part of the dynamic context (`Env.collections`,
`Env.uriCollections`); the host fills them in, and the evaluator does no
I/O.

Also the two functions that need another processor from the host:
`fn:load-xquery-module` (FOQM0006 when no XQuery processor is configured)
and `fn:transform` (FOXT0004 when XSLT transformation is not enabled).
-/
import L4Factoidal.XPath4.Lib
import L4Factoidal.XPath4.XmlParse

namespace L4Factoidal.XPath4

/-- Check the options map of the collection functions: `stable` and
    `recurse` are booleans; other options are implementation-defined
    and ignored (F&O 4.0 §1.6.4, the option parameter conventions). -/
def collectionOpts (opts : Seq) : M Unit := do
  let _ ← optBool opts "stable" true
  let _ ← optBool opts "recurse" false
  pure ()

/-- The key of a collection URI: `""` for the default collection; a
    relative reference is resolved against the base URI; a string that is
    not a URI reference is FODC0004. -/
def collectionKey (e : Env) (src : Seq) : M String := do
  match optAtom src with
  | none => pure ""
  | some u =>
    let s := u.str
    if s.any (fun c => c == ' ' || c == '\\' || c == '{' || c == '}' || c == '^' || c == '`' || c == '|' || c == '"' || c == '<' || c == '>')
       || (s.splitOn "#").length > 2 || s.startsWith ":" then
      err "FODC0004" ("not a valid collection URI: " ++ s)
    pure (if e.baseUri == "" then s else resolveUri e.baseUri s)

def collectionTable : List (String × LibFn) := [
  ent "collection" (fun _ e a => do
    collectionOpts (argN a 1)
    let k ← collectionKey e (argN a 0)
    match e.collections.lookup k with
    | some s => pure s
    | none =>
      -- an unresolved relative reference may be the key as written
      match optAtom (argN a 0) with
      | some u => match e.collections.lookup u.str with
        | some s => pure s
        | none => err "FODC0002" ("no collection is available for " ++ k)
      | none => err "FODC0002" "no default collection"),
  ent "uri-collection" (fun _ e a => do
    collectionOpts (argN a 1)
    let k ← collectionKey e (argN a 0)
    let found := match e.uriCollections.lookup k with
      | some us => some us
      | none => match optAtom (argN a 0) with
        | some u => e.uriCollections.lookup u.str
        | none => none
    match found with
    | some us => pure (us.map (fun u => .atom ⟨.b .anyURI, .str u⟩))
    | none => err "FODC0002" ("no URI collection is available for " ++ (if k == "" then "the default" else k))),
  -- F&O 4.0 §17.4.1: FOQM0006 "No suitable XQuery processor available";
  -- the XPath 4.0 host has none (the XQuery 4.0 host replaces this entry)
  ent "load-xquery-module" (fun _ _ _ => err "FOQM0006" "no XQuery processor is available to this XPath host"),
  -- F&O 4.0 §17.4.2: FOXT0004 "XSLT transformation has been disabled"
  ent "transform" (fun _ _ _ => err "FOXT0004" "XSLT transformation is not enabled in this XPath host")
]

end L4Factoidal.XPath4
