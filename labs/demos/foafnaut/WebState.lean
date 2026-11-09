import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import L4Factoidal.WHATWG.Encoding.Sniff

/-! Browser state: bookmarks, history, settings and open tabs, as Linked Web Storage
resources (design record: docs/designissues/2026-11-08-browser-state-lws.md).

Lean decides every resource: its path in the storage, its JSON-LD text, how two copies
merge, what a sync sends each way, which origins a sync may reach, and the pages
`foafnaut:bookmarks` and `foafnaut:history`. The host only carries bytes: to a local LWS
server on 127.0.0.1 (the native browser), to IndexedDB (the Hub), and to a remote pod.

Vocabulary: schema.org where it fits (`BookmarkAction`, `ViewAction`, `WebPage`, `url`,
`name`, `keywords`, `startTime`, `dateModified`), and a small `foafnaut:` namespace for
the rest (`Settings`, `Session`, `HistoryDay`, `visit`, `from`, `theme`, `textZoom`,
`classicUI`, `liberal`, `font`, `fontFallback`, `remotePod`, `tab`, `activeTab`, `scroll`, `deleted`).

Merge rules:
* history: one resource per UTC day; its visits are a set. Merge is set union of the
  canonical visit texts (`union`): commutative and idempotent for every input
  (`union_comm`, `union_self`), and nothing is lost (`mem_union`).
* bookmarks and settings: last writer wins per resource, by `dateModified`, then by the
  text (`lww`): commutative and idempotent (`lww_comm`, `lww_self`). A removed bookmark
  is a resource with `foafnaut:deleted true`, so a removal also syncs.
* open tabs (`session.jsonld`) belong to one device and do not sync. -/
namespace WebState
open L4Factoidal
open L4Factoidal.JSON (Json)

/-! ## Sets of texts, and last writer wins -/

/-- The union of two lists in `compare` order: equal heads are kept once. On two strictly
increasing lists it is their set union, strictly increasing. -/
def union : List String → List String → List String
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys =>
    match compare x y with
    | .lt => x :: union xs (y :: ys)
    | .gt => y :: union (x :: xs) ys
    | .eq => x :: union xs ys
termination_by xs ys => xs.length + ys.length

private theorem compare_swap' (a b : String) : compare b a = (compare a b).swap :=
  Std.OrientedCmp.eq_swap

private theorem eq_of_compare' {a b : String} (h : compare a b = .eq) : a = b :=
  Std.LawfulEqCmp.eq_of_compare h

private theorem compare_self' (a : String) : compare a a = .eq :=
  Std.ReflCmp.compare_self

theorem union_nil_right (xs : List String) : union xs [] = xs := by
  cases xs <;> simp [union]

/-- History merge does not depend on which side is local. -/
theorem union_comm : ∀ (xs ys : List String), union xs ys = union ys xs
  | [], ys => by rw [union_nil_right]; simp [union]
  | x :: xs, [] => by simp [union]
  | x :: xs, y :: ys => by
    have hs := compare_swap' x y
    cases h : compare x y with
    | lt =>
      rw [h] at hs
      simp only [union, h, hs, Ordering.swap]
      rw [union_comm xs (y :: ys)]
    | gt =>
      rw [h] at hs
      simp only [union, h, hs, Ordering.swap]
      rw [union_comm (x :: xs) ys]
    | eq =>
      have e := eq_of_compare' h
      subst e
      simp only [union, compare_self']
      rw [union_comm xs ys]
termination_by xs ys => xs.length + ys.length

/-- Merging a history with itself changes nothing. -/
theorem union_self : ∀ (xs : List String), union xs xs = xs
  | [] => by simp [union]
  | x :: xs => by simp only [union, compare_self']; rw [union_self xs]

/-- No visit is lost and none is made up. -/
theorem mem_union : ∀ (a : String) (xs ys : List String), a ∈ union xs ys ↔ a ∈ xs ∨ a ∈ ys
  | a, [], ys => by simp [union]
  | a, x :: xs, [] => by simp [union]
  | a, x :: xs, y :: ys => by
    have ih1 := mem_union a xs (y :: ys)
    have ih2 := mem_union a (x :: xs) ys
    have ih3 := mem_union a xs ys
    cases h : compare x y with
    | lt => simp only [union, h, List.mem_cons] at ih1 ih2 ih3 ⊢; grind
    | gt => simp only [union, h, List.mem_cons] at ih1 ih2 ih3 ⊢; grind
    | eq =>
      have e := eq_of_compare' h
      subst e
      simp only [union, compare_self', List.mem_cons] at ih1 ih2 ih3 ⊢; grind
termination_by _ xs ys => xs.length + ys.length

/-- Last writer wins on (dateModified, text); the text breaks a tie, so both sides pick
the same copy. -/
def lww (a b : String × String) : String × String :=
  match compare a.1 b.1 with
  | .lt => b
  | .gt => a
  | .eq => if compare a.2 b.2 == .lt then b else a

theorem lww_comm (a b : String × String) : lww a b = lww b a := by
  have h1 := compare_swap' a.1 b.1
  cases h : compare a.1 b.1 with
  | lt => rw [h] at h1; simp [lww, h, h1, Ordering.swap]
  | gt => rw [h] at h1; simp [lww, h, h1, Ordering.swap]
  | eq =>
    rw [h] at h1
    have e1 := eq_of_compare' h
    have h2 := compare_swap' a.2 b.2
    cases g : compare a.2 b.2 with
    | lt => rw [g] at h2; simp [lww, h, h1, Ordering.swap, g, h2]
    | gt => rw [g] at h2; simp [lww, h, h1, Ordering.swap, g, h2]
    | eq =>
      have e2 := eq_of_compare' g
      have : a = b := Prod.ext e1 e2
      subst this; rfl

theorem lww_self (a : String × String) : lww a a = a := by
  simp [lww]

/-- A JSON text, read by Factoidal's JSON parser. -/
def parse (s : String) : Option Json := JSON.parseJson? s

/-! ## Time and names -/

private def pad (width n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- Year, month and day of a count of days since 1970-01-01 (proleptic Gregorian). -/
def civil (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400, m, d)

/-- The UTC day of a time in milliseconds, `YYYY-MM-DD`. -/
def dayOf (ms : Nat) : String :=
  let (y, m, d) := civil (ms / 86400000)
  s!"{pad 4 y}-{pad 2 m}-{pad 2 d}"

/-- An `xsd:dateTime` in UTC with milliseconds. Same width for years 0 to 9999, so the
texts sort as the times do. -/
def isoOf (ms : Nat) : String :=
  let r := ms % 86400000
  s!"{dayOf ms}T{pad 2 (r / 3600000)}:{pad 2 (r / 60000 % 60)}:{pad 2 (r / 1000 % 60)}.{pad 3 (r % 1000)}Z"

#guard isoOf 0 == "1970-01-01T00:00:00.000Z"
#guard isoOf 951782400000 == "2000-02-29T00:00:00.000Z"
#guard isoOf 1794102985123 == "2026-11-08T01:56:25.123Z"
#guard isoOf 253402300799000 == "9999-12-31T23:59:59.000Z"
#guard dayOf 1794102985123 == "2026-11-08"

/-- FNV-1a, 64 bits, over the UTF-8 bytes: the stable name of a bookmark's resource. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

private def hex16 (v : UInt64) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList ((List.range 16).reverse.map fun i => digits[(v.toNat >>> (4 * i)) % 16]!)

#guard hex16 (fnv1a "") == "cbf29ce484222325"
#guard hex16 (fnv1a "a") == "af63dc4c8601ec8c"

/-! ## Where each resource goes -/

def root : String := "/foafnaut/"
def bookmarksDir : String := root ++ "bookmarks/"
def historyDir : String := root ++ "history/"
def settingsPath : String := root ++ "settings.jsonld"
def sessionPath : String := root ++ "session.jsonld"
def containers : List String := [root, bookmarksDir, historyDir]
def mediaType : String := "application/ld+json"

def bookmarkPath (url : String) : String := bookmarksDir ++ hex16 (fnv1a url) ++ ".jsonld"
def historyPath (ms : Nat) : String := historyDir ++ dayOf ms ++ ".jsonld"

inductive Kind where
  | bookmark | history | settings | session | other
  deriving BEq, Repr

private def isName (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isAlphanum || c == '-' || c == '.' || c == '_') && !(s.startsWith ".")

def kindOf (path : String) : Kind :=
  if path == settingsPath then .settings
  else if path == sessionPath then .session
  else if path.startsWith bookmarksDir && path.endsWith ".jsonld" && isName (path.drop bookmarksDir.length).toString then .bookmark
  else if path.startsWith historyDir && path.endsWith ".jsonld" && isName (path.drop historyDir.length).toString then .history
  else .other

/-- Bookmarks, history and settings go to every copy of the storage; open tabs stay. -/
def syncs (path : String) : Bool :=
  match kindOf path with | .bookmark | .history | .settings => true | _ => false

#guard kindOf (bookmarkPath "https://example.org/") == .bookmark
#guard kindOf (historyPath 0) == .history && historyPath 0 == "/foafnaut/history/1970-01-01.jsonld"
#guard kindOf "/foafnaut/bookmarks/../settings.jsonld" == .other
#guard kindOf "/foafnaut/bookmarks/sub/x.jsonld" == .other
#guard !syncs sessionPath && syncs settingsPath

/-- How the host writes a path: the URL, its container and the name to create it under,
and the containers to make first when it is missing (from the top down). -/
def writePlan (base path : String) : Json :=
  let parts := (path.splitOn "/").filter (· != "")
  let dirs := (List.range parts.length).map fun i => "/" ++ String.join ((parts.take i).map (· ++ "/"))
  let parent := dirs.getLast?.getD "/"
  let slug := parts.getLast?.getD ""
  let url := fun (p : String) => base ++ (p.drop 1).toString
  .object [("path", .string path), ("url", .string (url path)), ("parent", .string (url parent)),
    ("slug", .string slug), ("mediaType", .string mediaType),
    ("containers", .array ((dirs.drop 1).map fun d =>
      let ps := (d.splitOn "/").filter (· != "")
      .object [("url", .string (url d)), ("parent", .string (url ("/" ++ String.join ((ps.dropLast).map (· ++ "/"))))),
        ("slug", .string (ps.getLast?.getD ""))]))]

#guard (writePlan "http://127.0.0.1:9/" "/foafnaut/history/2026-11-08.jsonld").toString ==
  "{\"path\":\"/foafnaut/history/2026-11-08.jsonld\",\"url\":\"http://127.0.0.1:9/foafnaut/history/2026-11-08.jsonld\",\"parent\":\"http://127.0.0.1:9/foafnaut/history/\",\"slug\":\"2026-11-08.jsonld\",\"mediaType\":\"application/ld+json\",\"containers\":[{\"url\":\"http://127.0.0.1:9/foafnaut/\",\"parent\":\"http://127.0.0.1:9/\",\"slug\":\"foafnaut\"},{\"url\":\"http://127.0.0.1:9/foafnaut/history/\",\"parent\":\"http://127.0.0.1:9/foafnaut/\",\"slug\":\"history\"}]}"

/-! ## The JSON-LD text of each resource -/

def schema : String := "https://schema.org/"
def ns : String := "https://danbri.github.io/factoidal/ns/foafnaut#"

def context : Json :=
  .object [("@vocab", .string schema), ("foafnaut", .string ns),
    ("xsd", .string "http://www.w3.org/2001/XMLSchema#"),
    ("url", .object [("@type", .string "@id")]),
    ("startTime", .object [("@type", .string "xsd:dateTime")]),
    ("dateModified", .object [("@type", .string "xsd:dateTime")]),
    ("foafnaut:from", .object [("@type", .string "@id")]),
    ("foafnaut:remotePod", .object [("@type", .string "@id")]),
    ("foafnaut:visit", .object [("@container", .string "@set")]),
    ("foafnaut:tab", .object [("@container", .string "@list")]),
    ("keywords", .object [("@container", .string "@set")])]

private def num (n : Nat) : Json := .number (toString n)
private def str (j : Json) (key : String) (fallback := "") : String :=
  match j.field? key with | some (.string s) => s | _ => fallback
private def natField (j : Json) (key : String) (fallback := 0) : Nat :=
  match j.field? key with | some (.number n) => n.toNat?.getD fallback | _ => fallback
private def strings (j : Json) (key : String) : List String :=
  match j.field? key with
  | some (.array items) => items.filterMap fun | .string s => some s | _ => none
  | some (.string s) => [s]
  | _ => []
private def obj (j : Json) (key : String) : Json := (j.field? key).getD (.object [])

def document (type : String) (members : List (String × Json)) : Json :=
  .object ([("@context", context), ("@id", .string ""), ("@type", .string type)] ++ members)

def page (url title : String) : Json :=
  .object ([("@type", .string "WebPage"), ("url", .string url)] ++ (if title.isEmpty then [] else [("name", .string title)]))

/-! ### History -/

structure Visit where
  url : String
  title : String := ""
  /-- The page the link was followed from, or "". -/
  «from» : String := ""
  /-- Milliseconds since 1970. -/
  time : Nat
  deriving BEq, Repr

/-- The visit node. Its compact text is the element of the day's set; it starts with the
time, so the set's order is the time order. -/
def Visit.node (v : Visit) : Json :=
  .object ([("startTime", .string (isoOf v.time)), ("@type", .string "ViewAction"), ("object", page v.url v.title)] ++
    (if v.«from».isEmpty then [] else [("foafnaut:from", .string v.«from»)]))

def Visit.text (v : Visit) : String := v.node.toString

/-- Milliseconds of an `isoOf` text, or none for another text. -/
def millisOf (iso : String) : Option Nat := do
  let cs := iso.toList
  guard (cs.length == 24 && cs[4]? == some '-' && cs[10]? == some 'T' && cs[23]? == some 'Z')
  let n := fun (a b : Nat) => (String.ofList ((cs.drop a).take (b - a))).toNat?
  let y ← n 0 4; let m ← n 5 7; let d ← n 8 10
  let hh ← n 11 13; let mm ← n 14 16; let ss ← n 17 19; let ms ← n 20 23
  guard (1970 ≤ y && 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ 31 && hh < 24 && mm < 60 && ss < 60)
  -- Days from civil (the inverse of `civil`).
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  let days := era * 146097 + doe - 719468
  let t := ((days * 24 + hh) * 60 + mm) * 60 + ss
  let back := t * 1000 + ms
  guard (isoOf back == iso)
  return back

#guard millisOf "2026-11-08T01:56:25.123Z" == some 1794102985123
#guard millisOf "2000-02-30T00:00:00.000Z" == none

def Visit.ofNode (j : Json) : Option Visit := do
  let time ← millisOf (str j "startTime")
  let p := obj j "object"
  let url := str p "url"
  guard (!url.isEmpty)
  return { url, title := str p "name", «from» := str j "foafnaut:from", time }

/-- The canonical set of a day's visits: each node read and written again, in order, once. -/
def visitSet (doc : Json) : List String :=
  let nodes := match doc.field? "foafnaut:visit" with | some (.array items) => items | some n => [n] | none => []
  nodes.foldl (fun acc n => match Visit.ofNode n with | some v => union acc [v.text] | none => acc) []

def historyDoc (day : String) (texts : List String) : Json :=
  document "foafnaut:HistoryDay" [("foafnaut:day", .string day),
    ("foafnaut:visit", .array (texts.filterMap parse))]

def visits (doc : Json) : List Visit :=
  (visitSet doc).filterMap fun t => parse t >>= Visit.ofNode

/-! ### Bookmarks -/

structure Bookmark where
  url : String
  title : String := ""
  tags : List String := []
  added : Nat
  modified : Nat
  deleted : Bool := false
  deriving BEq, Repr

def Bookmark.doc (b : Bookmark) : Json :=
  document "BookmarkAction" ([("object", page b.url b.title),
    ("keywords", .array (b.tags.map .string)), ("startTime", .string (isoOf b.added)),
    ("dateModified", .string (isoOf b.modified))] ++ (if b.deleted then [("foafnaut:deleted", .bool true)] else []))

def Bookmark.ofDoc (j : Json) : Option Bookmark := do
  guard (str j "@type" == "BookmarkAction")
  let p := obj j "object"
  let url := str p "url"
  guard (!url.isEmpty)
  let added ← millisOf (str j "startTime")
  let modified ← millisOf (str j "dateModified")
  return { url, title := str p "name", tags := strings j "keywords", added, modified,
           deleted := match j.field? "foafnaut:deleted" with | some (.bool true) => true | _ => false }

/-! ### Settings and open tabs -/

structure Settings where
  theme : String := "next"
  /-- Text size in percent; the browsers start at 150. -/
  textZoom : Nat := 150
  /-- The classic chrome, always full (owner, 2026-11-08: on by default). Off, the chrome
  folds to the domain as the page scrolls down. -/
  classicUI : Bool := true
  /-- The page script engine (`WebRenderScript.engines`: "bubblepop", "quickjs", "none"); ""
  for the host's default (`WebRenderScript.defaultEngine`). -/
  scripts : String := ""
  /-- Liberal mode (`WebAccept`, the Settings checkbox "Be liberal in what we accept"): on
  (owner, 2026-11-09) unless a settings document says false. -/
  liberal : Bool := true
  /-- How a page that declares no encoding is read (`WHATWG.Encoding.Sniff.Fallback`):
  "" (detect, the default), "detect", "locale" or an encoding's name. -/
  encoding : String := ""
  fonts : List String := []
  fallback : List String := []
  remotePod : String := ""
  modified : Nat := 0
  deriving BEq, Repr

def Settings.doc (s : Settings) : Json :=
  document "foafnaut:Settings" ([("foafnaut:theme", .string s.theme), ("foafnaut:textZoom", num s.textZoom),
    ("foafnaut:classicUI", .bool s.classicUI), ("foafnaut:liberal", .bool s.liberal)] ++
    (if s.scripts.isEmpty then [] else [("foafnaut:scripts", .string s.scripts)]) ++
    (if s.encoding.isEmpty then [] else [("foafnaut:defaultEncoding", .string s.encoding)]) ++
    [("foafnaut:font", .array (s.fonts.map .string)), ("foafnaut:fontFallback", .array (s.fallback.map .string))] ++
    (if s.remotePod.isEmpty then [] else [("foafnaut:remotePod", .string s.remotePod)]) ++
    [("dateModified", .string (isoOf s.modified))])

def Settings.ofDoc (j : Json) : Settings :=
  { theme := str j "foafnaut:theme" "next", textZoom := max 50 (natField j "foafnaut:textZoom" 150),
    classicUI := (match j.field? "foafnaut:classicUI" with | some (.bool b) => b | _ => true),
    scripts := str j "foafnaut:scripts",
    liberal := j.field? "foafnaut:liberal" != some (.bool false), encoding := str j "foafnaut:defaultEncoding",
    fonts := strings j "foafnaut:font", fallback := strings j "foafnaut:fontFallback",
    remotePod := str j "foafnaut:remotePod", modified := (millisOf (str j "dateModified")).getD 0 }

-- The classic UI is on unless a settings document says false; it survives a round trip.
#guard (Settings.ofDoc (Json.object [])).classicUI
#guard !(Settings.ofDoc ({classicUI := false} : Settings).doc).classicUI
#guard (Settings.ofDoc ({} : Settings).doc).classicUI
-- The page script engine: the host's default until a choice; a choice survives a round trip.
#guard (Settings.ofDoc (Json.object [])).scripts == ""
#guard (Settings.ofDoc ({scripts := "quickjs"} : Settings).doc).scripts == "quickjs"
#guard (Settings.ofDoc (Json.object [])).liberal && !(Settings.ofDoc ({liberal := false} : Settings).doc).liberal
-- The default encoding: detect until a choice; a choice survives a round trip.
#guard (Settings.ofDoc (Json.object [])).encoding == ""
#guard (Settings.ofDoc ({encoding := "locale"} : Settings).doc).encoding == "locale"

/-! ## The default encoding of pages that declare none (`WHATWG.Encoding.Sniff`) -/

open L4Factoidal.WHATWG.Encoding in
/-- A setting as stored: "" for none, else `Fallback.setting` ("detect", "locale" or an
encoding's name). A value that names nothing is "". -/
def encodingSetting (v : String) : String :=
  if v.isEmpty then "" else (Sniff.Fallback.ofSetting v).setting

open L4Factoidal.WHATWG.Encoding in
/-- The settings page section (`<!--foafnaut:encoding-->`): the choice now, as a heading
in the style of the text size, then a button for each choice. `locale` is the system's
language as the host reads it. -/
def encodingChoicesHTML (setting locale : String) : String :=
  let current := Sniff.Fallback.ofSetting setting
  let localeEnc := (Sniff.localeEncoding locale).name
  let lang := if locale.isEmpty then "unknown" else locale
  let label := fun (f : Sniff.Fallback) => match f with
    | .detect => s!"Detect (UTF-8 when valid, else {localeEnc})"
    | .locale => s!"From system language ({lang}: {localeEnc})"
    | .fixed e => e.name
  let button := fun (f : Sniff.Fallback) =>
    let cls := if f == current then " class=\"chosen\"" else ""
    s!"<a{cls} href=\"foafnaut:encoding/{f.setting}\">{label f}</a>"
  let fixed := Encoding.all.filter (· != .replacement)
  s!"<h2 class=\"size\">Default encoding: {label current}</h2>" ++
  "<p class=\"presets\">" ++ button .detect ++ " " ++ button .locale ++ "</p>" ++
  "<p class=\"presets\">" ++ " ".intercalate (fixed.map (fun e => button (.fixed e))) ++ "</p>"

#guard encodingSetting "" == "" && encodingSetting "sjis" == "Shift_JIS" && encodingSetting "nonsense" == "detect"
#guard (encodingChoicesHTML "" "ja-JP").startsWith "<h2 class=\"size\">Default encoding: Detect (UTF-8 when valid, else Shift_JIS)</h2>"

structure Tab where
  url : String
  title : String := ""
  scroll : Nat := 0
  deriving BEq, Repr

def Tab.node (t : Tab) : Json :=
  .object ([("@type", .string "WebPage"), ("url", .string t.url)] ++
    (if t.title.isEmpty then [] else [("name", .string t.title)]) ++ [("foafnaut:scroll", num t.scroll)])

def sessionDoc (tabs : List Tab) (active modified : Nat) : Json :=
  document "foafnaut:Session" [("foafnaut:activeTab", num (min active (tabs.length - 1))),
    ("foafnaut:tab", .array (tabs.map Tab.node)), ("dateModified", .string (isoOf modified))]

def tabsOf (j : Json) : List Tab :=
  match j.field? "foafnaut:tab" with
  | some (.array items) => items.filterMap fun t =>
      let url := str t "url"; if url.isEmpty then none else some { url, title := str t "name", scroll := natField t "foafnaut:scroll" }
  | _ => []

/-! ## Merge of two copies of one resource -/

/-- The stamp a copy is judged by. -/
def stamp (j : Json) : String := str j "dateModified"

/-- The merged text of two copies of the resource at `path`. A copy that is not JSON
loses to one that is. -/
def merge (path a b : String) : String :=
  match parse a, parse b with
  | none, none => (lww ("", a) ("", b)).2
  | some _, none => a
  | none, some _ => b
  | some ja, some jb =>
    match kindOf path with
    | .history =>
      let day := ((path.drop historyDir.length).toString.dropEnd 7).toString
      (historyDoc day (union (visitSet ja) (visitSet jb))).toString
    | _ => (lww (stamp ja, a) (stamp jb, b)).2

theorem merge_history_comm (path a b : String) (h : kindOf path = .history)
    (ha : (parse a).isSome) (hb : (parse b).isSome) :
    merge path a b = merge path b a := by
  unfold merge
  cases pa : parse a <;> cases pb : parse b <;> simp_all [union_comm]

/-! ## What a sync sends each way -/

/-- For every path either side has: the merged text, and which side must take it. -/
def syncPlan (localSide remote : List (String × String)) : List (String × String) × List (String × String) :=
  let paths := (localSide.map (·.1) ++ remote.map (·.1)).foldl (fun acc p => union acc [p]) []
  paths.foldl (fun (toRemote, toLocal) path =>
    if !syncs path then (toRemote, toLocal) else
    match localSide.lookup path, remote.lookup path with
    | some l, none => (toRemote ++ [(path, l)], toLocal)
    | none, some r => (toRemote, toLocal ++ [(path, r)])
    | some l, some r =>
      let m := merge path l r
      (if m == r then toRemote else toRemote ++ [(path, m)], if m == l then toLocal else toLocal ++ [(path, m)])
    | none, none => (toRemote, toLocal)) ([], [])

/-! ## Which origins a sync may reach -/

/-- `scheme://host[:port]` of an http or https URL, lower case, or none. -/
def originOf (url : String) : Option (String × String) :=
  match url.splitOn "://" with
  | [scheme, rest] =>
    let scheme := scheme.toLower
    let authority := ((rest.splitOn "/").headD "").toLower
    let authority := ((authority.splitOn "?").headD "")
    let authority := ((authority.splitOn "#").headD "")
    if (scheme == "http" || scheme == "https") && !authority.isEmpty && !authority.contains '@' then
      let host := if authority.startsWith "[" then ((authority.splitOn "]").headD "") ++ "]" else (authority.splitOn ":").headD ""
      some (scheme ++ "://" ++ authority, host)
    else none
  | _ => none

def loopback (host : String) : Bool := host == "127.0.0.1" || host == "localhost" || host == "[::1]"

/-- A sync request may go to the configured pod's origin, and to loopback. A pod that is
not on loopback must be https. Every other URL is refused. -/
def fetchAllowed (url pod : String) : Bool × String :=
  match originOf url with
  | none => (false, "not an http or https URL")
  | some (origin, host) =>
    if loopback host then (true, "loopback")
    else match originOf pod with
      | some (podOrigin, podHost) =>
        if !podOrigin.startsWith "https://" && !loopback podHost then (false, "the pod is not https")
        else if origin == podOrigin then (true, "the pod's origin")
        else (false, "not the pod's origin")
      | none => (false, "no pod is set")

#guard (fetchAllowed "http://127.0.0.1:4000/foafnaut/" "").1
#guard (fetchAllowed "https://pod.example/x" "https://pod.example/").1
#guard !(fetchAllowed "https://evil.example/x" "https://pod.example/").1
#guard !(fetchAllowed "https://pod.example.evil/x" "https://pod.example/").1
#guard !(fetchAllowed "https://user@pod.example/x" "https://pod.example/").1
#guard !(fetchAllowed "http://pod.example/x" "http://pod.example/").1
#guard !(fetchAllowed "file:///etc/passwd" "https://pod.example/").1

/-! ## Pages -/

private def escape (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c == '"' then "&quot;" else if c.toNat < 32 then " " else c.toString)

private def shell (title body : String) : String :=
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>" ++ escape title ++
  "</title><style>body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:#f4f4ee}" ++
  "h1{margin:0 0 12px;font-size:18px;line-height:24px;color:#a0186a}h2{margin:12px 0 4px;font-size:14px;color:#a0186a}" ++
  "p{margin:0 0 4px}.dim{color:#6a7080}a{color:#1a4fa0}</style></head><body><h1>" ++ escape title ++ "</h1>" ++ body ++ "</body></html>"

private def safeHref (url : String) : Bool := (originOf url).isSome || url.startsWith "foafnaut:" || url.startsWith "file:"

private def linkTo (url title : String) : String :=
  let shown := if title.isEmpty then url else title
  if safeHref url then s!"<a href=\"{escape url}\">{escape shown}</a>" else escape shown

/-- Shown on a page at most. -/
def pageLimit : Nat := 200

def bookmarksPage (marks : List Bookmark) (whereStored : String) : String :=
  let live := (marks.filter (!·.deleted)).mergeSort (fun a b => a.added ≥ b.added)
  let rows := (live.take pageLimit).map fun b =>
    "<p>" ++ linkTo b.url b.title ++ (if b.tags.isEmpty then "" else " <span class=\"dim\">" ++ escape (", ".intercalate b.tags) ++ "</span>") ++
    " <span class=\"dim\">" ++ (dayOf b.added) ++ "</span></p>"
  shell "Bookmarks" (
    (if live.isEmpty then "<p>No bookmarks yet. Type :bookmark in the address bar to keep this page.</p>" else String.join rows) ++
    s!"<p class=\"dim\">{live.length} bookmarks. Stored in {escape whereStored}. :bookmark keeps the page shown; :unbookmark removes it; :sync exchanges them with the pod of the settings.</p>")

def historyPage (vs : List Visit) (whereStored : String) : String :=
  let newest := (vs.mergeSort (fun a b => a.time ≥ b.time)).take pageLimit
  let (body, _) := newest.foldl (fun (out, day) v =>
    let d := dayOf v.time
    (out ++ (if d == day then "" else s!"<h2>{d}</h2>") ++
      s!"<p><span class=\"dim\">{(isoOf v.time).drop 11 |>.take 5}</span> " ++ linkTo v.url v.title ++ "</p>", d)) ("", "")
  shell "History" (
    (if newest.isEmpty then "<p>No pages visited yet.</p>" else body) ++
    s!"<p class=\"dim\">The last {newest.length} of {vs.length} visits. Stored in {escape whereStored}.</p>")

/-! ## The ops -/

private def pairs (j : Json) (key : String) : List (String × String) :=
  match j.field? key with
  | some (.array items) => items.filterMap fun r =>
      let p := str r "path"
      match r.field? "body" with | some (.string b) => if p.isEmpty then none else some (p, b) | _ => none
  | _ => []

private def pairsJson (ps : List (String × String)) (base : String) : Json :=
  .array (ps.map fun (p, b) => match writePlan base p with
    | .object fields => .object (fields ++ [("body", .string b)])
    | other => other)

private def write (base path body : String) : String :=
  (match writePlan base path with
   | .object fields => Json.object (fields ++ [("body", Json.string body)])
   | other => other).toString

private def current (request : Json) : Option Json :=
  match request.field? "current" with | some (.string t) => parse t | _ => none

def ops : List String :=
  ["stateInfo", "stateVisit", "stateBookmark", "stateUnbookmark", "stateSettings", "stateSession",
   "stateRead", "statePage", "stateMerge", "stateSync", "stateFetchAllowed"]

def info : String :=
  (Json.object [("ops", .array (ops.map .string)), ("containers", .array (containers.map .string)),
    ("settings", .string settingsPath), ("session", .string sessionPath), ("mediaType", .string mediaType),
    ("vocabulary", .object [("schema", .string schema), ("foafnaut", .string ns)])]).toString

/-- The ops of this module, or `none` for another op. `base` is the storage root URL
(ending in `/`); `now` is milliseconds since 1970 from the host clock. -/
def op (name : String) (request : Json) : Except String (Option String) := do
  let base := str request "base" "/"
  let now := natField request "now"
  if name == "stateInfo" then return some info
  if name == "stateVisit" then
    let url := str request "url"
    if url.isEmpty then throw "stateVisit needs a url"
    -- Only web and file pages go into the history: not foafnaut: pages, not view-source tabs.
    if (originOf url).isNone && !url.startsWith "file:" || url.endsWith "#source" then
      return some (Json.object [("skip", .bool true)]).toString
    let v : Visit := { url, title := str request "title", «from» := str request "from", time := now }
    let path := historyPath now
    let old := (current request).map visitSet |>.getD []
    return some (write base path (historyDoc (dayOf now) (union old [v.text])).toString)
  if name == "stateBookmark" || name == "stateUnbookmark" then
    let url := str request "url"
    if url.isEmpty then throw s!"{name} needs a url"
    let old := (current request).bind Bookmark.ofDoc
    let added := match old with | some b => if b.deleted then now else b.added | none => now
    let title := str request "title" ((old.map Bookmark.title).getD "")
    let tags := match request.field? "tags" with
      | some _ => strings request "tags"
      | none => (old.map Bookmark.tags).getD []
    let b : Bookmark := { url := url, title := title, tags := tags, added := added, modified := now, deleted := name == "stateUnbookmark" }
    return some (write base (bookmarkPath url) b.doc.toString)
  if name == "stateSettings" then
    let old := ((current request).map Settings.ofDoc).getD {}
    let pod := str request "remotePod"
    if !pod.isEmpty && (!(fetchAllowed pod pod).1 || !pod.endsWith "/") then
      throw "the pod must be an https URL (or a loopback http URL) that ends in /"
    let fonts := match request.field? "fonts" with | some _ => strings request "fonts" | none => old.fonts
    let fallback := match request.field? "fallback" with | some _ => strings request "fallback" | none => old.fallback
    let s : Settings := {
      theme := str request "theme" old.theme, textZoom := max 50 (natField request "textZoom" old.textZoom),
      classicUI := (match request.field? "classicUI" with | some (.bool b) => b | _ => old.classicUI),
      scripts := (match request.field? "scripts" with
        | some (.string v) => if v.isEmpty || ["bubblepop", "quickjs", "none"].contains v then v else old.scripts
        | _ => old.scripts),
      liberal := (match request.field? "liberal" with | some (.bool b) => b | _ => old.liberal),
      encoding := (match request.field? "encoding" with
        | some (.string v) => encodingSetting v
        | _ => old.encoding),
      fonts := fonts, fallback := fallback, remotePod := str request "remotePod" old.remotePod, modified := now }
    return some (write base settingsPath s.doc.toString)
  if name == "stateSession" then
    let tabs := match request.field? "tabs" with
      | some (.array items) => items.filterMap fun t =>
          let url := str t "url"; if url.isEmpty then none else some ({ url, title := str t "title", scroll := natField t "scroll" } : Tab)
      | _ => []
    return some (write base sessionPath (sessionDoc tabs (natField request "active") now).toString)
  if name == "stateRead" || name == "statePage" then
    let rs := pairs request "resources"
    let docs := rs.filterMap fun (p, b) => (parse b).map (p, ·)
    let marks := docs.filterMap fun (p, j) => if kindOf p == .bookmark then Bookmark.ofDoc j else none
    let vs := (docs.filter (kindOf ·.1 == .history)).flatMap (visits ·.2)
    let settings := (docs.lookup settingsPath).map Settings.ofDoc
    let session := docs.lookup sessionPath
    if name == "statePage" then
      let whereStored := str request "where" "this browser"
      let which := str request "page"
      if which == "bookmarks" then
        return some (Json.object [("source", .string (bookmarksPage marks whereStored)), ("title", .string "Bookmarks")]).toString
      if which == "history" then
        return some (Json.object [("source", .string (historyPage vs whereStored)), ("title", .string "History")]).toString
      throw s!"statePage: no page {which}"
    let live := marks.filter (!·.deleted)
    return some (Json.object [
      ("bookmarks", .array (live.map fun b => .object [("url", .string b.url), ("title", .string b.title),
        ("tags", .array (b.tags.map .string)), ("added", num b.added)])),
      ("visits", num vs.length),
      ("settings", match settings with
        | some s => .object [("theme", .string s.theme), ("textZoom", num s.textZoom), ("classicUI", .bool s.classicUI), ("scripts", .string s.scripts), ("liberal", .bool s.liberal), ("encoding", .string s.encoding), ("fonts", .array (s.fonts.map .string)),
            ("fallback", .array (s.fallback.map .string)), ("remotePod", .string s.remotePod)]
        | none => .null),
      ("session", match session with
        | some j => .object [("active", num (natField j "foafnaut:activeTab")),
            ("tabs", .array ((tabsOf j).map fun t => .object [("url", .string t.url), ("title", .string t.title), ("scroll", num t.scroll)]))]
        | none => .null)]).toString
  if name == "stateMerge" then
    return some (Json.object [("body", .string (merge (str request "path") (str request "a") (str request "b")))]).toString
  if name == "stateSync" then
    let (toRemote, toLocal) := syncPlan (pairs request "local") (pairs request "remote")
    let remoteBase := str request "remoteBase" base
    return some (Json.object [("toRemote", pairsJson toRemote remoteBase), ("toLocal", pairsJson toLocal base)]).toString
  if name == "stateFetchAllowed" then
    let (allow, reason) := fetchAllowed (str request "url") (str request "pod")
    return some (Json.object [("allow", .bool allow), ("reason", .string reason)]).toString
  return none

end WebState
