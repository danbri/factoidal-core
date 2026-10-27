/-
L4Factoidal.WebDAV.Config — the mount files of `factoidal webdav-serve`.
https://github.com/danbri/factoidal/issues/1066

Owner, 2026-10-27, verbatim: "Also implement a WEBDAV server that native
file browsers can connect to to see factoidal-powered stuff eg initially lws
client and server, Client uses config markdown files".

A mount is one Markdown file `CONFIGDIR/<name>.md`. The folder the WebDAV
root shows for it is `<name>`. The format (design record
`docs/designissues/2026-10-27-webdav.md` § "Mount files"):

    # Display name
    - kind: local
    - path: ./alice-storage
    - writable: true

    Free text below the list is for people and is ignored.

* The first line that starts with `# ` gives the display name.
* The first run of lines that start with `- ` is the settings list. Each
  item is `- key: value`; the value is the rest of the line after the first
  `:`, with spaces removed at both ends. The list ends at the first line that
  does not start with `- ` (an empty line ends it).
* Lines inside a fenced code block (between two lines that start with three
  backquotes) are not read.
* Everything else is ignored.

Keys: `kind` (`local` or `lws`, required), `path` (local: the storage
directory, relative to CONFIGDIR), `url` (lws: the storage root),
`auth` (`none`, `did-key` or `bearer`), `key-file` (did-key: a private P-256
JWK), `token-file` (bearer: an access token), `writable` (`true` or
`false`; default `true` for local, `false` for lws), `storage` (local:
`snapshot` or `files`, the storage format of `lws-serve --storage`; default:
what the directory holds), `base` (local: the IRI the storage root has when
`lws-serve` serves it; default `http://localhost/`).

An unknown key, a repeated key, an item with no `:`, a value outside its
set, or a key that does not apply to the kind stops the start with the file
name and the line number (`mountOfMarkdown`).

The reader is one loop over the lines (`scan`, tail recursive with an
accumulator), so a file of any length is read in fixed stack
(`skills/danbri-function-precrime-checkers`).
-/

namespace L4Factoidal.WebDAV

/-- `s` with ASCII white space removed at both ends. -/
def trimS (s : String) : String := s.trimAscii.toString

/-- `s` without its first `n` characters. -/
def dropS (s : String) (n : Nat) : String := (s.drop n).toString

inductive MountKind where
  | localStore
  | lws
deriving DecidableEq, Repr, Inhabited

def MountKind.name : MountKind → String
  | .localStore => "local"
  | .lws => "lws"

inductive AuthKind where
  | none
  | didKey
  | bearer
deriving DecidableEq, Repr, Inhabited

def AuthKind.name : AuthKind → String
  | .none => "none"
  | .didKey => "did-key"
  | .bearer => "bearer"

/-- One mount, as its file states it. -/
structure Mount where
  /-- The folder name: the file name without `.md`. -/
  name : String
  /-- The display name: the text of the first `# ` heading, or `name`. -/
  title : String
  kind : MountKind
  /-- local: the storage directory, as written (relative to CONFIGDIR). -/
  path : String := ""
  /-- lws: the storage root, ending with `/`. -/
  url : String := ""
  auth : AuthKind := .none
  keyFile : String := ""
  tokenFile : String := ""
  writable : Bool
  /-- local: `some "snapshot"`, `some "files"`, or `none` (what the
  directory holds decides). -/
  storage : Option String := none
  /-- local: the IRI of the storage root. -/
  base : String := "http://localhost/"
deriving Repr, Inhabited

/-- The keys a mount file may hold. -/
def knownKeys : List String :=
  ["kind", "path", "url", "auth", "key-file", "token-file", "writable", "storage", "base"]

/-- Where the reader is in the file. -/
inductive Phase where
  /-- Before the settings list. -/
  | before
  /-- In the settings list. -/
  | inList
  /-- After the settings list: nothing more is read. -/
  | after
deriving DecidableEq, Repr

/-- What the reader has collected. -/
structure Scan where
  phase : Phase := .before
  fenced : Bool := false
  title : Option String := none
  /-- (key, value, line number), in file order. -/
  items : List (String × String × Nat) := []
deriving Repr

/-- A list item `- key: value`, read: the key and the value, or `none` when
the item has no `:`. -/
def itemOf (line : String) : Option (String × String) :=
  let body := dropS line 2
  match body.splitOn ":" with
  | [] | [_] => none
  | k :: rest => some (trimS k, trimS (":".intercalate rest))

#guard itemOf "- kind: local" == some ("kind", "local")
#guard itemOf "- url: https://s.example/a/" == some ("url", "https://s.example/a/")
#guard itemOf "- nothing here" == none

/-- A settings item, added to the list: refused when it has no `:`, an
unknown key, or a key given before. -/
def addItem (st : Scan) (n : Nat) (line : String) : Except (Nat × String) Scan :=
  match itemOf line with
  | none => .error (n, "a settings item is `- key: value`; this one has no `:`")
  | some (k, v) =>
    if knownKeys.contains k = false then
      .error (n, s!"unknown key \"{k}\" (known: {", ".intercalate knownKeys})")
    else if st.items.any (fun (k', _, _) => k' == k) then
      .error (n, s!"the key \"{k}\" is given twice")
    else .ok { st with phase := .inList, items := st.items ++ [(k, v, n)] }

/-- One line, its line end removed. `n` is its number (from 1). A refusal
is `.error (n, why)`. -/
def scanClean (st : Scan) (n : Nat) (line : String) : Except (Nat × String) Scan :=
  if st.phase == .after then .ok st
  else if line.startsWith "```" then
    -- A fence ends the list too: it is a line that is not an item.
    .ok { st with fenced := !st.fenced,
                  phase := if st.phase == .inList then .after else st.phase }
  else if st.fenced then .ok st
  else if line.startsWith "- " then addItem st n line
  else if st.phase == .inList then .ok { st with phase := .after }
  else if line.startsWith "# " && st.title.isNone then
    .ok { st with title := some (trimS (dropS line 2)) }
  else .ok st

/-- One line. A CR before the LF is part of the line end, not of the line. -/
def scanLine (st : Scan) (n : Nat) (raw : String) : Except (Nat × String) Scan :=
  scanClean st n (if raw.endsWith "\r" then (raw.dropEnd 1).toString else raw)

/-- Every line, in one loop. -/
def scan (st : Scan) (n : Nat) : List String → Except (Nat × String) Scan
  | [] => .ok st
  | l :: rest =>
    match scanLine st n l with
    | .error e => .error e
    | .ok st' => scan st' (n + 1) rest

/-- The value of a key and its line, if given. -/
def Scan.get? (st : Scan) (k : String) : Option (String × Nat) :=
  (st.items.find? (fun (k', _, _) => k' == k)).map (fun (_, v, n) => (v, n))

/-- Is `u` an `http` or `https` URL with an authority? -/
def isHttpUrl (u : String) : Bool :=
  (u.startsWith "http://" && u.length > 7) || (u.startsWith "https://" && u.length > 8)

/-- The checks that need the whole list: required keys, values in their
sets, keys that do not apply to the kind. -/
def validate (name : String) (st : Scan) : Except (Nat × String) Mount := do
  let line (k : String) : Nat := ((st.get? k).map (·.2)).getD 0
  let value (k : String) : Option String := (st.get? k).map (·.1)
  let kind ← match value "kind" with
    | some "local" => pure MountKind.localStore
    | some "lws" => pure MountKind.lws
    | some v => throw (line "kind", s!"kind is `local` or `lws`, not \"{v}\"")
    | none => throw (0, "the settings list has no `kind` (`local` or `lws`)")
  let auth ← match value "auth" with
    | none | some "none" => pure AuthKind.none
    | some "did-key" => pure AuthKind.didKey
    | some "bearer" => pure AuthKind.bearer
    | some v => throw (line "auth", s!"auth is `none`, `did-key` or `bearer`, not \"{v}\"")
  let writable ← match value "writable" with
    | none => pure (kind == .localStore)
    | some "true" => pure true
    | some "false" => pure false
    | some v => throw (line "writable", s!"writable is `true` or `false`, not \"{v}\"")
  let notFor (k : String) : Except (Nat × String) Unit :=
    match st.get? k with
    | some (_, n) => throw (n, s!"the key \"{k}\" does not apply to kind `{kind.name}`")
    | none => pure ()
  let title := (st.title.filter (· != "")).getD name
  match kind with
  | .localStore =>
    notFor "url"; notFor "key-file"; notFor "token-file"
    if auth != .none then throw (line "auth", "a local mount opens the storage as its owner; it takes no `auth`")
    let path ← match value "path" with
      | some p => if p == "" then throw (line "path", "path is empty") else pure p
      | none => throw (0, "a local mount needs `path` (the storage directory)")
    let storage ← match value "storage" with
      | none => pure none
      | some "snapshot" => pure (some "snapshot")
      | some "files" => pure (some "files")
      | some v => throw (line "storage", s!"storage is `snapshot` or `files`, not \"{v}\"")
    let base ← match value "base" with
      | none => pure "http://localhost/"
      | some b =>
        if isHttpUrl b && b.endsWith "/" then pure b
        else throw (line "base", "base is an http or https IRI that ends with `/`")
    pure { name, title, kind, path, writable, storage, base }
  | .lws =>
    notFor "path"; notFor "storage"; notFor "base"
    let url ← match value "url" with
      | some u =>
        if isHttpUrl u then pure (if u.endsWith "/" then u else u ++ "/")
        else throw (line "url", "url is an http or https URL (the storage root)")
      | none => throw (0, "an lws mount needs `url` (the storage root)")
    let keyFile ← match auth, value "key-file" with
      | .didKey, some f => if f == "" then throw (line "key-file", "key-file is empty") else pure f
      | .didKey, none => throw (line "auth", "auth `did-key` needs `key-file`")
      | _, some _ => throw (line "key-file", "key-file applies to auth `did-key` only")
      | _, none => pure ""
    let tokenFile ← match auth, value "token-file" with
      | .bearer, some f => if f == "" then throw (line "token-file", "token-file is empty") else pure f
      | .bearer, none => throw (line "auth", "auth `bearer` needs `token-file`")
      | _, some _ => throw (line "token-file", "token-file applies to auth `bearer` only")
      | _, none => pure ""
    pure { name, title, kind, url, auth, keyFile, tokenFile, writable }

/-- Is `name` usable as the folder name of a mount: not empty, not starting
with `.`, with no `/`, `\` or control character? -/
def mountNameOk (name : String) : Bool :=
  name != "" && !name.startsWith "." &&
  name.all (fun c => c != '/' && c != '\\' && c.toNat ≥ 0x20 && c.toNat != 0x7f)

/-- Read one mount file. `file` is its name in CONFIGDIR (`alice.md`); the
mount name is the file name without `.md`. A refusal names the file and the
line: `alice.md:3: unknown key "colour" (...)`; line 0 means the file as a
whole. -/
def mountOfMarkdown (file : String) (text : String) : Except String Mount :=
  let name := if file.endsWith ".md" then (file.dropEnd 3).toString else file
  if !mountNameOk name then
    .error s!"{file}: the file name does not give a usable folder name"
  else
    match scan {} 1 (text.splitOn "\n") >>= validate name with
    | .ok m => .ok m
    | .error (0, why) => .error s!"{file}: {why}"
    | .error (n, why) => .error s!"{file}:{n}: {why}"

/-- Which names of CONFIGDIR are mount files: a regular name that ends with
`.md`, other than `README.md` in any case, and not starting with `.`. The
host lists the directory; this decides. -/
def isMountFile (file : String) : Bool :=
  file.endsWith ".md" && file.length > 3 && !file.startsWith "." &&
  file.toLower != "readme.md"

/-! ## Tests -/

private def okName : Except String Mount → Option String
  | .ok m => some m.name
  | .error _ => none

private def errOf : Except String Mount → String
  | .ok _ => ""
  | .error e => e

#guard okName (mountOfMarkdown "alice.md" "# Alice\n- kind: local\n- path: ./alice\n") == some "alice"
#guard (match mountOfMarkdown "alice.md" "# Alice's files\n- kind: local\n- path: ./alice\n" with
        | .ok m => m.title == "Alice's files" && m.writable && m.path == "./alice" && m.storage.isNone
        | .error _ => false)
#guard (match mountOfMarkdown "bob.md" "- kind: lws\n- url: https://s.example/bob\n- auth: did-key\n- key-file: bob.jwk\n\nNotes for people.\n- kind: local\n" with
        | .ok m => m.title == "bob" && m.url == "https://s.example/bob/" && !m.writable &&
                   m.auth == .didKey && m.keyFile == "bob.jwk"
        | .error _ => false)
-- CRLF line ends, a fenced block before the list, free text after it.
#guard (match mountOfMarkdown "c.md" "Intro\r\n```\n- kind: nonsense\n```\r\n# Title\r\n- kind: lws\r\n- url: http://h/\r\n- writable: true\r\n\r\ntext\r\n" with
        | .ok m => m.title == "Title" && m.writable && m.url == "http://h/"
        | .error _ => false)
#guard errOf (mountOfMarkdown "a.md" "# A\n- kind: local\n- colour: red\n") ==
  "a.md:3: unknown key \"colour\" (known: kind, path, url, auth, key-file, token-file, writable, storage, base)"
#guard errOf (mountOfMarkdown "a.md" "- kind: local\n- kind: lws\n") == "a.md:2: the key \"kind\" is given twice"
#guard errOf (mountOfMarkdown "a.md" "- kind local\n") == "a.md:1: a settings item is `- key: value`; this one has no `:`"
#guard errOf (mountOfMarkdown "a.md" "# no list\n") == "a.md: the settings list has no `kind` (`local` or `lws`)"
#guard errOf (mountOfMarkdown "a.md" "- kind: local\n") == "a.md: a local mount needs `path` (the storage directory)"
#guard errOf (mountOfMarkdown "a.md" "- kind: local\n- path: x\n- url: http://h/\n") ==
  "a.md:3: the key \"url\" does not apply to kind `local`"
#guard errOf (mountOfMarkdown "a.md" "- kind: lws\n- url: ftp://h/\n") ==
  "a.md:2: url is an http or https URL (the storage root)"
#guard errOf (mountOfMarkdown "a.md" "- kind: lws\n- url: http://h/\n- auth: did-key\n") ==
  "a.md:3: auth `did-key` needs `key-file`"
#guard errOf (mountOfMarkdown "a.md" "- kind: lws\n- url: http://h/\n- writable: yes\n") ==
  "a.md:3: writable is `true` or `false`, not \"yes\""
#guard errOf (mountOfMarkdown ".x.md" "- kind: local\n- path: p\n") ==
  ".x.md: the file name does not give a usable folder name"
-- Only the first list is read: a second list after free text is ignored.
#guard okName (mountOfMarkdown "z.md" "- kind: local\n- path: p\n\n- colour: red\n") == some "z"
#guard isMountFile "alice.md" && !isMountFile "README.md" && !isMountFile "notes.txt" && !isMountFile ".hidden.md"

/-! ## Theorems -/

theorem addItem_known {st st' : Scan} {n : Nat} {l : String}
    (h : addItem st n l = .ok st') (hk : ∀ i ∈ st.items, knownKeys.contains i.1 = true) :
    ∀ i ∈ st'.items, knownKeys.contains i.1 = true := by
  unfold addItem at h
  split at h
  · cases h
  · rename_i k v _
    by_cases h1 : knownKeys.contains k = false
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : st.items.any (fun (k', _, _) => k' == k) = true
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        cases h
        intro i hi
        simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with hi | hi
        · exact hk i hi
        · subst hi; simpa using h1

/-- One line keeps every collected key known. -/
theorem scanClean_known {st st' : Scan} {n : Nat} {l : String}
    (h : scanClean st n l = .ok st') (hk : ∀ i ∈ st.items, knownKeys.contains i.1 = true) :
    ∀ i ∈ st'.items, knownKeys.contains i.1 = true := by
  unfold scanClean at h
  by_cases c1 : (st.phase == Phase.after) = true
  · rw [if_pos c1] at h; cases h; exact hk
  rw [if_neg c1] at h
  by_cases c2 : l.startsWith "```" = true
  · rw [if_pos c2] at h; cases h; exact hk
  rw [if_neg c2] at h
  by_cases c3 : st.fenced = true
  · rw [if_pos c3] at h; cases h; exact hk
  rw [if_neg c3] at h
  by_cases c4 : l.startsWith "- " = true
  · rw [if_pos c4] at h; exact addItem_known h hk
  rw [if_neg c4] at h
  by_cases c5 : (st.phase == Phase.inList) = true
  · rw [if_pos c5] at h; cases h; exact hk
  rw [if_neg c5] at h
  by_cases c6 : (l.startsWith "# " && st.title.isNone) = true
  · rw [if_pos c6] at h; cases h; exact hk
  · rw [if_neg c6] at h; cases h; exact hk

theorem scanLine_known {st st' : Scan} {n : Nat} {l : String}
    (h : scanLine st n l = .ok st') (hk : ∀ i ∈ st.items, knownKeys.contains i.1 = true) :
    ∀ i ∈ st'.items, knownKeys.contains i.1 = true :=
  scanClean_known h hk

/-- A file the reader accepts holds no unknown key: every collected item's
key is one of `knownKeys`. -/
theorem scan_known : ∀ (ls : List String) {st st' : Scan} {n : Nat},
    scan st n ls = .ok st' → (∀ i ∈ st.items, knownKeys.contains i.1 = true) →
    ∀ i ∈ st'.items, knownKeys.contains i.1 = true
  | [], st, st', n, h, hk => by
    simp only [scan] at h; cases h; exact hk
  | l :: rest, st, st', n, h, hk => by
    simp only [scan] at h
    split at h
    · cases h
    · rename_i st1 h1
      exact scan_known rest h (scanLine_known h1 hk)

end L4Factoidal.WebDAV
