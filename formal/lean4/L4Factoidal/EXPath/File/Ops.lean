/-
L4Factoidal.EXPath.File.Ops — the `file:` functions of the EXPath File
Module 4.0 (https://qt4cg.org/specifications/expath-file-40/Overview.html,
qtspecs commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c), written once
against the host interface `EXPath.File.Host`.

Every function receives its arguments already coerced to the signature
of `EXPath.Catalog`. Errors carry the expanded QName
`Q{http://expath.org/ns/file}local` as the code.

Paths (§ File Paths): a path string is a UNIX path, a Windows-style
path whose `\` separators are read as `/`, or a `file:` URI. A
relative path is resolved against the current working directory of
the host. A path that this module generates for a directory ends with
`/`; a name appended to a supplied path gets a `/` only when the
supplied path does not end with one.

Implementation-defined choices: the directory separator is `/`, the
line separator is `&#10;`, the path separator is `:`, the only root is
`/`, temporary names are `<prefix>tmp<n><suffix>` with a counter `n`,
glob matching in file:list is case-sensitive, text is written without
a byte order mark, and file properties are not kept by copy and move.
-/
import L4Factoidal.EXPath.File.Host
import L4Factoidal.EXPath.Binary.Lib

namespace L4Factoidal.EXPath.File

open L4Factoidal.XPath4
open L4Factoidal.XSD

def nsFILE : String := "http://expath.org/ns/file"

/-- A `file:` function in the host monad `m`. -/
abbrev FileFn (m : Type → Type) := Hooks → Env → List Seq → m Seq

def fileErr {m : Type → Type} [MonadExceptOf Err m] {α} (local_ : String) (msg : String := "") : m α :=
  throw { code := "Q{" ++ nsFILE ++ "}" ++ local_, msg }

/-- The functions that only compute with path strings: they need no
    file system (they read only the current working directory). -/
def pathOnlyFns : List String :=
  ["is-absolute", "name", "path-to-uri", "resolve-path", "dir-separator", "line-separator",
   "path-separator", "list-roots", "temp-dir", "base-dir", "current-dir"]

/-- The names of the functions that change the file system. The
    effect evaluator (`EXPath.File.Exec`) orders their calls; the pure
    evaluator refuses them. -/
def writingFns : List String :=
  ["append", "append-binary", "append-text", "append-text-lines", "copy", "create-dir",
   "create-temp-dir", "create-temp-file", "delete", "move", "write", "write-binary",
   "write-text", "write-text-lines"]

/-! ## Path strings -/

/-- `\` is read as a directory separator (§ File Paths: Windows paths
    are accepted). -/
def slashes (s : String) : String := s.replace "\\" "/"

def endsWithSep (s : String) : Bool := s.endsWith "/" || s.endsWith "\\"

/-- Append a name to a supplied path (§ File Paths). -/
def joinName (base name : String) : String :=
  if base == "" then name else if endsWithSep base then base ++ name else base ++ "/" ++ name

/-- `file:name`: the last segment of the path string. -/
def nameOf (s : String) : String :=
  let s := slashes ((fileUriPath? s).getD s)
  match (s.splitOn "/").filter (· != "") |>.getLast? with
  | some n => n
  | none => ""

/-- Glob matching with `*` and `?` (§ file:list). -/
def globMatch (pat name : List Char) : Bool :=
  let rec go (fuel : Nat) (p n : List Char) : Bool :=
    match fuel with
    | 0 => false
    | f + 1 =>
    match p, n with
    | [], [] => true
    | '*' :: pr, _ => go f pr n || (match n with | _ :: nr => go f p nr | [] => false)
    | '?' :: pr, _ :: nr => go f pr nr
    | c :: pr, d :: nr => c == d && go f pr nr
    | _, _ => false
  go ((pat.length + 1) * (name.length + 1) + 1) pat name

/-- Percent-encode a path for a `file:` URI (RFC 3986 path characters
    are kept). -/
def uriEncodePath (s : String) : String :=
  let keep (c : Char) := c.isAlphanum || "/-._~!$&'()*+,;=:@".toList.contains c
  String.join (s.toUTF8.data.toList.map (fun b =>
    let c := Char.ofNat b.toNat
    if b.toNat < 128 && keep c then String.singleton c
    else "%" ++ String.ofList [hexDigitChar (b.toNat / 16), hexDigitChar (b.toNat % 16)]))

/-! ## Arguments -/

def strArg (s : Seq) : String := strOf s
def optStr (s : Seq) : Option String := (optAtom s).map Atomic.str
def binArgD (s : Seq) : List Nat := (Binary.binArg s).getD []

/-- An entry of an options map. -/
def optEntry (opts : Seq) (key : String) : Option Seq :=
  match opts with
  | [.map kvs] => (kvs.find? (fun (k, _) => k.isStringLike && k.str == key)).map (·.2)
  | _ => none

/-! ## Text -/

/-- Encode text for writing; errors in the file namespace. -/
def encodeText {m} [Monad m] [MonadExceptOf Err m] (enc : String) (s : String) : m (List Nat) := do
  match Binary.encOfName? enc with
  | none => fileErr "unknown-encoding" ("encoding not supported: " ++ enc)
  | some e =>
    match Binary.encodeWith e s with
    -- `UTF-16` is written most significant byte first, after a byte
    -- order mark (implementation-defined, § file:write-text)
    | some bs => pure (if enc.toUpper == "UTF-16" then [0xFE, 0xFF] ++ bs else bs)
    | none => fileErr "io-error" ("a character cannot be written in " ++ enc)

/-- UTF-8 with every malformed sequence replaced by U+FFFD (the
    `fallback` option of file:read-text). -/
def decodeUtf8Lossy (bs : List Nat) : String := Id.run do
  let arr := bs.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let n := arr.size
  for _ in [0:n] do
    if i ≥ n then break
    let b := arr[i]!
    let (len, init) :=
      if b < 0x80 then (1, b) else if b &&& 0xE0 == 0xC0 then (2, b &&& 0x1F)
      else if b &&& 0xF0 == 0xE0 then (3, b &&& 0x0F) else if b &&& 0xF8 == 0xF0 then (4, b &&& 0x07)
      else (0, 0)
    if len == 0 then out := out.push '�'; i := i + 1; continue
    let mut cp := init
    let mut ok : Bool := decide (i + len ≤ n)
    if ok then
      for k in [1:len] do
        let c := arr[i + k]!
        if c &&& 0xC0 == 0x80 then cp := cp * 64 + (c &&& 0x3F) else ok := false
    let minCp := if len == 2 then 0x80 else if len == 3 then 0x800 else if len == 4 then 0x10000 else 0
    if ok && cp ≥ minCp && cp ≤ 0x10FFFF && !(0xD800 ≤ cp && cp ≤ 0xDFFF) then
      out := out.push (Char.ofNat cp); i := i + len
    else
      out := out.push '�'; i := i + 1
  return String.ofList out.toList

/-- Read the octets of a file as text (§ file:read-text). -/
def decodeText {m} [Monad m] [MonadExceptOf Err m] (bs : List Nat) (enc : Option String)
    (normalize fallback : Bool) : m String := do
  let s ← match Binary.inferEncoding bs enc with
    | none => fileErr "unknown-encoding" ("encoding not supported: " ++ enc.getD "")
    | some (n, o) =>
      match Binary.encOfName? n with
      | none => fileErr "unknown-encoding" ("encoding not supported: " ++ n)
      | some e =>
        match Binary.decodeWith e (bs.drop o) with
        | some s => pure s
        | none =>
          if fallback && e == .utf8 then pure (decodeUtf8Lossy (bs.drop o))
          else fileErr "io-error" ("the file is not valid " ++ n)
  let s ← if s.toList.all XML.isXmlChar then pure s
    else if fallback then pure (String.ofList (s.toList.map (fun c => if XML.isXmlChar c then c else '�')))
    else fileErr "io-error" "the file contains a character that is not allowed in XML"
  if normalize then pure ((s.replace "\r\n" "\n").replace "\r" "\n") else pure s

/-- The options of file:read-text: a string is the encoding. -/
def textOptions (opts : Seq) : Option String × Bool × Bool :=
  match opts with
  | [.map _] =>
    ((optEntry opts "encoding").bind optStr,
     ((optEntry opts "normalize-newlines").map boolOf).getD true,
     ((optEntry opts "fallback").map boolOf).getD false)
  | [.atom a] => (some a.str, true, false)
  | _ => (none, true, false)

def lines (s : String) : List String :=
  let ls := s.splitOn "\n"
  match ls.getLast? with
  | some "" => ls.dropLast
  | _ => ls

/-! ## The functions, over a host -/

section
variable {m : Type → Type} [Monad m] [MonadExceptOf Err m] (h : Host m)

def res (s : String) : Path := resolveSegs h.cwd (slashes s)

def statOf (p : Path) : m (Option Stat) := h.stat p

/-- The target of a write: not a directory, and its parent a directory. -/
def checkTarget (p : Path) : m Unit := do
  match ← h.stat p with
  | some (.dir _) => fileErr "is-dir" ("path is a directory: " ++ pathStr p)
  | _ =>
    match ← h.stat p.dropLast with
    | some (.dir _) => pure ()
    | _ => fileErr "no-dir" ("the parent directory does not exist: " ++ pathStr p.dropLast true)

def writeOrAppend (p : Path) (bs : List Nat) (append : Bool) : m Seq := do
  checkTarget h p
  let old ← if append then (match ← h.stat p with
      | some (.file _ _) => h.read p
      | _ => pure []) else pure []
  h.write p (old ++ bs)
  pure []

/-- Create a directory and its missing parents (§ file:create-dir). -/
def mkdirs (p : Path) : m Unit := do
  for k in [1:p.length + 1] do
    let q := p.take k
    match ← h.stat q with
    | some (.dir _) => pure ()
    | some (.file _ _) => fileErr "exists" ("a file exists at " ++ pathStr q)
    | none => h.mkdir q

/-- The entries below a directory, depth first, with their depth
    (1 = directly inside). A loop over a work list. -/
def walk (p : Path) (maxDepth : Option Nat := none) : m (List (Path × Bool × Nat)) := do
  let mut out : Array (Path × Bool × Nat) := #[]
  let mut todo : List (Path × Nat) := [(p, 0)]
  -- each directory is listed once; the loop ends when the work list is empty
  for _ in [0:1000000] do
    match todo with
    | [] => break
    | (d, k) :: rest =>
      todo := rest
      let names ← h.list d
      let mut sub : List (Path × Nat) := []
      for nm in names do
        let q := d ++ [nm]
        let isD := (← h.stat q).map Stat.isDir |>.getD false
        out := out.push (q, isD, k + 1)
        if isD && (maxDepth.map (fun x => decide (k + 1 < x))).getD true then sub := sub ++ [(q, k + 1)]
      todo := sub ++ todo
  return out.toList

/-- Remove a path and everything below it. -/
def removeTree (p : Path) : m Unit := do
  let ds ← walk h p
  for (q, _, _) in ds.reverse do h.remove q
  h.remove p

/-- Copy a file or a directory tree (no checks). -/
def copyTree (src dst : Path) : m Unit := do
  match ← h.stat src with
  | some (.file _ _) =>
    match ← h.stat dst with
    | some (.dir _) => fileErr "is-dir" ("a directory exists at " ++ pathStr dst)
    | _ => h.write dst (← h.read src)
  | some (.dir _) =>
    match ← h.stat dst with
    | some (.file _ _) => fileErr "exists" ("a file exists at " ++ pathStr dst)
    | some (.dir _) => pure ()
    | none => h.mkdir dst
    for (q, isD, _) in ← walk h src do
      let t := dst ++ q.drop src.length
      if isD then
        match ← h.stat t with
        | some (.dir _) => pure ()
        | some (.file _ _) => fileErr "exists" ("a file exists at " ++ pathStr t)
        | none => h.mkdir t
      else
        match ← h.stat t with
        | some (.dir _) => fileErr "is-dir" ("a directory exists at " ++ pathStr t)
        | _ => h.write t (← h.read q)
  | none => fileErr "not-found" ("no such file or directory: " ++ pathStr src)

/-- The common part of file:copy and file:move: the effective target. -/
def transferTarget (src dst : Path) (isMove : Bool) : m (Option Path) := do
  let some s ← h.stat src | fileErr "not-found" ("no such file or directory: " ++ pathStr src)
  if src == dst then return none
  match s with
  | .dir _ =>
    match ← h.stat dst with
    | some (.file _ _) => fileErr "exists" ("the target is a file: " ++ pathStr dst)
    | some (.dir _) =>
      let t := dst ++ [src.getLast?.getD ""]
      if src.isPrefixOf t then fileErr "cyclic" "the target is inside the source directory"
      if isMove then
        if let some (.dir _) ← h.stat t then
          fileErr "is-dir" ("the target directory already contains " ++ pathStr t)
      return some t
    | none =>
      if src.isPrefixOf dst then fileErr "cyclic" "the target is inside the source directory"
      mkdirs h dst.dropLast
      return some dst
  | .file _ _ =>
    match ← h.stat dst with
    | some (.dir _) =>
      let t := dst ++ [src.getLast?.getD ""]
      if let some (.dir _) ← h.stat t then
        fileErr "is-dir" ("the target directory contains a directory named " ++ pathStr t)
      return some t
    | _ =>
      mkdirs h dst.dropLast
      return some dst

def tempName (pre suf : Option String) : m String := do
  let n ← h.fresh
  pure (pre.getD "" ++ "tmp" ++ toString n ++ suf.getD "")

def createTemp (isDir : Bool) (a : List Seq) : m Seq := do
  let d := match optStr (argN a 2) with | some s => res h s | none => h.tmp
  match ← h.stat d with
  | some (.dir _) => pure ()
  | _ => fileErr "no-dir" ("not a directory: " ++ pathStr d)
  let mut p := d
  for _ in [0:1000] do
    p := d ++ [← tempName h (optStr (argN a 0)) (optStr (argN a 1))]
    if (← h.stat p).isNone then break
  if isDir then h.mkdir p else h.write p []
  pure (sStr (pathStr p isDir))

def mustExist (p : Path) : m Stat := do
  match ← h.stat p with
  | some s => pure s
  | none => fileErr "not-found" ("no such file or directory: " ++ pathStr p)

def mustDir (p : Path) : m Unit := do
  match ← mustExist h p with
  | .dir _ => pure ()
  | _ => fileErr "no-dir" ("not a directory: " ++ pathStr p)

/-- Serialize a value for file:write and file:append: through
    `fn:serialize` when the evaluator has it; otherwise, for a sequence
    of atomic values with the `xml`, `text` or `adaptive` method, the
    string values joined by the item separator (Serialization 3.1 §2
    sequence normalization). -/
def serialize (hk : Hooks) (v opts : Seq) : m String := do
  let fnSer : QN := { uri := nsFN, loc := "serialize" }
  let optsArg : Seq := match opts with | [] => [.map []] | o => o
  match hk.call (.fn (.builtin fnSer 2)) [v, optsArg] with
  | .ok r => pure (strOf r)
  | .error e =>
    if e.code != "XPST0017" then throw e else
    let meth := ((optEntry opts "method").bind optStr).getD "xml"
    let sep := ((optEntry opts "item-separator").bind optStr).getD " "
    if (meth == "xml" || meth == "text" || meth == "adaptive") && v.all (fun i => match i with | .atom _ => true | _ => false) then
      pure (String.intercalate sep (v.map (fun i => match i with | .atom x => x.str | _ => "")))
    else throw e

/-- The `file:` functions over the host `h`, by local name. -/
def fileTable : List (String × FileFn m) := [
  ("exists", show FileFn m from fun _ _ a => do pure (sBool (← h.stat (res h (strArg (argN a 0)))).isSome)),
  ("is-dir", show FileFn m from fun _ _ a => do pure (sBool (((← h.stat (res h (strArg (argN a 0)))).map Stat.isDir).getD false))),
  ("is-file", show FileFn m from fun _ _ a => do
    pure (sBool (match ← h.stat (res h (strArg (argN a 0))) with | some (.file _ _) => true | _ => false))),
  ("is-absolute", show FileFn m from fun _ _ a => pure (sBool (isAbsolute (slashes (strArg (argN a 0)))))),
  ("last-modified", show FileFn m from fun _ _ a => do
    let s ← mustExist h (res h (strArg (argN a 0)))
    pure (single (← liftM' (castAtomic (Atomic.ofStr s.mtime) (.b .dateTime))))),
  ("size", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    match ← mustExist h p with
    | .file n _ => pure (sInt n)
    | .dir _ =>
      if boolOf (argN a 1) then
        let mut t := 0
        for (q, isD, _) in ← walk h p do
          if !isD then
            if let some (.file n _) ← h.stat q then t := t + n
        pure (sInt t)
      else pure (sInt 0)),
  ("append", show FileFn m from fun hk _ a => do
    let opts := argN a 2
    let enc := ((optEntry opts "encoding").bind optStr).getD "UTF-8"
    writeOrAppend h (res h (strArg (argN a 0))) (← encodeText enc (← serialize hk (argN a 1) opts)) true),
  ("append-binary", show FileFn m from fun _ _ a => writeOrAppend h (res h (strArg (argN a 0))) (binArgD (argN a 1)) true),
  ("append-text", show FileFn m from fun _ _ a => do
    writeOrAppend h (res h (strArg (argN a 0)))
      (← encodeText ((optStr (argN a 2)).getD "UTF-8") (strArg (argN a 1))) true),
  ("append-text-lines", show FileFn m from fun _ _ a => do
    let txt := String.join ((argN a 1).map (fun i => match i with | .atom x => x.str ++ "\n" | _ => ""))
    writeOrAppend h (res h (strArg (argN a 0))) (← encodeText ((optStr (argN a 2)).getD "UTF-8") txt) true),
  ("copy", show FileFn m from fun _ _ a => do
    let src := res h (strArg (argN a 0))
    match ← transferTarget h src (res h (strArg (argN a 1))) false with
    | some t => copyTree h src t; pure []
    | none => pure []),
  ("create-dir", show FileFn m from fun _ _ a => do mkdirs h (res h (strArg (argN a 0))); pure []),
  ("create-temp-dir", show FileFn m from fun _ _ a => createTemp h true a),
  ("create-temp-file", show FileFn m from fun _ _ a => createTemp h false a),
  ("delete", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    match ← h.stat p with
    | none => pure []
    | some (.file _ _) => h.remove p; pure []
    | some (.dir _) =>
      if p.isEmpty then fileErr "io-error" "the root directory cannot be deleted" else
      if (← h.list p).isEmpty then h.remove p; pure []
      else if boolOf (argN a 1) then removeTree h p; pure []
      else fileErr "is-dir" ("the directory is not empty: " ++ pathStr p true)),
  ("list", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    mustDir h p
    let pat := optStr (argN a 2)
    let rec' := boolOf (argN a 1)
    let es ← walk h p (if rec' then none else some 1)
    pure (es.filterMap (fun (q, isD, _) =>
      let nm := q.getLast?.getD ""
      if (pat.map (fun g => globMatch g.toList nm.toList)).getD true then
        some (Item.atom (Atomic.ofStr (String.intercalate "/" (q.drop p.length) ++ (if isD then "/" else ""))))
      else none))),
  ("list-roots", show FileFn m from fun _ _ _ => pure (sStr "/")),
  ("move", show FileFn m from fun _ _ a => do
    let src := res h (strArg (argN a 0))
    match ← transferTarget h src (res h (strArg (argN a 1))) true with
    | some t =>
      copyTree h src t
      match ← h.stat src with
      | some (.dir _) => removeTree h src
      | _ => h.remove src
      pure []
    | none => pure []),
  ("read-binary", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    match ← mustExist h p with
    | .dir _ => fileErr "is-dir" ("path is a directory: " ++ pathStr p true)
    | .file _ _ =>
      let bs ← h.read p
      let off := intOf (argN a 1)
      let len := (optAtom (argN a 2)).map (fun _ => intOf (argN a 2))
      if off < 0 || off > bs.length then fileErr "out-of-range" s!"offset {off} is outside the file" else
      match len with
      | some l =>
        if l < 0 || off + l > bs.length then fileErr "out-of-range" s!"length {l} exceeds the file"
        else pure (Binary.b64 ((bs.drop off.toNat).take l.toNat))
      | none => pure (Binary.b64 (bs.drop off.toNat))),
  ("read-text", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    match ← mustExist h p with
    | .dir _ => fileErr "is-dir" ("path is a directory: " ++ pathStr p true)
    | .file _ _ =>
      let (enc, norm, fb) := textOptions (argN a 1)
      pure (sStr (← decodeText (← h.read p) enc norm fb))),
  ("read-text-lines", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    match ← mustExist h p with
    | .dir _ => fileErr "is-dir" ("path is a directory: " ++ pathStr p true)
    | .file _ _ =>
      let (enc, _, fb) := textOptions (argN a 1)
      let s ← decodeText (← h.read p) enc true fb
      pure ((lines s).map (fun l => Item.atom (Atomic.ofStr l)))),
  ("write", show FileFn m from fun hk _ a => do
    let opts := argN a 2
    let enc := ((optEntry opts "encoding").bind optStr).getD "UTF-8"
    writeOrAppend h (res h (strArg (argN a 0))) (← encodeText enc (← serialize hk (argN a 1) opts)) false),
  ("write-binary", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    checkTarget h p
    let bs := binArgD (argN a 1)
    -- no `$offset`: the file is replaced; an `$offset`: the octets
    -- from that position are overwritten (§ file:write-binary)
    let old ← match ← h.stat p with
      | some (.file _ _) => h.read p
      | _ => pure []
    let new ← match optAtom (argN a 2) with
      | none => pure bs
      | some _ =>
        let off := intOf (argN a 2)
        if off < 0 || off > old.length then fileErr "out-of-range" s!"offset {off} is outside the file" else
        let o := off.toNat
        pure (old.take o ++ bs ++ old.drop (o + bs.length))
    h.write p new
    pure []),
  ("write-text", show FileFn m from fun _ _ a => do
    writeOrAppend h (res h (strArg (argN a 0)))
      (← encodeText ((optStr (argN a 2)).getD "UTF-8") (strArg (argN a 1))) false),
  ("write-text-lines", show FileFn m from fun _ _ a => do
    let txt := String.join ((argN a 1).map (fun i => match i with | .atom x => x.str ++ "\n" | _ => ""))
    writeOrAppend h (res h (strArg (argN a 0))) (← encodeText ((optStr (argN a 2)).getD "UTF-8") txt) false),
  ("name", show FileFn m from fun _ _ a => pure (sStr (nameOf (strArg (argN a 0))))),
  ("parent", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    if p.isEmpty then pure [] else pure (sStr (pathStr p.dropLast true))),
  ("children", show FileFn m from fun _ _ a => do
    let s := strArg (argN a 0)
    let p := res h s
    mustDir h p
    let es ← walk h p (some 1)
    pure (es.map (fun (q, isD, _) =>
      Item.atom (Atomic.ofStr (joinName s (q.getLast?.getD "") ++ (if isD then "/" else "")))))),
  ("descendants", show FileFn m from fun hk _ a => do
    let s := strArg (argN a 0)
    let p := res h s
    mustDir h p
    let opts := argN a 1
    let depth : Option Nat := match (optEntry opts "depth").bind optAtom with
      | some d => some ((intOf [.atom d]).toNat + 1)
      | none => none
    let recurse := (optEntry opts "recurse").bind (fun v => match v with | [f] => some f | _ => none)
    let filter := (optEntry opts "filter").bind (fun v => match v with | [f] => some f | _ => none)
    let callP (f : Item) (path : String) : m Bool := do
      match ← liftM' (hk.callN f [sStr path]) with
      | [.atom ⟨_, .bool b⟩] => pure b
      | [] => pure false
      | _ => liftM' (err "XPTY0004" "a predicate must return xs:boolean?")
    let mut out : Array Item := #[]
    let mut todo : List (Path × String × Nat) := [(p, s, 0)]
    -- each directory is visited once; the loop ends when the work list is empty
    for _ in [0:1000000] do
      match todo with
      | [] => break
      | (d, ds, k) :: rest =>
        todo := rest
        let mut sub : List (Path × String × Nat) := []
        for nm in ← h.list d do
          let q := d ++ [nm]
          let isD := ((← h.stat q).map Stat.isDir).getD false
          let qs := joinName ds nm ++ (if isD then "/" else "")
          let keep ← match filter with | some f => callP f qs | none => pure true
          if keep then out := out.push (Item.atom (Atomic.ofStr qs))
          if isD && (depth.map (fun x => decide (k + 1 < x))).getD true then
            let go ← match recurse with | some f => callP f qs | none => pure true
            if go then sub := sub ++ [(q, qs, k + 1)]
        todo := sub ++ todo
    pure out.toList),
  ("path-to-native", show FileFn m from fun _ _ a => do
    let p := res h (strArg (argN a 0))
    let st ← mustExist h p
    pure (sStr (pathStr p st.isDir))),
  ("path-to-uri", show FileFn m from fun _ _ a => do
    let s := strArg (argN a 0)
    let p := res h s
    let isD := endsWithSep s || (s == "" || s == "." || s == "..")
    pure (single (Atomic.ofUri ("file://" ++ uriEncodePath (pathStr p isD))))),
  ("resolve-path", show FileFn m from fun _ _ a => do
    let s := slashes (strArg (argN a 0))
    let base ← match optStr (argN a 1) with
      | none => pure h.cwd
      | some b =>
        let b' := slashes b
        if !isAbsolute b' then fileErr "is-relative" ("the base is relative: " ++ b) else
        let bp := resolveSegs [] b'
        let isD := endsWithSep b' || ((← h.stat bp).map Stat.isDir).getD false
        pure (if isD then bp else bp.dropLast)
    let p := resolveSegs base s
    let isD := endsWithSep s || ((← h.stat p).map Stat.isDir).getD false
    pure (sStr (pathStr p isD))),
  ("dir-separator", show FileFn m from fun _ _ _ => pure (sStr "/")),
  ("line-separator", show FileFn m from fun _ _ _ => pure (sStr "\n")),
  ("path-separator", show FileFn m from fun _ _ _ => pure (sStr ":")),
  ("temp-dir", show FileFn m from fun _ _ _ => pure (sStr (pathStr h.tmp true))),
  ("base-dir", show FileFn m from fun _ env _ =>
    match fileUriPath? env.baseUri with
    | some p => pure (sStr (pathStr (resolveSegs [] p).dropLast true))
    | none => pure []),
  ("current-dir", show FileFn m from fun _ _ _ => pure (sStr (pathStr h.cwd true)))
]

end

end L4Factoidal.EXPath.File
