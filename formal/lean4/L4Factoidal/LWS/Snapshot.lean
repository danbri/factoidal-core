/-
L4Factoidal.LWS.Snapshot — the durable form of an in-memory storage.

`factoidal lws-serve DIR` and `factoidal solid-serve DIR` keep a storage in
an engine handle. A storage that loses every resource when the process stops
is not usable as storage, so the host writes this snapshot to `DIR` after
every request that changed the state, and gives it back to `lwsOpen` /
`solidOpen` on the next start. The LWS draft states no persistence rule;
the reason is the definition of a storage itself (§Terminology, "storage —
a space of URI-addressable resources"), which a server restart must not
empty.

The host only moves the bytes: it writes the document to a temporary file
in `DIR` and renames it over `DIR/lws-state.json`, so a crash leaves either
the old or the new snapshot. Which paths may appear is decided here:
`ofJson` refuses an entry whose path is not a valid storage path
(`validTarget`: no `..`, no `.`, no empty segment, no backslash, no encoded
slash, no NUL), so a snapshot edited by hand cannot introduce a resource the
request path check would refuse.

The document:

    {"format":"lws-snapshot-1","clock":N,
     "entries":[{"path":"/a","kind":"dataResource","contentType":"text/plain",
                 "body":"…","mtime":N}, …]}
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Binding

namespace L4Factoidal.LWS

open L4Factoidal.JSON

def snapshotFormat : String := "lws-snapshot-1"

def ResourceKind.name : ResourceKind → String
  | .container => "container"
  | .dataResource => "dataResource"
  | .storageRoot => "storageRoot"
  | .metadataResource => "metadataResource"
  | .linksetResource => "linksetResource"

def ResourceKind.ofName? : String → Option ResourceKind
  | "container" => some .container
  | "dataResource" => some .dataResource
  | "storageRoot" => some .storageRoot
  | "metadataResource" => some .metadataResource
  | "linksetResource" => some .linksetResource
  | _ => none

def entryJson (e : Entry) : Json :=
  .object [ ("path", .string e.path), ("kind", .string e.kind.name)
          , ("contentType", .string e.contentType), ("body", .string e.body)
          , ("mtime", .number (toString e.mtime)) ]

/-- The snapshot document of a state. Entries keep the state's order. -/
def snapshotJson (s : MemState) : Json :=
  .object [ ("format", .string snapshotFormat)
          , ("clock", .number (toString s.clock))
          , ("entries", .array (s.entries.map entryJson)) ]

private def natField (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number n) => n.toNat?
  | _ => none

def entryOfJson (j : Json) : Except String Entry := do
  let path ← (j.getString? "path").elim (.error "snapshot: an entry has no path") .ok
  if !validTarget path then .error s!"snapshot: refused path {path}" else
  let kind ← ((j.getString? "kind").bind ResourceKind.ofName?).elim
    (.error s!"snapshot: entry {path} has no valid kind") .ok
  let contentType := (j.getString? "contentType").getD "application/octet-stream"
  let body := (j.getString? "body").getD ""
  let mtime := (natField j "mtime").getD 0
  .ok { path, kind, contentType, body, mtime }

/-- Read a snapshot document back. The clock is raised above every stored
modification time, so the next write still stamps a strictly larger time. -/
def memStateOfJson (j : Json) : Except String MemState := do
  if j.getString? "format" != some snapshotFormat then
    .error s!"snapshot: format is not {snapshotFormat}" else
  let items ← (j.getArray? "entries").elim (.error "snapshot: no entries") .ok
  let entries ← items.mapM entryOfJson
  if !(entries.any (fun e => e.path == rootPath && e.kind == .storageRoot)) then
    .error "snapshot: no storage root" else
  let paths := entries.map (·.path)
  if paths.eraseDups.length != paths.length then .error "snapshot: a path repeats" else
  let maxM := entries.foldl (fun m e => max m e.mtime) 0
  .ok { entries, clock := max ((natField j "clock").getD 0) (maxM + 1) }

end L4Factoidal.LWS
