/-
L4Factoidal.WebDAV.Backend — what the WebDAV server asks of a storage.
https://github.com/danbri/factoidal/issues/1066

The server is written once, over an abstract storage, and runs against two
kinds of mount:

* `local` — an LWS storage directory, opened by the same ops `lws-serve`
  uses (`lwsOpen`, `lwsStep`), stepped as its owner with no HTTP between
  (`L4Factoidal.WebDAV.Local`);
* `lws` — a remote LWS storage, reached through the LWS client state
  machine (`L4Factoidal.LWS.Client.step`, `L4Factoidal.WebDAV.Remote`).

A WebDAV request is a PROGRAM over storage operations (`Prog`): the server
names one operation (`BOp`), the mount answers it (`BAns`), and the
program continues from the answer. A program is data, so the same handler
runs against a model in a `#guard`, against `LWS.step MemStore` in a
`#guard`, and against a real storage through the host, which carries each
operation (to `lwsStep`, or as the client's `fetch` requests) and nothing
else.

The six operations are the storage's own: stat (`head`), `list`, read
(`get`), write (`put`, with "only if absent" for MKCOL and for the empty
resource LOCK makes), `delete` (recursive for a container). Copy and move
are not storage operations: LWS has no copy, and its move (a change of the
`up` link, lws10-core §Moving Resources) keeps the name, where a WebDAV
MOVE also renames. The server builds both from the six (`Server.copyTree`),
for both kinds of mount.

A storage path is absolute in the mount's storage: `/` is the storage root,
a container ends with `/`, a data resource does not.
-/
import L4Factoidal.WebDAV.Path

namespace L4Factoidal.WebDAV

/-- One storage operation. -/
inductive BOp where
  /-- The metadata of one resource (HEAD). -/
  | head (path : String)
  /-- The members of a container (every page). -/
  | list (path : String)
  /-- The content of a data resource (GET). -/
  | get (path : String)
  /-- Write a resource (PUT). `onlyNew`: refused when it exists
  (`If-None-Match: *`). A container path with no content makes a
  container. -/
  | put (path : String) (contentType : String) (body : ByteArray) (onlyNew : Bool)
  /-- Delete a resource; a container with all it contains. -/
  | delete (path : String)

def BOp.path : BOp → String
  | .head p | .list p | .get p | .put p _ _ _ | .delete p => p

def BOp.name : BOp → String
  | .head _ => "head" | .list _ => "list" | .get _ => "get" | .put .. => "put" | .delete _ => "delete"

/-- What a storage knows of one resource. -/
structure Meta where
  path : String
  isColl : Bool
  etag : Option String := none
  contentType : Option String := none
  length : Option Nat := none
  /-- An HTTP-date (RFC 9110 §5.6.7). -/
  modified : Option String := none
deriving Repr, Inhabited, BEq

/-- The answer to one operation. `status` is the storage's HTTP status (0
when no answer came: a transport failure, or a refusal by the client before
any request). -/
structure BAns where
  status : Nat
  info : Option Meta := none
  members : List Meta := []
  body : ByteArray := ByteArray.empty
  detail : String := ""
deriving Inhabited

def BAns.ok (a : BAns) : Bool := 200 ≤ a.status && a.status < 300

/-- A program over storage operations. -/
inductive Prog (α : Type) where
  | pure : α → Prog α
  | call : BOp → (BAns → Prog α) → Prog α

def Prog.bind {α β : Type} : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .call op k, f => .call op (fun r => Prog.bind (k r) f)

instance : Monad Prog where
  pure := .pure
  bind := Prog.bind

/-- Ask the storage. -/
def ask (op : BOp) : Prog BAns := .call op .pure

/-- Run a program against a pure storage model `run`, at most `fuel`
operations; `none` when the fuel ends first. Used by the `#guard`s and the
theorems. One loop. -/
def Prog.runPure {σ α : Type} (run : σ → BOp → BAns × σ) : Nat → Prog α → σ → Option (α × σ)
  | _, .pure a, s => some (a, s)
  | 0, .call _ _, _ => none
  | n + 1, .call op k, s =>
    let (r, s') := run s op
    Prog.runPure run n (k r) s'

/-- The operations a program names before it finishes, against a model;
the theorems use it to state what a request does to the storage. -/
def Prog.trace {σ α : Type} (run : σ → BOp → BAns × σ) : Nat → Prog α → σ → List BOp
  | _, .pure _, _ => []
  | 0, .call _ _, _ => []
  | n + 1, .call op k, s =>
    let (r, s') := run s op
    op :: Prog.trace run n (k r) s'

/-- Is an operation a write? -/
def BOp.isWrite : BOp → Bool
  | .put .. | .delete _ => true
  | _ => false

end L4Factoidal.WebDAV
