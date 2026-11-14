/-
L4Factoidal.ClientStorage.IdbOps — IndexedDB in motion (Indexed Database API 3.0 §2.9
"Transactions", §2.10 "Requests", §5 "Algorithms", §6 "Database operations"): connections,
transactions and their lifetime, the request queue, cursors, opening and deleting a
database, and the commands of the `web_api` op that the page side calls.

## Decisions

* Everything a page can observe is decided here: the order of exceptions of each method,
  which transaction may run (`canStart`: creation order, scopes that overlap, read-only
  transactions together), when a transaction commits (no request left, not active, its
  last event delivered), what an abort undoes, the events of an open or delete request
  (`versionchange`, `blocked`, `upgradeneeded`, `success`, `error`) and their order.
  The page side holds the objects and dispatches the events it is given: it calls `pump`
  for the next event, dispatches it, and calls `done` with what the listeners did.
* A transaction works on a copy (`Txn.work`) taken when it starts. Requests change the copy
  only. `run` answers an `Effect` beside the new live state, and it is `Effect.none` for
  every command but `pump` (`run_effect`): the databases change only when `pump` commits a
  transaction or deletes a database (`IdbStore.applyEffect`). An abort drops the copy.
* A commit that would leave the storage key above its quota is an abort with
  `QuotaExceededError` (§5.3 "commit a transaction" allows the error).
* Ids (connections, transactions, requests, cursors) are counted per storage key, inside
  the key's shelf, so they tell a page nothing about another key.

Answers are tokens: `ok` and values, or `!` + the name of the exception.
-/
import L4Factoidal.ClientStorage.IdbStore
import L4Factoidal.EventLoop.Dispatch

namespace L4Factoidal.ClientStorage.Idb

open L4Factoidal.Net.Storage (get set del)

inductive Mode where
  | ro | rw | vc
  deriving DecidableEq, Repr, Inhabited

inductive TxState where
  | active | inactive
  deriving DecidableEq, Repr, Inhabited

structure Cursor where
  id : Nat
  store : Nat
  index : Option Nat
  range : Range
  dir : Dir
  keyOnly : Bool
  /-- (key, primary key) of the record the cursor is at. -/
  pos : Option (Key × Key) := none
  /-- "Got value flag" (§2.10): a record is loaded and no step is under way. -/
  got : Bool := false
  deriving Inhabited

inductive Op where
  | put (store : Nat) (key : Option Key) (val : Val) (noOverwrite : Bool)
  | delete (store : Nat) (range : Range)
  | clear (store : Nat)
  /-- `what`: 0 the value, 1 the primary key. -/
  | get (store : Nat) (index : Option Nat) (range : Range) (what : Nat)
  /-- `what`: 0 values, 1 primary keys, 2 records. -/
  | getAll (store : Nat) (index : Option Nat) (range : Range) (count : Nat) (dir : Dir) (what : Nat)
  | count (store : Nat) (index : Option Nat) (range : Range)
  /-- `n` steps of a cursor, the first to the targets. -/
  | step (cursor : Nat) (tkey tpk : Option Key) (n : Nat)
  deriving Inhabited

structure Req where
  id : Nat
  op : Op
  deriving Inhabited

structure Txn where
  id : Nat
  conn : Nat
  db : String
  mode : Mode
  /-- The ids of the object stores in scope (a version-change transaction: every store). -/
  scope : List Nat
  state : TxState := .active
  /-- The working copy is taken. -/
  started : Bool := false
  work : Db := {}
  /-- Requests not yet run, first in first out. -/
  queue : List Req := []
  cursors : List Cursor := []
  /-- `commit()` was called: no further request. -/
  commitAsked : Bool := false
  /-- An event of this transaction is with the page (between `pump` and `done`). -/
  busy : Bool := false
  /-- The exception to abort with at the next `pump` (an index made over records that break
  its unique constraint). -/
  doom : String := ""
  /-- The open request of an upgrade transaction. -/
  openReq : Option Nat := none
  /-- The page is cloning the value of a `put`, `add` or `update`: the transaction is
  inactive until that request arrives (§6.2 "add or put": the clone runs with the
  transaction inactive, so a getter of the value cannot make a request). -/
  cloning : Bool := false
  deriving Inhabited

structure Conn where
  id : Nat
  db : String
  version : Nat
  closePending : Bool := false
  deriving Inhabited

inductive Phase where
  | waiting | notified | blocked | upgrading
  deriving DecidableEq, Inhabited

structure OpenReq where
  id : Nat
  name : String
  version : Option Nat
  delete : Bool
  phase : Phase := .waiting
  deriving Inhabited

/-- The live state of one storage key: it ends with the session and is never persisted. -/
structure Live where
  conns : List Conn := []
  /-- Live transactions, in creation order. -/
  txns : List Txn := []
  opens : List OpenReq := []
  /-- Events that wait for `pump`. -/
  events : List (List Tok) := []
  next : Nat := 1
  deriving Inhabited

/-- Everything IndexedDB keeps for one storage key: the databases (what a backend would
persist) and the live state. -/
structure Shelf where
  dbs : List (String × Db) := []
  live : Live := {}
  deriving Inhabited

instance : Usage Shelf := ⟨fun s => sizeSum (fun p : String × Db => p.1.utf8ByteSize + p.2.usage) s.dbs⟩

/-! ## Tokens of answers and arguments -/

def S (x : String) : Tok := x.toUTF8
def N (n : Nat) : Tok := (toString n).toUTF8
def ok (xs : List Tok := []) : List Tok := S "ok" :: xs
def fail (name : String) : List Tok := [S ("!" ++ name)]

def strAt (a : Array Tok) (i : Nat) : String := (String.fromUTF8? (a.getD i ByteArray.empty)).getD ""
def natAt (a : Array Tok) (i : Nat) : Nat := (strAt a i).toNat?.getD 0

/-- A counted run of tokens at `i`: the tokens and the index after them. -/
def toksAt (a : Array Tok) (i : Nat) : Array Tok × Nat :=
  let n := natAt a i
  (a.extract (i + 1) (i + 1 + n), i + 1 + n)

/-- An optional key at `i`: `none` when the tokens are not a key (invalid). -/
def keyAt (a : Array Tok) (i : Nat) : Option (Option Key) × Nat :=
  let (ts, j) := toksAt a i
  if ts.size == 0 then (some none, j) else
  match Key.ofToks ts with
  | some k => (some (some k), j)
  | none => (none, j)

/-- A key range at `i` (flags: 1 lower open, 2 upper open, 4 not a range; then the lower
and the upper key, each counted): `none` for `DataError`. -/
def rangeAt (a : Array Tok) (i : Nat) : Option Range :=
  let flags := natAt a i
  let (lo, j) := keyAt a (i + 1)
  let (hi, _) := keyAt a j
  match lo, hi with
  | some lo, some hi =>
    let r : Range := { lower := lo, upper := hi, lowerOpen := flags % 2 == 1, upperOpen := flags / 2 % 2 == 1 }
    if flags / 4 % 2 == 1 || !r.valid then none else some r
  | _, _ => none

/-- A key path argument: `n` none, `s` + a path, `a` + paths on lines. -/
def keyPathOf (x : String) : KeyPath :=
  match x.toList with
  | 's' :: cs => .one (String.ofList cs)
  | 'a' :: cs => .many (if cs.isEmpty then [] else (String.ofList cs).splitOn "\n")
  | _ => .none

def keyPathStr : KeyPath → String
  | .none => "n"
  | .one p => "s" ++ p
  | .many ps => "a" ++ "\n".intercalate ps

/-- Names in the order of `DOMStringList` (sorted by code unit). -/
def sortNames (xs : List String) : List String :=
  (xs.foldl (fun acc x => Sorted.insert cmpNats acc (unitsOf x) x) []).map (·.2)

def counted (xs : List Tok) : List Tok := N xs.length :: xs

/-! ## Live state helpers -/

def Live.txn? (l : Live) (id : Nat) : Option Txn := l.txns.find? (·.id == id)
def Live.conn? (l : Live) (id : Nat) : Option Conn := l.conns.find? (·.id == id)
def Live.setTxn (l : Live) (t : Txn) : Live := { l with txns := l.txns.map fun x => if x.id == t.id then t else x }
def Live.push (l : Live) (e : List Tok) : Live := { l with events := l.events ++ [e] }

/-- The database a transaction reads: its copy once started, the committed one before. -/
def Txn.view (t : Txn) (dbs : List (String × Db)) : Db := if t.started then t.work else (get dbs t.db).getD {}

def overlap (a b : List Nat) : Bool := a.any fun x => b.contains x

/-- A transaction may start (§2.9.1): no live transaction made before it on the same
database has an overlapping scope, unless both only read; a version-change transaction
runs alone. -/
def canStart (l : Live) (t : Txn) : Bool :=
  (l.txns.takeWhile (·.id != t.id)).all fun e =>
    e.db != t.db || (t.mode != .vc && e.mode != .vc && (!overlap e.scope t.scope || (e.mode == .ro && t.mode == .ro)))

/-- The live version-change transaction of a connection. -/
def Live.upgradeOf (l : Live) (conn : Nat) : Option Txn := l.txns.find? fun t => t.conn == conn && t.mode == .vc

/-- Drop a connection that is closing once it has no transaction. -/
def Live.reap (l : Live) (conn : Nat) : Live :=
  match l.conn? conn with
  | some c => if c.closePending && !l.txns.any (·.conn == conn) then { l with conns := l.conns.filter (·.id != conn) } else l
  | none => l

def storeNames (d : Db) : List Tok := (sortNames (d.stores.map (·.2.name))).map S

/-- "Abort a transaction" (§5.4): its requests fail with `AbortError` in order, the
transaction's `abort` event follows, the working copy is dropped; an upgrade transaction's
connection is closed and its open request fails. Nothing here touches the databases. -/
def Live.abort (l : Live) (dbs : List (String × Db)) (id : Nat) (err : String) : Live :=
  match l.txn? id with
  | none => l
  | some t =>
    let names := storeNames (if t.mode == .vc then (get dbs t.db).getD {} else t.view dbs)
    let l := t.queue.foldl (fun l r => l.push [S "req", N r.id, N t.id, S "err", S "AbortError"]) l
    let l := l.push ([S "tx", N t.id, S "abort", S err] ++ names)
    let l := { l with txns := l.txns.filter (·.id != id) }
    match t.openReq with
    | some rq =>
      let l := { l with conns := l.conns.filter (·.id != t.conn), opens := l.opens.filter (·.id != rq) }
      l.push [S "open", N rq, S "error", S "AbortError", N t.conn, N (((get dbs t.db).map (·.version)).getD 0)]
    | none => l.reap t.conn

/-! ## Running one request (§6) -/

def cursorPayload (s : Store) (c : Cursor) (row : Key × Key) : List Tok :=
  let v := if c.keyOnly then [] else ((s.find row.2).getD #[]).toList
  [S "c", N c.id] ++ counted row.1.toToks.toList ++ counted row.2.toToks.toList ++ v

/-- The key generator's number after an explicit key (§2.11). -/
def genAfter (gen : Nat) : Key → Nat
  | .number v => max gen (min (floorOfImage v + 1) 9007199254740993)
  | _ => gen

/-- Run a request on the transaction's working copy: the transaction after it and the
result (a payload, or the name of the request's error). A failed request changes nothing. -/
def exec (t : Txn) (r : Req) : Txn × Except String (List Tok) :=
  let setStore (id : Nat) (s : Store) : Txn := { t with work := { t.work with stores := set t.work.stores id s } }
  let onStore (id : Nat) (f : Store → Txn × Except String (List Tok)) : Txn × Except String (List Tok) :=
    match get t.work.stores id with
    | some s => f s
    | none => (t, .error "InvalidStateError")
  match r.op with
  | .put id key val noOverwrite => onStore id fun s =>
    let made : Option (Key × Val × Store) :=
      match key with
      | some k => some (k, val, if s.autoInc then { s with gen := genAfter s.gen k } else s)
      | none =>
        if s.gen > 9007199254740992 then none else
        let k := Key.number (Int.ofNat (natBits s.gen))
        let v := match s.keyPath with
          | .one p => (inject val k.toToks 0 (identsOf p)).getD val
          | _ => val
        some (k, v, { s with gen := s.gen + 1 })
    match made with
    | none => (t, .error "ConstraintError")
    | some (k, v, s) =>
      if noOverwrite && (s.find k).isSome then (t, .error "ConstraintError")
      else if s.conflict k v then (t, .error "ConstraintError")
      else (setStore id (s.put k v), .ok (S "k" :: k.toToks.toList))
  | .delete id range => onStore id fun s => (setStore id (s.deleteRange range), .ok [S "u"])
  | .clear id => onStore id fun s => (setStore id s.clear, .ok [S "u"])
  | .get id index range what => onStore id fun s =>
    match (s.rows index).find? fun e => range.includes e.1.1 with
    | some e =>
      if what == 1 then (t, .ok (S "k" :: e.1.2.toToks.toList))
      else (t, .ok (S "v" :: ((s.find e.1.2).getD #[]).toList))
    | none => (t, .ok [S "u"])
  | .getAll id index range count dir what => onStore id fun s =>
    let rows := rowsIn (s.rows index) range dir count
    let items := rows.foldl (fun (acc : List Tok) row =>
      let v := ((s.find row.2).getD #[]).toList
      acc ++ (match what with
        | 0 => counted v
        | 1 => counted row.2.toToks.toList
        | _ => counted row.1.toToks.toList ++ counted row.2.toToks.toList ++ counted v)) []
    (t, .ok ([S "l", N what, N rows.length] ++ items))
  | .count id index range => onStore id fun s =>
    (t, .ok [S "n", N ((s.rows index).filter fun e => range.includes e.1.1).length])
  | .step cid tkey tpk n =>
    match t.cursors.find? (·.id == cid) with
    | none => (t, .ok [S "z"])
    | some c =>
      let setCursor (c : Cursor) : Txn := { t with cursors := t.cursors.map fun x => if x.id == c.id then c else x }
      match get t.work.stores c.store with
      | none => (setCursor { c with got := false }, .ok [S "z"])
      | some s =>
        let rows := s.rows c.index
        let first := stepRows rows c.range c.dir c.pos tkey tpk
        let last := (List.range (n - 1)).foldl
          (fun acc _ => acc.bind fun p => stepRows rows c.range c.dir (some p) none none) first
        match last with
        | some row => (setCursor { c with pos := some row, got := true }, .ok (cursorPayload s c row))
        | none => (setCursor { c with got := false }, .ok [S "z"])

/-! ## The page's commands -/

/-- The checks every request of a source shares, in the order of the specification: the
source exists (`InvalidStateError`), the transaction is active
(`TransactionInactiveError`), and for a write it is not read-only (`ReadOnlyError`). -/
def reqGuard (dbs : List (String × Db)) (l : Live) (tx store : Nat) (index : Option Nat) (write : Bool) :
    Except String (Txn × Store) :=
  match l.txn? tx with
  | none => .error "TransactionInactiveError"
  | some t =>
    match get (t.view dbs).stores store with
    | none => .error "InvalidStateError"
    | some s =>
      if (match index with | some ix => !s.indexes.any (·.id == ix) | none => false) then .error "InvalidStateError"
      else if t.state != .active || t.commitAsked then .error "TransactionInactiveError"
      else if write && t.mode == .ro then .error "ReadOnlyError"
      else .ok (t, s)

/-- The clone of a value is over: the transaction that waited for it is active again. -/
def Live.uncloning (l : Live) (tx : Nat) (isPut : Bool) : Live :=
  match l.txn? tx with
  | some t => if isPut && t.cloning then l.setTxn { t with state := .active, cloning := false } else l
  | none => l

/-- Queue a request on a transaction: the answer is its id. -/
def enqueue (l : Live) (t : Txn) (op : Op) : Live × List Tok :=
  let id := l.next
  (({ l with next := id + 1 }).setTxn { t with queue := t.queue ++ [({ id, op } : Req)] }, ok [N id])

def dirOf (a : Array Tok) (i : Nat) : Dir := natAt a i

/-- `req tx store index op …`: a request of an object store or index. -/
def cmdReq (dbs : List (String × Db)) (l : Live) (a : Array Tok) : Live × List Tok :=
  let tx := natAt a 1
  let store := natAt a 2
  let index := (strAt a 3).toNat?
  let name := strAt a 4
  let l := l.uncloning tx (name == "put" || name == "add")
  let write := name == "put" || name == "add" || name == "delete" || name == "clear"
  match reqGuard dbs l tx store index write with
  | .error e => (l, fail e)
  | .ok (t, s) =>
    let ranged (f : Range → Op) : Live × List Tok :=
      match rangeAt a 5 with
      | some r => enqueue l t (f r)
      | none => (l, fail "DataError")
    match name with
    | "put" | "add" =>
      let (key, j) := keyAt a 5
      let val := a.extract j a.size
      match key with
      | none => (l, fail "DataError")
      | some key =>
        -- in-line keys: the key is in the value, or the generator makes it and it must fit
        let inline := s.keyPath != .none
        let fromValue := if inline then extractKey val s.keyPath else none
        let bad := (inline && key.isSome) || (!inline && !s.autoInc && key.isNone) ||
          (match fromValue with
           | some none => true
           | some (some _) => false
           | none => inline && (!s.autoInc ||
               (match s.keyPath with
                | .one p => (inject val #[] 0 (identsOf p)).isNone
                | _ => true)))
        if bad then (l, fail "DataError")
        else enqueue l t (.put store (match fromValue with | some (some k) => some k | _ => key) val (name == "add"))
    | "delete" => ranged (.delete store)
    | "clear" => enqueue l t (.clear store)
    | "get" => ranged fun r => .get store index r 0
    | "getKey" => ranged fun r => .get store index r 1
    | "count" => ranged (.count store index)
    | "getAll" | "getAllKeys" | "getAllRecords" =>
      match rangeAt a 7 with
      | some r => enqueue l t (.getAll store index r (natAt a 5) (dirOf a 6)
          (if name == "getAll" then 0 else if name == "getAllKeys" then 1 else 2))
      | none => (l, fail "DataError")
    | "openCursor" | "openKeyCursor" =>
      match rangeAt a 6 with
      | some r =>
        let cid := l.next
        let rid := cid + 1
        let c : Cursor := { id := cid, store, index, range := r, dir := dirOf a 5, keyOnly := name == "openKeyCursor" }
        let t := { t with cursors := c :: t.cursors, queue := t.queue ++ [({ id := rid, op := .step cid none none 1 } : Req)] }
        (({ l with next := rid + 1 }).setTxn t, ok [N rid, N cid])
      | none => (l, fail "DataError")
    | _ => (l, fail "TypeError")

/-- `cur tx cursor what request …`: a method of a cursor. `request` is the cursor's own
request, which `continue` and `advance` use again. -/
def cmdCursor (dbs : List (String × Db)) (l : Live) (a : Array Tok) : Live × List Tok :=
  let what := strAt a 3
  let rid := natAt a 4
  let l := l.uncloning (natAt a 1) (what == "update")
  match l.txn? (natAt a 1) with
  | none => (l, fail "TransactionInactiveError")
  | some t =>
    if t.state != .active || t.commitAsked then (l, fail "TransactionInactiveError") else
    match t.cursors.find? (·.id == natAt a 2) with
    | none => (l, fail "InvalidStateError")
    | some c =>
      let src := (get (t.view dbs).stores c.store).bind fun s =>
        match c.index with
        | some ix => if s.indexes.any (·.id == ix) then some s else none
        | none => some s
      match src with
      | none => (l, fail "InvalidStateError")
      | some s =>
        let write := what == "update" || what == "delete" || what == "updatecheck"
        if write && t.mode == .ro then (l, fail "ReadOnlyError")
        else if what == "continuePrimaryKey" && (c.index.isNone || c.dir == 1 || c.dir == 3) then (l, fail "InvalidAccessError")
        else if !c.got then (l, fail "InvalidStateError")
        else if write && c.keyOnly then (l, fail "InvalidStateError")
        else
        let pos := c.pos.getD (Key.nil, Key.nil)
        let fwd := c.dir < 2
        -- `k` is not past the position in the cursor's direction
        let notPast (k p : Key) : Bool := if fwd then k.cmp p != .gt else k.cmp p != .lt
        let go (tkey tpk : Option Key) (n : Nat) : Live × List Tok :=
          let t := { t with cursors := t.cursors.map (fun x => if x.id == c.id then { c with got := false } else x),
                            queue := t.queue ++ [({ id := rid, op := .step c.id tkey tpk n } : Req)] }
          (l.setTxn t, ok [N rid])
        match what with
        | "updatecheck" => (l, ok)
        | "advance" => go none none (natAt a 5)
        | "continue" =>
          match (keyAt a 5).1 with
          | none => (l, fail "DataError")
          | some none => go none none 1
          | some (some k) => if notPast k pos.1 then (l, fail "DataError") else go (some k) none 1
        | "continuePrimaryKey" =>
          let (k, j) := keyAt a 5
          match k, (keyAt a j).1 with
          | some (some k), some (some pk) =>
            if (if fwd then k.cmp pos.1 == .lt else k.cmp pos.1 == .gt) || (k.cmp pos.1 == .eq && notPast pk pos.2)
            then (l, fail "DataError") else go (some k) (some pk) 1
          | _, _ => (l, fail "DataError")
        | "update" =>
          let val := a.extract 5 a.size
          let bad : Bool := match extractKey val s.keyPath with
            | some (some k) => k.cmp pos.2 != .eq
            | some none => true
            | none => s.keyPath != .none
          if bad then (l, fail "DataError") else enqueue l t (.put c.store (some pos.2) val false)
        | "delete" => enqueue l t (.delete c.store (Range.only pos.2))
        | _ => (l, fail "TypeError")

/-- The version-change transaction that a schema method of connection `conn` needs:
`InvalidStateError` when there is none, `TransactionInactiveError` when it is not active. -/
def upgradeGuard (l : Live) (conn : Nat) : Except String Txn :=
  match l.upgradeOf conn with
  | none => .error "InvalidStateError"
  | some t => if t.state != .active || t.commitAsked then .error "TransactionInactiveError" else .ok t

/-- The version-change transaction and the store that a schema method of a store needs. -/
def schemaGuard (l : Live) (tx store : Nat) : Except String (Txn × Store) :=
  match l.txn? tx with
  | none => .error "InvalidStateError"
  | some t =>
    if t.mode != .vc then .error "InvalidStateError" else
    match get t.work.stores store with
    | none => .error "InvalidStateError"
    | some s => if t.state != .active || t.commitAsked then .error "TransactionInactiveError" else .ok (t, s)

def setStoreOf (t : Txn) (id : Nat) (s : Store) : Txn := { t with work := { t.work with stores := set t.work.stores id s } }

/-- The index `ix` filled from the store's records; `none` when they break its unique
constraint. -/
def fillIndex (s : Store) (ix : Index) : Option Index :=
  s.records.foldl (fun acc r => acc.bind fun ix =>
    let ks := ix.keysOf r.2
    if ix.conflict ks r.1 then none else some (ix.withKeys ks r.1)) (some ix)

/-- The commands that are not `pump`: each answers the live state after it and its tokens.
None of them changes a database. -/
def sync (dbs : List (String × Db)) (l : Live) (a : Array Tok) : Live × List Tok :=
  match strAt a 0 with
  | "open" | "deleteDatabase" =>
    let id := l.next
    let rq : OpenReq := { id, name := strAt a 1, version := (strAt a 2).toNat?, delete := strAt a 0 == "deleteDatabase" }
    ({ l with next := id + 1, opens := l.opens ++ [rq] }, ok [N id])
  | "databases" =>
    (l, ok (N dbs.length :: dbs.foldr (fun p acc => S p.1 :: N p.2.version :: acc) []))
  | "cmp" =>
    let (x, j) := keyAt a 1
    match x, (keyAt a j).1 with
    | some (some x), some (some y) => (l, ok [S (match x.cmp y with | .lt => "-1" | .eq => "0" | .gt => "1")])
    | _, _ => (l, fail "DataError")
  | "range" => (l, if (rangeAt a 1).isSome then ok else fail "DataError")
  | "includes" =>
    -- a range, then a key: is the key in the range (`IDBKeyRange.includes`)
    let j := (keyAt a ((keyAt a 2).2)).2
    match rangeAt a 1, (keyAt a j).1 with
    | some r, some (some k) => (l, ok [S (if r.includes k then "1" else "0")])
    | _, _ => (l, fail "DataError")
  | "plan" =>
    -- the order of the listener calls of an event on a path of IndexedDB objects (request,
    -- transaction, connection): DOM §2.9 through `EventLoop.Dispatch.plan`. Arguments: 1
    -- when the event bubbles, the length of the path, the path (root first), then each
    -- listener as node, capture, callback.
    let k := natAt a 2
    let path := (List.range k).map fun i => natAt a (3 + i)
    let ls := (List.range ((a.size - 3 - k) / 3)).map fun i =>
      ({ node := natAt a (3 + k + 3 * i), capture := strAt a (4 + k + 3 * i) == "1", callback := natAt a (5 + k + 3 * i) } :
        L4Factoidal.EventLoop.Dispatch.Listener)
    let visits := L4Factoidal.EventLoop.Dispatch.plan path ls (strAt a 1 == "1")
    (l, ok (visits.flatMap fun v =>
      [N v.callback, N v.node, N ((match v.phase with | .capturing => 1 | .atTarget => 2 | .bubbling => 3) + (if v.capture then 8 else 0)), N v.depth]))
  | "dbinfo" =>
    match l.conn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some c =>
      let d := match l.upgradeOf c.id with | some t => t.work | none => (get dbs c.db).getD {}
      (l, ok ([S c.db, N c.version] ++ storeNames d))
  | "close" =>
    let id := natAt a 1
    (({ l with conns := l.conns.map fun (c : Conn) => if c.id == id then { c with closePending := true } else c }).reap id, ok)
  | "transaction" =>
    match l.conn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some c =>
      if (l.upgradeOf c.id).isSome || c.closePending then (l, fail "InvalidStateError") else
      let d := (get dbs c.db).getD {}
      let names := (a.extract 3 a.size).toList.map fun t => (String.fromUTF8? t).getD ""
      let ids := names.filterMap fun n => (d.storeNamed n).map (·.1)
      if ids.length != names.length then (l, fail "NotFoundError")
      else if names.isEmpty then (l, fail "InvalidAccessError")
      else if strAt a 2 != "readwrite" && strAt a 2 != "readonly" then (l, fail "TypeError")
      else
        let id := l.next
        let t : Txn := { id, conn := c.id, db := c.db, mode := if strAt a 2 == "readwrite" then .rw else .ro, scope := ids.eraseDups }
        ({ l with next := id + 1, txns := l.txns ++ [t] }, ok [N id])
  | "txinfo" =>
    match l.txn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some t =>
      let d := t.view dbs
      (l, ok ((sortNames ((d.stores.filter fun p => t.mode == .vc || t.scope.contains p.1).map (·.2.name))).map S))
  | "objectStore" =>
    match l.txn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some t =>
      match (t.view dbs).storeNamed (strAt a 2) with
      | some (id, _) => if t.mode == .vc || t.scope.contains id then (l, ok [N id]) else (l, fail "NotFoundError")
      | none => (l, fail "NotFoundError")
  | "commit" =>
    match l.txn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some t =>
      if t.state != .active || t.commitAsked then (l, fail "InvalidStateError")
      else (l.setTxn { t with commitAsked := true, state := .inactive }, ok)
  | "abort" =>
    match l.txn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some t => if t.commitAsked then (l, fail "InvalidStateError") else (l.abort dbs t.id "", ok)
  | "deactivate" =>
    match l.txn? (natAt a 1) with
    | some t => ((if t.busy then l else l.setTxn { t with state := .inactive }), ok)
    | none => (l, ok)
  | "active" =>
    -- the clone of a value runs with the transaction inactive (§6.2 "add or put" step 10)
    match l.txn? (natAt a 1) with
    | some t =>
      if strAt a 2 == "1" then (l.setTxn { t with state := .active, cloning := false }, ok)
      else (l.setTxn { t with state := .inactive, cloning := true }, ok)
    | none => (l, ok)
  | "putcheck" =>
    match reqGuard dbs l (natAt a 1) (natAt a 2) none true with
    | .error e => (l, fail e)
    | .ok (_, s) =>
      let hasKey := strAt a 3 == "1"
      if (s.keyPath != .none && hasKey) || (s.keyPath == .none && !s.autoInc && !hasKey) then (l, fail "DataError")
      else (l, ok)
  | "done" =>
    -- after an event of a transaction was dispatched: `threw` a listener threw; `error` the
    -- name of a request's error whose default was not prevented ("" otherwise)
    match l.txn? (natAt a 1) with
    | none => (l, ok)
    | some t =>
      let l := l.setTxn { t with busy := false, state := .inactive }
      if strAt a 2 == "1" then (l.abort dbs t.id "AbortError", ok)
      else if strAt a 3 != "" then (l.abort dbs t.id (strAt a 3), ok)
      else (l, ok)
  | "createStore" =>
    match upgradeGuard l (natAt a 1) with
    | .error e => (l, fail e)
    | .ok t =>
      let name := strAt a 2
      let kp := keyPathOf (strAt a 3)
      let autoInc := strAt a 4 == "1"
      if !kp.valid then (l, fail "SyntaxError")
      else if (t.work.storeNamed name).isSome then (l, fail "ConstraintError")
      else if autoInc && (kp == .one "" || (match kp with | .many _ => true | _ => false)) then (l, fail "InvalidAccessError")
      else
        let id := t.work.nextStore
        let work := { t.work with stores := t.work.stores ++ [(id, { name, keyPath := kp, autoInc })], nextStore := id + 1 }
        (l.setTxn { t with work, scope := id :: t.scope }, ok [N id])
  | "deleteStore" =>
    match upgradeGuard l (natAt a 1) with
    | .error e => (l, fail e)
    | .ok t =>
      match t.work.storeNamed (strAt a 2) with
      | none => (l, fail "NotFoundError")
      | some (id, _) => (l.setTxn { t with work := { t.work with stores := del t.work.stores id } }, ok)
  | "storeinfo" | "indexinfo" =>
    let d := match l.txn? (natAt a 1) with | some t => t.view dbs | none => (get dbs (strAt a 4)).getD {}
    match get d.stores (natAt a 2) with
    | none => (l, fail "gone")
    | some s =>
      if strAt a 0 == "storeinfo" then
        (l, ok ([S s.name, S (keyPathStr s.keyPath), S (if s.autoInc then "1" else "0")] ++ (sortNames (s.indexes.map (·.name))).map S))
      else
        match s.indexes.find? (·.id == natAt a 3) with
        | some ix => (l, ok [S ix.name, S (keyPathStr ix.keyPath), S (if ix.unique then "1" else "0"), S (if ix.multiEntry then "1" else "0")])
        | none => (l, fail "gone")
  | "renameStore" =>
    match schemaGuard l (natAt a 1) (natAt a 2) with
    | .error e => (l, fail e)
    | .ok (t, s) =>
      let name := strAt a 3
      if s.name == name then (l, ok)
      else if (t.work.storeNamed name).isSome then (l, fail "ConstraintError")
      else (l.setTxn (setStoreOf t (natAt a 2) { s with name }), ok)
  | "createIndex" =>
    match schemaGuard l (natAt a 1) (natAt a 2) with
    | .error e => (l, fail e)
    | .ok (t, s) =>
      let name := strAt a 3
      let kp := keyPathOf (strAt a 4)
      let multiEntry := strAt a 6 == "1"
      if s.indexes.any (·.name == name) then (l, fail "ConstraintError")
      else if !kp.valid || kp == .none then (l, fail "SyntaxError")
      else if multiEntry && (match kp with | .many _ => true | _ => false) then (l, fail "InvalidAccessError")
      else
        let ix : Index := { id := s.nextIndex, name, keyPath := kp, unique := strAt a 5 == "1", multiEntry }
        let (ix, doom) := match fillIndex s ix with | some full => (full, t.doom) | none => (ix, "ConstraintError")
        let t := setStoreOf { t with doom } (natAt a 2) { s with indexes := s.indexes ++ [ix], nextIndex := s.nextIndex + 1 }
        (l.setTxn t, ok [N ix.id])
  | "deleteIndex" =>
    match schemaGuard l (natAt a 1) (natAt a 2) with
    | .error e => (l, fail e)
    | .ok (t, s) =>
      if !s.indexes.any (·.name == strAt a 3) then (l, fail "NotFoundError")
      else (l.setTxn (setStoreOf t (natAt a 2) { s with indexes := s.indexes.filter (·.name != strAt a 3) }), ok)
  | "renameIndex" =>
    match schemaGuard l (natAt a 1) (natAt a 2) with
    | .error e => (l, fail e)
    | .ok (t, s) =>
      let name := strAt a 4
      match s.indexes.find? (·.id == natAt a 3) with
      | none => (l, fail "InvalidStateError")
      | some ix =>
        if ix.name == name then (l, ok)
        else if s.indexes.any (·.name == name) then (l, fail "ConstraintError")
        else (l.setTxn (setStoreOf t (natAt a 2)
          { s with indexes := s.indexes.map fun x => if x.id == ix.id then { x with name } else x }), ok)
  | "index" =>
    match l.txn? (natAt a 1) with
    | none => (l, fail "InvalidStateError")
    | some t =>
      match get (t.view dbs).stores (natAt a 2) with
      | none => (l, fail "InvalidStateError")
      | some s =>
        match s.indexes.find? (·.name == strAt a 3) with
        | some ix => (l, ok [N ix.id])
        | none => (l, fail "NotFoundError")
  | "req" => cmdReq dbs l a
  | "cur" => cmdCursor dbs l a
  | _ => (l, fail "NotSupportedError")

/-! ## The pump: the next event -/

/-- The first step of the open or delete request at the head of the queue (§5.1 "open a
database connection", §5.5 "delete a database"). -/
def openStep (dbs : List (String × Db)) (l : Live) : Live × Option (List Tok) × Effect :=
  match l.opens with
  | [] => (l, none, .none)
  | rq :: rest =>
    let old := ((get dbs rq.name).map (·.version)).getD 0
    let version := rq.version.getD (if old == 0 then 1 else old)
    let setPhase (p : Phase) : Live := { l with opens := { rq with phase := p } :: rest }
    let others := l.conns.filter (·.db == rq.name)
    let newTok : Tok := if rq.delete then S "null" else N version
    if !rq.delete && old > version then
      ({ l with opens := rest }, some [S "open", N rq.id, S "error", S "VersionError"], .none)
    else if !rq.delete && old == version then
      let id := l.next
      ({ l with opens := rest, next := id + 1, conns := l.conns ++ [{ id, db := rq.name, version }] },
        some [S "open", N rq.id, S "success", N id, N version], .none)
    else if rq.phase == .upgrading then (l, none, .none)
    else if !others.isEmpty then
      match rq.phase with
      | .waiting =>
        -- `versionchange` at every open connection that is not closing
        let l := (others.filter (!·.closePending)).foldl
          (fun l c => l.push [S "versionchange", N c.id, N old, newTok]) (setPhase .notified)
        (l, none, .none)
      | .notified => (setPhase .blocked, some [S "open", N rq.id, S "blocked", N old, newTok], .none)
      | _ => (l, none, .none)
    else if rq.delete then
      ({ l with opens := rest }, some [S "open", N rq.id, S "deleted", N old], .delete rq.name)
    else
      -- the upgrade transaction: a copy of the database with the new version, every store in scope
      let conn := l.next
      let tx := conn + 1
      let d := (get dbs rq.name).getD {}
      let t : Txn := { id := tx, conn, db := rq.name, mode := .vc, scope := d.stores.map (·.1), started := true,
                       work := { d with version }, busy := true, openReq := some rq.id }
      ({ l with opens := { rq with phase := .upgrading } :: rest, next := tx + 1,
                conns := l.conns ++ [{ id := conn, db := rq.name, version }], txns := l.txns ++ [t] },
        some [S "open", N rq.id, S "upgradeneeded", N conn, N tx, N old, N version], .none)

/-- One step of the first transaction that has something to do: abort a doomed one, run
its next request, or commit it. -/
def txStep (dbs : List (String × Db)) (quota : Nat) (l : Live) : Option (Live × Option (List Tok) × Effect) :=
  let ready := l.txns.find? fun t => !t.busy && t.state == .inactive && (t.started || canStart l t)
  match ready with
  | none => none
  | some t =>
    let t := if t.started then t else { t with started := true, work := (get dbs t.db).getD {} }
    if t.doom != "" then some ((l.setTxn t).abort dbs t.id t.doom, none, .none) else
    match t.queue with
    | r :: rest =>
      let (t, res) := exec { t with queue := rest } r
      let t := { t with busy := true, state := .active }
      some (l.setTxn t, some ([S "req", N r.id, N t.id] ++ (match res with
        | .ok payload => S "ok" :: payload
        | .error e => [S "err", S e])), .none)
    | [] =>
      let eff : Effect := match t.mode with
        | .ro => .none
        | .rw => .commit t.db t.work (some t.scope)
        | .vc => .commit t.db t.work none
      let after := applyEffect dbs eff
      let use (ds : List (String × Db)) : Nat := sizeSum (fun p : String × Db => p.2.usage) ds
      if use after > quota && use after > use dbs then
        some ((l.setTxn t).abort dbs t.id "QuotaExceededError", none, .none)
      else
        let l := { l with txns := l.txns.filter (·.id != t.id) }
        let l := (l.push ([S "tx", N t.id, S "complete"] ++ storeNames t.work)).reap t.conn
        match t.openReq with
        | some rq =>
          let l := { l with opens := l.opens.filter (·.id != rq) }
          some (l.push [S "open", N rq, S "success", N t.conn, N t.work.version], none, eff)
        | none => some (l, none, eff)

/-- `pump`: the next event for the page to dispatch (`idle` when there is none), and the
effect on the databases of what was done to find it. Steps that only queue events run on
(at most `fuel` of them) until an event is ready. -/
def pump (dbs : List (String × Db)) (quota : Nat) : Nat → Live → Live × List Tok × Effect
  | 0, l => (l, [S "idle"], .none)
  | fuel + 1, l =>
    match l.events with
    | e :: rest => ({ l with events := rest }, e, .none)
    | [] =>
      match txStep dbs quota l with
      | some (l, some e, eff) => (l, e, eff)
      | some (l, none, .none) => pump dbs quota fuel l
      | some (l, none, eff) =>
        -- a commit: its events are queued; hand the first over with the effect
        (match l.events with
         | e :: rest => ({ l with events := rest }, e, eff)
         | [] => (l, [S "idle"], eff))
      | none =>
        match openStep dbs l with
        | (l, some e, eff) => (l, e, eff)
        | (l', none, _) => if l'.events.isEmpty then (l', [S "idle"], .none) else pump dbs quota fuel l'

/-- One command: the live state after it, its answer, and its effect on the databases. -/
def run (dbs : List (String × Db)) (quota : Nat) (l : Live) (a : Array Tok) : Live × List Tok × Effect :=
  if strAt a 0 == "pump" then pump dbs quota 64 l
  else
    let r := sync dbs l a
    (r.1, r.2, .none)

/-- One command on the shelf of a storage key. -/
def op (quota : Nat) (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  let r := run s.dbs quota s.live a
  ({ dbs := applyEffect s.dbs r.2.2, live := r.1 }, r.2.1)

/-- Kind: transaction law (atomicity: requests and aborts). Says: every command but `pump`
has no effect on the databases: a request, a cursor step, a schema change in an upgrade, an
abort and the `done` that aborts after a listener threw all leave them exactly as they
were. So what a transaction did before it aborted was never in the databases. Does not say:
anything about `pump` (see `IdbStore.commit_visible` for what a commit does). -/
theorem run_effect (dbs : List (String × Db)) (quota : Nat) (l : Live) (a : Array Tok)
    (h : strAt a 0 ≠ "pump") : (run dbs quota l a).2.2 = .none := by
  simp [run, h]

/-- Kind: transaction law (atomicity, on the shelf). Says: after any command but `pump`,
the databases of the storage key equal the databases before it. -/
theorem op_dbs (quota : Nat) (s : Shelf) (a : Array Tok) (h : strAt a 0 ≠ "pump") :
    (op quota s a).1.dbs = s.dbs := by
  simp [op, run_effect _ _ _ _ h, applyEffect]

/-- One command for the context whose storage key is `k`, on the in-memory shed. -/
def opFor (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) : Shed Shelf × List Tok :=
  shed.act k (fun s => op defaultQuota s a) (fail "SecurityError")

/-- Kind: security theorem (IndexedDB is partitioned by storage key). Says: whatever a
context with one storage key does with IndexedDB, the answer another key then gets for any
command is the answer it would have got without it: no database, record, version, name or
id written under one key is read under another. Does not say: anything about two contexts
with the same key, about timing, or that the engine passes each caller's own key. -/
theorem opFor_noninterference (shed : Shed Shelf) (k k' : ClientStorage.Key) (a a' : Array Tok) (h : k ≠ k') :
    (opFor (opFor shed k a).1 k' a').2 = (opFor shed k' a').2 :=
  act_noninterference Shed.laws shed k k' _ _ _ _ h

end L4Factoidal.ClientStorage.Idb
