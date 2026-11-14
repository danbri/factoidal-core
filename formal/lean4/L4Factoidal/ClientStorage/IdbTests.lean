/-
L4Factoidal.ClientStorage.IdbTests — scenarios through `Idb.op`, the commands the page side
sends, in the order it sends them (the cases are those of WPT IndexedDB: idbfactory_open,
transaction-lifetime, idbobjectstore_add/put, idbcursor_continue, idbdatabase_close,
idbversionchange_event, idbtransaction_abort, keygenerator).
-/
import L4Factoidal.ClientStorage.IdbOps

namespace L4Factoidal.ClientStorage.Idb.Tests

private def T (xs : List String) : Array Tok := (xs.map String.toUTF8).toArray
private def shown (r : List Tok) : String := " ".intercalate (r.map fun t => (String.fromUTF8? t).getD "?")

/-- The answers of a list of commands, from a shelf. -/
private def answers (s : Shelf) (cmds : List (List String)) : Shelf × List String :=
  cmds.foldl (fun (acc : Shelf × List String) c =>
    let (s, r) := op defaultQuota acc.1 (T c)
    (s, acc.2 ++ [shown r])) (s, [])

private def one : String := "n3ff0000000000000"
private def two : String := "n4000000000000000"
private def three : String := "n4008000000000000"
private def noRange : List String := ["0", "0", "0"]
private def only (k : String) : List String := ["0", "1", k, "1", k]

-- open a new database at version 1, make a store with an index in the upgrade
private def setup : List (List String) :=
  [["open", "db", ""], ["pump"], ["createStore", "2", "books", "n", "0"], ["createIndex", "3", "1", "by_title", "stitle", "1", "0"],
   ["done", "3", "0", ""], ["pump"], ["pump"], ["pump"]]
private def s1 : Shelf := (answers {} setup).1
#guard (answers {} setup).2 ==
  ["ok 1", "open 1 upgradeneeded 2 3 0 1", "ok 1", "ok 1", "ok", "tx 3 complete books", "open 1 success 2 1", "idle"]
#guard (answers s1 [["databases"], ["dbinfo", "2"]]).2 == ["ok 1 db 1", "ok db 1 books"]
#guard (answers s1 [["dbnames", "db"], ["dbnames", "nope"]]).2 == ["ok books", "ok"]

-- a read-write transaction: put with an out-of-line key, the commit, then a read
private def book (t : String) : List String := ["o1", "ktitle", "s" ++ t]
private def write1 : List (List String) :=
  [["transaction", "2", "readwrite", "books"], ["objectStore", "4", "books"], ["putcheck", "4", "1", "1"], ["active", "4", "0"],
   ["req", "4", "1", "", "put", "1", one] ++ book "Dune", ["deactivate", "4"],
   ["pump"], ["done", "4", "0", ""], ["pump"], ["pump"]]
private def s2 : Shelf := (answers s1 write1).1
#guard (answers s1 write1).2 == ["ok 4", "ok 1", "ok", "ok", "ok 5", "ok", s!"req 5 4 ok k {one}", "ok", "tx 4 complete books", "idle"]
private def read (tx : String) (k : String) : List (List String) :=
  [["transaction", "2", "readonly", "books"], ["req", tx, "1", "", "get"] ++ only k, ["deactivate", tx], ["pump"], ["done", tx, "0", ""], ["pump"]]
#guard (answers s2 (read "6" one)).2 == ["ok 6", "ok 7", "ok", "req 7 6 ok v o1 ktitle sDune", "ok", "tx 6 complete books"]
#guard ((answers s2 (read "6" two)).2.drop 3).head? == some "req 7 6 ok u"

-- an abort: the put is never in the database
private def aborted : List (List String) :=
  [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "put", "1", two] ++ book "Emma", ["abort", "6"],
   ["pump"], ["pump"], ["pump"]]
#guard (answers s2 aborted).2 == ["ok 6", "ok 7", "ok", "req 7 6 err AbortError", "tx 6 abort  books", "idle"]
#guard ((answers (answers s2 aborted).1 (read "8" two)).2.drop 3).head? == some "req 9 8 ok u"
#guard (answers s2 aborted).1.dbs.map (·.2.usage) == s2.dbs.map (·.2.usage)

-- the order of exceptions: inactive, read-only, a key that is not a key, a unique conflict
#guard (answers s2 [["transaction", "2", "readonly", "books"], ["req", "6", "1", "", "put", "1", two] ++ book "x"]).2.getLast? == some "!ReadOnlyError"
#guard (answers s2 [["transaction", "2", "readwrite", "books"], ["deactivate", "6"], ["req", "6", "1", "", "put", "1", two] ++ book "x"]).2.getLast? == some "!TransactionInactiveError"
#guard (answers s2 [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "put", "1", "x"] ++ book "x"]).2.getLast? == some "!DataError"
#guard (answers s2 [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "get", "4", "0", "0"]]).2.getLast? == some "!DataError"
-- a handle of a finished transaction: its store deleted (or never committed) is InvalidStateError first, else not active
#guard (answers s2 [["req", "4", "1", "", "get"] ++ only one, ["req", "4", "9", "", "get"] ++ only one, ["req", "99", "1", "", "get"] ++ only one]).2 ==
  ["!TransactionInactiveError", "!InvalidStateError", "!TransactionInactiveError"]
-- schema methods on a handle of a finished transaction: an upgrade's live store is not active; a gone store or another mode is InvalidStateError
#guard (answers s2 [["createIndex", "3", "1", "by_title", "stitle", "1", "0"], ["createIndex", "3", "9", "x", "sx", "0", "0"],
  ["createIndex", "4", "1", "x", "sx", "0", "0"]]).2 == ["!TransactionInactiveError", "!InvalidStateError", "!InvalidStateError"]
#guard (answers s2 [["transaction", "2", "readwrite", "nope"]]).2.getLast? == some "!NotFoundError"
#guard (answers s2 [["transaction", "2", "readwrite"]]).2.getLast? == some "!InvalidAccessError"
#guard (answers s2 [["createStore", "2", "x", "n", "0"]]).2.getLast? == some "!InvalidStateError"
#guard (answers s2 [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "add", "1", two] ++ book "Dune",
  ["deactivate", "6"], ["pump"]]).2.getLast? == some "req 7 6 err ConstraintError"
#guard (answers s2 [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "add", "1", one] ++ book "Other",
  ["deactivate", "6"], ["pump"]]).2.getLast? == some "req 7 6 err ConstraintError"
-- an error event whose default is not prevented aborts the transaction
#guard (answers s2 [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "add", "1", one] ++ book "Other",
  ["deactivate", "6"], ["pump"], ["done", "6", "0", "ConstraintError"], ["pump"]]).2.getLast? == some "tx 6 abort ConstraintError books"

-- two read-write transactions on one store: the second runs after the first commits, and reads its write
private def twoTx : List (List String) :=
  [["transaction", "2", "readwrite", "books"], ["transaction", "2", "readwrite", "books"],
   ["req", "7", "1", "", "get"] ++ only two, ["req", "6", "1", "", "put", "1", two] ++ book "Emma",
   ["deactivate", "6"], ["deactivate", "7"], ["pump"], ["done", "6", "0", ""], ["pump"], ["pump"]]
#guard (answers s2 twoTx).2.drop 6 == [s!"req 9 6 ok k {two}", "ok", "tx 6 complete books", "req 8 7 ok v o1 ktitle sEmma"]
-- two read-only transactions run together: the first made does not hold the second
#guard (answers s2 [["transaction", "2", "readonly", "books"], ["transaction", "2", "readonly", "books"],
  ["req", "7", "1", "", "count"] ++ noRange, ["deactivate", "7"], ["pump"]]).2.getLast? == some "req 8 7 ok n 1"

-- a cursor over the index, and a key generator with an in-line key path
private def s3 : Shelf := (answers s2 [["transaction", "2", "readwrite", "books"],
  ["req", "6", "1", "", "put", "1", two] ++ book "Emma", ["req", "6", "1", "", "put", "1", three] ++ book "Ada",
  ["deactivate", "6"], ["pump"], ["done", "6", "0", ""], ["pump"], ["done", "6", "0", ""], ["pump"]]).1
private def cursorRun : List (List String) :=
  [["transaction", "2", "readonly", "books"], ["req", "9", "1", "1", "openCursor", "0"] ++ noRange, ["deactivate", "9"],
   ["pump"], ["cur", "9", "10", "continue", "11", "0"], ["done", "9", "0", ""],
   ["pump"], ["cur", "9", "10", "advance", "11", "1"], ["done", "9", "0", ""],
   ["pump"], ["cur", "9", "10", "continue", "11", "0"], ["done", "9", "0", ""], ["pump"], ["done", "9", "0", ""], ["pump"]]
#guard ((answers s3 cursorRun).2.filter (·.startsWith "req")) ==
  [s!"req 11 9 ok c 10 1 sAda 1 {three} o1 ktitle sAda", s!"req 11 9 ok c 10 1 sDune 1 {one} o1 ktitle sDune",
   s!"req 11 9 ok c 10 1 sEmma 1 {two} o1 ktitle sEmma", "req 11 9 ok z"]
#guard (answers s3 cursorRun).2.getLast? == some "tx 9 complete books"
#guard (answers s3 [["transaction", "2", "readonly", "books"], ["req", "9", "1", "", "getAllKeys", "2", "2"] ++ noRange,
  ["deactivate", "9"], ["pump"]]).2.getLast? == some s!"req 10 9 ok l 1 2 1 {three} 1 {two}"

-- a second version: `versionchange` at the open connection, `blocked` while it stays open, the upgrade after its close
private def upgrade : List (List String) :=
  [["open", "db", "2"], ["pump"], ["pump"], ["pump"], ["close", "2"], ["pump"],
   ["createStore", "10", "auto", "sid", "1"], ["req", "11", "2", "", "add", "0", "o0"], ["done", "11", "0", ""],
   ["pump"], ["done", "11", "0", ""], ["pump"], ["pump"]]
#guard (answers s3 upgrade).2 ==
  ["ok 9", "versionchange 2 1 2", "open 9 blocked 1 2", "idle", "ok", "open 9 upgradeneeded 10 11 1 2",
   "ok 2", "ok 12", "ok", s!"req 12 11 ok k {one}", "ok", "tx 11 complete auto books", "open 9 success 10 2"]
#guard ((answers (answers s3 upgrade).1 [["transaction", "10", "readonly", "auto"], ["req", "13", "2", "", "get"] ++ only one,
  ["deactivate", "13"], ["pump"]]).2.getLast?) == some s!"req 14 13 ok v o1 kid {one}"
-- an upgrade that aborts leaves the version and the stores as they were
#guard (answers s3 [["close", "2"], ["open", "db", "5"], ["pump"], ["createStore", "10", "gone", "n", "0"], ["abort", "11"],
  ["pump"], ["pump"], ["databases"]]).2.drop 5 == ["tx 11 abort  books", "open 9 error AbortError 10 1", "ok 1 db 1"]
-- a lower version is refused; deleting needs the connections closed
#guard (answers s3 [["open", "db", ""], ["pump"]]).2.getLast? == some "open 9 success 10 1"
#guard (answers (answers s3 upgrade).1 [["open", "db", "1"], ["pump"]]).2.getLast? == some "open 13 error VersionError"
#guard (answers s3 [["deleteDatabase", "db"], ["pump"], ["pump"], ["close", "2"], ["pump"], ["databases"]]).2 ==
  ["ok 9", "versionchange 2 1 null", "open 9 blocked 1 null", "ok", "open 9 deleted 1", "ok 0"]
-- key ranges and the listener order of an error event that bubbles from a request (30) to its transaction (20) and connection (10)
#guard (answers {} [["range", "0", "1", two, "1", one], ["range", "1", "1", one, "1", one], ["range", "0", "1", one, "1", two],
  ["includes", "2", "1", one, "1", two, "1", two], ["includes", "0", "1", one, "1", two, "1", two], ["includes", "0", "0", "0", "1", "x"]]).2 ==
  ["!DataError", "!DataError", "ok", "ok 0", "ok 1", "!DataError"]
#guard (answers {} [["plan", "1", "3", "10", "20", "30", "30", "0", "1", "20", "0", "2", "10", "1", "3", "20", "1", "4"]]).2 ==
  ["ok 3 10 9 0 4 20 9 1 1 30 2 2 2 20 3 1"]
#guard (answers {} [["plan", "0", "3", "10", "20", "30", "30", "0", "1", "20", "0", "2", "10", "1", "3"]]).2 == ["ok 3 10 9 0 1 30 2 2"]
#guard (answers s2 [["transaction", "2", "versionchange", "books"]]).2.getLast? == some "!TypeError"
-- cmp, and the quota: a commit above the quota is an abort
#guard (answers {} [["cmp", "1", one, "1", two], ["cmp", "1", "sa", "1", one], ["cmp", "1", "x", "1", one]]).2 == ["ok -1", "ok 1", "!DataError"]
#guard (shown (op 10 s2 (T ["pump"])).2) == "idle"
private def cmdsQuota (s : Shelf) : List String :=
  let (s, a) := op 10 s (T ["pump"])
  let (s, b) := op 10 s (T ["done", "6", "0", ""])
  let (_, c) := op 10 s (T ["pump"])
  [shown a, shown b, shown c]
#guard cmdsQuota (answers s2 [["transaction", "2", "readwrite", "books"], ["req", "6", "1", "", "put", "1", two] ++ book "Emma",
  ["deactivate", "6"]]).1 == ["req 7 6 ok k " ++ two, "ok", "tx 6 abort QuotaExceededError books"]

-- an upgrade aborted by the page: until its abort event the connection's schema methods are "not active", after it "no upgrade"
private def upgrade2 : List (List String) :=
  [["open", "db", ""], ["pump"], ["createStore", "2", "books", "n", "0"], ["done", "3", "0", ""], ["pump"], ["pump"], ["pump"],
   ["close", "2"], ["open", "db", "2"], ["pump"], ["abort", "6"]]
#guard ((answers {} (upgrade2 ++ [["createStore", "5", "books2", "n", "0"], ["deleteStore", "5", "books"]])).2.drop 11) ==
  ["!TransactionInactiveError", "!TransactionInactiveError"]
#guard ((answers {} (upgrade2 ++ [["txended", "6"], ["createStore", "5", "books2", "n", "0"]])).2.drop 12) == ["!InvalidStateError"]

end L4Factoidal.ClientStorage.Idb.Tests
