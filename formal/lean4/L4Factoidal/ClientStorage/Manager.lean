/-
L4Factoidal.ClientStorage.Manager — `StorageManager` (Storage Standard §5: `estimate()`,
`persist()`, `persisted()`), over the storage APIs of one storage key.

## Decisions

* `estimate()` answers the usage of the caller's own storage key: the sum of what each
  storage API holds for it (`usageOf`: IndexedDB's record bytes and store descriptions, the
  file system's file bytes, the Cache API's stored responses), and a quota that is a constant of the engine (each API's `defaultQuota`). Neither
  number is read from the host: an estimate says nothing about the machine's disk or about
  another origin (`op_local`).
* `persisted()` and `persist()` answer false: storage is in memory and ends with the
  session, so no bucket is persistent. What they answer once a persistence policy exists
  is a question for the owner (the record's "Questions").
* An opaque origin has no storage: `TypeError` (Storage Standard: "obtain a local storage
  shelf" fails).
-/
import L4Factoidal.ClientStorage.IdbOps
import L4Factoidal.ClientStorage.FileSystem
import L4Factoidal.ClientStorage.CacheStorage
import L4Factoidal.ClientStorage.Buckets
import L4Factoidal.ClientStorage.Budget

namespace L4Factoidal.ClientStorage.Manager

/-- The bytes a storage key holds: the sum over the storage APIs. A new API adds its term
here. -/
def usageOf (idb : Shed Idb.Shelf) (fs : Shed Fs.Shelf) (cs : Shed Caches.Shelf) (k : Key) : Nat :=
  Usage.usage (idb.shelf k) + Usage.usage (fs.shelf k) + Usage.usage (cs.shelf k)

/-- The quota of a storage key, its APIs together (`Budget.keyQuota`). -/
def quota : Nat := Budget.keyQuota

/-- The other storage keys of the session that hold data. -/
def heldOthers (idb : Shed Idb.Shelf) (fs : Shed Fs.Shelf) (cs : Shed Caches.Shelf) (k : Key) : Nat :=
  let total (k' : Key) := Usage.usage (idb.shelf k') + Usage.usage (fs.shelf k') + Usage.usage (cs.shelf k')
  ((idb.shelves.map (·.1) ++ fs.shelves.map (·.1) ++ cs.shelves.map (·.1)).eraseDups.filter
    fun k' => k' != k && total k' > 0).length

/-- The room of one API of key `k` (0 IndexedDB, 1 file system, 2 caches): `Budget.roomFor`
of what this API holds, what the key's other APIs hold, and how many other keys hold data. -/
def roomOf (idb : Shed Idb.Shelf) (fs : Shed Fs.Shelf) (cs : Shed Caches.Shelf) (k : Key) (api : Nat) : Nat :=
  let u0 := Usage.usage (idb.shelf k)
  let u1 := Usage.usage (fs.shelf k)
  let u2 := Usage.usage (cs.shelf k)
  let own := if api == 0 then u0 else if api == 1 then u1 else u2
  Budget.roomFor own (u0 + u1 + u2 - own) (heldOthers idb fs cs k)

/-- One command of `StorageManager` (`web_api` op 202) for the context whose key is `k`. -/
def op (idb : Shed Idb.Shelf) (fs : Shed Fs.Shelf) (cs : Shed Caches.Shelf) (k : Key) (a : Array ByteArray) : List ByteArray :=
  if !k.usable then Fs.fail "TypeError" else
  match Fs.strAt a 0 with
  | "estimate" =>
    Fs.ok [Fs.N (usageOf idb fs cs k), Fs.N quota, Fs.N (Usage.usage (idb.shelf k)), Fs.N (Usage.usage (fs.shelf k)),
      Fs.N (Usage.usage (cs.shelf k))]
  | "persisted" | "persist" => Fs.ok [Fs.S "0"]
  | _ => Fs.fail "NotSupportedError"

/-- `StorageBucket.estimate()` (`web_api` 205 `estimate name generation`): what the live
bucket's own storage holds (its caches) and its quota (the one asked for, else the default);
`UnknownError` for a deleted bucket. -/
def bucketEstimate (bs : Shed Buckets.Shelf) (cs : Shed Caches.Shelf) (origin : String) (a : Array ByteArray) : List ByteArray :=
  match Buckets.route bs origin (#["@b".toUTF8] ++ a.extract 1 3) with
  | none => Fs.fail "UnknownError"
  | some (k, _) =>
    match Buckets.live (bs.shelf { origin }) (Fs.strAt a 1) (Fs.natAt a 2) with
    | none => Fs.fail "UnknownError"
    | some b => Fs.ok [Fs.N (Usage.usage (cs.shelf k)), Fs.N (b.quota.getD defaultQuota)]

/-- Kind: accounting law. Says: the usage `estimate()` reports is the sum of the bytes the
storage APIs hold for the key (each of which is proved equal to the sum of its stored
sizes: `Idb.Store.put_wf` and the others, `Fs.usage_eq`). -/
theorem usageOf_sum (idb : Shed Idb.Shelf) (fs : Shed Fs.Shelf) (cs : Shed Caches.Shelf) (k : Key) :
    usageOf idb fs cs k = Usage.usage (idb.shelf k) + Usage.usage (fs.shelf k) + Usage.usage (cs.shelf k) := rfl

/-- Kind: security invariant (an estimate reveals only the caller's own storage). Says: the
answer of every `StorageManager` command is a function of the caller's key's own shelves:
two states that agree on them give the same answer, whatever other keys hold. With
`act_partition` (no other key's action changes those shelves): no origin can learn
anything about another origin's storage from `estimate()`. Does not say: anything about
timing; the quota is a constant, so it says nothing about the host. -/
theorem op_local (idb idb' : Shed Idb.Shelf) (fs fs' : Shed Fs.Shelf) (cs cs' : Shed Caches.Shelf) (k : Key) (a : Array ByteArray)
    (h1 : idb.shelf k = idb'.shelf k) (h2 : fs.shelf k = fs'.shelf k) (h3 : cs.shelf k = cs'.shelf k) :
    op idb fs cs k a = op idb' fs' cs' k a := by
  simp [op, usageOf, h1, h2, h3]

#guard (op {} {} {} { origin := "https://a.example" } #["estimate".toUTF8]).map (fun t => (String.fromUTF8? t).getD "") ==
  ["ok", "0", "33554432", "0", "0", "0"]
#guard (op {} {} {} { origin := "null" } #["estimate".toUTF8]).map (fun t => (String.fromUTF8? t).getD "") == ["!TypeError"]
#guard (op {} {} {} { origin := "https://a.example" } #["persist".toUTF8]).map (fun t => (String.fromUTF8? t).getD "") == ["ok", "0"]

-- a bucket's estimate: its own caches' usage and quota; a bucket that is gone: UnknownError
#guard (let bs := (Buckets.opFor {} { origin := "https://a.example" } #["open".toUTF8, "b".toUTF8, "".toUTF8, "".toUTF8, "500".toUTF8]).1;
  [(bucketEstimate bs {} "https://a.example" #["estimate".toUTF8, "b".toUTF8, "1".toUTF8]).map (fun t => (String.fromUTF8? t).getD ""),
   (bucketEstimate bs {} "https://a.example" #["estimate".toUTF8, "b".toUTF8, "2".toUTF8]).map (fun t => (String.fromUTF8? t).getD "")]) ==
  [["ok", "0", "500"], ["!UnknownError"]]

-- the room of the caches of a key: the whole key quota on an empty session; a cache entry of
-- 100 bytes elsewhere in the key leaves the file system the rest
#guard roomOf {} {} {} { origin := "https://a.example" } 2 == Budget.keyQuota
#guard (let cs := (Caches.opFor (Caches.opFor {} { origin := "https://a.example" } #["open".toUTF8, "c".toUTF8]).1 { origin := "https://a.example" }
          #["put".toUTF8, "1".toUTF8, "https://a.example/x".toUTF8, "GET".toUTF8, "".toUTF8, "200".toUTF8, "".toUTF8, ByteArray.mk (Array.replicate 100 65)]).1;
        (roomOf {} {} cs { origin := "https://a.example" } 1, heldOthers {} {} cs { origin := "https://b.example" })) == (Budget.keyQuota - 100, 1)
-- a put past the room is refused and changes nothing
#guard (let k : Key := { origin := "https://a.example" };
        let cs := (Caches.opFor {} k #["open".toUTF8, "c".toUTF8]).1;
        let r := Caches.opForQ cs k #["put".toUTF8, "1".toUTF8, "https://a.example/x".toUTF8, "GET".toUTF8, "".toUTF8, "200".toUTF8, "".toUTF8, ByteArray.mk (Array.replicate 100 65)] 50;
        ((r.2.map fun t => (String.fromUTF8? t).getD ""), Usage.usage (r.1.shelf k))) == (["!QuotaExceededError"], 0)

end L4Factoidal.ClientStorage.Manager
