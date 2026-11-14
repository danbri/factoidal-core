/-
L4Factoidal.ClientStorage.CacheStorage — the Cache API (Service Workers §5.4 `Cache`, §5.5
`CacheStorage`): the named caches of a storage key, each an ordered list of request and
response pairs, and the "query cache" algorithm that `match`, `matchAll`, `keys`, `delete`
and `put` share.

## Decisions

* The caches of a context are the shelf of its storage key in the storage core: one origin
  can neither list, open, read nor delete another's (`opFor_noninterference`).
* An entry keeps what matching needs (the request's URL, method and headers, the response's
  headers) and the response as opaque bytes the page side wrote (status, status text, body,
  type, URL). Matching never reads those bytes.
* "Request matches cached item" (§5.4.4): the URLs are compared without fragments (and
  without queries for `ignoreSearch`); a request that is not `GET` hits nothing unless
  `ignoreMethod`; each header the response's `Vary` names must have the same value in both
  requests (an absent header equals only an absent one), and `Vary: *` hits nothing,
  unless `ignoreVary`. Header names are compared in ASCII lower case.
* `put` (§5.4.7 steps): a request URL that is not `http` or `https`, a method other than
  `GET`, a response status of 206, or a response `Vary` naming `*`: `TypeError`. Otherwise
  every entry the request hits (with the default options) is replaced, and the new entry
  is appended (`put_matches`: the stored request finds its entry).
* In memory, per session; nothing is written to disk.

Commands (`web_api` op 206): see `op`. A request is three fields (URL, method, headers as
`name:value` lines); options are three flags (`ignoreSearch`, `ignoreMethod`, `ignoreVary`).
Answers: `ok` and values, or `!` + the exception's name.
-/
import L4Factoidal.ClientStorage.Core

namespace L4Factoidal.ClientStorage.Caches

/-- Header list: name (ASCII lower case) and value, in order. -/
abbrev Headers := List (String × String)

structure Req where
  url : String
  method : String := "GET"
  headers : Headers := []
  deriving Inhabited

structure Entry where
  req : Req
  respHeaders : Headers := []
  /-- The response as the page side wrote it: opaque here. -/
  blob : ByteArray := ByteArray.empty
  deriving Inhabited

structure Shelf where
  /-- Every cache made, by id: a deleted name leaves its cache to the objects that hold it. -/
  store : List (Nat × List Entry) := []
  /-- The names of the caches, in the order they were created, and their ids. -/
  names : List (String × Nat) := []
  next : Nat := 1
  deriving Inhabited

instance : Usage Shelf := ⟨fun s => sizeSum (fun c : Nat × List Entry => sizeSum (fun e : Entry => e.blob.size) c.2) s.store⟩

/-! ## Matching -/

def lowerChar (c : Char) : Char := if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
def lower (s : String) : String := String.map lowerChar s

def isWs (c : Char) : Bool := c == ' ' || c == '\t'
def trim (s : String) : String := String.ofList ((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- The combined value of a header (its values joined by `, `), or `none`. -/
def header (h : Headers) (name : String) : Option String :=
  match h.filter (·.1 == lower name) with
  | [] => none
  | vs => some (", ".intercalate (vs.map (·.2)))

/-- A URL without its fragment, and without its query when `noQuery`. -/
def urlKey (u : String) (noQuery : Bool) : String :=
  let cs := u.toList.takeWhile (· != '#')
  String.ofList (if noQuery then cs.takeWhile (· != '?') else cs)

/-- The field names a response's `Vary` lists. -/
def varyNames (h : Headers) : List String :=
  match header h "vary" with
  | none => []
  | some v => (v.splitOn ",").map fun x => lower (trim x)

structure Options where
  ignoreSearch : Bool := false
  ignoreMethod : Bool := false
  ignoreVary : Bool := false
  deriving Inhabited

/-- "Request matches cached item". -/
def hits (q : Req) (o : Options) (e : Entry) : Bool :=
  (o.ignoreMethod || q.method == "GET") &&
  urlKey q.url o.ignoreSearch == urlKey e.req.url o.ignoreSearch &&
  (o.ignoreVary || (varyNames e.respHeaders).all fun n => n != "*" && header q.headers n == header e.req.headers n)

/-- "Query cache": the entries a request hits, in order; every entry without a request. -/
def query (es : List Entry) (q : Option Req) (o : Options) : List Entry :=
  match q with
  | none => es
  | some q => es.filter (hits q o)

/-! ## Commands -/

abbrev Tok := ByteArray
def S (x : String) : Tok := x.toUTF8
def N (n : Nat) : Tok := (toString n).toUTF8
def ok (xs : List Tok := []) : List Tok := S "ok" :: xs
def fail (name : String) : List Tok := [S ("!" ++ name)]
def strAt (a : Array Tok) (i : Nat) : String := (String.fromUTF8? (a.getD i ByteArray.empty)).getD ""

/-- Header lines `name:value` (one per line) as a header list. -/
def headersOf (s : String) : Headers :=
  (s.splitOn "\n").filterMap fun l =>
    if l.isEmpty then none
    else some (lower (String.ofList (l.toList.takeWhile (· != ':'))), String.ofList ((l.toList.dropWhile (· != ':')).drop 1))

def headersText (h : Headers) : String := "\n".intercalate (h.map fun p => p.1 ++ ":" ++ p.2)

def reqAt (a : Array Tok) (i : Nat) : Req := { url := strAt a i, method := strAt a (i + 1), headers := headersOf (strAt a (i + 2)) }
def optsAt (a : Array Tok) (i : Nat) : Options :=
  { ignoreSearch := strAt a i == "1", ignoreMethod := strAt a (i + 1) == "1", ignoreVary := strAt a (i + 2) == "1" }

def cache (s : Shelf) (id : Nat) : Option (List Entry) := (s.store.find? (·.1 == id)).map (·.2)
def setCache (s : Shelf) (id : Nat) (es : List Entry) : Shelf :=
  { s with store := s.store.map fun c => if c.1 == id then (id, es) else c }
def idOf (s : Shelf) (n : String) : Option Nat := (s.names.find? (·.1 == n)).map (·.2)
def natAt (a : Array Tok) (i : Nat) : Nat := (strAt a i).toNat?.getD 0

def entryToks (e : Entry) : List Tok := [S e.req.url, S e.req.method, S (headersText e.req.headers), e.blob]

/-- The checks of `put` on the request and response: `none` when they pass, else the
exception. -/
def putCheck (q : Req) (status : String) (respHeaders : Headers) : Option String :=
  if !(q.url.startsWith "http:" || q.url.startsWith "https:") then some "TypeError"
  else if q.method != "GET" then some "TypeError"
  else if status == "206" then some "TypeError"
  else if (varyNames respHeaders).contains "*" then some "TypeError"
  else none

/-- `put` on the entries of one cache: the matching entries replaced by the new one, at the end. -/
def putEntries (es : List Entry) (e : Entry) : List Entry := es.filter (fun x => !hits e.req {} x) ++ [e]

/-- "Batch cache operations" (§5.4.10) step for `addAll`: two of the entries to put whose
requests match each other (the earlier one's response headers deciding `Vary`): the batch is
refused with `InvalidStateError`. -/
def batchDup (es : List Entry) : Bool :=
  (List.range es.length).any fun j => (es.take j).any fun e => hits (es.getD j default).req {} e

/-- The entries of a `batchcheck` command: `n`, then for each a request (three fields) and its
response's headers. -/
def batchAt (a : Array Tok) : List Entry :=
  (List.range (natAt a 1)).map fun i =>
    let p0 := 2 + 4 * i
    { req := reqAt a p0, respHeaders := headersOf (strAt a (p0 + 3)) }

/-- One command on the shelf of a storage key.
- `open n` (answers the cache's id), `has n`, `delete n` (the name: a `Cache` object of it
  keeps its entries), `names`;
- `smatch n` + request + options: the first match in the cache named `n`, or (`n` empty) in
  every cache in creation order;
- on a cache id: `match id` + request + options; `matchAll id` and `keys id` + has-request +
  request + options: the matching entries' tokens (four per entry); `put id` + request +
  status + response headers + blob; `remove id` + request + options: whether an entry was
  removed. -/
def op (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  let n := strAt a 1
  let id := natAt a 1
  match strAt a 0 with
  | "open" =>
    match idOf s n with
    | some i => (s, ok [N i])
    | none => ({ store := s.store ++ [(s.next, [])], names := s.names ++ [(n, s.next)], next := s.next + 1 }, ok [N s.next])
  | "has" => (s, ok [S (if (idOf s n).isSome then "1" else "0")])
  | "delete" => ({ s with names := s.names.filter (·.1 != n) }, ok [S (if (idOf s n).isSome then "1" else "0")])
  | "names" => (s, ok (s.names.map fun c => S c.1))
  | "smatch" =>
    let es := if n == "" then s.names.flatMap (fun c => (cache s c.2).getD []) else ((idOf s n).bind (cache s)).getD []
    match (query es (some (reqAt a 2)) (optsAt a 5)).head? with
    | some e => (s, ok (entryToks e))
    | none => (s, ok)
  | "match" =>
    match (query ((cache s id).getD []) (some (reqAt a 2)) (optsAt a 5)).head? with
    | some e => (s, ok (entryToks e))
    | none => (s, ok)
  | "matchAll" | "keys" =>
    let q := if strAt a 2 == "1" then some (reqAt a 3) else none
    (s, ok ((query ((cache s id).getD []) q (optsAt a 6)).flatMap entryToks))
  | "put" =>
    match cache s id with
    | none => (s, fail "InvalidStateError")
    | some es =>
      let q := reqAt a 2
      let rh := headersOf (strAt a 6)
      match putCheck q (strAt a 5) rh with
      | some err => (s, fail err)
      | none => (setCache s id (putEntries es { req := q, respHeaders := rh, blob := a.getD 7 ByteArray.empty }), ok)
  | "remove" =>
    match cache s id with
    | none => (s, ok [S "0"])
    | some es =>
      let q := reqAt a 2
      let o := optsAt a 5
      let gone := es.filter (hits q o)
      (setCache s id (es.filter fun x => !hits q o x), ok [S (if gone.isEmpty then "0" else "1")])
  | "batchcheck" => (s, if batchDup (batchAt a) then fail "InvalidStateError" else ok)
  | _ => (s, fail "NotSupportedError")

/-- One command for the context whose storage key is `k`, on the in-memory shed. -/
def opFor (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) : Shed Shelf × List Tok :=
  shed.act k (fun s => op s a) (fail "SecurityError")

/-- `opFor` under a quota (`ClientStorage.Budget`): a command after which the key's caches
would hold more than `quota` bytes (and more than before) changes nothing and answers
`QuotaExceededError` (`Backend.actQuota`, `actQuota_bound`). -/
def opForQ (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) (quota : Nat) : Shed Shelf × List Tok :=
  Shed.backend.actQuota quota shed k (fun s => op s a) (fail "SecurityError") (fail "QuotaExceededError")

/-- Kind: resource bound. Says: after a command under a quota the key's caches hold at most
the quota, or at most what they held before. -/
theorem opForQ_bound (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) (quota : Nat) :
    Usage.usage (Shed.backend.load (opForQ shed k a quota).1 k) ≤ max quota (Usage.usage (Shed.backend.load shed k)) :=
  actQuota_bound Shed.laws quota shed k _ _ _

/-! ## Theorems -/

/-- Kind: functional law. Says: a `GET` request hits an entry stored with that request,
whatever the response's `Vary` (except `*`, which `put` refuses) and whatever the options. -/
theorem matches_self (q : Req) (o : Options) (rh : Headers) (blob : ByteArray) (hm : q.method = "GET")
    (hv : (varyNames rh).contains "*" = false) : hits q o { req := q, respHeaders := rh, blob } = true := by
  simp only [hits, hm, beq_self_eq_true, Bool.or_true, Bool.true_and]
  cases o.ignoreVary
  · simp only [Bool.false_or, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, and_true]
    intro x hx h; subst h; simp [hx] at hv
  · rfl

/-- Kind: functional law. Says: after a `put` that passes its checks, the request finds the
new entry, under any options. -/
theorem put_matches (es : List Entry) (q : Req) (rh : Headers) (blob : ByteArray) (o : Options)
    (hm : q.method = "GET") (hv : (varyNames rh).contains "*" = false) :
    { req := q, respHeaders := rh, blob } ∈ query (putEntries es { req := q, respHeaders := rh, blob }) (some q) o := by
  simp only [query, putEntries, List.mem_filter, List.mem_append, List.mem_singleton, true_or, or_true, true_and]
  exact matches_self q o rh blob hm hv

/-- Kind: validity rule. Says: a batch with the same `GET` request twice (and no `Vary: *`
on the first response) is a duplicate. -/
theorem batchDup_twice (q : Req) (rh : Headers) (hm : q.method = "GET") (hv : (varyNames rh).contains "*" = false) :
    batchDup [{ req := q, respHeaders := rh }, { req := q, respHeaders := rh }] = true := by
  have h := matches_self q {} rh ByteArray.empty hm hv
  simp only [batchDup, List.any_eq_true, List.mem_range]
  refine ⟨1, by simp, ?_⟩
  simpa using h

/-- Kind: validity rule. Says: `put` refuses a request that is not `GET`. -/
theorem putCheck_method (q : Req) (st : String) (rh : Headers) (hu : q.url.startsWith "http:" = true)
    (hm : q.method ≠ "GET") : putCheck q st rh = some "TypeError" := by
  simp [putCheck, hu, hm]

/-- Kind: security theorem (caches are partitioned by storage key). Says: whatever a context
with one storage key does with caches, the answer another key then gets for any command is
the answer it would have got without it. -/
theorem opFor_noninterference (shed : Shed Shelf) (k k' : ClientStorage.Key) (a a' : Array Tok) (h : k ≠ k') :
    (opFor (opFor shed k a).1 k' a').2 = (opFor shed k' a').2 :=
  act_noninterference Shed.laws shed k k' _ _ _ _ h

/-! ## Checks (WPT service-workers/cache-storage: put, match, matchAll, keys, delete) -/

private def T (xs : List String) : Array Tok := (xs.map String.toUTF8).toArray
private def shown (r : List Tok) : String := " ".intercalate (r.map fun t => (String.fromUTF8? t).getD "?")
private def run (cmds : List (List String)) : List String :=
  (cmds.foldl (fun (acc : Shelf × List String) c => let (s, r) := op acc.1 (T c); (s, acc.2 ++ [shown r])) ({}, [])).2
private def put (u : String) (body : String) (m := "GET") (rh := "") (qh := "") (st := "200") : List String :=
  ["put", "1", u, m, qh, st, rh, body]
private def mt (u : String) (m := "GET") (qh := "") (is im iv : String := "0") : List String := ["match", "1", u, m, qh, is, im, iv]

#guard run [["open", "c"], ["has", "c"], ["has", "d"], ["open", "b"], ["open", "c"], ["names"], ["delete", "c"], ["names"], ["delete", "c"]] ==
  ["ok 1", "ok 1", "ok 0", "ok 2", "ok 1", "ok c b", "ok 1", "ok b", "ok 0"]
#guard run [["open", "c"], put "https://example.com/foo" "Hello", mt "https://example.com/foo", mt "https://example.com/foo#frag",
  mt "https://example.com/foo?q", mt "https://example.com/foo?q" (is := "1"), mt "https://example.com/foo" (m := "POST"),
  mt "https://example.com/foo" (m := "POST") (im := "1")] ==
  ["ok 1", "ok", "ok https://example.com/foo GET  Hello", "ok https://example.com/foo GET  Hello", "ok",
   "ok https://example.com/foo GET  Hello", "ok", "ok https://example.com/foo GET  Hello"]
-- put replaces the matching entry; a fragment does not make a new one
#guard run [["open", "c"], put "https://example.com/x#a" "1", put "https://example.com/x#b" "2", ["keys", "1", "0", "", "", "", "0", "0", "0"]] ==
  ["ok 1", "ok", "ok", "ok https://example.com/x#b GET  2"]
-- refusals: not http(s), POST, 206, Vary: *
#guard run [["open", "c"], put "file:///x" "", put "https://e.com/" "" (m := "POST"), put "https://e.com/" "" (st := "206"),
  put "https://e.com/" "" (rh := "vary:*"), put "https://e.com/" "" (rh := "vary:Accept, *"), put "https://e.com/" "" (st := "500")] ==
  ["ok 1", "!TypeError", "!TypeError", "!TypeError", "!TypeError", "!TypeError", "ok"]
-- Vary: the named request headers must agree, unless ignoreVary
#guard run [["open", "c"], put "https://e.com/v" "x" (rh := "vary:Cookies") (qh := "cookies:is-for-cookie"),
  mt "https://e.com/v" (qh := "cookies:is-for-cookie"), mt "https://e.com/v", mt "https://e.com/v" (qh := "cookies:no"),
  mt "https://e.com/v" (iv := "1")] ==
  ["ok 1", "ok", "ok https://e.com/v GET cookies:is-for-cookie x", "ok", "ok", "ok https://e.com/v GET cookies:is-for-cookie x"]
-- addAll: duplicates (also by fragment) refused; distinct URLs fine
#guard run [["batchcheck", "2", "https://e.com/a", "GET", "", "", "https://e.com/a#x", "GET", "", ""],
  ["batchcheck", "2", "https://e.com/a", "GET", "", "", "https://e.com/b", "GET", "", ""],
  ["batchcheck", "2", "https://e.com/v", "GET", "x:1", "vary:x", "https://e.com/v", "GET", "x:2", ""]] ==
  ["!InvalidStateError", "ok", "ok"]
-- delete one entry; a deleted name keeps its cache for the objects that hold it; a new one of that name is empty
#guard run [["open", "c"], put "https://e.com/a" "1", ["remove", "1", "https://e.com/a", "GET", "", "0", "0", "0"],
  ["remove", "1", "https://e.com/a", "GET", "", "0", "0", "0"], put "https://e.com/a" "1", ["delete", "c"],
  put "https://e.com/b" "2", ["open", "c"], ["keys", "2", "0", "", "", "", "0", "0", "0"], ["keys", "1", "0", "", "", "", "0", "0", "0"],
  ["smatch", "", "https://e.com/b", "GET", "", "0", "0", "0"], ["put", "9", "https://e.com/a", "GET", "", "200", "", "1"]] ==
  ["ok 1", "ok", "ok 1", "ok 0", "ok", "ok 1", "ok", "ok 2", "ok", "ok https://e.com/a GET  1 https://e.com/b GET  2", "ok", "!InvalidStateError"]

end L4Factoidal.ClientStorage.Caches
