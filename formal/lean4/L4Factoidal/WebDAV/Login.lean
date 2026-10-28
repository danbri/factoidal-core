/-
L4Factoidal.WebDAV.Login — the login of the `factoidal webdav-serve`
listener: a users file of PBKDF2-HMAC-SHA256 password hashes, HTTP Basic
(RFC 7617), a login cache, and the rule that keeps Basic off a plain-HTTP
listener that is not on a loopback address.
https://github.com/danbri/factoidal/issues/1108

EXPERT REVIEW REQUESTED: https://github.com/danbri/factoidal/issues/1117
(the password storage, the iteration count, the login cache, the constant-time
comparison and Basic only on loopback or TLS).

Owner, 2026-10-28, verbatim: "Re 3 if controversial or risk file issue to flag
for expert review" (answer 3: the WebDAV listener login with
PBKDF2-HMAC-SHA256). PBKDF2 itself is NOT computed here: the engine names one
derivation (password, salt, iteration count, 256 bits) and the host runs it
with WebCrypto (`crypto.subtle.deriveBits`, `PBKDF2`, `SHA-256`), as AES goes
through WebCrypto (`skills/crypto-policy/SKILL.md` § "AES through
WebCrypto"). Every decision is here: the file format, which header fields
count, which user, which salt and count, whether the derived bytes match,
the cache, and the 401.

The users file, one user per line (design record
`docs/designissues/2026-10-27-webdav.md` § "Login and HTTPS"):

    NAME:pbkdf2-sha256:ITERATIONS:SALT_B64:HASH_B64

* NAME: one or more characters, no `:` (RFC 7617 §2: a user-id with a colon
  cannot be sent) and no control character.
* ITERATIONS: decimal digits, at least `minIterations` (100000) and at most
  `maxIterations` (10000000). `webdav-user` writes `defaultIterations`
  (600000, the OWASP Password Storage Cheat Sheet figure of 2023 for
  PBKDF2-HMAC-SHA256).
* SALT_B64: base64 (RFC 4648 §4, padded) of at least 16 bytes.
* HASH_B64: base64 of exactly 32 bytes, PBKDF2-HMAC-SHA256 (RFC 8018 §5.2)
  of the password's UTF-8 bytes with that salt and count.
* An empty line, and a line that starts with `#`, is not a user. A CR before
  the line end is removed. A name given twice stops the start.

A malformed line stops the start with `FILE:LINE: reason` (`parseUsers`).
The reader is one `for` loop over the lines.

The login decision (`gate`, then `finish`):

1. No `Authorization` field, a scheme other than `Basic`, a token that is not
   base64, a decoded text with no `:` or not UTF-8: 401 at once, with no
   derivation.
2. A known user with a live cache entry whose tag and stored hash match:
   allowed with no derivation.
3. Else one derivation: for a known user with its salt and count; for an
   unknown user with a salt made from the cache secret and the default count,
   so the time of a 401 does not tell which names exist. The derived bytes are
   compared with the stored hash by `ctEq` (an OR of XORs over every byte, no
   early exit). A match adds the cache entry; anything else is 401.

The cache (`Cache`): at most one entry per user, kept in the handle's memory
only, never written to a file. An entry is the user, the tag
`H(secret ‖ len(name) ‖ name ‖ password)` with `H` SHA-256 (HACL\* in the
engine; a parameter here), the stored hash it matched, and an expiry
`cacheSeconds` (300) after the derivation. The secret is 32 bytes from the
host's random source at `webdavOpen`. An entry is used only while it has not
expired and while its stored hash equals the user's stored hash. A failed
login never writes the cache.

The failed-login limit (`Limits`, `Failures`,
https://github.com/danbri/factoidal/issues/1119). Owner, 2026-10-28,
verbatim: "Does “no rate limit” expose our server passwords to automated
hacking tools? In which case default to protection but have a
—dangerously-disable-ratelimits option ?" So the limit is on unless the
listener starts with `--dangerously-disable-ratelimits`. The numbers are the
implementer's:

* Two keys per attempt: the user name as sent (`name:` ++ name; a name that
  is not in the users file is counted the same way) and the client address
  (`address:` ++ `clientPrefix`: an IPv4 address, or the /64 prefix of an
  IPv6 address, because one client usually holds a whole /64).
* Each key has a fixed window that starts at its first failure: at most
  `Limits.maxFailures` failures (default 5) in `Limits.window` seconds
  (default 60). A key with that many failures in a live window is blocked.
* An attempt with credentials whose name key or address key is blocked gets
  429 with `Retry-After` (the seconds until the later window ends), before
  the cache is read and with no derivation: the right password gets 429 too
  until the window ends. The cache is not read because a cache hit is a
  password check that costs one SHA-256, and so it would let a blocked
  client go on guessing.
* A failure is a derivation that did not allow the request (`finish`). A
  request with no credentials, or with credentials that are not Basic, is a
  401 with no derivation and is not counted.
* A successful login resets no counter. A reset of the address counter would
  let one valid user on a shared address clear the count of an attacker on
  that address; a reset of the name counter would let the real user's own
  login give an attacker on another address a new set of guesses against
  that name. Cost: a user whose name is blocked waits for the window to end,
  also with the right password.
* Memory: at most `Limits.maxKeys` (10000) live counters. An expired counter
  is dropped. A new key that finds the table full evicts the counter with the
  oldest window that is not blocked and is not a key of this attempt. A
  blocked counter is never evicted (`evictable` skips it; #guards below), so a flood of
  new names or addresses cannot end a block early. When the table has no
  place for the keys of an attempt, the attempt gets 429 (`Failures.check`)
  before any derivation, until the first window ends.

`transportAllowsBasic`: Basic sends the password in clear, so with a users
file the listener must use TLS (`--cert`, `--key`) or be bound to a loopback
address (`127.0.0.0/8`, `::1`, `localhost`); else the start stops.

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.WebDAV.Server
import L4Factoidal.LWS.Snapshot
import Std.Data.HashSet

namespace L4Factoidal.WebDAV.Login

open L4Factoidal.WebDAV

/-! ## Constants -/

/-- The scheme name of a users file line. -/
def schemeName : String := "pbkdf2-sha256"

/-- The fewest iterations a users file may name. -/
def minIterations : Nat := 100000

/-- The most iterations a users file may name: a bound against a line that
would make each login run for minutes. -/
def maxIterations : Nat := 10000000

/-- The count `webdav-user` writes: the OWASP Password Storage Cheat Sheet
figure (2023) for PBKDF2-HMAC-SHA256. -/
def defaultIterations : Nat := 600000

/-- The salt `webdav-user` writes, and the fewest salt bytes a line may have. -/
def saltBytes : Nat := 16

/-- PBKDF2 output: 32 bytes (256 bits). -/
def hashBytes : Nat := 32

/-- How long a successful login is remembered, in seconds. -/
def cacheSeconds : Nat := 300

/-- The most bytes of a password `webdav-user` accepts. -/
def maxPasswordBytes : Nat := 1024

/-- The `WWW-Authenticate` value of a 401 (RFC 7617 §2, §2.1). -/
def challenge : String := "Basic realm=\"factoidal webdav\", charset=\"UTF-8\""

/-- The WebCrypto operation the host runs (`npm/factoidal/lib/cipher-host.mjs`). -/
def kdfOpName : String := "pbkdf2-hmac-sha256"

/-! ## Bytes -/

/-- Equality of two byte strings in time that depends on their lengths only:
an OR of the XORs of every pair of bytes, with no early exit. The lengths are
public here (the stored hash and the derived bytes are 32 bytes each). -/
def ctEq (a b : ByteArray) : Bool := Id.run do
  if a.size != b.size then return false
  let mut acc : UInt8 := 0
  for i in [0:a.size] do
    acc := acc ||| (a.get! i ^^^ b.get! i)
  return acc == 0

/-- Four bytes, big endian. -/
def u32be (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]⟩

def b64 (b : ByteArray) : String := L4Factoidal.LWS.Base64.encode b
def unb64 (t : String) : Option ByteArray := L4Factoidal.LWS.Base64.decode? t

/-! ## The users file -/

structure User where
  name : String
  iterations : Nat
  salt : ByteArray
  hash : ByteArray
deriving Inhabited

/-- A name a users file may hold: not empty, no `:`, no control character. -/
def validName (n : String) : Bool :=
  !n.isEmpty && n.all (fun c => c != ':' && c.toNat ≥ 0x20 && c.toNat != 0x7f)

/-- A decimal count: digits only, at most 9 of them. -/
def countOf? (s : String) : Option Nat :=
  if s.isEmpty || s.length > 9 || !s.all Char.isDigit then none else s.toNat?

def User.line (u : User) : String :=
  s!"{u.name}:{schemeName}:{u.iterations}:{b64 u.salt}:{b64 u.hash}"

/-- One line of a users file. -/
def parseLine (line : String) : Except String User :=
  match line.splitOn ":" with
  | [name, scheme, it, salt, hash] =>
    if !validName name then .error "the user name is empty or holds a control character"
    else if scheme != schemeName then .error s!"the scheme \"{scheme}\" is not known (this engine reads {schemeName})"
    else match countOf? it with
      | none => .error s!"the iteration count \"{it}\" is not a decimal number"
      | some n =>
        if n < minIterations then .error s!"the iteration count {n} is below {minIterations}"
        else if n > maxIterations then .error s!"the iteration count {n} is above {maxIterations}"
        else match unb64 salt, unb64 hash with
          | none, _ => .error "the salt is not base64"
          | _, none => .error "the hash is not base64"
          | some s, some h =>
            if s.size < saltBytes then .error s!"the salt has {s.size} bytes; at least {saltBytes} are needed"
            else if h.size != hashBytes then .error s!"the hash has {h.size} bytes; PBKDF2-HMAC-SHA256 here gives {hashBytes}"
            else .ok { name, iterations := n, salt := s, hash := h }
  | parts => .error s!"a line has 5 fields NAME:{schemeName}:ITERATIONS:SALT:HASH, this one has {parts.length}"

/-- A line without its CR. -/
def chompCr (raw : String) : String := if raw.endsWith "\r" then (raw.dropEnd 1).toString else raw

/-- Is this line a user (not empty, not a comment)? -/
def isUserLine (line : String) : Bool := !line.isEmpty && !line.startsWith "#"

/-- Read a users file. `file` names it in each error (`FILE:LINE: reason`). -/
def parseUsers (file text : String) : Except String (List User) := do
  let mut acc : Array User := #[]
  let mut seen : Std.HashSet String := {}
  let mut n := 0
  for raw in text.splitOn "\n" do
    n := n + 1
    let line := chompCr raw
    if isUserLine line then
      match parseLine line with
      | .error e => throw s!"{file}:{n}: {e}"
      | .ok u =>
        if seen.contains u.name then throw s!"{file}:{n}: the user \"{u.name}\" is given twice"
        seen := seen.insert u.name
        acc := acc.push u
  pure acc.toList

/-- The users of a listener: the file read, and at least one user. -/
def usersForServer (file text : String) : Except String (List User) := do
  let us ← parseUsers file text
  if us.isEmpty then throw s!"{file}: the users file holds no user (add one with factoidal webdav-user)"
  pure us

/-! ## The transport -/

/-- An IPv4 address in dotted decimal, each part 0 to 255. -/
def ipv4Parts? (h : String) : Option (List Nat) :=
  let ps := h.splitOn "."
  if ps.length != 4 then none
  else ps.mapM (fun p => match countOf? p with
    | some v => if v ≤ 255 && p.length ≤ 3 then some v else none
    | none => none)

/-- A loopback address: `127.0.0.0/8` (RFC 1122 §3.2.1.3), `::1` (RFC 4291
§2.5.3), with or without brackets, or the name `localhost` (RFC 6761 §6.3). -/
def isLoopback (host : String) : Bool :=
  let h := (if host.startsWith "[" && host.endsWith "]" then ((host.drop 1).dropEnd 1).toString else host).toLower
  h == "localhost" || h == "::1" || h == "0:0:0:0:0:0:0:1" ||
    (match ipv4Parts? h with
     | some (127 :: _) => true
     | _ => false)

/-- Basic is allowed on a TLS listener, or on a loopback address. -/
def transportAllowsBasic (tls : Bool) (host : String) : Bool := tls || isLoopback host

def transportRefusal (host : String) : String :=
  s!"--users with HTTP Basic sends each password in clear text, and {host} is not a loopback address: " ++
  "give --cert and --key (HTTPS), or bind 127.0.0.1 or ::1 (https://github.com/danbri/factoidal/issues/1108)"

/-! ## Basic credentials (RFC 7617) -/

structure Credentials where
  user : String
  password : ByteArray

/-- The index of the first `:` byte. -/
def firstColon (b : ByteArray) : Option Nat := Id.run do
  for i in [0:b.size] do
    if b.get! i == 58 then return some i
  return none

/-- The credentials of an `Authorization` value, `none` for anything that is
not `Basic` with base64 of `user-id ":" password` (RFC 7617 §2). The scheme
name is case-insensitive (RFC 9110 §11.1). -/
def credentialsOf? (value : String) : Option Credentials :=
  match ((value.trimAscii.toString).splitOn " ").filter (· != "") with
  | [scheme, token] =>
    if scheme.toLower != "basic" then none
    else match unb64 token with
      | none => none
      | some bytes =>
        match firstColon bytes with
        | none => none
        | some i =>
          match String.fromUTF8? (bytes.extract 0 i) with
          | none => none
          | some user => some { user, password := bytes.extract (i + 1) bytes.size }
  | _ => none

/-! ## The failed-login limit (https://github.com/danbri/factoidal/issues/1119) -/

/-- The default count of failures per key in one window. -/
def defaultLimitFailures : Nat := 5
/-- The default window, in seconds. -/
def defaultLimitWindow : Nat := 60
/-- The most keys that have a counter at one time. -/
def maxTrackedKeys : Nat := 10000
/-- The largest `--login-limit`. -/
def maxLimitFailures : Nat := 1000
/-- The largest `--login-window` (one day). -/
def maxLimitWindow : Nat := 86400

structure Limits where
  enabled : Bool := true
  maxFailures : Nat := defaultLimitFailures
  window : Nat := defaultLimitWindow
  maxKeys : Nat := maxTrackedKeys

/-- The failures of one key in its window. -/
structure Counter where
  key : String
  start : Nat
  failures : Nat
deriving Inhabited

structure Failures where
  counters : Array Counter := #[]

def Counter.live (l : Limits) (now : Nat) (c : Counter) : Bool := decide (now < c.start + l.window)

def Counter.blocked (l : Limits) (now : Nat) (c : Counter) : Bool :=
  c.live l now && decide (c.failures ≥ l.maxFailures)

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- One IPv6 group: one to four hexadecimal digits (lower case). -/
def hexGroup? (g : String) : Option Nat :=
  if g.isEmpty || g.length > 4 then none
  else g.foldl (fun acc c => acc.bind (fun n => (hexDigit? c).map (fun d => n * 16 + d))) (some 0)

/-- The eight groups of an IPv6 address in text form (RFC 4291 §2.2, forms 1
and 2; an address with an IPv4 tail other than `::ffff:` is `none`). -/
def ipv6Groups? (h : String) : Option (List Nat) :=
  let parts (t : String) : List String := if t.isEmpty then [] else t.splitOn ":"
  match h.splitOn "::" with
  | [a] => if (parts a).length == 8 then (parts a).mapM hexGroup? else none
  | [a, b] =>
    let n := (parts a).length + (parts b).length
    if n ≤ 7 then ((parts a) ++ List.replicate (8 - n) "0" ++ (parts b)).mapM hexGroup? else none
  | _ => none

/-- The part of a client address that a counter keys on: an IPv4 address
(also from `::ffff:a.b.c.d`), the /64 prefix of an IPv6 address, or the text
as given when it is neither. -/
def clientPrefix (addr : String) : String :=
  let h := (if addr.startsWith "[" && addr.endsWith "]" then ((addr.drop 1).dropEnd 1).toString else addr).toLower
  let v4 := if h.startsWith "::ffff:" then (h.drop 7).toString else h
  if (ipv4Parts? v4).isSome then v4
  else match ipv6Groups? h with
    | some gs => ":".intercalate ((gs.take 4).map (fun g => String.ofList (Nat.toDigits 16 g))) ++ "::/64"
    | none => h

/-- The two keys of a login attempt. -/
def loginKeys (user address : String) : List String :=
  ["name:" ++ user, "address:" ++ clientPrefix address]

def Failures.blocked (l : Limits) (f : Failures) (now : Nat) (k : String) : Bool :=
  f.counters.any (fun c => c.key == k && c.blocked l now)

/-- The seconds until the last blocked window of `keys` ends (at least 1). -/
def Failures.retryAfter (l : Limits) (f : Failures) (now : Nat) (keys : List String) : Nat :=
  max 1 (f.counters.foldl (fun acc c =>
    if keys.contains c.key && c.blocked l now then max acc (c.start + l.window - now) else acc) 0)

/-- The seconds until the first live window ends (at least 1). -/
def Failures.soonest (l : Limits) (f : Failures) (now : Nat) : Nat :=
  max 1 (f.counters.foldl (fun acc c =>
    if c.live l now then
      (if acc == 0 then c.start + l.window - now else min acc (c.start + l.window - now))
    else acc) 0)

/-- How many new counters fit: free places, plus live counters that are not
blocked and are not in `keep`. -/
def Failures.room (l : Limits) (f : Failures) (now : Nat) (keep : List String) : Nat :=
  let live := f.counters.filter (·.live l now)
  (l.maxKeys - live.size) + (live.filter (fun c => !c.blocked l now && !keep.contains c.key)).size

/-- `some seconds` when an attempt with these keys gets 429 before any
derivation: a key is blocked, or the keys that have no counter would not
fit. -/
def Failures.check (l : Limits) (f : Failures) (now : Nat) (keys : List String) : Option Nat :=
  if !l.enabled then none
  else if keys.any (f.blocked l now) then some (f.retryAfter l now keys)
  else
    let untracked := keys.filter (fun k => !f.counters.any (fun c => c.key == k && c.live l now))
    if f.room l now keys < untracked.length then some (f.soonest l now) else none

/-- The index of the counter to evict: the oldest window that is not
blocked and not one of `keep`. -/
def evictable (l : Limits) (now : Nat) (keep : List String) (cs : Array Counter) : Option Nat := Id.run do
  let mut best : Option (Nat × Nat) := none
  for i in [0:cs.size] do
    let c := cs[i]!
    if !c.blocked l now && !keep.contains c.key then
      match best with
      | some (_, s) => if c.start < s then best := some (i, c.start)
      | none => best := some (i, c.start)
  return best.map (·.1)

/-- One failure for each of `keys`: expired counters dropped, live ones
counted up, a new counter for a key that has none. -/
def Failures.record (l : Limits) (f : Failures) (now : Nat) (keys : List String) : Failures := Id.run do
  if !l.enabled then return f
  let mut cs := f.counters.filter (·.live l now)
  for k in keys do
    match cs.findIdx? (·.key == k) with
    | some i => cs := cs.modify i (fun c => { c with failures := c.failures + 1 })
    | none =>
      if cs.size ≥ l.maxKeys then
        match evictable l now keys cs with
        | some i => cs := cs.eraseIdxIfInBounds i
        | none => pure ()
      if cs.size < l.maxKeys then cs := cs.push { key := k, start := now, failures := 1 }
  return { counters := cs }

/-- The limit options of `webdav-serve`, as the host read them (values
unread): `--login-limit N`, `--login-window SECONDS`,
`--dangerously-disable-ratelimits`. -/
def limitsOf (users : Bool) (limit window : Option String) (disable : Bool) : Except String Limits := do
  if !users && (limit.isSome || window.isSome || disable) then
    throw "--login-limit, --login-window and --dangerously-disable-ratelimits need --users"
  if disable && (limit.isSome || window.isSome) then
    throw "--dangerously-disable-ratelimits turns the failed-login limit off; --login-limit and --login-window cannot go with it"
  if disable then return { enabled := false }
  let n ← match limit with
    | none => pure defaultLimitFailures
    | some t => match countOf? t with
      | some v => if 1 ≤ v && v ≤ maxLimitFailures then pure v
                  else throw s!"--login-limit {t}: give a whole number from 1 to {maxLimitFailures}"
      | none => throw s!"--login-limit {t}: give a whole number from 1 to {maxLimitFailures}"
  let w ← match window with
    | none => pure defaultLimitWindow
    | some t => match countOf? t with
      | some v => if 1 ≤ v && v ≤ maxLimitWindow then pure v
                  else throw s!"--login-window {t}: give a whole number of seconds from 1 to {maxLimitWindow}"
      | none => throw s!"--login-window {t}: give a whole number of seconds from 1 to {maxLimitWindow}"
  pure { maxFailures := n, window := w }

/-- The warnings the listener prints at start. -/
def limitsWarnings (l : Limits) : List String :=
  if l.enabled then []
  else ["--dangerously-disable-ratelimits: failed logins are NOT limited; any client that can reach this port " ++
        "can try passwords as fast as the host runs PBKDF2 (https://github.com/danbri/factoidal/issues/1119)"]

/-- The 429 of a blocked attempt (RFC 6585 §4), the same for every name. -/
def tooManyFailures (seconds : Nat) : DavResponse :=
  textResp 429 s!"webdav: too many failed logins for this user name or from this address; try again in {seconds} s"
    [("retry-after", toString seconds)]

/-! ## The cache -/

structure CacheEntry where
  user : String
  tag : ByteArray
  stored : ByteArray
  expires : Nat

structure Cache where
  entries : List CacheEntry := []
  /-- The counters of the failed-login limit, kept with the entries in the
  handle's memory. -/
  failures : Failures := {}

/-- The cache tag of a presented name and password. -/
def tagOf (hash : ByteArray → ByteArray) (secret : ByteArray) (user : String) (password : ByteArray) : ByteArray :=
  let u := user.toUTF8
  hash (secret ++ u32be u.size ++ u ++ password)

def Cache.prune (c : Cache) (now : Nat) : Cache := { c with entries := c.entries.filter (fun e => now < e.expires) }

/-- The cache with `e` as the one entry of its user. -/
def Cache.put (c : Cache) (e : CacheEntry) : Cache := { c with entries := e :: c.entries.filter (·.user != e.user) }

/-! ## The decision -/

/-- One derivation the host runs: PBKDF2-HMAC-SHA256 of `password` with
`salt` and `iterations`, 256 bits. `expected` is the stored hash (empty for
an unknown user, so no derived value matches). -/
structure Derive where
  user : String
  known : Bool
  password : ByteArray
  salt : ByteArray
  iterations : Nat
  expected : ByteArray
  /-- The limit's keys of the attempt (`loginKeys`): a failure counts there. -/
  keys : List String := []

/-- What the listener does with a request before WebDAV sees it. -/
inductive Gate where
  | allow (user : String)
  | refuse
  /-- 429: the failed-login limit, with the `Retry-After` seconds. -/
  | limited (seconds : Nat)
  | derive (d : Derive)

structure Settings where
  users : List User
  /-- 32 bytes from the host's random source at `webdavOpen`. -/
  secret : ByteArray
  /-- The failed-login limit (on by default). -/
  limits : Limits := {}

/-- The salt of an unknown user: from the secret, so it is the same for a
name each time and unknown outside the process. -/
def unknownSalt (hash : ByteArray → ByteArray) (s : Settings) : ByteArray :=
  (hash (s.secret ++ "factoidal webdav unknown user".toUTF8)).extract 0 saltBytes

/-- The answer to credentials that pass the limit: the cache, else one
derivation. -/
def gateCredentials (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (cr : Credentials)
    (keys : List String) : Gate :=
  match s.users.find? (·.name == cr.user) with
  | none =>
    .derive { user := cr.user, known := false, password := cr.password, salt := unknownSalt hash s
              iterations := defaultIterations, expected := ByteArray.empty, keys }
  | some u =>
    let hit := c.entries.any (fun e =>
      e.user == u.name && ctEq e.stored u.hash && ctEq e.tag (tagOf hash s.secret u.name cr.password))
    if hit then .allow u.name
    else .derive { user := u.name, known := true, password := cr.password, salt := u.salt
                   iterations := u.iterations, expected := u.hash, keys }

/-- The first decision: the client's address, the `Authorization` value
(`none` when the request has none), the cache and the clock. The limit is
checked before the cache and before any derivation. -/
def gate (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (address : String)
    (authorization : Option String) : Gate × Cache :=
  let c := c.prune now
  match authorization.bind credentialsOf? with
  | none => (.refuse, c)
  | some cr =>
    match c.failures.check s.limits now (loginKeys cr.user address) with
    | some seconds => (.limited seconds, c)
    | none => (gateCredentials hash s c cr (loginKeys cr.user address), c)

/-- One failure of the attempt `d`, counted under its keys. -/
def Cache.fail (s : Settings) (c : Cache) (now : Nat) (d : Derive) : Cache :=
  { c with failures := c.failures.record s.limits now d.keys }

/-- The second decision: the host's derived bytes (`none` when the host
refused). A match of a known user is remembered for `cacheSeconds`; anything
else is a failure under the attempt's keys. -/
def finish (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (d : Derive)
    (derived : Option ByteArray) : Bool × Cache :=
  match derived with
  | some got =>
    if d.known && ctEq got d.expected then
      (true, c.put { user := d.user, tag := tagOf hash s.secret d.user d.password, stored := d.expected
                     expires := now + cacheSeconds })
    else (false, c.fail s now d)
  | none => (false, c.fail s now d)

/-- The 401 (RFC 9110 §15.5.2, RFC 7617 §2). -/
def unauthorized : DavResponse :=
  textResp 401 "webdav: this server needs a user name and password (HTTP Basic, RFC 7617)"
    [("www-authenticate", challenge)]

/-! ## Who a request acts as (emergency mode, issue 1147)

https://github.com/danbri/factoidal/issues/1147: every request acts as one
named user, and a mount names the users who may use it (`users:`).

* No `Authorization` field: the guest user (`--guest NAME`), or 401 when
  the listener has no guest.
* An `Authorization` field (any scheme, also a malformed one): a login
  through the users file (`gate`, then `finish`); with no users file, 401,
  because there is no one to log in as. A failed login counts toward the
  failed-login limit, as before.

The guest name is a user name (`validName`) that is not also a user of the
users file: else a request with no credentials would act as that user. -/

/-- The guest setting at start: the name, refused when it is not a user name
or when the users file holds a user of that name. -/
def guestCheck (guest : String) (users : List User) : Except String String :=
  if !validName guest || guest.contains ',' then
    .error s!"--guest: the user name \"{guest}\" is empty or holds `:`, `,` or a control character"
  else if users.any (·.name == guest) then
    .error s!"--guest: \"{guest}\" is a user of the users file; a request with no credentials would act as that user (https://github.com/danbri/factoidal/issues/1147)"
  else .ok guest

/-- The first decision of a request: `.allow user` (the guest, or a user the
cache knows), `.refuse` (401), `.limited` (429), or one derivation. `s` is
the login of the listener (`none`: no users file). -/
def admit (hash : ByteArray → ByteArray) (s : Option Settings) (guest : Option String) (c : Cache)
    (now : Nat) (address : String) (authorization : Option String) : Gate × Cache :=
  match authorization with
  | none =>
    match guest with
    | some g => (.allow g, c)
    | none => (.refuse, c)
  | some a =>
    match s with
    | none => (.refuse, c)
    | some s => gate hash s c now address (some a)

/-! ## `webdav-user`: one line added or replaced -/

/-- The password `webdav-user` read: the input without one final line end
(LF or CR LF). Refused: empty, longer than `maxPasswordBytes`, or holding a
control character (RFC 7617 §2: the password is `*TEXT` with no CTL). -/
def passwordOfInput (input : ByteArray) : Except String ByteArray :=
  let n := input.size
  let p :=
    if n ≥ 2 && input.get! (n - 2) == 13 && input.get! (n - 1) == 10 then input.extract 0 (n - 2)
    else if n ≥ 1 && input.get! (n - 1) == 10 then input.extract 0 (n - 1)
    else input
  if p.size == 0 then .error "the password is empty"
  else if p.size > maxPasswordBytes then .error s!"the password is longer than {maxPasswordBytes} bytes"
  else if p.data.any (fun b => b < 32 || b == 127) then .error "the password holds a control character"
  else match String.fromUTF8? p with
    | none => .error "the password is not UTF-8"
    | some _ => .ok p

/-- What `webdav-user` asks the host to derive, after the checks. -/
structure AddPlan where
  name : String
  password : ByteArray
  salt : ByteArray
  iterations : Nat

def planAdd (file name : String) (input salt : ByteArray) (iterations : Nat) (text : String) :
    Except String AddPlan := do
  if !validName name then throw s!"the user name \"{name}\" is empty, holds \":\" or a control character"
  if iterations < minIterations || iterations > maxIterations then
    throw s!"the iteration count {iterations} is outside {minIterations} to {maxIterations}"
  if salt.size != saltBytes then throw s!"the host gave {salt.size} salt bytes; {saltBytes} are needed"
  let _ ← parseUsers file text
  let password ← passwordOfInput input
  pure { name, password, salt, iterations }

/-- The file's new text: the user's line replaced where it is, or added at
the end. Every other line is kept as written. -/
def withUser (text : String) (u : User) : String × Bool :=
  let lines := text.splitOn "\n"
  let isTheUser (raw : String) : Bool :=
    let l := chompCr raw
    isUserLine l && (l.splitOn ":").head? == some u.name
  if lines.any isTheUser then
    ("\n".intercalate (lines.map (fun l => if isTheUser l then u.line else l)), true)
  else if text.isEmpty then (u.line ++ "\n", false)
  else if text.endsWith "\n" then (text ++ u.line ++ "\n", false)
  else (text ++ "\n" ++ u.line ++ "\n", false)

/-- The last step of `webdav-user`: the derived bytes into a line. -/
def finishAdd (p : AddPlan) (derived : ByteArray) (text : String) : Except String (String × Bool) :=
  if derived.size != hashBytes then .error s!"the host gave {derived.size} derived bytes; {hashBytes} are needed"
  else .ok (withUser text { name := p.name, iterations := p.iterations, salt := p.salt, hash := derived })

/-! ## Theorems -/

/-- A request with no `Authorization` field is refused, and no derivation is
asked for. -/
theorem gate_none (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (address : String) :
    (gate hash s c now address none).1 = .refuse := by
  simp [gate, Option.bind]

/-- When the limit check answers `some seconds`, the gate answers 429 with
those seconds: no cache read, no derivation. -/
theorem gate_limited (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (address : String)
    (authorization : Option String) (cr : Credentials) (seconds : Nat)
    (hcr : authorization.bind credentialsOf? = some cr)
    (hl : c.failures.check s.limits now (loginKeys cr.user address) = some seconds) :
    (gate hash s c now address authorization).1 = .limited seconds := by
  simp [gate, hcr, Cache.prune, hl]

/-- With the limit on, a blocked key among the attempt's keys makes the
check answer 429. -/
theorem check_blocked (l : Limits) (f : Failures) (now : Nat) (keys : List String) (k : String)
    (he : l.enabled = true) (hk : k ∈ keys) (hb : f.blocked l now k = true) :
    (f.check l now keys).isSome = true := by
  have hany : keys.any (f.blocked l now) = true := List.any_eq_true.mpr ⟨k, hk, hb⟩
  simp [Failures.check, he, hany]

/-- With the limit on, no derivation is asked for when the name key or the
address key of the attempt is blocked: the gate answers 429. -/
theorem gate_no_derive_of_blocked (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat)
    (address : String) (authorization : Option String) (cr : Credentials) (k : String)
    (hcr : authorization.bind credentialsOf? = some cr) (he : s.limits.enabled = true)
    (hk : k ∈ loginKeys cr.user address) (hb : c.failures.blocked s.limits now k = true) :
    ∃ seconds, (gate hash s c now address authorization).1 = .limited seconds := by
  have h := check_blocked s.limits c.failures now (loginKeys cr.user address) k he hk hb
  match hc : c.failures.check s.limits now (loginKeys cr.user address), h with
  | some seconds, _ => exact ⟨seconds, gate_limited hash s c now address authorization cr seconds hcr hc⟩

/-- With the limit off, the check never answers 429. -/
theorem check_disabled (l : Limits) (f : Failures) (now : Nat) (keys : List String)
    (he : l.enabled = false) : f.check l now keys = none := by
  simp [Failures.check, he]

/-- A derivation for a name that is not in the users file never allows the
request, whatever the host answers. -/
theorem finish_unknown (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (d : Derive)
    (derived : Option ByteArray) (h : d.known = false) : (finish hash s c now d derived).1 = false := by
  unfold finish
  cases derived <;> simp [h]

/-- A refused derivation never allows the request. -/
theorem finish_refused (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (d : Derive) :
    (finish hash s c now d none).1 = false := rfl

/-! ## Checks -/

section Checks

/-- A stand-in hash for the checks: the pure-Lean SHA-256 over test data. -/
def H : ByteArray → ByteArray := L4Factoidal.Crypto.sha256

def errOf {α : Type} : Except String α → Option String
  | .error e => some e
  | .ok _ => none

def bytesOf (xs : List Nat) : ByteArray := ⟨(xs.map UInt8.ofNat).toArray⟩

-- RFC 7914 §11 / RFC 6070-style vector is checked by the host's WebCrypto;
-- here the stored hash is any 32 bytes.
def hashA : ByteArray := ⟨Array.replicate 32 7⟩
def saltA : ByteArray := ⟨Array.replicate 16 1⟩

def alice : User := { name := "alice", iterations := 600000, salt := saltA, hash := hashA }
def sA : Settings := { users := [alice], secret := ⟨Array.replicate 32 9⟩ }

#guard ctEq (bytesOf [1, 2, 3]) (bytesOf [1, 2, 3])
#guard !ctEq (bytesOf [1, 2, 3]) (bytesOf [1, 2, 4])
#guard !ctEq (bytesOf [1, 2, 3]) (bytesOf [1, 2])
#guard !ctEq (bytesOf [0]) ByteArray.empty
#guard ctEq ByteArray.empty ByteArray.empty

-- The users file.
#guard (parseUsers "u" alice.line).toOption.map (·.length) == some 1
#guard (parseUsers "u" ("# comment\n\n" ++ alice.line ++ "\r\n")).toOption.map (·.map (·.name)) == some ["alice"]
#guard (parseUsers "u" "").toOption.map (·.length) == some 0
#guard errOf (usersForServer "u" "# none\n") == some "u: the users file holds no user (add one with factoidal webdav-user)"
#guard errOf (parseUsers "users.txt" "alice:placeholder\n") ==
  some "users.txt:1: a line has 5 fields NAME:pbkdf2-sha256:ITERATIONS:SALT:HASH, this one has 2"
#guard errOf (parseUsers "u" ("\n" ++ "bob:pbkdf2-sha256:99999:" ++ b64 saltA ++ ":" ++ b64 hashA)) ==
  some "u:2: the iteration count 99999 is below 100000"
#guard errOf (parseUsers "u" ("bob:pbkdf2-sha1:600000:" ++ b64 saltA ++ ":" ++ b64 hashA)) ==
  some "u:1: the scheme \"pbkdf2-sha1\" is not known (this engine reads pbkdf2-sha256)"
#guard errOf (parseUsers "u" ("bob:pbkdf2-sha256:6e5:" ++ b64 saltA ++ ":" ++ b64 hashA)) ==
  some "u:1: the iteration count \"6e5\" is not a decimal number"
#guard errOf (parseUsers "u" ("bob:pbkdf2-sha256:600000:" ++ b64 (bytesOf [1, 2]) ++ ":" ++ b64 hashA)) ==
  some "u:1: the salt has 2 bytes; at least 16 are needed"
#guard errOf (parseUsers "u" ("bob:pbkdf2-sha256:600000:" ++ b64 saltA ++ ":" ++ b64 saltA)) ==
  some "u:1: the hash has 16 bytes; PBKDF2-HMAC-SHA256 here gives 32"
#guard errOf (parseUsers "u" ("bob:pbkdf2-sha256:600000:" ++ b64 saltA ++ ":!!")) == some "u:1: the hash is not base64"
#guard errOf (parseUsers "u" (alice.line ++ "\n" ++ alice.line)) == some "u:2: the user \"alice\" is given twice"

-- The transport.
#guard isLoopback "127.0.0.1" && isLoopback "127.1.2.3" && isLoopback "::1" && isLoopback "[::1]"
#guard isLoopback "localhost" && isLoopback "LOCALHOST"
#guard !isLoopback "0.0.0.0" && !isLoopback "192.168.1.2" && !isLoopback "::" && !isLoopback "127.0.0.256"
#guard !isLoopback "127.0.0" && !isLoopback "example.org"
#guard transportAllowsBasic true "0.0.0.0" && !transportAllowsBasic false "0.0.0.0"

-- Basic credentials: "alice:open sesame" and "alice:" and a password with ":".
#guard (credentialsOf? ("Basic " ++ b64 "alice:open sesame".toUTF8)).map (fun c => (c.user, c.password.size)) == some ("alice", 11)
#guard (credentialsOf? ("  basic   " ++ b64 "alice:a:b".toUTF8)).map (fun c => c.password == "a:b".toUTF8) == some true
#guard (credentialsOf? ("Bearer " ++ b64 "alice:x".toUTF8)).isNone
#guard (credentialsOf? ("Basic " ++ b64 "no colon".toUTF8)).isNone
#guard (credentialsOf? "Basic ***").isNone
#guard (credentialsOf? "Basic").isNone

-- The decision.
def authA (pw : String) : Option String := some ("Basic " ++ b64 ("alice:" ++ pw).toUTF8)

#guard (match (gate H sA {} 100 "127.0.0.1" none).1 with | .refuse => true | _ => false)
#guard (match (gate H sA {} 100 "127.0.0.1" (some "Digest x")).1 with | .refuse => true | _ => false)
-- A known user, no cache: one derivation with the stored salt and count.
#guard (match (gate H sA {} 100 "127.0.0.1" (authA "pw")).1 with
  | .derive d => d.known && d.user == "alice" && d.iterations == 600000 && ctEq d.salt saltA && ctEq d.expected hashA
  | _ => false)
-- An unknown user: a derivation too (the time of the 401 does not tell),
-- with the default count, and it never allows.
#guard (match (gate H sA {} 100 "127.0.0.1" (some ("Basic " ++ b64 "mallory:pw".toUTF8))).1 with
  | .derive d => !d.known && d.iterations == defaultIterations && d.salt.size == saltBytes &&
      !(finish H sA {} 100 d (some hashA)).1
  | _ => false)

instance : Inhabited Derive := ⟨{ user := "", known := false, password := .empty, salt := .empty, iterations := 0, expected := .empty }⟩

def dA : Derive := match (gate H sA {} 100 "127.0.0.1" (authA "pw")).1 with
  | .derive d => d
  | _ => default

-- The derived bytes equal to the stored hash: allowed, and cached.
#guard (finish H sA {} 100 dA (some hashA)).1
#guard (finish H sA {} 100 dA (some hashA)).2.entries.length == 1
-- Other bytes, or a refusal: 401, nothing cached.
#guard !(finish H sA {} 100 dA (some ⟨Array.replicate 32 8⟩)).1
#guard (finish H sA {} 100 dA (some ⟨Array.replicate 32 8⟩)).2.entries.isEmpty
#guard !(finish H sA {} 100 dA none).1

def cA : Cache := (finish H sA {} 100 dA (some hashA)).2

-- With the cache: the same password is allowed with no derivation...
#guard (match (gate H sA cA 150 "127.0.0.1" (authA "pw")).1 with | .allow u => u == "alice" | _ => false)
-- ... another password still derives (and then fails) ...
#guard (match (gate H sA cA 150 "127.0.0.1" (authA "other")).1 with | .derive _ => true | _ => false)
-- ... and the entry ends after cacheSeconds.
#guard (match (gate H sA cA (100 + cacheSeconds) "127.0.0.1" (authA "pw")).1 with | .derive _ => true | _ => false)
#guard (gate H sA cA (100 + cacheSeconds) "127.0.0.1" (authA "pw")).2.entries.isEmpty
-- A users file whose hash for alice changed does not use the old entry.
#guard (match (gate H { sA with users := [{ alice with hash := ⟨Array.replicate 32 3⟩ }] } cA 150 "127.0.0.1" (authA "pw")).1 with
  | .derive _ => true | _ => false)

-- The failed-login limit (https://github.com/danbri/factoidal/issues/1119).
def isLimited : Gate → Option Nat
  | .limited n => some n
  | _ => none
def isDerive : Gate → Bool
  | .derive _ => true
  | _ => false

/-- `n` failed attempts with password `pw` for `user` from `addr`, starting
at `t0`, one second apart: the cache after them. -/
def failN (s : Settings) (c : Cache) (user addr : String) (n t0 : Nat) : Cache := Id.run do
  let mut c := c
  for i in [0:n] do
    match gate H s c (t0 + i) addr (some ("Basic " ++ b64 (user ++ ":wrong").toUTF8)) with
    | (.derive d, c') => c := (finish H s c' (t0 + i) d (some ⟨Array.replicate 32 8⟩)).2
    | (_, c') => c := c'
  return c

def authU (u pw : String) : Option String := some ("Basic " ++ b64 (u ++ ":" ++ pw).toUTF8)

-- Under the limit: four failures, the fifth attempt still derives.
#guard isDerive (gate H sA (failN sA {} "alice" "10.0.0.1" 4 100) 104 "10.0.0.1" (authA "wrong")).1
-- At the limit: five failures, the sixth attempt is 429 with no derivation,
-- with the right password too, and Retry-After is the rest of the window.
#guard isLimited (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 105 "10.0.0.1" (authA "pw")).1 == some 55
-- The name is blocked from every address; the address for every name.
#guard isLimited (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 105 "10.0.0.2" (authA "pw")).1 == some 55
#guard isLimited (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 105 "10.0.0.1" (authU "bob" "x")).1 == some 55
-- Another name from another address is not blocked.
#guard isDerive (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 105 "10.0.0.2" (authU "bob" "x")).1
-- Window expiry: at 160 (100 + 60) the window has ended.
#guard isLimited (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 159 "10.0.0.1" (authA "pw")).1 == some 1
#guard isDerive (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 160 "10.0.0.1" (authA "pw")).1
-- No credentials stays 401 (not counted, not 429).
#guard (match (gate H sA (failN sA {} "alice" "10.0.0.1" 5 100) 105 "10.0.0.1" none).1 with | .refuse => true | _ => false)
-- An unknown name gets the same answers as a known one.
#guard isDerive (gate H sA (failN sA {} "mallory" "10.0.0.1" 4 100) 104 "10.0.0.3" (authU "mallory" "x")).1
#guard isLimited (gate H sA (failN sA {} "mallory" "10.0.0.1" 5 100) 105 "10.0.0.3" (authU "mallory" "x")).1 == some 55
#guard isLimited (gate H sA (failN sA {} "mallory" "10.0.0.1" 5 100) 105 "10.0.0.1" (authU "alice" "pw")).1 == some 55
-- A success counts nothing and resets nothing.
#guard (finish H sA (failN sA {} "alice" "10.0.0.1" 3 100) 103 dA (some hashA)).2.failures.counters.map (·.failures) ==
  #[3, 3]
-- A blocked cache entry is not read: alice cached, then blocked, gets 429.
#guard isLimited (gate H sA (failN sA cA "alice" "10.0.0.1" 5 100) 105 "10.0.0.1" (authA "pw")).1 == some 55
-- Disabled: eight failures, the ninth still derives; the warning is given.
def sOff : Settings := { sA with limits := { enabled := false } }
#guard isDerive (gate H sOff (failN sOff {} "alice" "10.0.0.1" 8 100) 108 "10.0.0.1" (authA "pw")).1
#guard (failN sOff {} "alice" "10.0.0.1" 8 100).failures.counters.isEmpty
#guard (limitsWarnings { enabled := false }).length == 1 && (limitsWarnings {}).isEmpty

-- Eviction, with a table of 3 keys and a limit of 2.
def lSmall : Limits := { maxFailures := 2, window := 60, maxKeys := 3 }
def fBlocked : Failures := { counters := #[{ key := "name:alice", start := 100, failures := 2 }
                                         , { key := "address:10.0.0.1", start := 101, failures := 1 }
                                         , { key := "name:bob", start := 102, failures := 1 }] }
-- A new key evicts the oldest counter that is not blocked; the blocked one stays.
#guard ((fBlocked.record lSmall 110 ["name:carol"]).counters.map (·.key)) ==
  #["name:alice", "name:bob", "name:carol"]
#guard (fBlocked.record lSmall 110 ["name:carol"]).blocked lSmall 110 "name:alice"
-- A flood of new names never evicts the blocked counter.
#guard ((["n1", "n2", "n3", "n4", "n5", "n6"].foldl (fun f n => f.record lSmall 110 [n]) fBlocked).blocked lSmall 110 "name:alice")
-- When every counter is blocked, an attempt with an untracked key is 429
-- until the first window ends, and the record does not add it.
def fFull : Failures := { counters := #[{ key := "a", start := 100, failures := 2 }, { key := "b", start := 101, failures := 2 }
                                      , { key := "c", start := 102, failures := 2 }] }
#guard fFull.check lSmall 110 ["d"] == some 50
#guard (fFull.record lSmall 110 ["d"]).counters.size == 3
#guard fFull.check lSmall 160 ["d"] == none
-- Expired counters are dropped by the record.
#guard (fFull.record lSmall 200 ["d"]).counters.map (·.key) == #["d"]

-- The address key: IPv4, IPv4-mapped IPv6, and the /64 of IPv6.
#guard clientPrefix "127.0.0.1" == "127.0.0.1"
#guard clientPrefix "::ffff:192.0.2.7" == "192.0.2.7"
#guard clientPrefix "2001:db8:1:2:3:4:5:6" == "2001:db8:1:2::/64"
#guard clientPrefix "2001:DB8:1:2::9" == clientPrefix "2001:db8:1:2:ffff::1"
#guard clientPrefix "::1" == "0:0:0:0::/64"
#guard clientPrefix "" == ""
#guard loginKeys "alice" "10.0.0.1" == ["name:alice", "address:10.0.0.1"]

-- The options.
#guard (limitsOf true none none false).toOption.map (fun l => (l.enabled, l.maxFailures, l.window)) == some (true, 5, 60)
#guard (limitsOf true (some "10") (some "300") false).toOption.map (fun l => (l.maxFailures, l.window)) == some (10, 300)
#guard (limitsOf true none none true).toOption.map (·.enabled) == some false
#guard errOf (limitsOf true (some "0") none false) == some "--login-limit 0: give a whole number from 1 to 1000"
#guard errOf (limitsOf true (some "x") none false) == some "--login-limit x: give a whole number from 1 to 1000"
#guard errOf (limitsOf true none (some "86401") false) ==
  some "--login-window 86401: give a whole number of seconds from 1 to 86400"
#guard (errOf (limitsOf true (some "3") none true)).isSome
#guard errOf (limitsOf false none none true) ==
  some "--login-limit, --login-window and --dangerously-disable-ratelimits need --users"
#guard (tooManyFailures 42).status == 429 && (tooManyFailures 42).headers.lookup "retry-after" == some "42"

-- `webdav-user`.
#guard (passwordOfInput "secret\n".toUTF8).toOption.map (· == "secret".toUTF8) == some true
#guard (passwordOfInput "secret\r\n".toUTF8).toOption.map (· == "secret".toUTF8) == some true
#guard (passwordOfInput "secret".toUTF8).toOption.map (· == "secret".toUTF8) == some true
#guard errOf (passwordOfInput "\n".toUTF8) == some "the password is empty"
#guard errOf (passwordOfInput "a\nb\n".toUTF8) == some "the password holds a control character"
#guard (planAdd "u" "a:b" "pw".toUTF8 saltA 600000 "").toOption.isNone
#guard (planAdd "u" "bob" "pw".toUTF8 saltA 50000 "").toOption.isNone
#guard (planAdd "u" "bob" "pw".toUTF8 (bytesOf [1]) 600000 "").toOption.isNone
#guard errOf (planAdd "u" "bob" "pw\n".toUTF8 saltA 600000 "junk\n") ==
  some "u:1: a line has 5 fields NAME:pbkdf2-sha256:ITERATIONS:SALT:HASH, this one has 1"
#guard (withUser "" alice).1 == alice.line ++ "\n"
#guard (withUser "# users\n" alice) == ("# users\n" ++ alice.line ++ "\n", false)
#guard (withUser "# users" alice) == ("# users\n" ++ alice.line ++ "\n", false)
-- Replacing keeps every other line where it is.
def aliceOld : User := { alice with iterations := 100000 }
def bob : User := { alice with name := "bob" }
#guard (withUser ("# x\n" ++ aliceOld.line ++ "\n" ++ bob.line ++ "\n") alice) ==
  ("# x\n" ++ alice.line ++ "\n" ++ bob.line ++ "\n", true)
#guard (parseUsers "u" (withUser (withUser "" alice).1 bob).1).toOption.map (·.map (·.name)) == some ["alice", "bob"]

-- Issue 1147: who a request acts as.
#guard (match (admit H (some sA) (some "guest") {} 100 "127.0.0.1" none).1 with | .allow u => u == "guest" | _ => false)
#guard (match (admit H none (some "guest") {} 100 "127.0.0.1" none).1 with | .allow u => u == "guest" | _ => false)
#guard (match (admit H (some sA) none {} 100 "127.0.0.1" none).1 with | .refuse => true | _ => false)
#guard (match (admit H none none {} 100 "127.0.0.1" none).1 with | .refuse => true | _ => false)
-- Credentials with no users file: 401, also with a guest.
#guard (match (admit H none (some "guest") {} 100 "127.0.0.1" (authA "pw")).1 with | .refuse => true | _ => false)
-- Credentials that are not Basic: 401, never the guest.
#guard (match (admit H (some sA) (some "guest") {} 100 "127.0.0.1" (some "Digest x")).1 with | .refuse => true | _ => false)
#guard (match (admit H (some sA) (some "guest") {} 100 "127.0.0.1" (some "")).1 with | .refuse => true | _ => false)
-- Credentials with a users file: the login.
#guard (match (admit H (some sA) (some "guest") {} 100 "127.0.0.1" (authA "pw")).1 with
  | .derive d => d.known && d.user == "alice" | _ => false)
#guard (match (admit H (some sA) none cA 150 "127.0.0.1" (authA "pw")).1 with | .allow u => u == "alice" | _ => false)
-- A failed login still counts toward the limit.
#guard (match (admit H (some { sA with limits := { maxFailures := 1 } }) (some "guest") (cA.fail { sA with limits := { maxFailures := 1 } } 100 dA) 101
  "127.0.0.1" (authA "pw")).1 with | .limited _ => true | _ => false)
#guard (guestCheck "guest" [alice]).toOption == some "guest"
#guard (guestCheck "alice" [alice]).toOption.isNone
#guard (guestCheck "" []).toOption.isNone
#guard (guestCheck "a:b" []).toOption.isNone
#guard (guestCheck "a,b" []).toOption.isNone

end Checks

/-- With no credentials, a request acts as the guest, or is refused when
there is no guest. -/
theorem admit_none (hash : ByteArray → ByteArray) (s : Option Settings) (guest : Option String)
    (c : Cache) (now : Nat) (address : String) :
    (admit hash s guest c now address none).1 = (match guest with | some g => .allow g | none => .refuse) := by
  cases guest <;> rfl

/-- With credentials and no users file, a request is refused (401). -/
theorem admit_no_users (hash : ByteArray → ByteArray) (guest : Option String) (c : Cache) (now : Nat)
    (address a : String) : (admit hash none guest c now address (some a)).1 = .refuse := rfl

/-- The credentials step allows only a user of the users file. -/
theorem gateCredentials_allow (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (cr : Credentials)
    (keys : List String) (u : String) (h : gateCredentials hash s c cr keys = .allow u) :
    ∃ x ∈ s.users, x.name = u := by
  unfold gateCredentials at h
  split at h
  · cases h
  · rename_i x hx
    dsimp only at h
    split at h
    · cases h; exact ⟨x, List.mem_of_find?_eq_some hx, rfl⟩
    · cases h

/-- With credentials, `admit` allows only a user of the users file (never
the guest by a fall back). -/
theorem admit_some_allow (hash : ByteArray → ByteArray) (s : Option Settings) (guest : Option String)
    (c : Cache) (now : Nat) (address a u : String)
    (h : (admit hash s guest c now address (some a)).1 = .allow u) :
    ∃ s' x, s = some s' ∧ x ∈ s'.users ∧ x.name = u := by
  cases s with
  | none => cases h
  | some s' =>
    simp only [admit, gate] at h
    split at h
    · cases h
    · rename_i cr _
      split at h
      · cases h
      · exact (gateCredentials_allow hash s' _ cr _ u h).elim (fun x hx => ⟨s', x, rfl, hx.1, hx.2⟩)

/-- A login that `finish` allows is a user of the users file. -/
theorem finish_allow_known (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (d : Derive)
    (got : Option ByteArray) (h : (finish hash s c now d got).1 = true) : d.known = true := by
  unfold finish at h
  split at h
  · split at h
    · rename_i hk; simp only [Bool.and_eq_true] at hk; exact hk.1
    · cases h
  · cases h

end L4Factoidal.WebDAV.Login
