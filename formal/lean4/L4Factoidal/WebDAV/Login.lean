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

/-! ## The cache -/

structure CacheEntry where
  user : String
  tag : ByteArray
  stored : ByteArray
  expires : Nat

structure Cache where
  entries : List CacheEntry := []

/-- The cache tag of a presented name and password. -/
def tagOf (hash : ByteArray → ByteArray) (secret : ByteArray) (user : String) (password : ByteArray) : ByteArray :=
  let u := user.toUTF8
  hash (secret ++ u32be u.size ++ u ++ password)

def Cache.prune (c : Cache) (now : Nat) : Cache := { entries := c.entries.filter (fun e => now < e.expires) }

/-- The cache with `e` as the one entry of its user. -/
def Cache.put (c : Cache) (e : CacheEntry) : Cache := { entries := e :: c.entries.filter (·.user != e.user) }

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

/-- What the listener does with a request before WebDAV sees it. -/
inductive Gate where
  | allow (user : String)
  | refuse
  | derive (d : Derive)

structure Settings where
  users : List User
  /-- 32 bytes from the host's random source at `webdavOpen`. -/
  secret : ByteArray

/-- The salt of an unknown user: from the secret, so it is the same for a
name each time and unknown outside the process. -/
def unknownSalt (hash : ByteArray → ByteArray) (s : Settings) : ByteArray :=
  (hash (s.secret ++ "factoidal webdav unknown user".toUTF8)).extract 0 saltBytes

/-- The first decision: the `Authorization` value (`none` when the request
has none), the cache and the clock. -/
def gate (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat)
    (authorization : Option String) : Gate × Cache :=
  let c := c.prune now
  match authorization.bind credentialsOf? with
  | none => (.refuse, c)
  | some cr =>
    match s.users.find? (·.name == cr.user) with
    | none =>
      (.derive { user := cr.user, known := false, password := cr.password, salt := unknownSalt hash s
                 iterations := defaultIterations, expected := ByteArray.empty }, c)
    | some u =>
      let hit := c.entries.any (fun e =>
        e.user == u.name && ctEq e.stored u.hash && ctEq e.tag (tagOf hash s.secret u.name cr.password))
      if hit then (.allow u.name, c)
      else (.derive { user := u.name, known := true, password := cr.password, salt := u.salt
                      iterations := u.iterations, expected := u.hash }, c)

/-- The second decision: the host's derived bytes (`none` when the host
refused). A match of a known user is remembered for `cacheSeconds`. -/
def finish (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) (d : Derive)
    (derived : Option ByteArray) : Bool × Cache :=
  match derived with
  | some got =>
    if d.known && ctEq got d.expected then
      (true, c.put { user := d.user, tag := tagOf hash s.secret d.user d.password, stored := d.expected
                     expires := now + cacheSeconds })
    else (false, c)
  | none => (false, c)

/-- The 401 (RFC 9110 §15.5.2, RFC 7617 §2). -/
def unauthorized : DavResponse :=
  textResp 401 "webdav: this server needs a user name and password (HTTP Basic, RFC 7617)"
    [("www-authenticate", challenge)]

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
theorem gate_none (hash : ByteArray → ByteArray) (s : Settings) (c : Cache) (now : Nat) :
    (gate hash s c now none).1 = .refuse := by
  simp [gate, Option.bind]

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

#guard (match (gate H sA {} 100 none).1 with | .refuse => true | _ => false)
#guard (match (gate H sA {} 100 (some "Digest x")).1 with | .refuse => true | _ => false)
-- A known user, no cache: one derivation with the stored salt and count.
#guard (match (gate H sA {} 100 (authA "pw")).1 with
  | .derive d => d.known && d.user == "alice" && d.iterations == 600000 && ctEq d.salt saltA && ctEq d.expected hashA
  | _ => false)
-- An unknown user: a derivation too (the time of the 401 does not tell),
-- with the default count, and it never allows.
#guard (match (gate H sA {} 100 (some ("Basic " ++ b64 "mallory:pw".toUTF8))).1 with
  | .derive d => !d.known && d.iterations == defaultIterations && d.salt.size == saltBytes &&
      !(finish H sA {} 100 d (some hashA)).1
  | _ => false)

instance : Inhabited Derive := ⟨{ user := "", known := false, password := .empty, salt := .empty, iterations := 0, expected := .empty }⟩

def dA : Derive := match (gate H sA {} 100 (authA "pw")).1 with
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
#guard (match (gate H sA cA 150 (authA "pw")).1 with | .allow u => u == "alice" | _ => false)
-- ... another password still derives (and then fails) ...
#guard (match (gate H sA cA 150 (authA "other")).1 with | .derive _ => true | _ => false)
-- ... and the entry ends after cacheSeconds.
#guard (match (gate H sA cA (100 + cacheSeconds) (authA "pw")).1 with | .derive _ => true | _ => false)
#guard (gate H sA cA (100 + cacheSeconds) (authA "pw")).2.entries.isEmpty
-- A users file whose hash for alice changed does not use the old entry.
#guard (match (gate H { sA with users := [{ alice with hash := ⟨Array.replicate 32 3⟩ }] } cA 150 (authA "pw")).1 with
  | .derive _ => true | _ => false)

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

end Checks

end L4Factoidal.WebDAV.Login
