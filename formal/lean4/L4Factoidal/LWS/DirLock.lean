/-
L4Factoidal.LWS.DirLock — one writing process per storage directory, and the
start notice about encryption at rest.

Issue: https://github.com/danbri/factoidal/issues/1135 (row C11, invariant
I11 of `docs/designissues/2026-10-28-feature-combination-safety.md`).

## The lock

A server that keeps a storage in a directory DIR (`lws-serve DIR`,
`solid-serve DIR`, a `webdav-serve` mount of `kind: local`) holds the file
`DIR/lws.lock` while it runs. This module decides the file name, its
contents and what a start does; the host performs exactly three operations:
an exclusive create of the file (`O_EXCL`, Node flag `wx`), a liveness probe
of a process id (`kill(pid, 0)`), and the removal of the file at a clean
exit. The host passes the result of each as data to `decide`.

The contents (format `lws-lock-1`, one JSON object and a line end):

    {"format":"lws-lock-1","pid":N,"command":"lws-serve","started":"<ISO 8601>",
     "host":"<host name>","token":"<random text of the process>"}

`token` is a random text that the host draws once per process. It tells a
lock this process wrote from a lock of an earlier process that had the same
process id (a container that restarts gives its first process the same id
every time).

`decide`, in order:

1. no file: create it with this process's contents (`Action.create`);
2. a file that is not a lock of this format: refuse, name the file;
3. a holder on another host: refuse; a probe on this host says nothing about
   a process on another host;
4. a holder with this process id: this process wrote it (same `token`):
   refuse, the directory is already open in this process; another `token`:
   a dead earlier process with the same id, so take over with a warning;
5. another process id and no probe result yet: ask the host to probe
   (`Action.probe`);
6. the probe says alive: refuse, name the file and the holder;
7. the probe says not alive: take over with a warning (`Action.replace`).

Theorems: `decide_absent` (no file gives a create), `decide_create_absent`
(a create only when there is no file), `decide_alive_refuses` (a live holder
on this host is refused), `decide_otherHost_refuses`,
`decide_sameInstance_refuses`, and `decide_replace_dead`: a take-over only
when the probe said the holder is not alive, or the holder has this process
id and another token.

What the lock does not stop: a process that does not take the lock (another
program, an old Factoidal build) still writes DIR. After a `replace` the host
removes the file and creates it again with `O_EXCL`; when two starts take
over the same stale lock at the same time, one create fails and that start
asks again from step 1 (at most a fixed number of times). A start that
removes the file after the other start created it is not excluded: the
remove-then-create of a take-over is not atomic. The window is the time
between the probe and the create of a take-over, after a crash only.

## The start notice

`atRestNotice` is the line a server prints at start, after the experimental
code notice: with no storage key, that the storage is written in clear text
and how to turn on encryption at rest; with a key, that the storage is sealed
and the key id (`Seal.keyIdOf`). Encryption at rest stays off by default
(owner, 2026-10-21: "Yes env var please. Again off by default but good to
show we can."; owner, 2026-10-28: "For our lws encourage attention to
encryption at rest also").

`newStorageKey` gives the text of a new key from 32 random bytes of the host
(`factoidal lws-keygen`), in the hex form `Seal.parseStorageKey` reads.
-/
import L4Factoidal.LWS.SnapshotSeal
import L4Factoidal.Crypto.SHA2
import L4Factoidal.JSON.Serialize
import L4Factoidal.JSON.Parser

namespace L4Factoidal.LWS.DirLock

open L4Factoidal.JSON

/-! ## The lock file -/

/-- The lock file, relative to the storage directory. -/
def lockFile : String := "lws.lock"

/-- The format id of the lock file. -/
def lockFormat : String := "lws-lock-1"

/-- The issue that records the rule, named in every refusal. -/
def lockIssue : String := "https://github.com/danbri/factoidal/issues/1135"

/-- The process that holds (or wants) the lock. -/
structure Holder where
  pid : Nat
  command : String
  started : String
  host : String
  token : String
deriving DecidableEq, Repr, Inhabited

def holderJson (h : Holder) : Json :=
  .object [ ("format", .string lockFormat), ("pid", .number (toString h.pid))
          , ("command", .string h.command), ("started", .string h.started)
          , ("host", .string h.host), ("token", .string h.token) ]

/-- The bytes of the lock file, as text. -/
def contentsOf (h : Holder) : String := (holderJson h).toString ++ "\n"

def natOf? : Option Json → Option Nat
  | some (.number s) => s.toNat?
  | _ => none

/-- A holder from the JSON of a lock file: every member present, the format
this module writes. -/
def holderOfJson (j : Json) : Option Holder :=
  if j.getString? "format" != some lockFormat then none else do
    let pid ← natOf? (j.field? "pid")
    let command ← j.getString? "command"
    let started ← j.getString? "started"
    let host ← j.getString? "host"
    let tok ← j.getString? "token"
    pure { pid, command, started, host, token := tok }

/-- A holder from the text of a lock file. -/
def parseHolder (text : String) : Option Holder :=
  match parseJson text with
  | .ok j => holderOfJson j
  | .error _ => none

#guard parseHolder (contentsOf { pid := 4242, command := "lws-serve", started := "2026-10-28T10:00:00.000Z",
                                 host := "box", token := "q1w2e3" }) ==
  some { pid := 4242, command := "lws-serve", started := "2026-10-28T10:00:00.000Z",
         host := "box", token := "q1w2e3" }
#guard parseHolder "not json" == none
#guard parseHolder "{\"format\":\"lws-lock-0\",\"pid\":1}" == none

/-! ## The decision -/

/-- What a start asks: the storage directory (for the messages only), this
process, the text of the lock file when the exclusive create found one, and
the result of the liveness probe when the host made it. -/
structure Request where
  dir : String
  self : Holder
  present : Option String := none
  alive : Option Bool := none
deriving Repr

/-- What the host does next. -/
inductive Action where
  /-- Create `file` with `O_EXCL` and write `contents`. -/
  | create (file contents : String)
  /-- Probe process `pid` and ask again with `alive`. -/
  | probe (pid : Nat)
  /-- Stop the start with `message`. -/
  | refuse (message : String)
  /-- Remove `file`, create it with `O_EXCL`, write `contents`, print
  `warning`. -/
  | replace (file contents warning : String)
deriving DecidableEq, Repr

def pathOf (dir : String) : String :=
  if dir.endsWith "/" then dir ++ lockFile else dir ++ "/" ++ lockFile

def describe (h : Holder) : String :=
  s!"process {h.pid} ({h.command}, started {h.started}) on host {h.host}"

def unreadableMessage (dir : String) : String :=
  s!"the storage directory {dir} has a file {pathOf dir} that is not a lock file of format {lockFormat}. " ++
  s!"One process writes a storage directory ({lockIssue}). Remove the file only if no server uses the directory."

def otherHostMessage (dir : String) (h self : Holder) : String :=
  s!"the storage directory {dir} is locked: {pathOf dir} names {describe h}. This host ({self.host}) cannot " ++
  s!"tell if that process runs. One process writes a storage directory ({lockIssue}). " ++
  s!"Remove the file only if that process does not run."

def sameProcessMessage (dir : String) : String :=
  s!"the storage directory {dir} is already open in this process ({pathOf dir}). " ++
  s!"One process writes a storage directory, and it opens it once ({lockIssue})."

def aliveMessage (dir : String) (h : Holder) : String :=
  s!"the storage directory {dir} is in use: {pathOf dir} names {describe h}, and that process runs. " ++
  s!"One process writes a storage directory ({lockIssue}). Stop that process first."

def staleWarning (dir : String) (h : Holder) : String :=
  s!"{pathOf dir} named {describe h}, which does not run (a stale lock, for example after a crash). " ++
  s!"This process takes the lock over."

/-- The decision of a start. -/
def decide (r : Request) : Action :=
  match r.present with
  | none => .create lockFile (contentsOf r.self)
  | some text =>
      match parseHolder text with
      | none => .refuse (unreadableMessage r.dir)
      | some h =>
          if h.host != r.self.host then .refuse (otherHostMessage r.dir h r.self)
          else if h.pid == r.self.pid then
            if h.token == r.self.token then .refuse (sameProcessMessage r.dir)
            else .replace lockFile (contentsOf r.self) (staleWarning r.dir h)
          else match r.alive with
            | none => .probe h.pid
            | some true => .refuse (aliveMessage r.dir h)
            | some false => .replace lockFile (contentsOf r.self) (staleWarning r.dir h)

/-! ## Theorems -/

/-- No lock file: the start creates it with this process's contents. -/
theorem decide_absent (r : Request) (h : r.present = none) :
    decide r = .create lockFile (contentsOf r.self) := by
  simp [decide, h]

/-- A create only when there is no lock file. -/
theorem decide_create_absent (r : Request) (f c : String) (h : decide r = .create f c) :
    r.present = none := by
  unfold decide at h
  cases hp : r.present with
  | none => rfl
  | some text =>
      rw [hp] at h
      simp only at h
      cases hh : parseHolder text with
      | none => rw [hh] at h; simp at h
      | some k =>
          rw [hh] at h
          simp only at h
          split at h
          · simp at h
          · split at h
            · split at h <;> simp at h
            · cases ha : r.alive with
              | none => rw [ha] at h; simp at h
              | some b => cases b <;> (rw [ha] at h; simp at h)

/-- A holder on this host, another process, that the probe found alive: the
start is refused. -/
theorem decide_alive_refuses (r : Request) (text : String) (k : Holder)
    (hp : r.present = some text) (hk : parseHolder text = some k)
    (hhost : k.host = r.self.host) (hpid : k.pid ≠ r.self.pid) (ha : r.alive = some true) :
    decide r = .refuse (aliveMessage r.dir k) := by
  simp [decide, hp, hk, hhost, hpid, ha]

/-- A holder on another host: the start is refused, whatever the probe. -/
theorem decide_otherHost_refuses (r : Request) (text : String) (k : Holder)
    (hp : r.present = some text) (hk : parseHolder text = some k)
    (hhost : k.host ≠ r.self.host) :
    decide r = .refuse (otherHostMessage r.dir k r.self) := by
  simp [decide, hp, hk, hhost]

/-- A lock this process wrote (same host, process id and token): the
second open in this process is refused. -/
theorem decide_sameInstance_refuses (r : Request) (text : String) (k : Holder)
    (hp : r.present = some text) (hk : parseHolder text = some k)
    (hhost : k.host = r.self.host) (hpid : k.pid = r.self.pid)
    (htok : k.token = r.self.token) :
    decide r = .refuse (sameProcessMessage r.dir) := by
  simp [decide, hp, hk, hhost, hpid, htok]

/-- A take-over only of a lock whose holder is known not to run: on this host,
either the probe said not alive, or the holder has this process id and was
written by another process (another token). -/
theorem decide_replace_dead (r : Request) (f c w : String) (h : decide r = .replace f c w) :
    ∃ text k, r.present = some text ∧ parseHolder text = some k ∧ k.host = r.self.host ∧
      ((k.pid ≠ r.self.pid ∧ r.alive = some false) ∨
       (k.pid = r.self.pid ∧ k.token ≠ r.self.token)) := by
  unfold decide at h
  cases hp : r.present with
  | none => rw [hp] at h; simp at h
  | some text =>
      rw [hp] at h
      simp only at h
      cases hh : parseHolder text with
      | none => rw [hh] at h; simp at h
      | some k =>
          rw [hh] at h
          simp only at h
          refine ⟨text, k, rfl, hh, ?_⟩
          by_cases hhost : k.host = r.self.host
          · refine ⟨hhost, ?_⟩
            by_cases hpid : k.pid = r.self.pid
            · by_cases htok : k.token = r.self.token
              · simp [hhost, hpid, htok] at h
              · exact Or.inr ⟨hpid, htok⟩
            · cases ha : r.alive with
              | none => simp [hhost, hpid, ha] at h
              | some b =>
                  cases b
                  · exact Or.inl ⟨hpid, rfl⟩
                  · simp [hhost, hpid, ha] at h
          · simp [hhost] at h

#guard decide { dir := "/s", self := default } == .create "lws.lock" (contentsOf default)
#guard decide { dir := "/s", self := { (default : Holder) with host := "a", pid := 2, token := "x" },
                present := some (contentsOf { (default : Holder) with host := "a", pid := 1, token := "y" }) } == .probe 1

/-! ## The start notice about encryption at rest -/

/-- Where the documentation of encryption at rest is. -/
def atRestDocs : String := "https://danbri.github.io/factoidal/web/hub/servers/#encryption-at-rest"

/-- The start notice of a server that keeps a storage in `dir`: with no key,
that the storage is clear text and how to seal it; with a key, the key id. -/
def atRestNotice (dir : String) (key? : Option ByteArray) : String :=
  match key? with
  | none =>
      s!"encryption at rest is OFF: the storage in {dir} is written to disk in clear text. " ++
      s!"To seal it, make a key with `factoidal lws-keygen`, keep a copy of the key in a safe place " ++
      s!"(a lost key is lost data), and start with FACTOIDAL_LWS_KEY set to it on an empty storage " ++
      s!"directory. See {atRestDocs}"
  | some key =>
      s!"encryption at rest is ON: the storage in {dir} is sealed with ChaCha20-Poly1305 " ++
      s!"under key id {Seal.keyIdOf key}."

/-- The notice of a start: the key text as the host read it (none for no
key); a key text that is not a storage key is refused with
`Seal.parseStorageKey`'s message. -/
def noticeOf (dir : String) (keyText? : Option String) : Except String (String × Option String) :=
  match keyText? with
  | none => .ok (atRestNotice dir none, none)
  | some t => do
      let key ← Seal.parseStorageKey t
      pure (atRestNotice dir (some key), some (Seal.keyIdOf key))

/-- With no key, the notice says that the storage is clear text. -/
theorem noticeOf_none (dir : String) :
    noticeOf dir none = .ok (atRestNotice dir none, none) := rfl

/-- A new storage key from 32 random bytes of the host, as 64 hex digits, and
its key id. Fewer or more bytes are refused. -/
def newStorageKey (random : ByteArray) : Except String (String × String) :=
  if random.size == 32 then .ok (L4Factoidal.Crypto.bytesToHex random, Seal.keyIdOf random)
  else .error s!"lws-keygen: a storage key is 32 random bytes, the host gave {random.size}"

#guard (newStorageKey (ByteArray.mk (Array.replicate 32 7))).toOption.map (·.1) ==
  some "0707070707070707070707070707070707070707070707070707070707070707"
#guard (do
  let (t, _) ← (newStorageKey (ByteArray.mk (Array.replicate 32 171))).toOption
  (Seal.parseStorageKey t).toOption) == some (ByteArray.mk (Array.replicate 32 171))
#guard (newStorageKey (ByteArray.mk (Array.replicate 31 7))).toOption == none

end L4Factoidal.LWS.DirLock
