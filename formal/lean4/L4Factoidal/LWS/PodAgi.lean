/-
L4Factoidal.LWS.PodAgi — build handlers in a pod (`agi-bin/`): small
programs that build files when other files change, what they can do, and what
they cannot.

The foafos shell runs them (`packages/foafos/src/agi.mjs`, and
`handlersFor`, `approveHandler`, `_runTriggers`, `_gather` and the trigger in
`invoke` in `packages/foafos/src/pods.mjs`, branch `pod-agi`). This module is a
specification of that behaviour: it states definitions and proves theorems
about them. That the JavaScript computes what these definitions compute is not
proved here; it is a matter for differential tests (four of which were run
against the JS on 2026-11-12, see "Gaps found" below).

## The model

* **A pod** (`Pod`) is a list of (path, bytes). `get` reads a path, `set`
  writes one (it removes every old entry for the path), `remove` deletes one.
  `size` is the sum of the lengths of the bytes, `sizeAt` the bytes at one
  path (what `_sizeOf`, a HEAD, gives; 0 if there is nothing).
* **A handler** is `agi-bin/<name>.wasm` and `agi-bin/<name>.json`. The
  manifest (`Manifest`) has a kind (`file` or `folder`), a pattern `pat`
  (the compiled glob, as a Boolean function of a path), an `outputDir` and an
  `output` template. `outputPathFor` is the JS function: for a file handler
  it fills `{dir}`, `{name}` and `{path}` from the input path in that order
  (`String.replace`, as the JS `replaceAll`); for a folder handler the output
  is the fixed `output`; then the path must be clean (`cleanRel`), under
  `outputDir`, not under `agi-bin/`, and not matched by the handler's own
  pattern, or there is no output.
* **The environment** (`Env`) holds what the shell and the server give and
  nothing else: `parse` (JSON.parse with `checkManifest`), `sem` (running a
  module in a Worker: the bytes of the module, a time bound `fuel`, and the
  input give the output, or `none` for a refusal: timeout, trap, bad module,
  bad imports), `hash` (SHA-256 as hex), the limits, the pod's quota, and
  `putOk` (whether the server stores a handler's PUT). A program is a
  function of its input only, because `sem` is a function: this is how the
  model states that a handler imports nothing but its memory (no network,
  clock, randomness or pod).
* **Approval** (`Approvals`) maps a handler name to a hash. `approved`
  lists the handlers in `agi-bin/` (at most 32, in listing order) whose
  manifest parses and whose current `.wasm` hashes to the approval for the
  name: the JS `handlersFor(...).filter(h => h.approved && h.manifest)`.
* **An event** (`Event`) is an app's successful `pod.put` or `pod.delete`
  through `invoke`, with `shared` set when it came through a share. Writes by
  handlers are not events.
* **A step** (`step`) is: the app's write, with the quota check of `invoke`
  (`appWrite`); then the approved handlers whose pattern matches the written
  path, in order (`triggered`; none for a write in `agi-bin/` or through a
  share), each run once (`runOne`): a file handler is skipped on a delete;
  the input is the written bytes (file) or every file in the pod that the
  pattern matches (folder, `gather`, read from the pod as it is when that
  handler runs); the program runs; the output is checked against the quota
  and stored with a PUT. The counter `used` is moved before the PUT, as in
  the JS today (`countAfterPut = false`), or after a successful PUT (the
  proposed fix, `countAfterPut = true`).
* **The queue** (`Machine`, `machineStep`): a work list of handler runs; a
  handler's write puts `triggered … (byHandler := true)` on the list, which
  is empty. `step` is the result of running this machine until its list is
  empty.

## What is proved

Paths and pods: `get_set`, `get_remove`, `size_set`, `size_remove`,
`isAgi_wasmPath`, `isAgi_jsonPath`, `jsonPath_ne_wasmPath`.

Where a handler may write: `outputPathFor_confined` (clean, under its
`outputDir`, not in `agi-bin/`, not matched by its own pattern),
`outputPathFor_ne_input` (never the file that set it off).

Approval by bytes: `approved_mem` (a handler that runs has an approval equal
to the hash of the `.wasm` bytes now in the pod, and those are the bytes it
runs), `program_change_withdraws`, `program_change_withdraws_of_injective`
(any other bytes at `<name>.wasm` are not run on the old approval, given that
the hash tells them apart), `withdrawn_not_approved`, `approved_set_other`,
`approved_remove_other` (an app write outside `agi-bin/` changes no handler
or approval), `step_runs_approved`.

Confined writes: `runOne_changes_only_output`, `runOne_keeps_agi`,
`runOne_keeps_own_inputs`, `runs_changes_only_outputs`, `runs_keep_agi`
(no handler run changes `agi-bin/`, so no handler can rewrite or approve a
handler).

No chains and a bound: `triggered_byHandler`, `machineStep_idle`,
`machine_runs_queue` (after as many machine steps as there are queued
handlers, the list is empty and the state is `step`'s; further steps change
nothing: `machine_done`), `approved_length`, `queue_length_le` and
`step_log_le` (one app write makes at most 32 handler runs, and at most one
per approved handler).

Only what was asked: `step_only_asked` (a path changed by a step is the
app's path or the output path of a handler set off by it),
`step_keeps_agi` (in `agi-bin/`, only the app's own path can change),
`queue_after_write` (the handlers set off are the same whether read before or
after the app's write).

Determinism: `step_congr_sem` (the result depends on the programs only
through the approved ones). That the result depends on nothing but the pod,
the approvals, the event and `Env` holds by the type of `step`.

Quota: `size_set`/`size_remove`, `appWrite_inv`, `store_inv`, `runs_inv`,
`stepWith_inv`, `step_inv`: if the counter equals the pod's size and is
within the quota before a step, both hold after it, when every PUT succeeds or when the
counter is moved only after a successful PUT. This covers two handlers with
the same output path (the second measures the first's output) and an output
that replaces a file.

The proposed fix for the manifest gap: `approvedFix_mem`,
`fix_manifest_change_withdraws`, and the confinement and quota theorems hold
for it unchanged (they are stated for any list of handlers: `stepWith`).

## Gaps found (each was run against the JS, 2026-11-12)

1. **The approval does not cover the manifest.** The approval names the hash
   of the `.wasm` only, but the manifest decides what the program reads (its
   pattern) and where it writes (`outputDir`, `output`), and the shell shows
   the owner the manifest when it asks for approval ("reads …, writes …").
   A write to `agi-bin/<name>.json` changes what an approved program does
   without a new approval (`manifest_change_keeps_approval`, and the example
   `leakStep`). Run in the JS: an app with `pod:write` on the whole pod and
   `pod:read` on `public/` only rewrote `agi-bin/md2html.json` to
   `{match: "private/*.md", outputDir: "public/", output: "public/{name}.html"}`;
   the handler stayed approved; when the owner saved `private/diary.md`, the
   app read its text in `public/diary.html`. Fix (`approvedFix`): the
   approval names both hashes, the program's and the manifest's (for example
   `{wasm: sha256, manifest: sha256}`, or the hash of both), and the shell
   asks again when either changes.
2. **The quota counter moves before the PUT.** `_runTriggers` sets
   `u.used = u.used - before + r.bytes.length` and then PUTs; if the PUT fails
   (507, 409, 403, unreachable, or `_ensureContainers` throws) the counter is
   wrong. When the output would have replaced a larger file, the counter is
   now below the pod's real size, and later writes pass the check while the
   pod is over its quota (`putFailGap`). Run in the JS: a 600-byte
   `site/notes/a.html`, quota real+100, a failed PUT of the 107-byte page: the
   counter fell by 493, and an app then wrote `quota - counter` bytes and was
   allowed, ending 493 bytes over the quota. (When the output is larger than
   what it replaces, a failed PUT leaves the counter above the real size, and
   writes are refused early.) Fix: move the counter after `w.ok`
   (`countAfterPut = true`, `store_inv`).
3. **App writes and handler runs are not serialised with each other.** The
   queue serialises handler runs, but `invoke` measures `before`, PUTs, and
   moves the counter later, with awaits between; a handler run can write the
   same path in between. Each then subtracts the same old size (`raceGap`).
   Run in the JS: after `notes/a.md` set off md2html, the app wrote
   `site/notes/a.html` (600 bytes, replacing 600 bytes) on a slow PUT; the
   counter ended 493 bytes below the real size. This model's `step` is
   atomic, so it describes the fixed behaviour; fix: one per-pod queue for
   the measure, write and count of an app write and of a handler run (or
   chain app writes onto `_agiQueue`).
4. **Taking an approval out of the pod record does not stop a handler.**
   `handlersFor` caches each handler's `approved`; `approveHandler` clears the
   cache but `update(id, {agi})` does not, so a handler whose approval was
   removed runs until something in `agi-bin/` changes or the pod reconnects
   (run in the JS: `update('home', {agi: {}})`, then a write to
   `notes/b.md` still built `site/notes/b.html`). In this model `step` reads
   the approvals given to it (`withdrawn_not_approved`); the example
   `staleApprovalGap` runs the step with the cached approvals. Fix: clear
   `this.agi` in `update` when `changes.agi` is given, or compare
   `this.pods.get(pod).agi[name]` with `entry.hash` in `_runTriggers`.

## Behaviour that is allowed, stated

* **Stale outputs.** A handler's output is never an event, so a file that is
  one handler's output and matches another handler's pattern does not set
  the second one off; the second handler's output is stale until an app
  writes a file it matches (example `staleChain`). A folder handler reads the
  pod as it is when it runs, so it does read earlier outputs of the same step.
* **Two handlers, one output path.** Both run, in listing order; the last
  write wins (example `sameOutput`); the quota stays right (`step_inv`).
* **An app writes into an output folder.** Allowed; the next run of the
  handler replaces the file (example `appIntoOutput`).
* **Deletes.** A delete does not run file handlers (their output stays until
  rebuilt) and does run folder handlers (the examples on `podD`).
* **A handler's inputs.** A handler never writes a path its own pattern
  matches (`runOne_keeps_own_inputs`); another handler in the same step can.

## What is not proved, and the assumptions

* **Refinement.** That the JS computes what these definitions compute is not
  proved. In particular `globToRegExp` and `checkManifest` are not modelled
  (`pat` and `parse` are given), nor is the order of files in `_gather` (the
  model uses pod order; the JS uses the server's listing order, walked from
  the pattern's fixed folder, and stops after 400 containers, so a very
  large pod can give a folder handler part of its input).
* **The hash.** That SHA-256 tells two programs apart is an assumption
  (`program_change_withdraws_of_injective` takes it as a hypothesis).
* **Isolation.** That a module whose only import is `env.memory` cannot reach
  the network, a clock or the pod, and that the Worker is stopped at
  `timeMs`, are properties of the WebAssembly engine and the browser; the
  model takes them as given by making `sem` a function.
* **Concurrency.** `step` is atomic. In the JS, handler runs are queued and
  run after `invoke` returns, so other app writes can come between (gap 3).
  The handler list is read once per run of `_runTriggers`, from a cache.
* **Measuring.** `_measure` sums container listings and can stop early
  (`partial`); containers made by `_ensureContainers` are not counted. The
  quota theorems assume the counter starts equal to the pod's size.
* **Who may write `agi-bin/`.** Any holder of a write grant that covers it
  (prefix `''` or `agi-bin/`). The model does not model grants; gap 1 is
  about what such a writer can do with an approved program.
-/

namespace L4Factoidal.LWS.PodAgi

/-! ## Paths and pods -/

/-- Bytes. -/
abbrev Bytes := List UInt8

/-- A path in the pod, relative to its root (`notes/a.md`). -/
abbrev Path := String

/-- `p` starts with `dir` (the JS `p.startsWith(dir)`). -/
def under (dir p : String) : Bool := dir.toList.isPrefixOf p.toList

/-- The handlers' folder. -/
def agiDir : String := "agi-bin/"

/-- A path in `agi-bin/`. -/
def isAgi (p : Path) : Bool := under agiDir p

/-- `p` ends with `s`. -/
def endsIn (s p : String) : Bool := s.toList.isSuffixOf p.toList

/-- The JS `cleanRel`: not empty, not starting with `/`, and no segment that
is empty, `.` or `..`. (An empty path or a leading `/` gives an empty
segment.) -/
def cleanRel (p : String) : Bool :=
  (p.splitOn "/").all (fun s => s != "" && s != "." && s != "..")

/-- A pod: paths and their bytes. -/
abbrev Pod := List (Path × Bytes)

/-- The bytes at a path. -/
def get (pod : Pod) (p : Path) : Option Bytes :=
  (pod.find? (fun e => e.1 == p)).map (·.2)

/-- Write bytes at a path, replacing what was there. -/
def set (pod : Pod) (p : Path) (b : Bytes) : Pod :=
  (p, b) :: pod.filter (fun e => e.1 != p)

/-- Delete a path. -/
def remove (pod : Pod) (p : Path) : Pod :=
  pod.filter (fun e => e.1 != p)

/-- Bytes in the pod. -/
def size (pod : Pod) : Nat := (pod.map (·.2.length)).sum

/-- Bytes at one path (the HEAD in `_sizeOf`; 0 if there is nothing). -/
def sizeAt (pod : Pod) (p : Path) : Nat :=
  ((pod.filter (fun e => e.1 == p)).map (·.2.length)).sum

/-- Removing the entries for `p` does not change the lookup of another path.
-/
theorem find_filter_ne {pod : Pod} {p q : Path} (h : p ≠ q) :
    (pod.filter (fun e => e.1 != p)).find? (fun e => e.1 == q) = pod.find? (fun e => e.1 == q) := by
  induction pod with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨a, x⟩ := e
    by_cases ha : a = p
    · subst ha
      have : (a == q) = false := by simpa using h
      simp [this, ih]
    · by_cases hq : a = q
      · subst hq; simp [ha]
      · simp [ha, hq, ih]

/-- Reading a path after a write: the written bytes at that path, the old
bytes everywhere else. -/
theorem get_set (pod : Pod) (p q : Path) (b : Bytes) :
    get (set pod p b) q = if p = q then some b else get pod q := by
  unfold get set
  by_cases h : p = q
  · subst h; simp
  · simp [h, find_filter_ne h]

/-- Reading a path after a delete: nothing at that path, the old bytes
everywhere else. -/
theorem get_remove (pod : Pod) (p q : Path) :
    get (remove pod p) q = if p = q then none else get pod q := by
  unfold get remove
  by_cases h : p = q
  · subst h; simp
  · simp [h, find_filter_ne h]

/-- The size of a pod is the size without a path plus the bytes at it. -/
theorem size_split (pod : Pod) (p : Path) : size pod = size (remove pod p) + sizeAt pod p := by
  unfold size remove sizeAt
  induction pod with
  | nil => simp
  | cons e rest ih =>
    by_cases he : e.1 = p
    · simp [he]; omega
    · simp [he]; omega

/-- Writing `b` at `p` changes the size by `b`'s length less what was at `p`. -/
theorem size_set (pod : Pod) (p : Path) (b : Bytes) :
    size (set pod p b) + sizeAt pod p = size pod + b.length := by
  have h := size_split pod p
  have : size (set pod p b) = b.length + size (remove pod p) := by
    simp [size, set, remove]
  omega

/-- Deleting `p` takes away what was at `p`. -/
theorem size_remove (pod : Pod) (p : Path) :
    size (remove pod p) + sizeAt pod p = size pod := (size_split pod p).symm

/-- The bytes at a path are part of the pod's size. -/
theorem sizeAt_le (pod : Pod) (p : Path) : sizeAt pod p ≤ size pod := by
  have := size_split pod p; omega

/-! ## Handlers and where they write -/

/-- A file handler runs once per file; a folder handler reads every file its
pattern matches. -/
inductive Kind
  | file
  | folder
  deriving DecidableEq, Repr

/-- A checked manifest (`checkManifest`). `pat` is the compiled `match`
glob. -/
structure Manifest where
  kind : Kind
  pat : Path → Bool
  outputDir : String
  output : String

/-- The folder part of a path, with its `/` (`notes/` for `notes/a.md`). -/
def dirOf (p : Path) : String :=
  let parts := p.splitOn "/"
  if parts.length ≤ 1 then "" else String.intercalate "/" parts.dropLast ++ "/"

/-- The file part of a path. -/
def fileOf (p : Path) : String := ((p.splitOn "/").getLast?).getD ""

/-- A file name without its extension (the JS: before the last `.`, unless
that `.` is the first character). -/
def stemOf (file : String) : String :=
  let s := String.intercalate "." (file.splitOn ".").dropLast
  if s.isEmpty then file else s

/-- The output template filled from an input path, `{dir}`, then `{name}`,
then `{path}` (as the JS `replaceAll` calls). -/
def fill (m : Manifest) (input : Path) : String :=
  ((m.output.replace "{dir}" (dirOf input)).replace "{name}" (stemOf (fileOf input))).replace
    "{path}" input

/-- The output path before the checks: the filled template (file) or the
fixed path (folder). -/
def rawOutput (m : Manifest) (input : Path) : String :=
  match m.kind with
  | .file => fill m input
  | .folder => m.output

/-- The checks on an output path: clean, under the output folder, outside
`agi-bin/`, not matched by the handler's own pattern. -/
def admits (m : Manifest) (out : Path) : Bool :=
  cleanRel out && under m.outputDir out && !isAgi out && !m.pat out

/-- Where a handler writes for this input, or `none` (the JS
`outputPathFor`). -/
def outputPathFor (m : Manifest) (input : Path) : Option Path :=
  if admits m (rawOutput m input) then some (rawOutput m input) else none

/-- An output path is clean, under the handler's output folder, outside
`agi-bin/`, and not matched by the handler's own pattern. -/
theorem outputPathFor_confined {m : Manifest} {input out : Path}
    (h : outputPathFor m input = some out) :
    cleanRel out = true ∧ under m.outputDir out = true ∧ isAgi out = false ∧ m.pat out = false := by
  unfold outputPathFor at h
  by_cases ha : admits m (rawOutput m input) = true
  · simp only [ha, if_true, Option.some.injEq] at h
    subst h
    simp only [admits, Bool.and_eq_true, Bool.not_eq_true'] at ha
    exact ⟨ha.1.1.1, ha.1.1.2, ha.1.2, ha.2⟩
  · simp [ha] at h

/-- A handler never writes the file that set it off. -/
theorem outputPathFor_ne_input {m : Manifest} {input out : Path}
    (hm : m.pat input = true) (h : outputPathFor m input = some out) : out ≠ input := by
  intro he
  have := (outputPathFor_confined h).2.2.2
  rw [he, hm] at this
  cases this

/-! ## Approval -/

/-- What the shell and the server provide. -/
structure Env where
  /-- `JSON.parse` and `checkManifest` of `agi-bin/<name>.json`. -/
  parse : String → Bytes → Option Manifest
  /-- Run a module (its bytes) within a time bound on an input; `none` is a
  refusal (timeout, trap, a bad module or a bad import). -/
  sem : Bytes → Nat → Bytes → Option Bytes
  /-- The time bound (`AGI_LIMITS.timeMs`). -/
  fuel : Nat
  /-- SHA-256, as hex. -/
  hash : Bytes → String
  /-- `AGI_LIMITS.inputBytes`, `inputFiles`, `outputBytes`. -/
  maxIn : Nat
  maxFiles : Nat
  maxOut : Nat
  /-- The pod's quota, if it has one. -/
  quota : Option Nat
  /-- The server stores a handler's PUT of these bytes at this path. -/
  putOk : Path → Bytes → Bool
  /-- `false`: the counter is moved before the PUT (the JS today); `true`:
  only after a successful PUT (the proposed fix). -/
  countAfterPut : Bool

/-- The owner's approvals, from the pod record: handler name to hash. -/
abbrev Approvals := String → Option String

/-- A handler as loaded: its name, manifest and program bytes. -/
structure Handler where
  name : String
  man : Manifest
  wasm : Bytes

/-- `agi-bin/<n>.json`. -/
def jsonPath (n : String) : Path := agiDir ++ n ++ ".json"

/-- `agi-bin/<n>.wasm`. -/
def wasmPath (n : String) : Path := agiDir ++ n ++ ".wasm"

/-- The handler name of a path `agi-bin/<n>.json` with no `/` in `n`. -/
def nameOf? (p : Path) : Option String :=
  let l := p.toList
  let n := String.ofList ((l.drop 8).take (l.length - 13))
  if isAgi p && endsIn ".json" p && 13 ≤ l.length && !(n.toList.contains '/') then some n
  else none

/-- The handler names in `agi-bin/`, in listing order, at most 32. -/
def handlerNames (pod : Pod) : List String :=
  ((pod.filter (fun e => isAgi e.1)).filterMap (fun e => nameOf? e.1)).take 32

/-- Load one handler: its manifest parses and its program's hash is the
approval for its name. -/
def loadOne (env : Env) (appr : Approvals) (pod : Pod) (n : String) : Option Handler :=
  match get pod (jsonPath n), get pod (wasmPath n) with
  | some j, some w =>
    match env.parse n j with
    | some m => if appr n == some (env.hash w) then some ⟨n, m, w⟩ else none
    | none => none
  | _, _ => none

/-- The approved handlers of a pod (`handlersFor`, filtered by
`approved && manifest`). -/
def approved (env : Env) (appr : Approvals) (pod : Pod) : List Handler :=
  (handlerNames pod).filterMap (loadOne env appr pod)

/-- A path that starts with `agi-bin/` is in `agi-bin/`. -/
theorem isAgi_append (s : String) : isAgi (agiDir ++ s) = true := by
  simp [isAgi, under, String.toList_append]

/-- A handler's program is in `agi-bin/`. -/
theorem isAgi_wasmPath (n : String) : isAgi (wasmPath n) = true := by
  rw [wasmPath, String.append_assoc]; exact isAgi_append _

/-- A handler's manifest is in `agi-bin/`. -/
theorem isAgi_jsonPath (n : String) : isAgi (jsonPath n) = true := by
  rw [jsonPath, String.append_assoc]; exact isAgi_append _

/-- A handler's manifest and program are two files. -/
theorem jsonPath_ne_wasmPath (n : String) : jsonPath n ≠ wasmPath n := by
  intro h
  have := congrArg String.toList h
  simp [jsonPath, wasmPath, String.toList_append] at this

/-- A loaded handler has the name asked for, the program now in the pod, an
approval equal to that program's hash, and the manifest now in the pod. -/
theorem loadOne_some {env : Env} {appr : Approvals} {pod : Pod} {n : String} {h : Handler}
    (hl : loadOne env appr pod n = some h) :
    h.name = n ∧ get pod (wasmPath n) = some h.wasm ∧ appr n = some (env.hash h.wasm) ∧
      ∃ j, get pod (jsonPath n) = some j ∧ env.parse n j = some h.man := by
  unfold loadOne at hl
  split at hl
  · rename_i j w hj hw
    split at hl
    · rename_i m hm
      split at hl
      · rename_i ha
        cases hl
        exact ⟨rfl, hw, by simpa using ha, j, hj, hm⟩
      · cases hl
    · cases hl
  · cases hl

/-- **Approval by bytes.** A handler that runs is approved for exactly the
program now at `agi-bin/<name>.wasm`: those are the bytes it runs, and the
owner's approval for its name is their hash. Its manifest is the one now at
`agi-bin/<name>.json`. -/
theorem approved_mem {env : Env} {appr : Approvals} {pod : Pod} {h : Handler}
    (hm : h ∈ approved env appr pod) :
    h.name ∈ handlerNames pod ∧ get pod (wasmPath h.name) = some h.wasm ∧
      appr h.name = some (env.hash h.wasm) ∧
      ∃ j, get pod (jsonPath h.name) = some j ∧ env.parse h.name j = some h.man := by
  obtain ⟨n, hn, hl⟩ := List.mem_filterMap.mp hm
  have := loadOne_some hl
  obtain ⟨rfl, h2⟩ := this
  exact ⟨hn, h2⟩

/-- **A changed program is not run on the old approval.** If the approval for
`n` is the hash of `w`, and the pod now holds bytes `w'` at
`agi-bin/<n>.wasm` whose hash is different, no handler named `n` runs. -/
theorem program_change_withdraws {env : Env} {appr : Approvals} {pod : Pod} {n : String}
    {w w' : Bytes} (ha : appr n = some (env.hash w)) (hw : get pod (wasmPath n) = some w')
    (hne : env.hash w' ≠ env.hash w) : ∀ h ∈ approved env appr pod, h.name ≠ n := by
  intro h hm hn
  obtain ⟨_, hw', ha', _⟩ := approved_mem hm
  rw [hn] at hw' ha'
  rw [hw] at hw'
  cases hw'
  rw [ha] at ha'
  exact hne (Option.some.inj ha').symm

/-- The same, for a hash that tells programs apart (as SHA-256 is assumed
to): any write of other bytes to `agi-bin/<n>.wasm` withdraws the effect of
the approval. -/
theorem program_change_withdraws_of_injective {env : Env} {appr : Approvals} {pod : Pod}
    {n : String} {w w' : Bytes} (hinj : ∀ a b, env.hash a = env.hash b → a = b)
    (ha : appr n = some (env.hash w)) (hw : get pod (wasmPath n) = some w') (hne : w' ≠ w) :
    ∀ h ∈ approved env appr pod, h.name ≠ n :=
  program_change_withdraws ha hw (fun he => hne (hinj _ _ he))

/-- A handler with no approval does not run. -/
theorem withdrawn_not_approved {env : Env} {appr : Approvals} {pod : Pod} {n : String}
    (ha : appr n = none) : ∀ h ∈ approved env appr pod, h.name ≠ n := by
  intro h hm hn
  have := (approved_mem hm).2.2.1
  rw [hn, ha] at this
  cases this

/-- A write outside `agi-bin/` leaves the `agi-bin/` entries as they were, in
the same order. -/
theorem filter_agi_set {pod : Pod} {p : Path} {b : Bytes} (hp : isAgi p = false) :
    (set pod p b).filter (fun e => isAgi e.1) = pod.filter (fun e => isAgi e.1) := by
  simp only [set, List.filter_cons, hp, Bool.false_eq_true, if_false, List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases he : isAgi e.1 = true
  · have : e.1 ≠ p := by intro h; rw [h, hp] at he; cases he
    simp [he, this]
  · simp [he]

/-- A delete outside `agi-bin/` leaves the `agi-bin/` entries as they were, in
the same order. -/
theorem filter_agi_remove {pod : Pod} {p : Path} (hp : isAgi p = false) :
    (remove pod p).filter (fun e => isAgi e.1) = pod.filter (fun e => isAgi e.1) := by
  simp only [remove, List.filter_filter]
  apply List.filter_congr
  intro e _
  by_cases he : isAgi e.1 = true
  · have : e.1 ≠ p := by intro h; rw [h, hp] at he; cases he
    simp [he, this]
  · simp [he]

/-- A write outside `agi-bin/` leaves every file in `agi-bin/` as it was. -/
theorem get_set_agi {pod : Pod} {p q : Path} {b : Bytes} (hp : isAgi p = false)
    (hq : isAgi q = true) : get (set pod p b) q = get pod q := by
  rw [get_set]
  have : p ≠ q := by intro h; rw [h, hq] at hp; cases hp
  simp [this]

/-- A delete outside `agi-bin/` leaves every file in `agi-bin/` as it was. -/
theorem get_remove_agi {pod : Pod} {p q : Path} (hp : isAgi p = false)
    (hq : isAgi q = true) : get (remove pod p) q = get pod q := by
  rw [get_remove]
  have : p ≠ q := by intro h; rw [h, hq] at hp; cases hp
  simp [this]

/-- A write outside `agi-bin/` changes no handler and no approval. -/
theorem approved_set_other {env : Env} {appr : Approvals} {pod : Pod} {p : Path} {b : Bytes}
    (hp : isAgi p = false) : approved env appr (set pod p b) = approved env appr pod := by
  unfold approved handlerNames loadOne
  rw [filter_agi_set hp]
  simp only [get_set_agi hp (isAgi_jsonPath _), get_set_agi hp (isAgi_wasmPath _)]

/-- A delete outside `agi-bin/` changes no handler and no approval. -/
theorem approved_remove_other {env : Env} {appr : Approvals} {pod : Pod} {p : Path}
    (hp : isAgi p = false) : approved env appr (remove pod p) = approved env appr pod := by
  unfold approved handlerNames loadOne
  rw [filter_agi_remove hp]
  simp only [get_remove_agi hp (isAgi_jsonPath _), get_remove_agi hp (isAgi_wasmPath _)]

/-- **Gap 1: the approval does not cover the manifest.** A handler loaded
with one manifest is still loaded, with the same approval and program, after
any write of a manifest that parses to `agi-bin/<n>.json`, whatever it reads
and wherever it writes. -/
theorem manifest_change_keeps_approval {env : Env} {appr : Approvals} {pod : Pod}
    {h : Handler} {j' : Bytes} {m' : Manifest}
    (hl : loadOne env appr pod h.name = some h) (hp : env.parse h.name j' = some m') :
    loadOne env appr (set pod (jsonPath h.name) j') h.name = some ⟨h.name, m', h.wasm⟩ := by
  obtain ⟨_, hw, ha, _⟩ := loadOne_some hl
  have hw' : get (set pod (jsonPath h.name) j') (wasmPath h.name) = some h.wasm := by
    rw [get_set]; simp [jsonPath_ne_wasmPath, hw]
  unfold loadOne
  rw [hw', get_set]
  simp [hp, ha]

/-! ### The proposed fix: approve the program and the manifest -/

/-- An approval that names the hash of the program and of the manifest. -/
abbrev ApprovalsFix := String → Option (String × String)

/-- Load one handler under the fix: both hashes must match. -/
def loadOneFix (env : Env) (appr : ApprovalsFix) (pod : Pod) (n : String) : Option Handler :=
  match get pod (jsonPath n), get pod (wasmPath n) with
  | some j, some w =>
    match env.parse n j with
    | some m => if appr n == some (env.hash w, env.hash j) then some ⟨n, m, w⟩ else none
    | none => none
  | _, _ => none

/-- The approved handlers under the fix. -/
def approvedFix (env : Env) (appr : ApprovalsFix) (pod : Pod) : List Handler :=
  (handlerNames pod).filterMap (loadOneFix env appr pod)

/-- Under the fix, a handler that runs has an approval naming both its
program's bytes and its manifest's bytes, as they are in the pod now. -/
theorem approvedFix_mem {env : Env} {appr : ApprovalsFix} {pod : Pod} {h : Handler}
    (hm : h ∈ approvedFix env appr pod) :
    get pod (wasmPath h.name) = some h.wasm ∧
      ∃ j, get pod (jsonPath h.name) = some j ∧ env.parse h.name j = some h.man ∧
        appr h.name = some (env.hash h.wasm, env.hash j) := by
  obtain ⟨n, _, hl⟩ := List.mem_filterMap.mp hm
  unfold loadOneFix at hl
  split at hl
  · rename_i j w hj hw
    split at hl
    · rename_i m hpm
      split at hl
      · rename_i ha
        cases hl
        exact ⟨hw, j, hj, hpm, by simpa using ha⟩
      · cases hl
    · cases hl
  · cases hl

/-- Under the fix, a manifest whose hash differs from the approved one
withdraws the approval: no handler of that name runs. -/
theorem fix_manifest_change_withdraws {env : Env} {appr : ApprovalsFix} {pod : Pod}
    {n : String} {hw hj : String} {j' : Bytes} (ha : appr n = some (hw, hj))
    (hj' : get pod (jsonPath n) = some j') (hne : env.hash j' ≠ hj) :
    ∀ h ∈ approvedFix env appr pod, h.name ≠ n := by
  intro h hm hn
  obtain ⟨_, j, hj2, _, ha2⟩ := approvedFix_mem hm
  rw [hn] at hj2 ha2
  rw [hj'] at hj2
  cases hj2
  rw [ha] at ha2
  exact hne (Prod.mk.inj (Option.some.inj ha2)).2.symm

/-! ## Events, runs and steps -/

/-- What an app did: a write of bytes, or a delete. -/
inductive Op
  | put (b : Bytes)
  | del

/-- A delete. -/
def Op.isDel : Op → Bool
  | .del => true
  | .put _ => false

/-- An app's successful `pod.put` or `pod.delete` through `invoke`. `shared`:
it came through a share (which sets off no handler). -/
structure Event where
  path : Path
  op : Op
  shared : Bool := false

/-- What one handler run did. -/
inductive Outcome
  | wrote (out : Path)
  | refused (why : String)
  deriving DecidableEq, Repr

/-- The runs of a step, in order: handler name and outcome (`agiLog`). -/
abbrev Log := List (String × Outcome)

/-- The pod and the shell's count of its bytes (`usage.used`). -/
structure State where
  pod : Pod
  used : Nat

/-- Which handlers a write to `p` sets off (the JS `triggered`). A write made
by a handler sets off none, and so does a write in `agi-bin/`. -/
def triggered (hs : List Handler) (p : Path) (byHandler : Bool) : List Handler :=
  if byHandler || isAgi p then [] else hs.filter (fun h => h.man.pat p)

/-- The handler runs an app's event queues: none through a share. -/
def queueFor (hs : List Handler) (e : Event) : List Handler :=
  if e.shared then [] else triggered hs e.path false

/-- A little-endian u32. -/
def u32 (n : Nat) : Bytes :=
  [n.toUInt8, (n / 256).toUInt8, (n / 65536).toUInt8, (n / 16777216).toUInt8]

/-- UTF-8 bytes of a string. -/
def utf8 (s : String) : Bytes := s.toUTF8.toList

/-- A file handler's input: `path`, a 0 byte, the bytes (`frameInput`). -/
def frameFile (p : Path) (b : Bytes) : Bytes := utf8 p ++ [0] ++ b

/-- A folder handler's input: a count, then each name and its bytes, with
their lengths (`frameInput`). -/
def frameFolder (fs : List (Path × Bytes)) : Bytes :=
  u32 fs.length ++ (fs.map (fun f => u32 (utf8 f.1).length ++ utf8 f.1 ++ u32 f.2.length ++ f.2)).flatten

/-- The files a folder handler reads: those its pattern matches, as the pod is
when it runs (`_gather`). -/
def gather (h : Handler) (pod : Pod) : List (Path × Bytes) :=
  pod.filter (fun e => h.man.pat e.1)

/-- A handler's input for an event, or `none` when there is too much. -/
def inputFor (env : Env) (h : Handler) (e : Event) (pod : Pod) : Option Bytes :=
  match h.man.kind, e.op with
  | .file, .put b => some (frameFile e.path b)
  | .file, .del => none
  | .folder, _ =>
    let fs := gather h pod
    if env.maxFiles < fs.length || env.maxIn < (fs.map (·.2.length)).sum then none
    else some (frameFolder fs)

/-- The output path and bytes of a run, or why there are none. -/
def produce (env : Env) (e : Event) (pod : Pod) (h : Handler) : Except String (Path × Bytes) :=
  match outputPathFor h.man e.path with
  | none => .error "output-refused"
  | some out =>
    match inputFor env h e pod with
    | none => .error "too-large"
    | some input =>
      if env.maxIn < input.length then .error "too-large" else
      match env.sem h.wasm env.fuel input with
      | none => .error "refused"
      | some r => if env.maxOut < r.length then .error "too-large" else .ok (out, r)

/-- Store an output: the quota check, the count and the PUT, in the order of
`_runTriggers` (or, with `countAfterPut`, the count after a successful PUT).
Counts are natural numbers, so `used + r.length - before` is the JS
`Math.max(0, used - before + r.length)`; while the count equals the pod's
size the two are the same as the JS `used - before + r.length`. -/
def store (env : Env) (s : State) (out : Path) (r : Bytes) : State × Outcome :=
  match env.quota with
  | none => if env.putOk out r then (⟨set s.pod out r, s.used⟩, .wrote out) else (s, .refused "http")
  | some q =>
    let used' := s.used + r.length - sizeAt s.pod out
    if q < used' then (s, .refused "quota")
    else if env.putOk out r then (⟨set s.pod out r, used'⟩, .wrote out)
    else (if env.countAfterPut then s else ⟨s.pod, used'⟩, .refused "http")

/-- One handler run for an event. A file handler is skipped on a delete. -/
def runOne (env : Env) (e : Event) (acc : State × Log) (h : Handler) : State × Log :=
  if h.man.kind == .file && e.op.isDel then acc
  else match produce env e acc.1.pod h with
    | .error why => (acc.1, acc.2 ++ [(h.name, .refused why)])
    | .ok (out, r) =>
      let so := store env acc.1 out r
      (so.1, acc.2 ++ [(h.name, so.2)])

/-- The runs of a queue, one after the other. -/
def runs (env : Env) (e : Event) (q : List Handler) (acc : State × Log) : State × Log :=
  q.foldl (runOne env e) acc

/-- The pod after the app's write. -/
def applyOp (pod : Pod) (e : Event) : Pod :=
  match e.op with
  | .put b => set pod e.path b
  | .del => remove pod e.path

/-- The app's write through `invoke`, with its quota check: a put that would
take the count over the quota is refused (`none`). -/
def appWrite (env : Env) (s : State) (e : Event) : Option State :=
  match env.quota with
  | none => some ⟨applyOp s.pod e, s.used⟩
  | some q =>
    match e.op with
    | .put b =>
      let used' := s.used + b.length - sizeAt s.pod e.path
      if q < used' then none else some ⟨applyOp s.pod e, used'⟩
    | .del => some ⟨applyOp s.pod e, s.used - sizeAt s.pod e.path⟩

/-- A step, for a given way of loading handlers: the app's write, then the
runs it sets off. -/
def stepWith (load : Pod → List Handler) (env : Env) (s : State) (e : Event) : State × Log :=
  match appWrite env s e with
  | none => (s, [])
  | some s1 => runs env e (queueFor (load s1.pod) e) (s1, [])

/-- A step of the shell: handlers loaded as `handlersFor` loads them,
approved by the program's hash. -/
def step (env : Env) (appr : Approvals) : State → Event → State × Log :=
  stepWith (approved env appr) env

/-! ## What a run can write -/

theorem store_pod (env : Env) (s : State) (out : Path) (r : Bytes) :
    (store env s out r).1.pod = s.pod ∨ (store env s out r).1.pod = set s.pod out r := by
  unfold store
  cases env.quota with
  | none => by_cases hp : env.putOk out r <;> simp [hp]
  | some q =>
    by_cases h1 : q < s.used + r.length - sizeAt s.pod out <;>
      by_cases hp : env.putOk out r <;> by_cases hc : env.countAfterPut <;> simp [h1, hp, hc]

/-- When a run produces output, its path is the handler's output path for the
event. -/
theorem produce_out {env : Env} {e : Event} {pod : Pod} {h : Handler} {out : Path} {r : Bytes}
    (hp : produce env e pod h = .ok (out, r)) : outputPathFor h.man e.path = some out := by
  unfold produce at hp
  split at hp
  · cases hp
  · rename_i o ho
    split at hp
    · cases hp
    · split at hp
      · cases hp
      · split at hp
        · cases hp
        · split at hp
          · cases hp
          · cases hp; exact ho

/-- A run either leaves the pod as it was or writes one file, at the handler's
output path for the event. -/
theorem runOne_pod (env : Env) (e : Event) (acc : State × Log) (h : Handler) :
    (runOne env e acc h).1.pod = acc.1.pod ∨
      ∃ out r, outputPathFor h.man e.path = some out ∧
        (runOne env e acc h).1.pod = set acc.1.pod out r := by
  unfold runOne
  split
  · left; rfl
  · split
    · left; rfl
    · rename_i out r hp
      rcases store_pod env acc.1 out r with h1 | h1
      · left; exact h1
      · right; exact ⟨out, r, produce_out hp, h1⟩

/-- **A run writes only its output path.** A path whose bytes differ after a
handler run is that handler's output path for the event. -/
theorem runOne_changes_only_output {env : Env} {e : Event} {acc : State × Log} {h : Handler}
    {p : Path} (hne : get (runOne env e acc h).1.pod p ≠ get acc.1.pod p) :
    outputPathFor h.man e.path = some p := by
  rcases runOne_pod env e acc h with h1 | ⟨out, r, ho, h1⟩
  · rw [h1] at hne; exact absurd rfl hne
  · rw [h1, get_set] at hne
    by_cases hp : out = p
    · rw [← hp]; exact ho
    · simp [hp] at hne

/-- **A run never changes `agi-bin/`.** -/
theorem runOne_keeps_agi {env : Env} {e : Event} {acc : State × Log} {h : Handler} {p : Path}
    (hp : isAgi p = true) : get (runOne env e acc h).1.pod p = get acc.1.pod p := by
  apply Classical.byContradiction
  intro hne
  have := (outputPathFor_confined (runOne_changes_only_output hne)).2.2.1
  rw [hp] at this; cases this

/-- **A run never changes its own inputs**: no path that the handler's
pattern matches. -/
theorem runOne_keeps_own_inputs {env : Env} {e : Event} {acc : State × Log} {h : Handler}
    {p : Path} (hp : h.man.pat p = true) : get (runOne env e acc h).1.pod p = get acc.1.pod p := by
  apply Classical.byContradiction
  intro hne
  have := (outputPathFor_confined (runOne_changes_only_output hne)).2.2.2
  rw [hp] at this; cases this

/-- **Runs write only output paths.** After a queue of runs, a changed path
is the output path, for the event, of a handler in the queue. -/
theorem runs_changes_only_outputs {env : Env} {e : Event} :
    ∀ (q : List Handler) (acc : State × Log) (p : Path),
      get (runs env e q acc).1.pod p ≠ get acc.1.pod p →
        ∃ h ∈ q, outputPathFor h.man e.path = some p
  | [], acc, p, hne => by simp [runs] at hne
  | h :: rest, acc, p, hne => by
    simp only [runs, List.foldl_cons] at hne
    by_cases h1 : get (runOne env e acc h).1.pod p = get acc.1.pod p
    · rw [← h1] at hne
      obtain ⟨h', hm, ho⟩ := runs_changes_only_outputs rest _ p hne
      exact ⟨h', List.mem_cons_of_mem _ hm, ho⟩
    · exact ⟨h, List.mem_cons_self .., runOne_changes_only_output h1⟩

/-- **No handler run changes `agi-bin/`**, so no handler can rewrite a
handler, its manifest, or (since approvals are in the pod record, not the
pod) any approval. -/
theorem runs_keep_agi {env : Env} {e : Event} (q : List Handler) (acc : State × Log) {p : Path}
    (hp : isAgi p = true) : get (runs env e q acc).1.pod p = get acc.1.pod p := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨h, _, ho⟩ := runs_changes_only_outputs q acc p hne
  have := (outputPathFor_confined ho).2.2.1
  rw [hp] at this; cases this

/-! ## No chains, and a bound -/

/-- A handler's write sets off nothing. -/
theorem triggered_byHandler (hs : List Handler) (p : Path) : triggered hs p true = [] := by
  simp [triggered]

/-- The queue of runs, as the shell keeps it: the state, the log, the runs
still to do, and the handlers. -/
structure Machine where
  state : State
  log : Log
  queue : List Handler
  handlers : List Handler

/-- One step of the queue: run the first handler, and queue what its write
sets off (`triggered … true`, which is nothing). -/
def machineStep (env : Env) (e : Event) (m : Machine) : Machine :=
  match m.queue with
  | [] => m
  | h :: rest =>
    let r := runOne env e (m.state, m.log) h
    let next := match outputPathFor h.man e.path with
      | some out => triggered m.handlers out true
      | none => []
    { m with state := r.1, log := r.2, queue := rest ++ next }

/-- `n` applications of `f`. -/
def iterate {α : Type} (f : α → α) (n : Nat) (x : α) : α :=
  (List.replicate n ()).foldl (fun y _ => f y) x

/-- `n + 1` applications are one application and then `n`. -/
theorem iterate_succ {α : Type} (f : α → α) (n : Nat) (x : α) :
    iterate f (n + 1) x = iterate f n (f x) := by
  simp [iterate, List.replicate_succ, List.foldl_cons]

/-- An empty queue is finished: a step does nothing. -/
theorem machineStep_idle (env : Env) (e : Event) (m : Machine) (h : m.queue = []) :
    machineStep env e m = m := by
  unfold machineStep; rw [h]

/-- Once the queue is empty, no number of steps changes anything. -/
theorem machine_done (env : Env) (e : Event) (m : Machine) (h : m.queue = []) :
    ∀ n, iterate (machineStep env e) n m = m
  | 0 => rfl
  | n + 1 => by rw [iterate_succ, machineStep_idle env e m h]; exact machine_done env e m h n

/-- **Termination.** Starting from a queue of `k` runs, after `k` steps the
queue is empty and the state and log are those of running the queue in
order: no run adds to the queue. -/
theorem machine_runs_queue (env : Env) (e : Event) (hs : List Handler) :
    ∀ (q : List Handler) (st : State) (log : Log),
      iterate (machineStep env e) q.length ⟨st, log, q, hs⟩ =
        ⟨(runs env e q (st, log)).1, (runs env e q (st, log)).2, [], hs⟩
  | [], st, log => rfl
  | h :: rest, st, log => by
    rw [List.length_cons, iterate_succ]
    have hnext : (match outputPathFor h.man e.path with
        | some out => triggered hs out true
        | none => []) = [] := by
      split <;> simp [triggered]
    have : machineStep env e ⟨st, log, h :: rest, hs⟩ =
        ⟨(runOne env e (st, log) h).1, (runOne env e (st, log) h).2, rest, hs⟩ := by
      simp only [machineStep, hnext, List.append_nil]
    rw [this, machine_runs_queue env e hs rest]
    rfl

/-- A run adds at most one entry to the log. -/
theorem runOne_log (env : Env) (e : Event) (acc : State × Log) (h : Handler) :
    (runOne env e acc h).2.length ≤ acc.2.length + 1 := by
  unfold runOne
  split
  · omega
  · split <;> simp

/-- A queue of runs adds at most one log entry per queued handler. -/
theorem runs_log (env : Env) (e : Event) :
    ∀ (q : List Handler) (acc : State × Log), (runs env e q acc).2.length ≤ acc.2.length + q.length
  | [], acc => by simp [runs]
  | h :: rest, acc => by
    simp only [runs, List.foldl_cons, List.length_cons] at *
    have := runs_log env e rest (runOne env e acc h)
    have := runOne_log env e acc h
    simp only [runs] at *
    omega

/-- At most 32 handlers are loaded (`names.slice(0, 32)`). -/
theorem approved_length (env : Env) (appr : Approvals) (pod : Pod) :
    (approved env appr pod).length ≤ 32 :=
  Nat.le_trans (List.length_filterMap_le _ _) (List.length_take_le _ _)

/-- An event queues at most one run per handler. -/
theorem queue_length_le (hs : List Handler) (e : Event) : (queueFor hs e).length ≤ hs.length := by
  unfold queueFor triggered
  split
  · simp
  · split
    · simp
    · exact List.length_filter_le _ _

/-- **One app write makes at most 32 handler runs** (at most one per approved
handler), and nothing else: a step's log has at most that many entries. -/
theorem step_log_le (env : Env) (appr : Approvals) (s : State) (e : Event) :
    (step env appr s e).2.length ≤ 32 := by
  unfold step stepWith
  split
  · simp
  · rename_i s1 _
    have h1 := runs_log env e (queueFor (approved env appr s1.pod) e) (s1, [])
    have h2 := queue_length_le (approved env appr s1.pod) e
    have h3 := approved_length env appr s1.pod
    simp only [List.length_nil] at h1
    omega

/-! ## A whole step -/

theorem appWrite_pod {env : Env} {s s1 : State} {e : Event} (h : appWrite env s e = some s1) :
    s1.pod = applyOp s.pod e := by
  unfold appWrite at h
  cases hq : env.quota with
  | none => simp [hq] at h; rw [← h]
  | some q =>
    cases hop : e.op with
    | put b =>
      by_cases h1 : q < s.used + b.length - sizeAt s.pod e.path <;> simp [hq, hop, h1] at h
      rw [← h]
    | del => simp [hq, hop] at h; rw [← h]

/-- The app's write changes only the app's path. -/
theorem get_applyOp_other (pod : Pod) (e : Event) {p : Path} (hp : e.path ≠ p) :
    get (applyOp pod e) p = get pod p := by
  unfold applyOp
  split
  · rw [get_set]; simp [hp]
  · rw [get_remove]; simp [hp]

/-- The handlers an event sets off are the same whether they are read before
or after the app's write (a write in `agi-bin/` sets off none). -/
theorem queue_after_write (env : Env) (appr : Approvals) (pod : Pod) (e : Event) :
    queueFor (approved env appr (applyOp pod e)) e = queueFor (approved env appr pod) e := by
  by_cases ha : isAgi e.path = true
  · simp [queueFor, triggered, ha]
  · have ha' : isAgi e.path = false := by simpa using ha
    unfold applyOp
    split
    · rw [approved_set_other ha']
    · rw [approved_remove_other ha']

/-- **Only what was asked.** A path whose bytes a step changes is the app's
own path, or the output path, for this event, of an approved handler that
the event set off. -/
theorem step_only_asked {env : Env} {appr : Approvals} {s : State} {e : Event} {p : Path}
    (hne : get (step env appr s e).1.pod p ≠ get s.pod p) :
    p = e.path ∨ ∃ h ∈ queueFor (approved env appr s.pod) e, outputPathFor h.man e.path = some p := by
  unfold step stepWith at hne
  split at hne
  · exact absurd rfl hne
  · rename_i s1 hw
    by_cases hp : e.path = p
    · left; exact hp.symm
    · right
      have h1 : get s1.pod p = get s.pod p := by
        rw [appWrite_pod hw]; exact get_applyOp_other _ _ hp
      rw [← h1] at hne
      obtain ⟨h, hm, ho⟩ := runs_changes_only_outputs _ _ p hne
      rw [appWrite_pod hw, queue_after_write] at hm
      exact ⟨h, hm, ho⟩

/-- **A step changes `agi-bin/` only where the app wrote.** -/
theorem step_keeps_agi {env : Env} {appr : Approvals} {s : State} {e : Event} {p : Path}
    (hp : isAgi p = true) (hne : p ≠ e.path) : get (step env appr s e).1.pod p = get s.pod p := by
  apply Classical.byContradiction
  intro h
  rcases step_only_asked h with h1 | ⟨h', _, ho⟩
  · exact hne h1
  · have := (outputPathFor_confined ho).2.2.1
    rw [hp] at this; cases this

/-- **Every run is of an approved handler, set off by this app write.** A
handler in the queue is approved for its current bytes, its pattern matches
the written path, the path is outside `agi-bin/`, and the write did not come
through a share. -/
theorem step_runs_approved {env : Env} {appr : Approvals} {pod : Pod} {e : Event} {h : Handler}
    (hm : h ∈ queueFor (approved env appr pod) e) :
    h ∈ approved env appr pod ∧ h.man.pat e.path = true ∧ isAgi e.path = false ∧ e.shared = false := by
  unfold queueFor triggered at hm
  by_cases hs : e.shared = true
  · simp [hs] at hm
  · by_cases ha : isAgi e.path = true
    · simp [hs, ha] at hm
    · simp only [hs, ha, Bool.false_eq_true, if_false, Bool.or_false] at hm
      have := List.mem_filter.mp hm
      exact ⟨this.1, this.2, by simpa using ha, by simpa using hs⟩

/-! ## Determinism -/

/-- A run gives the same result under two ways of running programs that agree
on its program. -/
theorem runOne_congr_sem (env : Env) (sem' : Bytes → Nat → Bytes → Option Bytes) (e : Event)
    (acc : State × Log) (h : Handler) (hs : env.sem h.wasm = sem' h.wasm) :
    runOne env e acc h = runOne { env with sem := sem' } e acc h := by
  simp only [runOne, produce, store, inputFor, hs]

/-- Runs give the same result under two ways of running programs that agree on
every queued handler's program. -/
theorem runs_congr_sem (env : Env) (sem' : Bytes → Nat → Bytes → Option Bytes) (e : Event) :
    ∀ (q : List Handler) (acc : State × Log), (∀ h ∈ q, env.sem h.wasm = sem' h.wasm) →
      runs env e q acc = runs { env with sem := sem' } e q acc
  | [], _, _ => rfl
  | h :: rest, acc, hs => by
    simp only [runs, List.foldl_cons]
    rw [runOne_congr_sem env sem' e acc h (hs h (List.mem_cons_self ..))]
    exact runs_congr_sem env sem' e rest _ (fun h' hm => hs h' (List.mem_cons_of_mem _ hm))

/-- **Determinism.** The result of a step depends on the programs only
through the approved ones: two ways of running programs that agree on every
program whose hash is approved give the same pod, count and log. (A step
has no other inputs than the pod, the count, the approvals, the event and
`Env`: no clock, no randomness, no network.) -/
theorem step_congr_sem (env : Env) (appr : Approvals) (sem' : Bytes → Nat → Bytes → Option Bytes)
    (hs : ∀ w, (∃ n, appr n = some (env.hash w)) → env.sem w = sem' w) (s : State) (e : Event) :
    step env appr s e = step { env with sem := sem' } appr s e := by
  unfold step stepWith
  have happ : appWrite { env with sem := sem' } s e = appWrite env s e := rfl
  rw [happ]
  split
  · rfl
  · rename_i s1 _
    have hload : approved { env with sem := sem' } appr s1.pod = approved env appr s1.pod := rfl
    rw [hload]
    apply runs_congr_sem
    intro h hm
    exact hs _ ⟨h.name, (approved_mem (step_runs_approved hm).1).2.2.1⟩

/-! ## The quota -/

/-- The count is the pod's size, and within the quota. -/
def Inv (q : Nat) (s : State) : Prop := s.used = size s.pod ∧ s.used ≤ q

/-- A state whose count is its pod's size and is within the quota satisfies
`Inv`. -/
theorem inv_mk {q : Nat} {pod : Pod} {u : Nat} (h1 : u = size pod) (h2 : u ≤ q) :
    Inv q ⟨pod, u⟩ := ⟨h1, h2⟩

/-- An app's write keeps the count right and within the quota. -/
theorem appWrite_inv {env : Env} {q : Nat} {s s1 : State} {e : Event} (hq : env.quota = some q)
    (hi : Inv q s) (hw : appWrite env s e = some s1) : Inv q s1 := by
  have hle := sizeAt_le s.pod e.path
  obtain ⟨hu, hb⟩ := hi
  unfold appWrite at hw
  rw [hq] at hw
  cases hop : e.op with
  | put b =>
    have hsz := size_set s.pod e.path b
    by_cases h1 : q < s.used + b.length - sizeAt s.pod e.path <;> simp [hop, h1] at hw
    rw [← hw]
    simp only [applyOp, hop]
    exact inv_mk (by omega) (by omega)
  | del =>
    have hsz := size_remove s.pod e.path
    simp [hop] at hw
    rw [← hw]
    simp only [applyOp, hop]
    exact inv_mk (by omega) (by omega)

/-- Storing a handler's output keeps the count right and within the quota,
when the PUT succeeds or the count is moved only after a successful PUT. -/
theorem store_inv {env : Env} {q : Nat} {s : State} {out : Path} {r : Bytes}
    (hq : env.quota = some q) (hi : Inv q s)
    (hput : env.countAfterPut = true ∨ env.putOk out r = true) : Inv q (store env s out r).1 := by
  have hle := sizeAt_le s.pod out
  have hsz := size_set s.pod out r
  obtain ⟨hu, hb⟩ := hi
  unfold store
  rw [hq]
  by_cases h1 : q < s.used + r.length - sizeAt s.pod out
  · simp [h1]; exact ⟨hu, hb⟩
  · by_cases hp : env.putOk out r = true
    · simp [h1, hp]; exact inv_mk (by omega) (by omega)
    · rcases hput with hc | hp'
      · simp [h1, hp, hc]; exact ⟨hu, hb⟩
      · exact absurd hp' hp

/-- A handler run keeps the count right and within the quota, when every PUT
succeeds or the count is moved only after a successful PUT. -/
theorem runOne_inv {env : Env} {q : Nat} {e : Event} {acc : State × Log} {h : Handler}
    (hq : env.quota = some q) (hi : Inv q acc.1)
    (hput : env.countAfterPut = true ∨ ∀ p r, env.putOk p r = true) :
    Inv q (runOne env e acc h).1 := by
  unfold runOne
  split
  · exact hi
  · split
    · exact hi
    · rename_i out r _
      exact store_inv hq hi (hput.elim Or.inl (fun hp => Or.inr (hp out r)))

/-- A queue of runs keeps the count right and within the quota, under the same
condition. -/
theorem runs_inv {env : Env} {q : Nat} {e : Event} (hq : env.quota = some q)
    (hput : env.countAfterPut = true ∨ ∀ p r, env.putOk p r = true) :
    ∀ (hs : List Handler) (acc : State × Log), Inv q acc.1 → Inv q (runs env e hs acc).1
  | [], _, hi => hi
  | h :: rest, acc, hi => by
    simp only [runs, List.foldl_cons]
    exact runs_inv hq hput rest _ (runOne_inv hq hi hput)

/-- **Quota.** If the count equals the pod's size and is within the quota
before a step, both hold after it, for any handlers (including two with the
same output path, and outputs that replace files), when every PUT succeeds
or the count is moved only after a successful PUT. -/
theorem stepWith_inv {load : Pod → List Handler} {env : Env} {q : Nat} {s : State} {e : Event}
    (hq : env.quota = some q) (hi : Inv q s)
    (hput : env.countAfterPut = true ∨ ∀ p r, env.putOk p r = true) :
    Inv q (stepWith load env s e).1 := by
  unfold stepWith
  split
  · exact hi
  · rename_i s1 hw
    exact runs_inv hq hput _ _ (appWrite_inv hq hi hw)

/-- The quota theorem for the shell's step. -/
theorem step_inv {env : Env} {appr : Approvals} {q : Nat} {s : State} {e : Event}
    (hq : env.quota = some q) (hi : Inv q s)
    (hput : env.countAfterPut = true ∨ ∀ p r, env.putOk p r = true) :
    Inv q (step env appr s e).1 :=
  stepWith_inv hq hi hput

/-! ## Examples

A toy shell: a manifest is one of a few words, a program is `copy` (its
output is its input) or `one` (its output is the byte 1); anything else is
refused. The hash spells out the bytes, so it tells programs apart. -/

/-- The UTF-8 bytes of a short text. -/
def txt (s : String) : Bytes := utf8 s

/-- `notes/**/*.md` to `site/{dir}{name}.html`, as in the shell's test. -/
def mdMan : Manifest := ⟨.file, fun p => under "notes/" p && endsIn ".md" p, "site/", "site/{dir}{name}.html"⟩
/-- The same program, pointed at `private/` and writing into `public/`. -/
def leakMan : Manifest := ⟨.file, fun p => under "private/" p && endsIn ".md" p, "public/", "public/{name}.html"⟩
/-- A feed over `posts/*.md`. -/
def feedMan : Manifest := ⟨.folder, fun p => under "posts/" p && endsIn ".md" p, "site/", "site/feed.xml"⟩
/-- A handler over `site/**`. -/
def echoMan : Manifest := ⟨.file, fun p => under "site/" p, "echo/", "echo/{name}.txt"⟩
/-- A folder handler whose pattern matches everything: it has no output. -/
def greedyMan : Manifest := ⟨.folder, fun _ => true, "out/", "out/all.txt"⟩

def toyParse (_ : String) (b : Bytes) : Option Manifest :=
  if b == txt "md" then some mdMan else if b == txt "leak" then some leakMan
  else if b == txt "feed" then some feedMan else if b == txt "echo" then some echoMan
  else none

def toySem (w : Bytes) (_ : Nat) (input : Bytes) : Option Bytes :=
  if w == txt "copy" then some input else if w == txt "one" then some [1] else none

def toyHash (w : Bytes) : String := String.ofList (w.map (fun b => Char.ofNat b.toNat))

def toyEnv : Env :=
  { parse := toyParse, sem := toySem, fuel := 2000, hash := toyHash, maxIn := 1000,
    maxFiles := 200, maxOut := 1000, quota := none, putOk := fun _ _ => true,
    countAfterPut := false }

/-- `md2html` approved for the program `copy`. -/
def apprCopy : Approvals := fun n => if n == "md2html" then some (toyHash (txt "copy")) else none

def podA : Pod :=
  [("agi-bin/md2html.json", txt "md"), ("agi-bin/md2html.wasm", txt "copy"),
   ("private/diary.md", txt "code 4321")]

def putEv (p : Path) (b : Bytes) : Event := { path := p, op := .put b }
def delEv (p : Path) : Event := { path := p, op := .del }

-- Output paths: the template filled from the input; refused when not clean,
-- or in agi-bin/, or matched by the handler's own pattern.
#guard outputPathFor mdMan "notes/trip.md" == some "site/notes/trip.html"
#guard outputPathFor mdMan "notes/a/b.c.md" == some "site/notes/a/b.c.html"
#guard outputPathFor ⟨.file, fun _ => false, "site/", "site/{path}/../x"⟩ "a.md" == none
#guard outputPathFor ⟨.file, fun _ => false, "agi-bin/", "agi-bin/{name}.wasm"⟩ "a.md" == none
#guard outputPathFor ⟨.file, fun _ => false, "site/", "out/{name}"⟩ "a.md" == none
#guard outputPathFor greedyMan "x" == none
#guard handlerNames podA == ["md2html"]
#guard (approved toyEnv apprCopy podA).map (·.name) == ["md2html"]

-- An approved handler runs on a matching app write; the output is the program
-- applied to `path\0bytes`.
#guard get (step toyEnv apprCopy ⟨podA, 0⟩ (putEv "notes/a.md" (txt "# A"))).1.pod
    "site/notes/a.html" == some (frameFile "notes/a.md" (txt "# A"))
-- Not approved: nothing runs.
#guard (step toyEnv (fun _ => none) ⟨podA, 0⟩ (putEv "notes/a.md" (txt "# A"))).2 == []
-- Through a share: nothing runs.
#guard (step toyEnv apprCopy ⟨podA, 0⟩ { path := "notes/a.md", op := .put (txt "# A"), shared := true }).2 == []
-- The program changes (a write to md2html.wasm): the old approval no longer
-- matches, and the next write runs nothing.
#guard (approved toyEnv apprCopy (set podA (wasmPath "md2html") (txt "one"))) |>.isEmpty
#guard (step toyEnv apprCopy ⟨set podA (wasmPath "md2html") (txt "one"), 0⟩
    (putEv "notes/a.md" (txt "# A"))).2 == []

/-! ### Gap 1: a manifest edit re-points an approved program -/

/-- `podA` after a write of the manifest only: `md2html.json` now says
`private/*.md` to `public/{name}.html`. -/
def podLeak : Pod := set podA (jsonPath "md2html") (txt "leak")

/-- The owner saves `private/diary.md`. -/
def leakStep : State × Log :=
  step toyEnv apprCopy ⟨podLeak, 0⟩ (putEv "private/diary.md" (txt "code 4321"))

-- The approval still holds, and the diary's text is now in public/.
#guard (approved toyEnv apprCopy podLeak).map (·.name) == ["md2html"]
#guard get leakStep.1.pod "public/diary.html" == some (frameFile "private/diary.md" (txt "code 4321"))
#guard leakStep.2 == [("md2html", .wrote "public/diary.html")]

/-- Under the fix, the owner approved the program and the manifest `md`. -/
def apprFixA : ApprovalsFix := fun n =>
  if n == "md2html" then some (toyHash (txt "copy"), toyHash (txt "md")) else none

#guard (approvedFix toyEnv apprFixA podA).map (·.name) == ["md2html"]
#guard (approvedFix toyEnv apprFixA podLeak).isEmpty
#guard (stepWith (approvedFix toyEnv apprFixA) toyEnv ⟨podLeak, 0⟩
    (putEv "private/diary.md" (txt "code 4321"))).2 == []

/-! ### Gap 2: the count moves before the PUT -/

/-- `md2html` runs `one`; `site/notes/a.html` holds 50 bytes; the quota is
60; the server refuses PUTs under `site/`. -/
def podQ : Pod :=
  [("agi-bin/md2html.json", txt "md"), ("agi-bin/md2html.wasm", txt "one"),
   ("site/notes/a.html", List.replicate 50 7)]

def apprOne : Approvals := fun n => if n == "md2html" then some (toyHash (txt "one")) else none

def envQ (afterPut : Bool) : Env :=
  { toyEnv with quota := some 60, putOk := fun p _ => !under "site/" p, countAfterPut := afterPut }

#guard size podQ == 55

/-- An app writes `notes/a.md` (1 byte); the handler's 1-byte PUT fails; then
the app writes 53 bytes to `big.txt`. -/
def putFailGap (afterPut : Bool) : State :=
  let s1 := (step (envQ afterPut) apprOne ⟨podQ, 55⟩ (putEv "notes/a.md" [35])).1
  (step (envQ afterPut) apprOne s1 (putEv "big.txt" (List.replicate 53 0))).1

-- As the JS does it: after the failed PUT the count is 7 for 56 bytes, the
-- 53-byte write is allowed, and the pod holds 109 bytes against a quota of 60.
#guard (step (envQ false) apprOne ⟨podQ, 55⟩ (putEv "notes/a.md" [35])).1.used == 7
#guard size (step (envQ false) apprOne ⟨podQ, 55⟩ (putEv "notes/a.md" [35])).1.pod == 56
#guard size (putFailGap false).pod == 109
-- With the count moved after a successful PUT, the 53-byte write is refused.
#guard (putFailGap true).used == 56 && size (putFailGap true).pod == 56

/-! ### Gap 3: an app write and a handler run interleaved -/

/-- The app measured `before` in `s0`, a handler's write came in between
(`s1`), and the app's write and count land on `s1` (the JS `invoke`). -/
def appWriteMeasuredEarlier (s0 s1 : State) (p : Path) (b : Bytes) : State :=
  ⟨set s1.pod p b, s1.used + b.length - sizeAt s0.pod p⟩

def podR : Pod := [("site/notes/a.html", List.replicate 50 7)]

/-- The handler stores 1 byte at `site/notes/a.html`, then the app's 50-byte
write of the same path lands, counted against the 50 bytes it measured. -/
def raceGap : State :=
  let s0 : State := ⟨podR, 50⟩
  let s1 := (store { toyEnv with quota := some 100 } s0 "site/notes/a.html" [1]).1
  appWriteMeasuredEarlier s0 s1 "site/notes/a.html" (List.replicate 50 9)

-- The pod holds 50 bytes; the count says 1.
#guard size raceGap.pod == 50 && raceGap.used == 1

/-! ### Gap 4: a removed approval, read from a cache -/

/-- The approval was removed from the pod record (`apprNone`), but the shell
runs from the handler list it read when the approval was there (`apprCopy`). -/
def staleApprovalGap : State × Log :=
  stepWith (fun _ => approved toyEnv apprCopy podA) toyEnv ⟨podA, 0⟩ (putEv "notes/b.md" (txt "# B"))

#guard staleApprovalGap.2 == [("md2html", .wrote "site/notes/b.html")]
#guard (step toyEnv (fun _ => none) ⟨podA, 0⟩ (putEv "notes/b.md" (txt "# B"))).2 == []

/-! ### Allowed interactions -/

/-- Two handlers: `md2html` and `echo` (over `site/**`), both on `copy`. -/
def podE : Pod :=
  [("agi-bin/md2html.json", txt "md"), ("agi-bin/md2html.wasm", txt "copy"),
   ("agi-bin/echo.json", txt "echo"), ("agi-bin/echo.wasm", txt "copy")]

def apprBoth : Approvals := fun _ => some (toyHash (txt "copy"))

/-- md2html's output is in `site/`, which echo reads; outputs set off
nothing, so echo does not run and `echo/a.txt` is stale (absent). -/
def staleChain : State × Log := step toyEnv apprBoth ⟨podE, 0⟩ (putEv "notes/a.md" (txt "# A"))

#guard staleChain.2 == [("md2html", .wrote "site/notes/a.html")]
#guard get staleChain.1.pod "echo/a.txt" == none

/-- An app writes into md2html's output folder: allowed (and it sets off
echo, since it is an app write); the next save of `notes/a.md` replaces it. -/
def appIntoOutput : State × Log :=
  let s1 := (step toyEnv apprBoth ⟨podE, 0⟩ (putEv "site/notes/a.html" (txt "mine"))).1
  step toyEnv apprBoth s1 (putEv "notes/a.md" (txt "# A"))

#guard (step toyEnv apprBoth ⟨podE, 0⟩ (putEv "site/notes/a.html" (txt "mine"))).2 ==
  [("echo", .wrote "echo/a.txt")]
#guard get appIntoOutput.1.pod "site/notes/a.html" == some (frameFile "notes/a.md" (txt "# A"))

/-- Two handlers with the same output path (`md2html` on `copy` and `md2`, the
same manifest, on `one`), with a quota: both run, in listing order, the last
write wins, and the count equals the size. -/
def podS : Pod :=
  [("agi-bin/md2html.json", txt "md"), ("agi-bin/md2html.wasm", txt "copy"),
   ("agi-bin/md2.json", txt "md"), ("agi-bin/md2.wasm", txt "one")]

def apprS : Approvals := fun n =>
  if n == "md2html" then some (toyHash (txt "copy")) else if n == "md2" then some (toyHash (txt "one"))
  else none

def sameOutput : State × Log :=
  step { toyEnv with quota := some 100 } apprS ⟨podS, size podS⟩ (putEv "notes/a.md" (txt "# A"))

#guard sameOutput.2 == [("md2html", .wrote "site/notes/a.html"), ("md2", .wrote "site/notes/a.html")]
#guard get sameOutput.1.pod "site/notes/a.html" == some [1]
#guard sameOutput.1.used == size sameOutput.1.pod

/-- A feed over `posts/` and md2html: a delete runs the folder handler (the
feed is rebuilt without the post) and skips the file handler. -/
def podD : Pod :=
  [("agi-bin/feed.json", txt "feed"), ("agi-bin/feed.wasm", txt "copy"),
   ("agi-bin/md2html.json", txt "md"), ("agi-bin/md2html.wasm", txt "copy"),
   ("posts/a.md", txt "A"), ("posts/b.md", txt "B"), ("notes/x.md", txt "X")]

#guard (step toyEnv apprBoth ⟨podD, 0⟩ (delEv "posts/a.md")).2 == [("feed", .wrote "site/feed.xml")]
#guard get (step toyEnv apprBoth ⟨podD, 0⟩ (delEv "posts/a.md")).1.pod "site/feed.xml" ==
  some (frameFolder [("posts/b.md", txt "B")])
#guard (step toyEnv apprBoth ⟨podD, 0⟩ (delEv "notes/x.md")).2 == []
-- The queue machine gives the same as the fold, and then stays put.
#guard (iterate (machineStep toyEnv (putEv "notes/a.md" (txt "# A"))) 5
    ⟨⟨podE, 0⟩, [], queueFor (approved toyEnv apprBoth podE) (putEv "notes/a.md" (txt "# A")),
     approved toyEnv apprBoth podE⟩).queue.isEmpty

end L4Factoidal.LWS.PodAgi
