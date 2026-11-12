/-
L4Factoidal.LWS.PodArchives — archives as read-only folders in a pod: what a
read inside a zip or tar file may return, what it may cost, and what it can
never do.

The foafos shell lets an app read inside zip, tar and tar.gz files in a pod
(`packages/foafos/src/archive.mjs`, and `FoafPods._inArchive` in
`packages/foafos/src/pods.mjs`). A path such as `a.zip!/b.tar!/c.txt` splits
at each `!/`: the first part is a resource in the pod, each later part is a
name inside the archive before it. This module is a specification of that
view. It states the limits, the guards and the theorems that the definitions
here satisfy. That the JavaScript refines these definitions is not proved
here; that is a matter for a differential test.

## The model

* **Limits** (`Limits`, `Limits.default`): an archive is opened only if it is
  at most `archiveBytes` (8 MiB); an entry is unpacked to at most
  `entryBytes` (8 MiB) and at most `ratio` (200) times its packed size; at
  most `entries` (10000) entries are read from one archive; at most `depth`
  (3) archives are opened for one path.
* **Decompression is not modelled; it is an adversary.** An entry carries
  `Data`: for a stored entry, the bytes at its offset (`raw`, any list); for a
  deflated entry, the chunks that the decompressor emits (`chunks`, any list
  of lists, of any lengths). The theorems hold for every such value, so they
  hold for a correct decompressor, a buggy one and a hostile archive.
* **The streaming guard** (`guard`) consumes chunks in order and refuses as
  soon as the running total passes the limit. `readEntry` first refuses an
  entry whose declared size is over the per-entry limit (`limitOf`), then
  runs the guard (deflate) or takes the stored bytes (stored).
* **Archive parsing is also an adversary.** `openArc` takes any parser from
  bytes to raw entries (`RawEntry`: a name as a string, sizes, method, data).
  It refuses an archive over `archiveBytes` or with more than `entries`
  entries, and keeps only the entries whose name `safeName` accepts.
* **Names.** `safeName` refuses an empty name, a name that starts with `/`,
  contains a backslash or NUL, or has an empty, `.` or `..` segment. A
  trailing `/` marks a folder. Pod paths under a root are lists of segments;
  `resolve` applies segments the way a file system does (`..` goes up one).
* **A path** (`getParts`, `listParts`) is opened level by level: the outer
  resource is fetched from the pod (`fetch`, any function), each inner
  archive is read with `readEntry` and opened with `openArc`, and the last
  part is read (`get`) or listed as a folder (`list`).
* **The pod** (`Pod`) is a list of (path, bytes). `handle` serves `list`,
  `get`, `put` and `delete`; on a path with `!/` it serves `list` and `get`
  from the archive view and refuses `put` and `delete` with `readOnly`.
* **Tar.** A tar entry is uncompressed, so the model treats it as a stored
  entry whose packed size is its size. The shell checks only
  `size ≤ entryBytes` for tar; with `ratio ≥ 1` the model's extra ratio check
  always passes for such an entry, so the two agree.

## What is proved

Bounded output per entry: `guard_eq` and `guard_nil` (the guard returns
exactly the concatenated chunks when they fit, and refuses otherwise),
`guard_stops` (once the chunks so far pass the limit, nothing that follows
can change the refusal), `readEntry_le_entryBytes`, `readEntry_le_ratio`,
`readEntry_le_limit` (a successful read is at most
`min entryBytes (ratio × max 1 packed)` bytes, whatever the entry declared
and whatever the decompressor emitted), `readEntry_lie_refused` (an entry
that unpacks to more than its limit is refused, whatever it declared),
`readEntry_declared_refused`, `readEntry_deflate_exact` (an entry within its
limits is returned whole, not cut short).

Bounded work per path: `getParts_bounded` and `getArc_bounded` (a successful
read of a path returns at most `entryBytes` bytes, and the bytes unpacked on
the way, counted over every level, are at most
`(number of !/ marks) × entryBytes ≤ depth × entryBytes`),
`getParts_tooDeep` and `getArc_tooDeep` (a path with more than `depth` marks
is refused before the pod is read).

Names never escape: `safeName_segs` (every segment of an accepted name is
non-empty and is not `.` or `..`), `safeName_relative` (an accepted name does
not start with `/` and has no backslash or NUL), `resolve_safe` and
`name_under_root` (an accepted name, applied under any root, gives the root
followed by the name's segments, so the result is under the root).

Read-only: `handle_list_keeps`, `handle_get_keeps` (a read never changes the
pod), `handle_archive_keeps` (no request on an archive path changes the pod),
`handle_put_archive_refused`, `handle_delete_archive_refused`,
`runAll_keeps` (any sequence of reads and archive-path requests leaves the
pod as it was), `handle_put_get` (an ordinary write is still served, so the
model does not prove read-only by refusing everything),
`handle_get_archive_bounded` (a body served from an archive is at most
`entryBytes` bytes).

Listing is faithful: `listDir_file` and `listDir_folder` (every entry
directly in a folder is listed; every deeper entry makes its first folder
appear), `listDir_sound` (every listed item comes from an entry in that
folder), `openArc_good` and `listParts_sound` (every listed item comes from
an entry whose name `safeName` accepted, and the item's name is a safe
segment), `listParts_length` (at most `entries` items).

## What is not proved, and the assumptions

* **Refinement.** That `archive.mjs` and `_inArchive` compute what these
  definitions compute is not proved. In particular, that JavaScript's
  `name.split('/')`, `startsWith`, `includes('!/')` and the zip and tar
  header parsers agree with the string functions used here is assumed.
* **Decompression correctness.** No theorem says that the bytes returned are
  the bytes that were compressed. The theorems bound size and cost only.
* **The refusing chunk.** The guard refuses at the first chunk that takes the
  total past the limit. That chunk has already been produced; its size is
  set by the platform's `DecompressionStream`, not by this model. So the
  bytes held at a refusal are at most the limit plus one chunk; no bound on
  one chunk is proved.
* **CPU time** is not modelled. The bound is on bytes unpacked and returned,
  not on the time to parse headers or to inflate.
* **The gzip layer of tar.gz.** The shell inflates the whole `.tar.gz` to at
  most `4 × archiveBytes` (32 MiB) before it reads the tar. In this model
  that step is inside the adversarial parser, so the 32 MiB limit is not
  proved, and the gunzipped tar is not counted in the work bound.
* **Work on refusal.** `getParts_bounded` counts the bytes unpacked on a
  successful read. A refused read stops at the level that refused; the
  levels before it are each bounded by `readEntry_le_limit`, but no single
  theorem states the total for a refused path.
* **Fetch size.** The outer resource is limited by `archiveBytes` when it is
  opened (`openArc`). The shell also refuses early on a `Content-Length`
  over the limit; that early refusal is not modelled.
* **Order and sizes in a listing.** The shell sorts the items by name and
  gives each file its declared size. The model lists names and the folder
  flag only, without an order.
* **Zip64, encryption, other methods.** The shell refuses these; the model
  has stored and deflate only.
* **The shell's cache** of opened archives (keyed by URL and ETag) is not
  modelled. It is shell state, not pod state, and it does not change the pod.
* **Access control.** Which app may read the outer resource is decided
  before the archive view runs; `fetch` is the result of that decision. This
  module does not prove that decision correct.

No `sorry`, no `axiom`, no `partial`. Lean core only (no Mathlib).
-/

namespace L4Factoidal.LWS.PodArchives

/-! ## Limits and reasons -/

/-- The limits on one archive read. -/
structure Limits where
  /-- The largest archive that is opened, in bytes. -/
  archiveBytes : Nat
  /-- The most bytes one entry may unpack to. -/
  entryBytes : Nat
  /-- The most an entry may grow on unpacking: `ratio` times its packed size. -/
  ratio : Nat
  /-- The most entries read from one archive. -/
  entries : Nat
  /-- The most archives opened for one path. -/
  depth : Nat
  deriving Repr

/-- The shell's limits (`ARCHIVE_LIMITS` in `archive.mjs`). -/
def Limits.default : Limits :=
  { archiveBytes := 8 * 1024 * 1024, entryBytes := 8 * 1024 * 1024, ratio := 200,
    entries := 10000, depth := 3 }

/-- Why a request was refused. -/
inductive Reason
  | tooLarge | tooDeep | readOnly | notFound | badParams
  deriving DecidableEq, Repr

/-! ## The streaming guard -/

/-- Consume the decompressor's chunks in order, keeping what has come so far
in `acc`. Refuse as soon as the total passes `limit`. -/
def guard (limit : Nat) : List α → List (List α) → Except Reason (List α)
  | acc, [] => .ok acc
  | acc, c :: cs =>
    if acc.length + c.length > limit then .error .tooLarge else guard limit (acc ++ c) cs

/-- The guard, exactly: starting with at most `limit` bytes, it returns
everything (what it had, then every chunk, in order) when the total fits in
`limit`, and refuses when it does not. It never returns a cut-down result. -/
theorem guard_eq (limit : Nat) :
    ∀ (cs : List (List α)) (acc : List α), acc.length ≤ limit →
      guard limit acc cs =
        if acc.length + cs.flatten.length ≤ limit then .ok (acc ++ cs.flatten)
        else .error .tooLarge
  | [], acc, h => by simp [guard, h]
  | c :: cs, acc, h => by
      unfold guard
      by_cases hc : acc.length + c.length > limit
      · have : ¬ acc.length + (c :: cs).flatten.length ≤ limit := by
          simp only [List.flatten_cons, List.length_append]; omega
        rw [if_pos hc, if_neg this]
      · have hl : (acc ++ c).length ≤ limit := by simp only [List.length_append]; omega
        rw [if_neg hc, guard_eq limit cs (acc ++ c) hl]
        simp only [List.flatten_cons, List.length_append, List.append_assoc]
        have e : acc.length + c.length + cs.flatten.length =
            acc.length + (c.length + cs.flatten.length) := by omega
        rw [e]

/-- The guard from nothing: the chunks, joined, if they fit in `limit`;
otherwise a refusal. -/
theorem guard_nil (limit : Nat) (cs : List (List α)) :
    guard limit [] cs =
      if cs.flatten.length ≤ limit then .ok cs.flatten else .error .tooLarge := by
  rw [guard_eq limit cs [] (Nat.zero_le _)]
  simp

/-- The guard stops at the limit: once the chunks so far (`cs`) pass the
limit, the read is refused, whatever the decompressor would emit afterwards
(`rest`). -/
theorem guard_stops (limit : Nat) (cs rest : List (List α))
    (h : cs.flatten.length > limit) : guard limit [] (cs ++ rest) = .error .tooLarge := by
  rw [guard_nil]
  have : ¬ (cs ++ rest).flatten.length ≤ limit := by
    simp only [List.flatten_append, List.length_append]; omega
  rw [if_neg this]

/-! ## Entries -/

/-- How an entry is packed. A tar entry is `stored`, with packed size equal
to its size. -/
inductive Method
  | stored | deflate
  deriving DecidableEq, Repr

/-- What the archive gives for an entry, chosen by the archive (and so
possibly hostile): the stored bytes at the entry's offset, and the chunks the
decompressor emits for it. -/
structure Data (α : Type) where
  raw : List α
  chunks : List (List α)

/-- An accepted entry name: its segments, and whether it names a folder (a
trailing `/`). -/
structure Name where
  segs : List String
  dir : Bool
  deriving DecidableEq, Repr

/-- A name as a path inside the archive: segments joined by `/`, with a
trailing `/` for a folder. -/
def Name.render (n : Name) : String :=
  String.intercalate "/" n.segs ++ (if n.dir then "/" else "")

/-- An entry as the parser gives it: the name as stored in the archive, the
declared (unpacked) size, the packed size, the method and the data. -/
structure RawEntry (α : Type) where
  name : String
  declared : Nat
  packed : Nat
  method : Method
  data : Data α

/-- An entry whose name was accepted. -/
structure Entry (α : Type) where
  name : Name
  declared : Nat
  packed : Nat
  method : Method
  data : Data α

/-- The most bytes this entry may unpack to: `entryBytes`, and `ratio` times
its packed size (a packed size of 0 counts as 1, as in the shell). -/
def limitOf (L : Limits) (e : Entry α) : Nat :=
  min L.entryBytes (L.ratio * max 1 e.packed)

/-- Read one entry. Refuse it if its declared size is over the per-entry
limit. A stored entry gives its first `packed` stored bytes, refused if they
are over `entryBytes`. A deflated entry gives what the guard lets through,
with the limit `limitOf`. -/
def readEntry (L : Limits) (e : Entry α) : Except Reason (List α) :=
  if e.declared > L.entryBytes then .error .tooLarge
  else if e.declared > L.ratio * max 1 e.packed then .error .tooLarge
  else match e.method with
    | .stored =>
      if (e.data.raw.take e.packed).length > L.entryBytes then .error .tooLarge
      else .ok (e.data.raw.take e.packed)
    | .deflate => guard (limitOf L e) [] e.data.chunks

/-- Once its declared size passes both checks, a deflated entry's read is the
guard's result on its chunks. -/
private theorem readEntry_deflate {L : Limits} {e : Entry α} (hm : e.method = .deflate)
    (h1 : ¬ e.declared > L.entryBytes) (h2 : ¬ e.declared > L.ratio * max 1 e.packed) :
    readEntry L e = guard (limitOf L e) [] e.data.chunks := by
  simp [readEntry, h1, h2, hm]

/-- A successful read of one entry is at most `entryBytes` bytes, whatever
the entry declared and whatever the decompressor emitted. -/
theorem readEntry_le_entryBytes {L : Limits} {e : Entry α} {b : List α}
    (h : readEntry L e = .ok b) : b.length ≤ L.entryBytes := by
  unfold readEntry at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h
    · cases h
    · cases h; omega
  · rw [guard_nil] at h
    split at h
    · cases h; rename_i hle; exact Nat.le_trans hle (Nat.min_le_left _ _)
    · cases h

/-- A successful read of one entry is at most `ratio` times its packed size
(with a packed size of 0 counted as 1), whatever it declared and whatever the
decompressor emitted. This needs `ratio ≥ 1`, true of the shell's 200. -/
theorem readEntry_le_ratio {L : Limits} (hr : 1 ≤ L.ratio) {e : Entry α} {b : List α}
    (h : readEntry L e = .ok b) : b.length ≤ L.ratio * max 1 e.packed := by
  unfold readEntry at h
  split at h; · cases h
  split at h; · cases h
  split at h
  · split at h
    · cases h
    · cases h
      have h1 : (e.data.raw.take e.packed).length ≤ max 1 e.packed := by
        simp only [List.length_take]; omega
      exact Nat.le_trans h1 (Nat.le_mul_of_pos_left _ hr)
  · rw [guard_nil] at h
    split at h
    · cases h; rename_i hle; exact Nat.le_trans hle (Nat.min_le_right _ _)
    · cases h

/-- Bounded output per entry: a successful read is at most
`min entryBytes (ratio × max 1 packed)` bytes. -/
theorem readEntry_le_limit {L : Limits} (hr : 1 ≤ L.ratio) {e : Entry α} {b : List α}
    (h : readEntry L e = .ok b) : b.length ≤ limitOf L e :=
  Nat.le_min.mpr ⟨readEntry_le_entryBytes h, readEntry_le_ratio hr h⟩

/-- An entry that lies: a deflated entry whose decompressor emits more than
its limit is refused, whatever size it declared. -/
theorem readEntry_lie_refused {L : Limits} {e : Entry α} (hm : e.method = .deflate)
    (h : e.data.chunks.flatten.length > limitOf L e) : readEntry L e = .error .tooLarge := by
  by_cases h1 : e.declared > L.entryBytes
  · simp [readEntry, h1]
  by_cases h2 : e.declared > L.ratio * max 1 e.packed
  · simp [readEntry, h1, h2]
  rw [readEntry_deflate hm h1 h2, guard_nil, if_neg (Nat.not_le.mpr h)]

/-- An entry that declares more than its limit is refused before anything
is unpacked. -/
theorem readEntry_declared_refused {L : Limits} {e : Entry α}
    (h : e.declared > limitOf L e) : readEntry L e = .error .tooLarge := by
  unfold limitOf at h
  by_cases h1 : e.declared > L.entryBytes
  · simp [readEntry, h1]
  · have h2 : e.declared > L.ratio * max 1 e.packed := by
      rcases Nat.le_total L.entryBytes (L.ratio * max 1 e.packed) with hl | hl
      · rw [Nat.min_eq_left hl] at h; omega
      · rw [Nat.min_eq_right hl] at h; exact h
    simp [readEntry, h1, h2]

/-- No false refusal and no cut: a deflated entry within its limits, both
declared and actual, is returned whole. -/
theorem readEntry_deflate_exact {L : Limits} {e : Entry α} (hm : e.method = .deflate)
    (hd : e.declared ≤ limitOf L e) (ha : e.data.chunks.flatten.length ≤ limitOf L e) :
    readEntry L e = .ok e.data.chunks.flatten := by
  unfold limitOf at hd
  have h1 : ¬ e.declared > L.entryBytes := by
    have := Nat.min_le_left L.entryBytes (L.ratio * max 1 e.packed); omega
  have h2 : ¬ e.declared > L.ratio * max 1 e.packed := by
    have := Nat.min_le_right L.entryBytes (L.ratio * max 1 e.packed); omega
  rw [readEntry_deflate hm h1 h2, guard_nil, if_pos ha]

/-! ## Names -/

/-- A segment that is never accepted: empty, `.` or `..`. -/
def badSeg (p : String) : Bool := p == "" || p == "." || p == ".."

/-- A name refused before it is split: empty, absolute, or with a backslash
or NUL. -/
def badWhole (s : String) : Bool :=
  s.isEmpty || s.startsWith "/" || s.contains '\\' || s.contains (Char.ofNat 0)

/-- The segments of a name: split at `/`; a folder's trailing empty segment
is dropped. -/
def segsOf (s : String) : List String :=
  if s.endsWith "/" then (s.splitOn "/").dropLast else s.splitOn "/"

/-- The shell's `safeName`: `none` for a refused name, otherwise its
segments and whether it is a folder. -/
def safeName (s : String) : Option Name :=
  if badWhole s then none
  else if (segsOf s).any badSeg then none
  else some ⟨segsOf s, s.endsWith "/"⟩

/-- Every segment of an accepted name is non-empty, and is not `.` or `..`. -/
theorem safeName_segs {s : String} {n : Name} (h : safeName s = some n) :
    ∀ x ∈ n.segs, x ≠ "" ∧ x ≠ "." ∧ x ≠ ".." := by
  unfold safeName at h
  split at h; · cases h
  split at h; · cases h
  rename_i hany
  cases h
  intro x hx
  have hb : badSeg x = false := by
    cases hbx : badSeg x
    · rfl
    · exact absurd (List.any_eq_true.mpr ⟨x, hx, hbx⟩) hany
  simp [badSeg] at hb
  exact ⟨hb.1.1, hb.1.2, hb.2⟩

/-- An accepted name is relative (it does not start with `/`) and has no
backslash and no NUL. -/
theorem safeName_relative {s : String} {n : Name} (h : safeName s = some n) :
    s.startsWith "/" = false ∧ s.contains '\\' = false ∧ s.contains (Char.ofNat 0) = false := by
  unfold safeName at h
  split at h; · cases h
  rename_i hw
  simp only [badWhole, Bool.or_eq_true, not_or, Bool.not_eq_true] at hw
  exact ⟨hw.1.1.2, hw.1.2, hw.2⟩

/-- One step of path resolution under a folder: `..` goes up, `.` and an
empty segment stay, any other segment goes down. -/
def step (cur : List String) (seg : String) : List String :=
  if seg = ".." then cur.dropLast else if seg = "." ∨ seg = "" then cur else cur ++ [seg]

/-- Apply a name's segments under `root`, as a file system does. -/
def resolve (root segs : List String) : List String := segs.foldl step root

/-- Segments with no empty, `.` or `..` part resolve to the root followed by
those segments. -/
theorem resolve_safe : ∀ (segs root : List String),
    (∀ x ∈ segs, x ≠ "" ∧ x ≠ "." ∧ x ≠ "..") → resolve root segs = root ++ segs
  | [], root, _ => by simp [resolve]
  | x :: xs, root, h => by
      have hx := h x (List.mem_cons_self ..)
      have hs : step root x = root ++ [x] := by
        simp [step, hx.1, hx.2.1, hx.2.2]
      have ih := resolve_safe xs (root ++ [x]) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [resolve, List.foldl_cons, hs] at ih ⊢
      rw [ih]; simp

/-- Names never escape: an accepted name, applied under any root (the
archive's place in the pod, or a folder inside it), stays under that root. -/
theorem name_under_root {s : String} {n : Name} (h : safeName s = some n)
    (root : List String) : root <+: resolve root n.segs := by
  rw [resolve_safe n.segs root (safeName_segs h)]
  exact List.prefix_append _ _

/-! ## Opening an archive -/

/-- Keep an entry only if its name is accepted. -/
def accept1 (r : RawEntry α) : Option (Entry α) :=
  match safeName r.name with
  | none => none
  | some n => some ⟨n, r.declared, r.packed, r.method, r.data⟩

/-- An entry whose name `safeName` accepted for some stored name. -/
def Accepted (e : Entry α) : Prop := ∃ s, safeName s = some e.name

theorem accept1_accepted {r : RawEntry α} {e : Entry α} (h : accept1 r = some e) :
    Accepted e := by
  unfold accept1 at h
  split at h
  · cases h
  · rename_i n hn; cases h; exact ⟨r.name, hn⟩

/-- Open an archive with a parser (any function, possibly hostile): refuse
it if it is over `archiveBytes` or has more than `entries` entries; keep the
entries with accepted names. -/
def openArc (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (bytes : List α) : Except Reason (List (Entry α)) :=
  if bytes.length > L.archiveBytes then .error .tooLarge
  else match parse bytes with
    | .error r => .error r
    | .ok raws => if raws.length > L.entries then .error .tooLarge
      else .ok (raws.filterMap accept1)

/-- What an opened archive holds: only entries with accepted names, and at
most `entries` of them. -/
def Good (L : Limits) (es : List (Entry α)) : Prop :=
  (∀ e ∈ es, Accepted e) ∧ es.length ≤ L.entries

/-- An opened archive holds only entries with accepted names, at most
`entries` of them, whatever the parser did. -/
theorem openArc_good {L : Limits} {parse : List α → Except Reason (List (RawEntry α))}
    {bytes : List α} {es : List (Entry α)} (h : openArc L parse bytes = .ok es) : Good L es := by
  unfold openArc at h
  split at h; · cases h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rename_i raws _ hn
      refine ⟨fun e he => ?_, ?_⟩
      · obtain ⟨r, _, hr⟩ := List.mem_filterMap.mp he
        exact accept1_accepted hr
      · exact Nat.le_trans (List.length_filterMap_le _ _) (by omega)

/-! ## Paths through nested archives -/

/-- The file entry with this name, if there is one. -/
def lookup (es : List (Entry α)) (n : String) : Option (Entry α) :=
  es.find? (fun e => e.name.render == n && !e.name.dir)

/-- Go down through nested archives, one name per level. Returns the entries
of the last archive opened, and the bytes unpacked on the way. -/
def descend (L : Limits) (parse : List α → Except Reason (List (RawEntry α))) :
    List (Entry α) → List String → Except Reason (List (Entry α) × Nat)
  | es, [] => .ok (es, 0)
  | es, n :: ns =>
    match lookup es n with
    | none => .error .notFound
    | some e =>
      match readEntry L e with
      | .error r => .error r
      | .ok b =>
        match openArc L parse b with
        | .error r => .error r
        | .ok es' =>
          match descend L parse es' ns with
          | .error r => .error r
          | .ok (es'', w) => .ok (es'', b.length + w)

/-- Going down `ns` levels unpacks at most `ns.length × entryBytes` bytes. -/
theorem descend_work {L : Limits} {parse : List α → Except Reason (List (RawEntry α))} :
    ∀ (ns : List String) (es es' : List (Entry α)) (w : Nat),
      descend L parse es ns = .ok (es', w) → w ≤ ns.length * L.entryBytes
  | [], es, es', w, h => by simp [descend] at h; omega
  | n :: ns, es, es', w, h => by
      unfold descend at h
      split at h; · cases h
      split at h; · cases h
      rename_i b hb
      split at h; · cases h
      split at h; · cases h
      rename_i es'' w' hd
      cases h
      have h1 := readEntry_le_entryBytes hb
      have h2 := descend_work ns _ _ _ hd
      simp only [List.length_cons, Nat.succ_mul]
      omega

/-- The entries `descend` ends at are either the ones it started from (no
levels) or an opened archive's. -/
theorem descend_out {L : Limits} {parse : List α → Except Reason (List (RawEntry α))} :
    ∀ (ns : List String) (es es' : List (Entry α)) (w : Nat),
      descend L parse es ns = .ok (es', w) → es' = es ∨ ∃ b, openArc L parse b = .ok es'
  | [], es, es', w, h => by simp [descend] at h; exact Or.inl h.1.symm
  | n :: ns, es, es', w, h => by
      unfold descend at h
      split at h; · cases h
      split at h; · cases h
      split at h; · cases h
      rename_i b _ _ es₁ ho
      split at h; · cases h
      rename_i es'' w' hd
      cases h
      rcases descend_out ns _ _ _ hd with he | hb
      · subst he; exact Or.inr ⟨b, ho⟩
      · exact Or.inr hb

/-- Read the file at a path already split at `!/`: the outer resource, then
one name per nested archive, then the file. Returns the file's bytes and the
bytes unpacked in all, including the file. -/
def getParts (L : Limits) (fetch : String → Option (List α))
    (parse : List α → Except Reason (List (RawEntry α))) :
    List String → Except Reason (List α × Nat)
  | [] => .error .badParams
  | [_] => .error .badParams
  | outer :: r :: rs =>
    if rs.length + 1 > L.depth then .error .tooDeep
    else match fetch outer with
      | none => .error .notFound
      | some bytes =>
        match openArc L parse bytes with
        | .error x => .error x
        | .ok es =>
          match descend L parse es (r :: rs).dropLast with
          | .error x => .error x
          | .ok (es', w) =>
            match lookup es' ((r :: rs).getLast (List.cons_ne_nil _ _)) with
            | none => .error .notFound
            | some e =>
              match readEntry L e with
              | .error x => .error x
              | .ok b => .ok (b, w + b.length)

/-- `pod.get` on a path with `!/`. -/
def getArc (L : Limits) (fetch : String → Option (List α))
    (parse : List α → Except Reason (List (RawEntry α))) (path : String) :
    Except Reason (List α × Nat) :=
  getParts L fetch parse (path.splitOn "!/")

/-- A path with more than `depth` archive marks is refused before the pod is
read. -/
theorem getParts_tooDeep {L : Limits} {fetch : String → Option (List α)}
    {parse : List α → Except Reason (List (RawEntry α))} {parts : List String}
    (h : parts.length - 1 > L.depth) : getParts L fetch parse parts = .error .tooDeep := by
  match parts, h with
  | [], h => simp at h
  | [_], h => simp at h
  | outer :: r :: rs, h =>
    simp only [List.length_cons] at h
    simp only [getParts]
    rw [if_pos (by omega)]

/-- Bounded work per path: a successful read returns at most `entryBytes`
bytes, and unpacks at most (number of `!/` marks) × `entryBytes` bytes in all,
which is at most `depth × entryBytes`. -/
theorem getParts_bounded {L : Limits} {fetch : String → Option (List α)}
    {parse : List α → Except Reason (List (RawEntry α))} {parts : List String}
    {b : List α} {w : Nat} (h : getParts L fetch parse parts = .ok (b, w)) :
    b.length ≤ L.entryBytes ∧ w ≤ (parts.length - 1) * L.entryBytes ∧
      w ≤ L.depth * L.entryBytes := by
  match parts, h with
  | [], h => simp [getParts] at h
  | [_], h => simp [getParts] at h
  | outer :: r :: rs, h =>
    simp only [getParts] at h
    split at h; · cases h
    rename_i hd
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i es' w' hdes
    split at h; · cases h
    split at h; · cases h
    rename_i b' hb
    cases h
    have h1 := readEntry_le_entryBytes hb
    have h2 := descend_work _ _ _ _ hdes
    have hl : (r :: rs).dropLast.length = rs.length := by simp
    rw [hl] at h2
    have h3 : w' + b.length ≤ (rs.length + 1) * L.entryBytes := by
      rw [Nat.succ_mul]; omega
    have h4 : (rs.length + 1) * L.entryBytes ≤ L.depth * L.entryBytes :=
      Nat.mul_le_mul_right _ (by omega)
    refine ⟨h1, ?_, Nat.le_trans h3 h4⟩
    simpa using h3

/-- `getArc` refuses a path with more than `depth` marks. -/
theorem getArc_tooDeep {L : Limits} {fetch : String → Option (List α)}
    {parse : List α → Except Reason (List (RawEntry α))} {path : String}
    (h : (path.splitOn "!/").length - 1 > L.depth) :
    getArc L fetch parse path = .error .tooDeep :=
  getParts_tooDeep h

/-- `getArc`: a successful read returns at most `entryBytes` bytes and
unpacks at most `depth × entryBytes` bytes in all. -/
theorem getArc_bounded {L : Limits} {fetch : String → Option (List α)}
    {parse : List α → Except Reason (List (RawEntry α))} {path : String}
    {b : List α} {w : Nat} (h : getArc L fetch parse path = .ok (b, w)) :
    b.length ≤ L.entryBytes ∧ w ≤ L.depth * L.entryBytes :=
  let k := getParts_bounded h
  ⟨k.1, k.2.2⟩

/-! ## Listing a folder in an archive -/

/-- One item of a listing: a name directly in the folder, and whether it is
a folder. -/
structure Item where
  name : String
  dir : Bool
  deriving DecidableEq, Repr

/-- What an entry shows in the folder `dir`: nothing if it is not under it
(or is the folder itself); itself if it is directly in it; otherwise the
folder it is in, one level down. -/
def itemOf (dir : List String) (e : Entry α) : Option Item :=
  if e.name.segs.take dir.length = dir then
    match e.name.segs.drop dir.length with
    | [] => none
    | [x] => some ⟨x, e.name.dir⟩
    | x :: _ :: _ => some ⟨x, true⟩
  else none

/-- Remove repeats. -/
def dedup [DecidableEq β] : List β → List β
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup [DecidableEq β] {x : β} : ∀ {l : List β}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: ys => by
      unfold dedup
      split
      · rename_i hy
        rw [mem_dedup, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | h)
          · exact mem_dedup.mp hy
          · exact h
      · rw [List.mem_cons, List.mem_cons, mem_dedup]

theorem length_dedup_le [DecidableEq β] : ∀ (l : List β), (dedup l).length ≤ l.length
  | [] => by simp [dedup]
  | y :: ys => by
      unfold dedup
      have := length_dedup_le ys
      split <;> simp <;> omega

/-- The listing of folder `dir` in an archive's entries, without repeats. -/
def listDir (es : List (Entry α)) (dir : List String) : List Item :=
  dedup (es.filterMap (itemOf dir))

/-- Every entry directly in a folder is listed, as a file or a folder as the
entry says. -/
theorem listDir_file {es : List (Entry α)} {dir : List String} {e : Entry α} {x : String}
    (he : e ∈ es) (hs : e.name.segs = dir ++ [x]) : ⟨x, e.name.dir⟩ ∈ listDir es dir := by
  unfold listDir
  rw [mem_dedup, List.mem_filterMap]
  refine ⟨e, he, ?_⟩
  simp [itemOf, hs]

/-- Every entry deeper under a folder makes its first folder appear in the
listing (an implied folder), even when the archive has no entry for that
folder. -/
theorem listDir_folder {es : List (Entry α)} {dir : List String} {e : Entry α}
    {x y : String} {r : List String}
    (he : e ∈ es) (hs : e.name.segs = dir ++ x :: y :: r) : ⟨x, true⟩ ∈ listDir es dir := by
  unfold listDir
  rw [mem_dedup, List.mem_filterMap]
  refine ⟨e, he, ?_⟩
  simp [itemOf, hs]

/-- Every listed item comes from an entry under the folder: the item's name
is the entry's next segment after the folder. If the entry is directly in
the folder, the item is a folder exactly when the entry is; if it is deeper,
the item is a folder. -/
theorem listDir_sound {es : List (Entry α)} {dir : List String} {it : Item}
    (h : it ∈ listDir es dir) :
    ∃ e ∈ es, ∃ r, e.name.segs = dir ++ it.name :: r ∧
      ((r = [] ∧ it.dir = e.name.dir) ∨ (r ≠ [] ∧ it.dir = true)) := by
  unfold listDir at h
  rw [mem_dedup, List.mem_filterMap] at h
  obtain ⟨e, he, hi⟩ := h
  refine ⟨e, he, ?_⟩
  unfold itemOf at hi
  split at hi
  · rename_i ht
    have hsplit : e.name.segs = dir ++ e.name.segs.drop dir.length := by
      conv => lhs; rw [← List.take_append_drop dir.length e.name.segs]
      rw [ht]
    split at hi
    · cases hi
    · rename_i x hx; cases hi
      exact ⟨[], by rw [hsplit, hx], Or.inl ⟨rfl, rfl⟩⟩
    · rename_i x y r hx; cases hi
      exact ⟨y :: r, by rw [hsplit, hx], Or.inr ⟨List.cons_ne_nil _ _, rfl⟩⟩
  · cases hi

/-- The folder named by the last part of a list path: `""` is the archive's
top; otherwise the part must end with `/`. -/
def dirSegs (s : String) : Option (List String) :=
  if s = "" then some [] else if s.endsWith "/" then some (s.splitOn "/").dropLast else none

/-- List the folder at a path already split at `!/`. -/
def listParts (L : Limits) (fetch : String → Option (List α))
    (parse : List α → Except Reason (List (RawEntry α))) :
    List String → Except Reason (List Item)
  | [] => .error .badParams
  | [_] => .error .badParams
  | outer :: r :: rs =>
    if rs.length + 1 > L.depth then .error .tooDeep
    else match fetch outer with
      | none => .error .notFound
      | some bytes =>
        match openArc L parse bytes with
        | .error x => .error x
        | .ok es =>
          match descend L parse es (r :: rs).dropLast with
          | .error x => .error x
          | .ok (es', _) =>
            match dirSegs ((r :: rs).getLast (List.cons_ne_nil _ _)) with
            | none => .error .badParams
            | some d => .ok (listDir es' d)

/-- `pod.list` on a path with `!/`. -/
def listArc (L : Limits) (fetch : String → Option (List α))
    (parse : List α → Except Reason (List (RawEntry α))) (path : String) :
    Except Reason (List Item) :=
  listParts L fetch parse (path.splitOn "!/")

/-- The entries a list or get reaches are those of an opened archive, so
they are `Good`. -/
private theorem reached_good {L : Limits} {parse : List α → Except Reason (List (RawEntry α))}
    {bytes : List α} {es es' : List (Entry α)} {ns : List String} {w : Nat}
    (ho : openArc L parse bytes = .ok es) (hd : descend L parse es ns = .ok (es', w)) :
    Good L es' := by
  rcases descend_out ns es es' w hd with he | ⟨b, hb⟩
  · subst he; exact openArc_good ho
  · exact openArc_good hb

/-- A successful listing, end to end: every listed item comes from an
entry whose name `safeName` accepted, lying under the folder asked for, and
the item's name is a safe segment (not empty, `.` or `..`). -/
theorem listParts_sound {L : Limits} {fetch : String → Option (List α)}
    {parse : List α → Except Reason (List (RawEntry α))} {parts : List String}
    {items : List Item} (h : listParts L fetch parse parts = .ok items) :
    ∀ it ∈ items, ∃ e : Entry α, Accepted e ∧ ∃ d r, e.name.segs = d ++ it.name :: r ∧
      it.name ≠ "" ∧ it.name ≠ "." ∧ it.name ≠ ".." := by
  match parts, h with
  | [], h => simp [listParts] at h
  | [_], h => simp [listParts] at h
  | outer :: r :: rs, h =>
    simp only [listParts] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i es ho
    split at h; · cases h
    rename_i es' w hdes
    split at h; · cases h
    rename_i d _
    cases h
    intro it hit
    obtain ⟨e, he, r', hs, _⟩ := listDir_sound hit
    have hg := (reached_good ho hdes).1 e he
    obtain ⟨s, hsn⟩ := hg
    have hsafe := safeName_segs hsn it.name (by rw [hs]; simp)
    exact ⟨e, ⟨s, hsn⟩, d, r', hs, hsafe⟩

/-- A listing has at most `entries` items. -/
theorem listParts_length {L : Limits} {fetch : String → Option (List α)}
    {parse : List α → Except Reason (List (RawEntry α))} {parts : List String}
    {items : List Item} (h : listParts L fetch parse parts = .ok items) :
    items.length ≤ L.entries := by
  match parts, h with
  | [], h => simp [listParts] at h
  | [_], h => simp [listParts] at h
  | outer :: r :: rs, h =>
    simp only [listParts] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i es ho
    split at h; · cases h
    rename_i es' w hdes
    split at h; · cases h
    rename_i d _
    cases h
    have hg := (reached_good ho hdes).2
    exact Nat.le_trans (length_dedup_le _)
      (Nat.le_trans (List.length_filterMap_le _ _) hg)

/-! ## The pod, and read-only -/

/-- A pod: resources by path, with their bytes. -/
abbrev Pod (α : Type) := List (String × List α)

/-- The bytes at a path in the pod, if any. -/
def podFetch (pod : Pod α) (p : String) : Option (List α) :=
  (pod.find? (fun r => r.1 == p)).map (·.2)

/-- A request from an app. -/
inductive Req (α : Type)
  | list (p : String)
  | get (p : String)
  | put (p : String) (body : List α)
  | delete (p : String)

/-- The path a request is about. -/
def Req.path : Req α → String
  | .list p | .get p | .put p _ | .delete p => p

/-- Does the request only read? -/
def Req.isRead : Req α → Bool
  | .list _ | .get _ => true
  | _ => false

/-- A response. -/
inductive Resp (α : Type)
  | done
  | body (b : List α)
  | items (l : List Item)
  | paths (l : List String)
  | refused (r : Reason)
  deriving DecidableEq

/-- Is this a path inside an archive (it has a `!/` mark)? -/
def inArchive (p : String) : Bool := decide (1 < (p.splitOn "!/").length)

/-- Serve one request. A path inside an archive is served by the archive
view for `list` and `get`, and refused `readOnly` for `put` and `delete`.
Other paths are the pod's own. -/
def handle (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (req : Req α) (pod : Pod α) : Resp α × Pod α :=
  match req with
  | .list p =>
    if inArchive p then
      (match listArc L (podFetch pod) parse p with
        | .ok l => .items l
        | .error r => .refused r, pod)
    else (.paths ((pod.map (·.1)).filter (·.startsWith p)), pod)
  | .get p =>
    if inArchive p then
      (match getArc L (podFetch pod) parse p with
        | .ok (b, _) => .body b
        | .error r => .refused r, pod)
    else
      (match podFetch pod p with
        | some b => .body b
        | none => .refused .notFound, pod)
  | .put p b =>
    if inArchive p then (.refused .readOnly, pod)
    else (.done, (p, b) :: pod.filter (fun r => r.1 != p))
  | .delete p =>
    if inArchive p then (.refused .readOnly, pod)
    else (.done, pod.filter (fun r => r.1 != p))

/-- A `list` never changes the pod. -/
theorem handle_list_keeps (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (p : String) (pod : Pod α) : (handle L parse (.list p) pod).2 = pod := by
  simp only [handle]; split <;> rfl

/-- A `get` never changes the pod. -/
theorem handle_get_keeps (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (p : String) (pod : Pod α) : (handle L parse (.get p) pod).2 = pod := by
  simp only [handle]; split <;> rfl

/-- No request on a path inside an archive changes the pod: not a read, and
not a `put` or `delete`. -/
theorem handle_archive_keeps (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (req : Req α) (pod : Pod α) (h : inArchive req.path = true) :
    (handle L parse req pod).2 = pod := by
  cases req with
  | list p => exact handle_list_keeps L parse p pod
  | get p => exact handle_get_keeps L parse p pod
  | put p b => simp only [Req.path] at h; simp [handle, h]
  | delete p => simp only [Req.path] at h; simp [handle, h]

/-- A `put` to a path inside an archive is refused `readOnly`. -/
theorem handle_put_archive_refused (L : Limits)
    (parse : List α → Except Reason (List (RawEntry α))) (p : String) (b : List α)
    (pod : Pod α) (h : inArchive p = true) :
    handle L parse (.put p b) pod = (.refused .readOnly, pod) := by
  simp [handle, h]

/-- A `delete` of a path inside an archive is refused `readOnly`. -/
theorem handle_delete_archive_refused (L : Limits)
    (parse : List α → Except Reason (List (RawEntry α))) (p : String) (pod : Pod α)
    (h : inArchive p = true) :
    handle L parse (.delete p) pod = (.refused .readOnly, pod) := by
  simp [handle, h]

/-- The model is not read-only by refusing everything: a `put` to an
ordinary path is served, and a `get` after it returns what was written. -/
theorem handle_put_get (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (p : String) (b : List α) (pod : Pod α) (h : inArchive p = false) :
    (handle L parse (.get p) (handle L parse (.put p b) pod).2).1 = .body b := by
  simp [handle, h, podFetch]

/-- A body served from inside an archive is at most `entryBytes` bytes. -/
theorem handle_get_archive_bounded (L : Limits)
    (parse : List α → Except Reason (List (RawEntry α))) (p : String) (pod : Pod α)
    (b : List α) (h : (handle L parse (.get p) pod).1 = .body b) (ha : inArchive p = true) :
    b.length ≤ L.entryBytes := by
  simp only [handle, ha, if_true] at h
  split at h
  · rename_i b' w hg
    cases h
    exact (getArc_bounded hg).1
  · cases h

/-- Serve requests in order; the pod after all of them. -/
def runAll (L : Limits) (parse : List α → Except Reason (List (RawEntry α)))
    (reqs : List (Req α)) (pod : Pod α) : Pod α :=
  reqs.foldl (fun q r => (handle L parse r q).2) pod

/-- Read-only, over any history: a sequence of requests each of which is a
read, or is on a path inside an archive, leaves the pod as it was. -/
theorem runAll_keeps (L : Limits) (parse : List α → Except Reason (List (RawEntry α))) :
    ∀ (reqs : List (Req α)) (pod : Pod α),
      (∀ r ∈ reqs, r.isRead = true ∨ inArchive r.path = true) → runAll L parse reqs pod = pod
  | [], pod, _ => rfl
  | r :: rs, pod, h => by
      have hr : (handle L parse r pod).2 = pod := by
        rcases h r (List.mem_cons_self ..) with hr | hr
        · cases r with
          | list p => exact handle_list_keeps L parse p pod
          | get p => exact handle_get_keeps L parse p pod
          | put p b => simp [Req.isRead] at hr
          | delete p => simp [Req.isRead] at hr
        · exact handle_archive_keeps L parse r pod hr
      simp only [runAll, List.foldl_cons, hr]
      exact runAll_keeps L parse rs pod (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-! ## Examples -/

private def L₀ : Limits := Limits.default

-- The shell's limits satisfy `ratio ≥ 1`, which `readEntry_le_ratio` needs.
example : 1 ≤ Limits.default.ratio := by decide

/-- A 1 KiB deflated entry that declares 10 bytes. -/
private def lying (chunks : List (List Unit)) : Entry Unit :=
  { name := ⟨["bomb.txt"], false⟩, declared := 10, packed := 1024, method := .deflate,
    data := { raw := [], chunks := chunks } }

-- Its limit is min(8 MiB, 200 × 1 KiB) = 204800 bytes.
#guard limitOf L₀ (lying []) == 204800
-- It unpacks to 1 MiB (16 chunks of 64 KiB): refused, though it declared 10 bytes.
#guard readEntry L₀ (lying (List.replicate 16 (List.replicate 65536 ()))) matches
  .error .tooLarge
-- The same entry unpacking to 10 KiB is returned whole.
#guard (match readEntry L₀ (lying (List.replicate 10 (List.replicate 1024 ()))) with
  | .ok b => b.length == 10240 | .error _ => false)
-- An entry that declares 1 MiB from 1 KiB packed is refused before unpacking.
#guard readEntry L₀ { lying [] with declared := 1024 * 1024 } matches .error .tooLarge

-- Names.
#guard safeName "../evil" == none
#guard safeName "a/../../evil" == none
#guard safeName "/etc/passwd" == none
#guard safeName "a\\b" == none
#guard safeName "a/./b" == none
#guard safeName "a//b" == none
#guard safeName "" == none
#guard safeName "a\x00b" == none
#guard safeName "docs/2024/beach.jpg" == some ⟨["docs", "2024", "beach.jpg"], false⟩
#guard safeName "docs/2024/" == some ⟨["docs", "2024"], true⟩
-- Why `..` is refused: applied under a root, it climbs out of it.
#guard resolve ["home", "a.zip"] ["..", "..", "etc"] == ["etc"]
#guard resolve ["home", "a.zip"] ["docs", "x"] == ["home", "a.zip", "docs", "x"]

/-- A toy archive format over `Nat`: archive `[0]` holds `b.tar` (stored,
the bytes `[1]`), `x/y/z.txt`, `top.txt` and `../evil`; archive `[1]` holds
`c.txt` (the bytes `[7, 7, 7]`). -/
private def toyParse : List Nat → Except Reason (List (RawEntry Nat))
  | [0] =>
    .ok [ ⟨"b.tar", 1, 1, .stored, ⟨[1], []⟩⟩,
          ⟨"x/y/z.txt", 2, 2, .stored, ⟨[5, 5], []⟩⟩,
          ⟨"top.txt", 1, 1, .stored, ⟨[6], []⟩⟩,
          ⟨"../evil", 1, 1, .stored, ⟨[9], []⟩⟩ ]
  | [1] => .ok [⟨"c.txt", 3, 3, .stored, ⟨[7, 7, 7], []⟩⟩]
  | _ => .error .badParams

private def toyPod : Pod Nat := [("a.zip", [0]), ("notes.txt", [3])]

-- A nested read: 3 bytes returned, 4 unpacked (1 for b.tar, 3 for c.txt).
#guard (match getArc L₀ (podFetch toyPod) toyParse "a.zip!/b.tar!/c.txt" with
  | .ok (b, w) => b == [7, 7, 7] && w == 4 | .error _ => false)
-- A name that climbs out is not in the archive view.
#guard getArc L₀ (podFetch toyPod) toyParse "a.zip!/../evil" matches .error .notFound
-- Depth 4 is refused, before the pod is read.
#guard getArc L₀ (fun _ => none) toyParse "a.zip!/b.zip!/c.zip!/d.zip!/e.txt" matches
  .error .tooDeep
-- The top of a.zip lists b.tar, the implied folder x, and top.txt; not ../evil.
#guard (match listArc L₀ (podFetch toyPod) toyParse "a.zip!/" with
  | .ok l => l.length == 3 && (⟨"x", true⟩ : Item) ∈ l && (⟨"top.txt", false⟩ : Item) ∈ l
      && (⟨"b.tar", false⟩ : Item) ∈ l
  | .error _ => false)
-- Writes inside an archive are refused and the pod is unchanged.
#guard handle L₀ toyParse (.put "a.zip!/top.txt" [1]) toyPod == (.refused .readOnly, toyPod)
#guard handle L₀ toyParse (.delete "a.zip!/top.txt") toyPod == (.refused .readOnly, toyPod)
#guard (handle L₀ toyParse (.get "a.zip!/top.txt") toyPod).1 == .body [6]
-- An ordinary write still works.
#guard (handle L₀ toyParse (.put "notes.txt" [4]) toyPod).2 == [("notes.txt", [4]), ("a.zip", [0])]

end L4Factoidal.LWS.PodArchives
