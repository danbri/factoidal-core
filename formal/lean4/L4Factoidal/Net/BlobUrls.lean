/-
L4Factoidal.Net.BlobUrls — blob URLs (File API §8.3, https://w3c.github.io/FileAPI/#url):
`URL.createObjectURL(blob)` and `URL.revokeObjectURL(url)`, and the entry a request for a
`blob:` URL reads (`Net.PageFetch.blobStep`). `web_api` ops 90 and 91.

## Decisions

* A blob URL belongs to the origin that made it. Only a request of that origin resolves it
  (`resolve_origin`), and only that origin revokes it (`revoke_other`): what one origin
  stores under a blob URL is never read through the URL by another (File API §8.3.2
  "resolve a blob URL" with the origin check of Fetch's scheme fetch).
* The URL is `blob:`, the serialized origin, `/`, and a UUID the engine draws
  (`WebApi.randomBytes`): a page cannot choose or guess another page's.
* In memory, for the session: at most `maxEntries` URLs and `maxHeld` bytes
  (`add_bounds`); past them `createObjectURL` is refused. Nothing is written to disk.
-/

namespace L4Factoidal.Net.BlobUrls

/-- One blob URL: the URL, the origin that made it, and the blob's type and bytes. -/
structure Entry where
  url : String
  origin : String
  type : String
  body : ByteArray
  deriving Inhabited

/-- The blob URLs of the session. -/
structure Store where
  entries : List Entry := []
  /-- The bytes the entries hold. -/
  held : Nat := 0
  deriving Inhabited

/-- URLs at one time. -/
def maxEntries : Nat := 4096
/-- Bytes at one time: 256 MiB. -/
def maxHeld : Nat := 268435456

/-- "Generate a new blob URL" (File API §8.3.1) for `origin` with the UUID `uuid`. -/
def urlFor (origin uuid : String) : String := "blob:" ++ origin ++ "/" ++ uuid

/-- A URL without its fragment (a blob URL is looked up without it, §8.3.2). -/
def withoutFragment (url : String) : String := (url.splitOn "#").headD ""

/-- Add a blob for `origin`: the store and the new URL, or `none` past a bound (or when the
UUID was drawn before). -/
def add (s : Store) (origin uuid type : String) (body : ByteArray) : Option (Store × String) :=
  if s.entries.length ≥ maxEntries || s.held + body.size > maxHeld ||
      s.entries.any (fun e => e.url == urlFor origin uuid) then none
  else some ({ entries := { url := urlFor origin uuid, origin, type, body } :: s.entries,
               held := s.held + body.size }, urlFor origin uuid)

/-- The entry that a request of `origin` reads for `url`: only one that `origin` made. -/
def resolve (s : Store) (origin url : String) : Option Entry :=
  s.entries.find? fun e => e.url == withoutFragment url && e.origin == origin

/-- `URL.revokeObjectURL(url)` by a page of `origin`: only its own URL goes. -/
def revoke (s : Store) (origin url : String) : Store :=
  let keep := s.entries.filter fun e => !(e.url == url && e.origin == origin)
  { entries := keep, held := keep.foldl (fun n e => n + e.body.size) 0 }

/-! ## Theorems -/

/-- Kind: security invariant (blob URL partition, read side). Says: an entry that a request
of `origin` resolves was made by `origin`: a blob URL is never read by another origin, even
by a page that knows the URL. Does not say: that the engine passes the right origin
(`Net.Xhr.beginFetch` gives the page's, `PageFetch.Page.origin`). -/
theorem resolve_origin (s : Store) (origin url : String) (e : Entry)
    (h : resolve s origin url = some e) : e.origin = origin := by
  unfold resolve at h
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

/-- Kind: security invariant (blob URL partition, write side). Says: a revocation by one
origin leaves what every other origin resolves unchanged. -/
theorem revoke_other (s : Store) (o o' url url' : String) (h : o ≠ o') :
    resolve (revoke s o url) o' url' = resolve s o' url' := by
  unfold resolve revoke
  simp only
  rw [List.find?_filter]
  congr 1
  funext e
  by_cases ho : e.origin = o'
  · have hne : ¬ (o' = o) := fun x => h x.symm
    cases hu : e.url == withoutFragment url' <;> simp_all
  · simp [ho]

/-- Kind: security invariant (blob URL partition, write side). Says: a URL made by one origin
changes nothing that another origin resolves. -/
theorem add_other (s s' : Store) (o o' uuid type url u : String) (body : ByteArray)
    (h : o ≠ o') (ha : add s o uuid type body = some (s', u)) :
    resolve s' o' url = resolve s o' url := by
  unfold add at ha
  split at ha
  · simp at ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    rw [← ha.1]
    unfold resolve
    rw [List.find?_cons]
    have : ((urlFor o uuid == withoutFragment url) && (o == o')) = false := by
      have : (o == o') = false := by simpa using h
      simp [this]
    simp [this]

/-- Kind: functional law. Says: the origin that made a URL resolves it to the blob given.
Does not say: anything after a revocation. -/
theorem resolve_add (s s' : Store) (o uuid type u : String) (body : ByteArray)
    (ha : add s o uuid type body = some (s', u)) (hu : withoutFragment u = u) :
    (resolve s' o u).map (fun e => (e.type, e.body)) = some (type, body) := by
  unfold add at ha
  split at ha
  · simp at ha
  · simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨h1, h2⟩ := ha
    subst h1
    rw [← h2] at hu ⊢
    unfold resolve
    rw [List.find?_cons]
    simp [hu]

/-- Kind: resource bound. Says: a store that `add` gives holds at most `maxEntries` URLs when
the one before did, and counts `body.size` more bytes, within `maxHeld`. -/
theorem add_bounds (s s' : Store) (o uuid type u : String) (body : ByteArray)
    (ha : add s o uuid type body = some (s', u)) :
    s'.entries.length ≤ maxEntries ∧ s'.held = s.held + body.size ∧ s'.held ≤ maxHeld := by
  unfold add at ha
  split at ha
  · simp at ha
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    rw [← ha.1]
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Nat.not_lt] at hc
    refine ⟨?_, rfl, ?_⟩
    · simp only [List.length_cons]
      exact hc.1.1
    · exact hc.1.2

/-! ## Checks -/

private def b (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 7)
private def s1 : Store := ((add {} "http://a.example" "u1" "text/plain" (b 3)).map (·.1)).getD {}

#guard ((add {} "http://a.example" "u1" "text/plain" (b 3)).map (·.2)) == some "blob:http://a.example/u1"
#guard ((resolve s1 "http://a.example" "blob:http://a.example/u1").map (·.type)) == some "text/plain"
#guard ((resolve s1 "http://a.example" "blob:http://a.example/u1#frag").map (·.body.size)) == some 3
-- another origin does not read it, even with the URL
#guard (resolve s1 "http://b.example" "blob:http://a.example/u1").isNone
#guard (resolve s1 "http://a.example" "blob:http://a.example/u2").isNone
-- revoke: by the owner only
#guard (resolve (revoke s1 "http://b.example" "blob:http://a.example/u1") "http://a.example" "blob:http://a.example/u1").isSome
#guard (resolve (revoke s1 "http://a.example" "blob:http://a.example/u1") "http://a.example" "blob:http://a.example/u1").isNone
#guard (revoke s1 "http://a.example" "blob:http://a.example/u1").held == 0 && s1.held == 3
-- the bounds
#guard (add { held := maxHeld } "http://a.example" "u" "" (b 1)).isNone
#guard (add s1 "http://a.example" "u1" "" (b 1)).isNone

end L4Factoidal.Net.BlobUrls
