/-
L4Factoidal.LWS.Snapshot — the durable form of an in-memory storage.

`factoidal lws-serve DIR` and `factoidal solid-serve DIR` keep a storage in
an engine handle. A storage that loses every resource when the process stops
is not usable as storage, so the host writes this snapshot to `DIR` after
every request that changed the state, and gives it back to `lwsOpen` /
`solidOpen` on the next start. The LWS draft states no persistence rule;
the reason is the definition of a storage itself (§Terminology, "storage —
a space of URI-addressable resources"), which a server restart must not
empty.

The host only moves the bytes: it writes the document to a temporary file
in `DIR` and renames it over `DIR/lws-state.json`, so a crash leaves either
the old or the new snapshot. Which paths may appear is decided here:
`ofJson` refuses an entry whose path is not a valid storage path
(`validTarget`: no `..`, no `.`, no empty segment, no backslash, no encoded
slash, no NUL), so a snapshot edited by hand cannot introduce a resource the
request path check would refuse.

The document (format 2, written since
https://github.com/danbri/factoidal/issues/889):

    {"format":"lws-snapshot-2","clock":N,
     "entries":[{"path":"/a","kind":"dataResource","contentType":"image/png",
                 "bodyBase64":"…","mtime":N}, …]}

`bodyBase64` is the representation data in the base64 encoding of RFC 4648
§4, so a body that is not UTF-8 (an image, any binary file) is kept byte for
byte; JSON strings cannot carry such a body. Format 1 (`"format":
"lws-snapshot-1"`, the body as a JSON string member `body`) is still read:
its bodies are the UTF-8 encoding of that string, which is what the format-1
writer stored.

Theorems: `Base64.decode_encode` (decoding the encoding of any byte array
gives it back), `entryOfJson_entryJson` (an entry written by `entryJson`
reads back as the same entry) and `memStateOfJson_snapshotJson` (a storage
written by `snapshotJson` reads back as the same storage, under the checks
the reader makes and the clock invariant).
-/
import L4Factoidal.LWS.Store
import L4Factoidal.LWS.Binding

namespace L4Factoidal.LWS.Base64

/-! ## Base64 (RFC 4648 §4)

The encoder and the decoder are loops with an accumulator (`encGo`,
`decGo`), so their stack use does not grow with the body. `encSpec` is the
structural specification of the encoder; `encGo_toList` relates the loop to
it, and `decode_encode` is the round trip. The decoder accepts the padded
form that the encoder writes; it refuses a length that is not a multiple of
four and any character outside the alphabet. -/

/-- The base64 alphabet of RFC 4648 §4, Table 1: index to symbol. -/
def b64Sym (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else if n < 52 then Char.ofNat (71 + n)
  else if n < 62 then Char.ofNat (n - 4)
  else if n == 62 then '+' else '/'

/-- Symbol to index; `none` for a character outside the alphabet. -/
def b64Val? (c : Char) : Option Nat :=
  let k := c.toNat
  if 65 ≤ k && k ≤ 90 then some (k - 65)
  else if 97 ≤ k && k ≤ 122 then some (k - 71)
  else if 48 ≤ k && k ≤ 57 then some (k + 4)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

theorem b64Val_sym_fin : ∀ n : Fin 64, b64Val? (b64Sym n.val) = some n.val := by decide

theorem b64Val_sym (n : Nat) (h : n < 64) : b64Val? (b64Sym n) = some n :=
  b64Val_sym_fin ⟨n, h⟩

theorem b64Sym_ne_pad_fin : ∀ n : Fin 64, b64Sym n.val ≠ '=' := by decide

theorem b64Sym_ne_pad (n : Nat) (h : n < 64) : b64Sym n ≠ '=' := b64Sym_ne_pad_fin ⟨n, h⟩

/-- The four symbols of one three-byte group. -/
def group3 (a b c : UInt8) : List Char :=
  [ b64Sym (a.toNat / 4), b64Sym (a.toNat % 4 * 16 + b.toNat / 16)
  , b64Sym (b.toNat % 16 * 4 + c.toNat / 64), b64Sym (c.toNat % 64) ]

def group2 (a b : UInt8) : List Char :=
  [ b64Sym (a.toNat / 4), b64Sym (a.toNat % 4 * 16 + b.toNat / 16)
  , b64Sym (b.toNat % 16 * 4), '=' ]

def group1 (a : UInt8) : List Char :=
  [ b64Sym (a.toNat / 4), b64Sym (a.toNat % 4 * 16), '=', '=' ]

/-- The encoding as a list, by structural recursion: the specification. -/
noncomputable def encSpec : List UInt8 → List Char
  | a :: b :: c :: rest => group3 a b c ++ encSpec rest
  | [a, b] => group2 a b
  | [a] => group1 a
  | [] => []

/-- The encoder that runs: a loop with an accumulator. -/
def encGo : List UInt8 → Array Char → Array Char
  | a :: b :: c :: rest, acc => encGo rest (acc ++ (group3 a b c).toArray)
  | [a, b], acc => acc ++ (group2 a b).toArray
  | [a], acc => acc ++ (group1 a).toArray
  | [], acc => acc

theorem encGo_toList (bs : List UInt8) (acc : Array Char) :
    (encGo bs acc).toList = acc.toList ++ encSpec bs := by
  induction bs, acc using encGo.induct with
  | case1 a b c rest acc ih => simp [encGo, encSpec, ih]
  | case2 a b acc => simp [encGo, encSpec]
  | case3 a acc => simp [encGo, encSpec]
  | case4 acc => simp [encGo, encSpec]

/-- The bytes of one decoded group. -/
def byte0 (v0 v1 : Nat) : UInt8 := UInt8.ofNat (v0 * 4 + v1 / 16)
def byte1 (v1 v2 : Nat) : UInt8 := UInt8.ofNat (v1 % 16 * 16 + v2 / 4)
def byte2 (v2 v3 : Nat) : UInt8 := UInt8.ofNat (v2 % 4 * 64 + v3)

/-- The decoder that runs: a loop with an accumulator. -/
def decGo : List Char → Array UInt8 → Option (Array UInt8)
  | [c0, c1, '=', '='], acc =>
      match b64Val? c0, b64Val? c1 with
      | some v0, some v1 => some (acc.push (byte0 v0 v1))
      | _, _ => none
  | [c0, c1, c2, '='], acc =>
      match b64Val? c0, b64Val? c1, b64Val? c2 with
      | some v0, some v1, some v2 => some ((acc.push (byte0 v0 v1)).push (byte1 v1 v2))
      | _, _, _ => none
  | c0 :: c1 :: c2 :: c3 :: rest, acc =>
      match b64Val? c0, b64Val? c1, b64Val? c2, b64Val? c3 with
      | some v0, some v1, some v2, some v3 =>
          decGo rest (((acc.push (byte0 v0 v1)).push (byte1 v1 v2)).push (byte2 v2 v3))
      | _, _, _, _ => none
  | [], acc => some acc
  | _, _ => none

theorem toNat_lt (a : UInt8) : a.toNat < 256 := a.toNat_lt

theorem byte0_eq (a b : UInt8) :
    byte0 (a.toNat / 4) (a.toNat % 4 * 16 + b.toNat / 16) = a := by
  have ha := toNat_lt a; have hb := toNat_lt b
  unfold byte0
  have : a.toNat / 4 * 4 + (a.toNat % 4 * 16 + b.toNat / 16) / 16 = a.toNat := by omega
  rw [this]; exact UInt8.ofNat_toNat

theorem byte1_eq (a b c : UInt8) :
    byte1 (a.toNat % 4 * 16 + b.toNat / 16) (b.toNat % 16 * 4 + c.toNat / 64) = b := by
  have hb := toNat_lt b; have hc := toNat_lt c
  unfold byte1
  have : (a.toNat % 4 * 16 + b.toNat / 16) % 16 * 16 + (b.toNat % 16 * 4 + c.toNat / 64) / 4
      = b.toNat := by omega
  rw [this]; exact UInt8.ofNat_toNat

theorem byte1_eq2 (a b : UInt8) :
    byte1 (a.toNat % 4 * 16 + b.toNat / 16) (b.toNat % 16 * 4) = b := by
  have hb := toNat_lt b
  unfold byte1
  have : (a.toNat % 4 * 16 + b.toNat / 16) % 16 * 16 + (b.toNat % 16 * 4) / 4 = b.toNat := by omega
  rw [this]; exact UInt8.ofNat_toNat

theorem byte2_eq (b c : UInt8) :
    byte2 (b.toNat % 16 * 4 + c.toNat / 64) (c.toNat % 64) = c := by
  have hc := toNat_lt c
  unfold byte2
  have : (b.toNat % 16 * 4 + c.toNat / 64) % 4 * 64 + c.toNat % 64 = c.toNat := by omega
  rw [this]; exact UInt8.ofNat_toNat

theorem byte0_eq1 (a : UInt8) : byte0 (a.toNat / 4) (a.toNat % 4 * 16) = a := by
  have ha := toNat_lt a
  unfold byte0
  have : a.toNat / 4 * 4 + a.toNat % 4 * 16 / 16 = a.toNat := by omega
  rw [this]; exact UInt8.ofNat_toNat

theorem decGo_encSpec (bs : List UInt8) (acc : Array UInt8) :
    decGo (encSpec bs) acc = some (acc ++ bs.toArray) := by
  induction bs using encSpec.induct generalizing acc with
  | case1 a b c rest ih =>
      have h0 := b64Val_sym (a.toNat / 4) (by have := toNat_lt a; omega)
      have h1 := b64Val_sym (a.toNat % 4 * 16 + b.toNat / 16) (by have := toNat_lt b; omega)
      have h2 := b64Val_sym (b.toNat % 16 * 4 + c.toNat / 64) (by have := toNat_lt c; omega)
      have h3 := b64Val_sym (c.toNat % 64) (by omega)
      have n2 := b64Sym_ne_pad (b.toNat % 16 * 4 + c.toNat / 64) (by have := toNat_lt c; omega)
      have n3 := b64Sym_ne_pad (c.toNat % 64) (by omega)
      simp only [encSpec, group3, List.cons_append, List.nil_append]
      rw [decGo.eq_def]
      simp [h0, h1, h2, h3, n2, n3, ih, byte0_eq, byte1_eq, byte2_eq]
  | case2 a b =>
      have h0 := b64Val_sym (a.toNat / 4) (by have := toNat_lt a; omega)
      have h1 := b64Val_sym (a.toNat % 4 * 16 + b.toNat / 16) (by have := toNat_lt b; omega)
      have h2 := b64Val_sym (b.toNat % 16 * 4) (by have := toNat_lt b; omega)
      have n2 := b64Sym_ne_pad (b.toNat % 16 * 4) (by have := toNat_lt b; omega)
      simp only [encSpec, group2]
      rw [decGo.eq_def]
      simp [h0, h1, h2, byte0_eq, byte1_eq2]
      apply Array.toList_inj.mp; simp
  | case3 a =>
      have h0 := b64Val_sym (a.toNat / 4) (by have := toNat_lt a; omega)
      have h1 := b64Val_sym (a.toNat % 4 * 16) (by have := toNat_lt a; omega)
      simp only [encSpec, group1]
      rw [decGo.eq_def]
      simp [h0, h1, byte0_eq1]
  | case4 => simp [encSpec, decGo]

def encode (b : ByteArray) : String := String.ofList (encGo b.data.toList #[]).toList

def decode? (s : String) : Option ByteArray := (decGo s.toList #[]).map ByteArray.mk

theorem decode_encode (b : ByteArray) : decode? (encode b) = some b := by
  simp [decode?, encode, encGo_toList, decGo_encSpec]



end L4Factoidal.LWS.Base64

namespace L4Factoidal.LWS

open L4Factoidal.JSON

/-- The snapshot format this module writes. -/
def snapshotFormat : String := "lws-snapshot-2"

/-- The earlier format, read but not written: bodies as JSON strings. -/
def snapshotFormatV1 : String := "lws-snapshot-1"

def ResourceKind.name : ResourceKind → String
  | .container => "container"
  | .dataResource => "dataResource"
  | .storageRoot => "storageRoot"
  | .metadataResource => "metadataResource"
  | .linksetResource => "linksetResource"

def ResourceKind.ofName? : String → Option ResourceKind
  | "container" => some .container
  | "dataResource" => some .dataResource
  | "storageRoot" => some .storageRoot
  | "metadataResource" => some .metadataResource
  | "linksetResource" => some .linksetResource
  | _ => none

/-- A client-managed link: `href`, `rel`, and its target attributes. -/
def linkJson (l : Link) : Json :=
  .object [ ("href", .string l.target), ("rel", .string l.rel)
          , ("attrs", .object (l.attrs.map (fun (k, v) => (k, .string v)))) ]

def attrsOfJson (fs : List (String × Json)) : Option (List (String × String)) :=
  fs.mapM (fun (k, v) => v.asString?.map (fun s => (k, s)))

def linkOfJson (j : Json) : Option Link := do
  let target ← j.getString? "href"
  let rel ← j.getString? "rel"
  let attrs ← match j.field? "attrs" with
    | some (.object fs) => attrsOfJson fs
    | _ => none
  some { target, rel, attrs }

/-- The client links of a snapshot entry. An absent member (every entry of a
snapshot written before client links existed) is no links. -/
def linksOfJson (path : String) (j : Json) : Except String (List Link) :=
  match j.field? "links" with
  | none => .ok []
  | some (.array xs) =>
      match xs.mapM linkOfJson with
      | some ls => .ok ls
      | none => .error s!"snapshot: entry {path} has a malformed link"
  | some _ => .error s!"snapshot: entry {path} has a links member that is not an array"

theorem attrsOfJson_map (as : List (String × String)) :
    attrsOfJson (as.map (fun (k, v) => (k, Json.string v))) = some as := by
  induction as with
  | nil => rfl
  | cons a t ih =>
      obtain ⟨k, v⟩ := a
      unfold attrsOfJson at ih ⊢
      rw [List.map_cons, List.mapM_cons, ih]
      rfl

theorem linkOfJson_linkJson (l : Link) : linkOfJson (linkJson l) = some l := by
  obtain ⟨t, r, as⟩ := l
  simp [linkOfJson, linkJson, Json.getString?, Json.field?, Json.asString?, attrsOfJson_map]

theorem mapM_linkOfJson (ls : List Link) : (ls.map linkJson).mapM linkOfJson = some ls := by
  induction ls with
  | nil => rfl
  | cons l t ih => simp [List.mapM_cons, linkOfJson_linkJson, ih]

theorem mapM_linkOfJson_comp (ls : List Link) : ls.mapM (linkOfJson ∘ linkJson) = some ls := by
  induction ls with
  | nil => rfl
  | cons l t ih => simp [List.mapM_cons, linkOfJson_linkJson, ih]

def entryJson (e : Entry) : Json :=
  .object ([ ("path", .string e.path), ("kind", .string e.kind.name)
          , ("contentType", .string e.contentType)
          , ("bodyBase64", .string (Base64.encode e.body))
          , ("mtime", .number (toString e.mtime)) ] ++
          (if e.links.isEmpty then [] else [("links", .array (e.links.map linkJson))]))

/-- The snapshot document of a state. Entries keep the state's order. -/
def snapshotJson (s : MemState) : Json :=
  .object [ ("format", .string snapshotFormat)
          , ("clock", .number (toString s.clock))
          , ("entries", .array (s.entries.map entryJson)) ]

/-! ## Decimal numerals

The clock and the modification times are JSON numbers. `decimal?` reads the
digits `toString` writes (a loop with an accumulator), and `decimal_repr` is
its round trip. A sign, a fraction or an exponent is refused. -/

/-- Decimal digits to a number, a loop with an accumulator. -/
def decAcc : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => if c.isDigit then decAcc cs (acc * 10 + (c.toNat - 48)) else none

def decimal? (s : String) : Option Nat :=
  if s.toList.isEmpty then none else decAcc s.toList 0

theorem decAcc_append (l1 l2 : List Char) (acc : Nat) :
    decAcc (l1 ++ l2) acc = (decAcc l1 acc).bind (decAcc l2) := by
  induction l1 generalizing acc with
  | nil => simp [decAcc]
  | cons c cs ih =>
      simp only [List.cons_append, decAcc]
      split <;> simp [ih]

theorem decAcc_repr (n : Nat) : ∀ acc, decAcc n.repr.toList acc = some (acc * 10 ^ n.repr.length + n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : n < 10
    · rw [Nat.repr_of_lt h]
      have hd : (Nat.digitChar n).isDigit = true := by simp [Nat.isDigit_digitChar, h]
      simp [decAcc, hd, Nat.toNat_digitChar_sub_48_of_lt_ten h]
    · have h10 : 10 ≤ n := by omega
      have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h1 : (n % 10).repr.length = 1 := by
        rw [Nat.repr_of_lt hm]; simp
      rw [Nat.repr_eq_repr_append_repr h10, String.toList_append, decAcc_append,
        ih (n / 10) (by omega) acc, Option.bind_some, ih (n % 10) (by omega),
        String.length_append, h1]
      congr 1
      have hdm := Nat.div_add_mod n 10
      rw [Nat.pow_one, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]
      omega

theorem decimal_repr (n : Nat) : decimal? n.repr = some n := by
  have hne : n.repr.toList.isEmpty = false := by
    cases h : n.repr.toList with
    | nil => exact absurd (String.toList_eq_nil_iff.mp h) Nat.repr_ne_empty
    | cons _ _ => rfl
  simp only [decimal?, hne]
  rw [decAcc_repr]; simp


private def natField (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number n) => decimal? n
  | _ => none

/-- The body of a snapshot entry: `bodyBase64` in format 2, the UTF-8
encoding of `body` in format 1. An absent member is an empty body. -/
def entryBodyOfJson (v1 : Bool) (path : String) (j : Json) : Except String ByteArray :=
  if v1 then .ok (textBytes ((j.getString? "body").getD ""))
  else match j.getString? "bodyBase64" with
    | none => .ok ByteArray.empty
    | some t =>
        match Base64.decode? t with
        | some b => .ok b
        | none => .error s!"snapshot: entry {path} has a bodyBase64 that is not base64"

def entryOfJson (j : Json) (v1 : Bool := false) : Except String Entry := do
  let path ← (j.getString? "path").elim (.error "snapshot: an entry has no path") .ok
  if !validTarget path then .error s!"snapshot: refused path {path}" else
  let kind ← ((j.getString? "kind").bind ResourceKind.ofName?).elim
    (.error s!"snapshot: entry {path} has no valid kind") .ok
  let contentType := (j.getString? "contentType").getD "application/octet-stream"
  let body ← entryBodyOfJson v1 path j
  let mtime := (natField j "mtime").getD 0
  let links ← linksOfJson path j
  .ok { path, kind, contentType, body, mtime, links }

/-- Read a snapshot document back. The clock is raised above every stored
modification time, so the next write still stamps a strictly larger time. -/
def memStateOfJson (j : Json) : Except String MemState := do
  let format := j.getString? "format"
  if format != some snapshotFormat && format != some snapshotFormatV1 then
    .error s!"snapshot: format is not {snapshotFormat} or {snapshotFormatV1}" else
  let v1 := format == some snapshotFormatV1
  let items ← (j.getArray? "entries").elim (.error "snapshot: no entries") .ok
  let entries ← items.mapM (entryOfJson · v1)
  if !(entries.any (fun e => e.path == rootPath && e.kind == .storageRoot)) then
    .error "snapshot: no storage root" else
  let paths := entries.map (·.path)
  if paths.eraseDups.length != paths.length then .error "snapshot: a path repeats" else
  let maxM := entries.foldl (fun m e => max m e.mtime) 0
  .ok { entries, clock := max ((natField j "clock").getD 0) (maxM + 1) }

/-! ## Round trip -/

theorem ResourceKind.ofName?_name (k : ResourceKind) : ResourceKind.ofName? k.name = some k := by
  cases k <;> rfl

/-- An entry written by `entryJson` reads back as the same entry: path,
kind, media type, every byte of the body, the modification time and the
client links. The
hypothesis is the path check `entryOfJson` makes on every entry. -/
theorem entryOfJson_entryJson (e : Entry) (h : validTarget e.path = true) :
    entryOfJson (entryJson e) = .ok e := by
  obtain ⟨path, kind, ct, body, mtime, links⟩ := e
  cases links with
  | nil =>
      simp_all [entryOfJson, entryJson, entryBodyOfJson, natField, Json.getString?, Json.field?,
        Json.asString?, ResourceKind.ofName?_name, Base64.decode_encode, decimal_repr, linksOfJson]
      simp [bind, Except.bind, h]
  | cons l t =>
      simp_all [entryOfJson, entryJson, entryBodyOfJson, natField, Json.getString?, Json.field?,
        Json.asString?, ResourceKind.ofName?_name, Base64.decode_encode, decimal_repr, linksOfJson,
        mapM_linkOfJson_comp, linkOfJson_linkJson]
      simp [bind, Except.bind, h]

theorem mapM_entryOfJson (es : List Entry) (h : ∀ e ∈ es, validTarget e.path = true) :
    (es.map entryJson).mapM (entryOfJson · false) = .ok es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      have he := entryOfJson_entryJson e (h e (by simp))
      have hr := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.mapM_cons, he, hr]
      rfl

/-- The snapshot round trip for a whole storage: reading back the document
`snapshotJson s` writes gives `s`, every entry and the clock. The
hypotheses are the checks `memStateOfJson` makes (valid paths, a storage
root, no repeated path) and the clock invariant the operations keep (the
clock is above every modification time, `StoreLaws.nowTick`). -/
theorem memStateOfJson_snapshotJson (s : MemState)
    (hv : ∀ e ∈ s.entries, validTarget e.path = true)
    (hroot : s.entries.any (fun e => e.path == rootPath && e.kind == .storageRoot) = true)
    (hdup : (s.entries.map (·.path)).eraseDups.length = (s.entries.map (·.path)).length)
    (hclock : s.entries.foldl (fun m e => max m e.mtime) 0 + 1 ≤ s.clock) :
    memStateOfJson (snapshotJson s) = .ok s := by
  have hm := mapM_entryOfJson s.entries hv
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hroot
  obtain ⟨r, hr, hrp, hrk⟩ := hroot
  simp [memStateOfJson, snapshotJson, Json.getString?, Json.field?, Json.getArray?, Json.asString?,
    Json.asArray?, natField, snapshotFormat, snapshotFormatV1, hm, decimal_repr, bind,
    Except.bind]
  have hnot : ¬ (∀ (x : Entry), x ∈ s.entries → x.path = rootPath →
      ¬x.kind = ResourceKind.storageRoot) := fun hall => hall r hr hrp hrk
  have hlen : (List.map (fun x => x.path) s.entries).eraseDups.length = s.entries.length := by
    rw [hdup, List.length_map]
  rw [if_neg hnot, if_pos hlen, Nat.max_eq_left hclock]

end L4Factoidal.LWS
