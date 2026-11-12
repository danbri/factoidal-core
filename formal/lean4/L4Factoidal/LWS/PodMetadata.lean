/-
L4Factoidal.LWS.PodMetadata — what a photo says about itself, and how its
place is removed before it is shared.

The foafos shell reads the metadata in a file (`readMetadata` in
`packages/foafos/src/metadata.mjs`) and, when a file is read through a share,
gives the reader a copy without the photo's position (`withoutLocation` in the
same file, called from `FoafPods.invoke` in `packages/foafos/src/pods.mjs`).
This module is a specification of those two functions and of the share rule.
It states the definitions and the theorems that they satisfy. That the
JavaScript computes what these definitions compute is not proved here; that is
a matter for a differential test.

## The model

* **Bytes and reads.** A TIFF block (the body of EXIF) is a `List UInt8`. Every
  read is `t[i]?`, which gives `none` past the end. `u16` and `u32` read two
  and four bytes at an offset, little- or big-endian, and give `none` if a
  byte is missing (the JS `u16`/`u32` give `null`).
* **Entries and IFDs.** `readEntry` reads the 12-byte entry at an offset: tag,
  type, count, and either the inline value (4 bytes or fewer) or a pointer to
  it. An entry with an unknown type, more than 1 MiB of value, or a value that
  does not end inside the block is skipped. `readIfd` reads the entry count at
  an offset (refused over 512) and then each entry. These are the JS `ifd`.
* **The value window.** An entry's value is read only through its window
  (`win`): `max bytes 4` bytes from its value offset. Every value read in
  `readTiff` (text, short, long, rationals) is a read inside that window.
* **The reader** (`readTiff`) checks the header, reads IFD0 at the offset in
  bytes 4–7, reads its entries in order (`scan0`: make, model, orientation,
  date modified, the Exif pointer 0x8769 and the GPS pointer 0x8825; the last
  pointer of each tag wins), then the Exif IFD (date taken, width, height) and
  the GPS IFD. The location is read from GPS tags 1–4 only.
* **Emptying the GPS IFD** (`emptyGps`, the JS `emptyGps`): every byte in the
  `zeroRanges` is set to 0. These are the GPS IFD's count and entry table and
  every GPS entry's value bytes, as the reader found them in the input. Every
  other byte is copied.
* **A file** (`File`) is a kind (JPEG, PNG or other) and a list of segments
  (`Seg`): an EXIF segment (JPEG APP1 with `Exif\0\0`, or PNG `eXIf`, which
  also has a CRC), an XMP segment (JPEG APP1 with the XMP header, or PNG
  `iTXt`/`tEXt` with key `XML:com.adobe.xmp`), or any other segment (image
  data, SOF, IHDR, other text). `strip` is the JS `withoutLocation`: it
  empties the GPS IFD in each EXIF segment, recomputes a PNG CRC, drops every
  XMP segment and copies every other segment. A file of another kind is
  copied unchanged.
* **The checked strip** (`stripChecked`) is not in the JS. It is `strip`
  plus one check: after emptying, the block is read again, and if a GPS IFD
  with entries is still found, the whole EXIF segment is dropped. It is here
  because `strip` has a gap on crafted files (below), and this variant has no
  gap.
* **The share rule** (`handle`): the owner reads the stored file; a share
  reads only the shared path, and gets `strip` of the stored file from a
  read and metadata with no location from `pod.meta`. Reads do not change
  the store.

## What is proved

The disjointness condition. `disjoint t` is a Boolean check: the byte ranges
that `emptyGps` sets to zero (`zeroRanges t`) do not overlap the byte ranges
from which the rest of the structure is read (`keepRanges t`: the header,
the IFD0 table and the value windows of its entries, and the Exif IFD table
and windows). Files written by cameras and editors keep the GPS IFD and its
values in their own bytes, so they satisfy it (this is assumed, not proved;
see below). It is the hypothesis of the theorems marked (D).

For a TIFF block:
`emptyGps_length`, `getElem?_emptyGps` (only bytes in the zero ranges change,
and they change to 0), `readTiff_emptyGps_location` (D) (no location after
emptying), `readTiff_emptyGps_fields` (D) (every other field is the same),
`emptyGps_idem` (D) (emptying twice is emptying once),
`readTiff_emptyGps_gps` (D) (the GPS IFD is still found, with 0 entries).

For a file: `strip_no_location` (D), `strip_keeps_fields` (D),
`strip_idem` (D), `strip_no_xmp`, `strip_keeps_other`, `strip_png_crc`,
`strip_other_kind`; and for the checked strip, with no hypothesis:
`stripChecked_no_location`, `stripChecked_idem`, `stripChecked_no_xmp`,
`stripChecked_keeps_other`, and (D) `stripChecked_eq_strip`.

Reading in bounds: `u16_some`, `u32_some` (a read gives a value only when
every byte it needs is inside the block), `slice_getElem?` (a window byte is
the block byte at `valAt + j`, read with `t[_]?`), `readEntry_some`,
`readEntry_past_end`, `readIfd_some` (an entry that is read lies inside the
block; at most 512 entries per IFD; at most 1 MiB per value),
`ascii_length` (a text field is at most 512 bytes). A failed read gives
`none`, and `none` only removes that entry or field (`filterMap`,
`Option.bind`); every function here is total, so nothing throws.

The share rule: `owner_get`, `share_get`, `share_get_no_location` (D),
`share_meta_no_location`, `share_meta_fields`, `read_keeps`, `reads_keep`,
`owner_put_get`, `share_put_readonly`.

## The gap: crafted files that overlap (proved by example)

Without the disjointness condition, `strip` can expose a location. The
example `overlapTiff` below is a TIFF block whose IFD0 has two GPS pointers.
The reader takes the last one, to a GPS IFD with no position. That GPS IFD
has an entry whose value bytes lie over the tag of the second pointer.
Emptying zeroes them, so the second pointer is no longer read, and the
reader now takes the first pointer, to a second GPS IFD that has a position.
The `#guard` lines show: no location before `strip`, a location after it,
and `strip` twice differs from `strip` once. The same bytes in a JPEG were
run through `metadata.mjs` (2026-11-12): `readMetadata` gave `location:
null`, `readMetadata(withoutLocation(x))` gave `{lat: 51, lon: 1}`.

What remains true for every input is `getElem?_emptyGps`: only the bytes in
the zero ranges change, and they become 0; the length is kept; segments that
are not EXIF or XMP are kept byte for byte (`strip_keeps_other`); and no XMP
segment is left (`strip_no_xmp`). Fields read from bytes outside the zero
ranges are the same; a field whose bytes overlap them can change or
disappear. `stripChecked` closes the gap: for every input, no location is
found in its output, and it is idempotent. When `disjoint` holds it is equal
to `strip`; when it does not, it can drop the whole EXIF segment, so the
camera fields of that segment are lost (it fails closed). Since 2026-11-12
the shell's `withoutLocation` does what `stripChecked` does: it reads the
block again after emptying and drops the EXIF segment if a GPS IFD with
entries or a position is still found (danbri/glitchcan-minigam PR 1027, with
`overlapTiff` as a regression test).

## What is not proved, and the assumptions

* **Refinement.** That `metadata.mjs` computes what these definitions compute
  is not proved. In particular: the JS parses JPEG segments and PNG chunks
  from bytes (`jpegSegments`, `pngChunks`); this model starts from the list
  of segments. That writing the stripped segments back to bytes and parsing
  them again gives the same list (with the XMP segments removed) is assumed.
* **Real files satisfy `disjoint`.** Assumed from the TIFF/EXIF layout, not
  checked on a corpus here. The JS does not need it: it does what
  `stripChecked` does, which has no condition.
* **Value decoding.** The JS cleans text (`clean`), parses dates
  (`exifDate`) and divides rationals; the model keeps the raw window bytes
  and number pairs. Those steps are functions of the same bytes, so the
  field theorems carry over; they are not modelled. The JS also refuses a
  latitude over 90 or a longitude over 180; the model reports a location in
  those cases too, so "no location in the model" implies "no location in the
  JS", not the reverse.
* **Other places a position can be.** Only the GPS IFD and XMP segments
  with the standard header are handled, in JPEG and PNG. Not handled, in
  the JS or here: Extended XMP (JPEG APP1 with
  `http://ns.adobe.com/xmp/extension/`), PNG `zTXt` with the XMP key,
  vendor MakerNotes inside the Exif IFD, IPTC (APP13) place names, images
  embedded after the first image (MPF, APP2, gain maps), the IFD1
  thumbnail's own metadata, HEIC, WebP, TIFF, video and PDF (a PDF can hold
  XMP; it is copied unchanged). A position in the pixels is not in scope.
* **Bytes no reader reaches.** Emptying sets the GPS IFD's count to 0 and
  zeroes its whole table and the value bytes of each entry the reader
  read. The value bytes of a GPS entry the reader skipped (unknown type,
  value over 1 MiB) are not zeroed. Its table entry is zeroed, so no reader
  that follows the GPS IFD reaches them, but the bytes stay in the file.
* **CPU time** is not modelled. Counts are capped (512 entries per IFD,
  1 MiB per value, 512 bytes per text field).
* **Access control.** Which app holds which share is decided before
  `handle` runs; that decision is not proved here. A share that may write
  (`pod.put`) replaces the owner's file; that is the owner's grant.

No `sorry`, no `axiom`, no `partial`. Lean core only (no Mathlib).
-/

namespace L4Factoidal.LWS.PodMetadata

/-! ## Bytes and reads -/

/-- A byte. -/
abbrev Byte := UInt8
/-- A run of bytes: a TIFF block, a segment body. -/
abbrev Bytes := List Byte

/-- The most entries read from one IFD (`READ_LIMITS.ifdEntries`). -/
def maxEntries : Nat := 512
/-- The most bytes of one text field (`READ_LIMITS.string`). -/
def maxString : Nat := 512
/-- The largest value an entry may have, in bytes (1 MiB). -/
def maxValue : Nat := 1024 * 1024

/-- Two bytes at offset `o` as a number, little-endian if `le`; `none` if
either byte is past the end. -/
def u16 (le : Bool) (t : Bytes) (o : Nat) : Option Nat :=
  match t[o]?, t[o + 1]? with
  | some a, some b => some (if le then a.toNat + 256 * b.toNat else 256 * a.toNat + b.toNat)
  | _, _ => none

/-- Four bytes at offset `o` as a number; `none` if any byte is past the end. -/
def u32 (le : Bool) (t : Bytes) (o : Nat) : Option Nat :=
  match u16 le t o, u16 le t (o + 2) with
  | some a, some b => some (if le then a + 65536 * b else 65536 * a + b)
  | _, _ => none

/-- `n` bytes from offset `a` (fewer if the block ends first). -/
def slice (t : Bytes) (r : Nat × Nat) : Bytes := (t.drop r.1).take r.2

/-! ## Entries and IFDs -/

/-- The size in bytes of one value of a TIFF type; 0 for a type the reader
does not know (the JS `SIZE`). -/
def typeSize : Nat → Nat
  | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 7 => 1 | 9 => 4 | 10 => 8 | _ => 0

/-- One IFD entry as the reader found it. -/
structure Entry where
  /-- The tag (for example 0x8825, the GPS pointer). -/
  tag : Nat
  /-- The TIFF type. -/
  type : Nat
  /-- The number of values. -/
  count : Nat
  /-- Where the value starts: the entry's own 4 value bytes when the value
  fits in them, otherwise the offset written there. -/
  valAt : Nat
  /-- The value's size: `typeSize type * count`. -/
  bytes : Nat
  /-- Where the 12-byte entry starts. -/
  entry : Nat
  deriving DecidableEq, Repr

/-- Read the 12-byte entry at `e`. Skipped (`none`) if a field is past the
end, the type is unknown, the value is over 1 MiB, or the value does not end
inside the block. -/
def readEntry (le : Bool) (t : Bytes) (e : Nat) : Option Entry :=
  match u16 le t e, u16 le t (e + 2), u32 le t (e + 4) with
  | some tag, some type, some count =>
    if typeSize type = 0 ∨ typeSize type * count > maxValue then none
    else
      match (if typeSize type * count ≤ 4 then some (e + 8) else u32 le t (e + 8)) with
      | some a =>
        if a + typeSize type * count ≤ t.length then
          some { tag, type, count, valAt := a, bytes := typeSize type * count, entry := e }
        else none
      | none => none
  | _, _, _ => none

/-- An IFD as the reader found it: where it is, the count it declares, and
the entries that were read. -/
structure Ifd where
  /-- The IFD's offset. -/
  off : Nat
  /-- The entry count written at `off`. -/
  n : Nat
  /-- The entries that were read (skipped ones are absent). -/
  entries : List Entry
  deriving DecidableEq, Repr

/-- Read the IFD at `off`: the count (refused over 512), then each entry. -/
def readIfd (le : Bool) (t : Bytes) (off : Nat) : Option Ifd :=
  match u16 le t off with
  | none => none
  | some n =>
    if n > maxEntries then none
    else some { off, n, entries := (List.range n).filterMap fun i => readEntry le t (off + 2 + 12 * i) }

/-- The bytes an IFD at `off` occupies as far as the reader is concerned:
the count and the table of the count's entries. -/
def tableAt (le : Bool) (t : Bytes) (off : Nat) : Nat × Nat :=
  (off, 2 + 12 * (u16 le t off).getD 0)

/-- The range an entry's value is read from: `max bytes 4` bytes at its
value offset. For an inline value these are the entry's own 4 value bytes. -/
def winRange (x : Entry) : Nat × Nat := (x.valAt, max x.bytes 4)

/-- The bytes of an entry's value window. -/
def win (t : Bytes) (x : Entry) : Bytes := slice t (winRange x)

/-- An IFD's entries, each with its value window. -/
abbrev View := List (Entry × Bytes)

/-- The entries of `g` with their windows in `t`. -/
def view (t : Bytes) (g : Ifd) : View := g.entries.map fun x => (x, win t x)

/-! ## Values and fields -/

/-- A field value: text (the raw bytes, up to 512) or a number. -/
inductive Val
  | text (b : Bytes)
  | num (n : Nat)
  deriving DecidableEq, Repr

/-- A text value: at most `min count 512` bytes of the window. -/
def ascii (x : Entry) (w : Bytes) : Option Val := some (.text (w.take (min x.count maxString)))

/-- A SHORT value: two bytes at the start of the window. -/
def short (le : Bool) (w : Bytes) : Option Val := (u16 le w 0).map .num

/-- A SHORT or LONG value (the JS `long`): two bytes for type 3, else four. -/
def long (le : Bool) (x : Entry) (w : Bytes) : Option Nat :=
  if x.type = 3 then u16 le w 0 else u32 le w 0

/-- Fields as the JS builds them: a name and a value or `null`. -/
abbrev Fields := List (String × Option Val)

/-- `fields[k] = v` (later writes win). -/
def assign (fs : Fields) (k : String) (v : Option Val) : Fields :=
  (k, v) :: fs.filter fun p => p.1 != k

/-- `fields[k] ??= v` (kept if already set to a value). -/
def assignIfAbsent (fs : Fields) (k : String) (v : Option Val) : Fields :=
  match (fs.find? fun p => p.1 == k) with
  | some (_, some _) => fs
  | _ => assign fs k v

/-- The final step of the JS reader: fields that are `null` or empty text
are removed. -/
def cleanup (fs : Fields) : List (String × Val) :=
  fs.filterMap fun p =>
    match p.2 with
    | some (.text []) => none
    | some v => some (p.1, v)
    | none => none

/-- What the IFD0 loop keeps: the fields so far and the last Exif and GPS
pointers. -/
structure Scan where
  /-- Fields so far. -/
  fields : Fields := []
  /-- The last Exif IFD pointer (tag 0x8769), if it could be read. -/
  exifOff : Option Nat := none
  /-- The last GPS IFD pointer (tag 0x8825), if it could be read. -/
  gpsOff : Option Nat := none

/-- One step of the IFD0 loop. -/
def scan0 (le : Bool) (s : Scan) (p : Entry × Bytes) : Scan :=
  let x := p.1
  let w := p.2
  if x.tag = 0x010f ∧ x.type = 2 then { s with fields := assign s.fields "make" (ascii x w) }
  else if x.tag = 0x0110 ∧ x.type = 2 then { s with fields := assign s.fields "model" (ascii x w) }
  else if x.tag = 0x0112 ∧ x.type = 3 then { s with fields := assign s.fields "orientation" (short le w) }
  else if x.tag = 0x0132 ∧ x.type = 2 then { s with fields := assign s.fields "modified" (ascii x w) }
  else if x.tag = 0x8769 then { s with exifOff := long le x w }
  else if x.tag = 0x8825 then { s with gpsOff := long le x w }
  else s

/-- One step of the Exif IFD loop. -/
def scanExif (le : Bool) (fs : Fields) (p : Entry × Bytes) : Fields :=
  let x := p.1
  let w := p.2
  if x.tag = 0x9003 ∧ x.type = 2 then assign fs "taken" (ascii x w)
  else if x.tag = 0xa002 ∧ (x.type = 3 ∨ x.type = 4) then assignIfAbsent fs "width" ((long le x w).map .num)
  else if x.tag = 0xa003 ∧ (x.type = 3 ∨ x.type = 4) then assignIfAbsent fs "height" ((long le x w).map .num)
  else fs

/-- A position as read from the GPS IFD: degrees, minutes, seconds as
(numerator, denominator) pairs, and the N/S and E/W reference bytes. -/
structure Loc where
  lat : List (Option Nat × Option Nat)
  latRef : Option Byte
  lon : List (Option Nat × Option Nat)
  lonRef : Option Byte
  deriving DecidableEq, Repr

/-- The first entry with tag `tag`. -/
def findTag (v : View) (tag : Nat) : Option (Entry × Bytes) := v.find? fun p => p.1.tag == tag

/-- Up to four rationals from a window. -/
def rationals (le : Bool) (x : Entry) (w : Bytes) : List (Option Nat × Option Nat) :=
  (List.range (min x.count 4)).map fun i => (u32 le w (8 * i), u32 le w (8 * i + 4))

/-- Degrees from GPS tag 2 or 4: type RATIONAL, at least 3 values. -/
def deg (le : Bool) (v : View) (tag : Nat) : Option (List (Option Nat × Option Nat)) :=
  match findTag v tag with
  | some (x, w) => if x.type = 5 ∧ x.count ≥ 3 then some (rationals le x w) else none
  | none => none

/-- The reference byte from GPS tag 1 or 3 (N/S, E/W). -/
def gpsRef (v : View) (tag : Nat) : Option Byte :=
  match findTag v tag with
  | some (x, w) => if x.type = 2 then w.head? else none
  | none => none

/-- The location in a GPS IFD's view: both latitude and longitude, or none. -/
def location (le : Bool) (v : View) : Option Loc :=
  match deg le v 2, deg le v 4 with
  | some a, some b => some { lat := a, latRef := gpsRef v 1, lon := b, lonRef := gpsRef v 3 }
  | _, _ => none

/-! ## The TIFF reader -/

/-- The header: `II` or `MM`, then 42. Gives the byte order. -/
def header (t : Bytes) : Option Bool :=
  if t.length < 8 then none
  else
    let le := t[0]? == some 0x49 && t[1]? == some 0x49
    if !le && !(t[0]? == some 0x4d && t[1]? == some 0x4d) then none
    else if u16 le t 2 = some 42 then some le else none

/-- IFD0, at the offset in bytes 4–7. -/
def ifd0 (t : Bytes) : Option (Bool × Ifd) :=
  match header t with
  | none => none
  | some le =>
    match u32 le t 4 with
    | none => none
    | some o => (readIfd le t o).map fun g => (le, g)

/-- IFD0 and the result of its loop. -/
def scan (t : Bytes) : Option (Bool × Ifd × Scan) :=
  (ifd0 t).map fun p => (p.1, p.2, (view t p.2).foldl (scan0 p.1) {})

/-- The Exif IFD, if IFD0 points to one that can be read. -/
def exifIfd (t : Bytes) : Option Ifd :=
  match scan t with
  | some (le, _, s) => s.exifOff.bind (readIfd le t)
  | none => none

/-- The GPS IFD, if IFD0 points to one that can be read. -/
def gpsIfd (t : Bytes) : Option Ifd :=
  match scan t with
  | some (le, _, s) => s.gpsOff.bind (readIfd le t)
  | none => none

/-- What the reader gives: fields, location, and the GPS IFD it found. -/
structure TiffRead where
  fields : List (String × Val)
  location : Option Loc
  gps : Option Ifd

/-- The JS `readTiff`. -/
def readTiff (t : Bytes) : TiffRead :=
  match scan t with
  | none => { fields := [], location := none, gps := none }
  | some (le, _, s) =>
    { fields := cleanup (match exifIfd t with
        | some e => (view t e).foldl (scanExif le) s.fields
        | none => s.fields)
      location := match gpsIfd t with
        | some g => location le (view t g)
        | none => none
      gps := gpsIfd t }

/-! ## Emptying the GPS IFD -/

/-- Is `i` in one of the ranges `(start, length)`? -/
def inRanges (rs : List (Nat × Nat)) (i : Nat) : Bool := rs.any fun r => r.1 ≤ i && i < r.1 + r.2

/-- Set every byte in the ranges to 0; copy the rest. -/
def zeroAt (rs : List (Nat × Nat)) (t : Bytes) : Bytes :=
  t.mapIdx fun i b => if inRanges rs i then 0 else b

/-- The bytes the JS `emptyGps` sets to 0: the GPS IFD's count and table,
and each GPS entry's value bytes. -/
def zeroRanges (t : Bytes) : List (Nat × Nat) :=
  match gpsIfd t with
  | none => []
  | some g => (g.off, 2 + 12 * g.n) :: g.entries.map fun x => (x.valAt, x.bytes)

/-- Empty the GPS IFD (the JS `emptyGps`). -/
def emptyGps (t : Bytes) : Bytes := zeroAt (zeroRanges t) t

/-- The bytes the rest of the structure is read from: the header, the IFD0
table and its entries' windows, the Exif IFD table and its entries'
windows. -/
def keepRanges (t : Bytes) : List (Nat × Nat) :=
  match ifd0 t with
  | none => [(0, 8)]
  | some (le, g) =>
    let s := (view t g).foldl (scan0 le) {}
    (0, 8) :: tableAt le t g.off :: g.entries.map winRange ++
      (match s.exifOff with
       | none => []
       | some eo =>
         tableAt le t eo :: (match readIfd le t eo with
           | some e => e.entries.map winRange
           | none => []))

/-- Two ranges do not overlap (an empty range overlaps nothing). -/
def apart (r z : Nat × Nat) : Bool :=
  r.2 == 0 || z.2 == 0 || r.1 + r.2 ≤ z.1 || z.1 + z.2 ≤ r.1

/-- The disjointness condition: no byte that `emptyGps` zeroes is a byte the
rest of the structure is read from. -/
def disjoint (t : Bytes) : Bool :=
  (keepRanges t).all fun r => (zeroRanges t).all fun z => apart r z

/-! ## Reading stays in bounds -/

/-- A two-byte read succeeds only when both bytes are inside the block. -/
theorem u16_some {le : Bool} {t : Bytes} {o v : Nat} (h : u16 le t o = some v) :
    o + 1 < t.length := by
  unfold u16 at h
  cases h1 : t[o + 1]? with
  | none => rw [h1] at h; split at h <;> simp_all
  | some b => exact (List.getElem?_eq_some_iff.mp h1).1

/-- A four-byte read succeeds only when all four bytes are inside the block. -/
theorem u32_some {le : Bool} {t : Bytes} {o v : Nat} (h : u32 le t o = some v) :
    o + 3 < t.length := by
  unfold u32 at h
  cases h2 : u16 le t (o + 2) with
  | none => rw [h2] at h; split at h <;> simp_all
  | some b => have := u16_some h2; omega

/-- A window byte is the block's byte at the window's offset plus its
position, and nothing past the window's length: every value the reader
decodes is read at an index `valAt + j` of the block, through `t[_]?`. -/
theorem slice_getElem? (t : Bytes) (r : Nat × Nat) (j : Nat) :
    (slice t r)[j]? = if j < r.2 then t[r.1 + j]? else none := by
  simp [slice, List.getElem?_take, List.getElem?_drop]

/-- An entry that is read has its 8 header bytes and its whole value inside
the block, and a value of at most 1 MiB. -/
theorem readEntry_some {le : Bool} {t : Bytes} {e : Nat} {x : Entry}
    (h : readEntry le t e = some x) :
    x.entry = e ∧ e + 8 ≤ t.length ∧ x.valAt + x.bytes ≤ t.length ∧ x.bytes ≤ maxValue ∧
      x.bytes = typeSize x.type * x.count := by
  unfold readEntry at h
  cases h3 : u32 le t (e + 4) with
  | none => rw [h3] at h; split at h <;> simp_all
  | some c =>
    have hb := u32_some h3
    rw [h3] at h
    split at h
    · rename_i tag ty cnt _ _ hc
      cases hc
      split at h
      · simp at h
      · rename_i hz
        split at h
        · rename_i a _
          split at h
          · rename_i hle
            cases h
            simp only [not_or, Nat.not_lt] at hz
            exact ⟨rfl, by omega, hle, hz.2, rfl⟩
          · simp at h
        · simp at h
    · simp at h

/-- An entry whose value would end past the block is skipped. -/
theorem readEntry_past_end {le : Bool} {t : Bytes} {e a : Nat} {x : Entry}
    (h : readEntry le t e = some x) (ha : x.valAt = a) : a + x.bytes ≤ t.length := by
  have := (readEntry_some h).2.2.1; omega

/-- An IFD that is read: at its offset, a count of at most 512, at most that
many entries, each inside the block. -/
theorem readIfd_some {le : Bool} {t : Bytes} {off : Nat} {g : Ifd}
    (h : readIfd le t off = some g) :
    g.off = off ∧ u16 le t off = some g.n ∧ g.n ≤ maxEntries ∧ g.entries.length ≤ g.n ∧
      ∀ x ∈ g.entries, x.valAt + x.bytes ≤ t.length ∧ x.bytes ≤ maxValue := by
  unfold readIfd at h
  cases hn : u16 le t off with
  | none => rw [hn] at h; simp at h
  | some n =>
    rw [hn] at h
    simp only at h
    split at h
    · simp at h
    · rename_i hle
      cases h
      refine ⟨rfl, rfl, by simp only; omega, ?_, ?_⟩
      · exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)
      · intro x hx
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hx
        have := readEntry_some hi
        exact ⟨this.2.2.1, this.2.2.2.1⟩

/-- A text field has at most 512 bytes. -/
theorem ascii_length {x : Entry} {w b : Bytes} (h : ascii x w = some (.text b)) :
    b.length ≤ maxString := by
  simp only [ascii, Option.some.injEq, Val.text.injEq] at h
  subst h; simp; omega

/-! ## Agreement: what a read depends on -/

/-- `t'` has the same bytes as `t` at every index in `[a, a + n)`. -/
def Agree (t t' : Bytes) (a n : Nat) : Prop := ∀ i, a ≤ i → i < a + n → t'[i]? = t[i]?

/-- Agreement on a range gives agreement on every range inside it. -/
theorem Agree.mono {t t' : Bytes} {a n b m : Nat} (h : Agree t t' a n) (h1 : a ≤ b)
    (h2 : b + m ≤ a + n) : Agree t t' b m := fun i hi hi' => h i (by omega) (by omega)

/-- A two-byte read depends only on its two bytes. -/
theorem u16_congr {le : Bool} {t t' : Bytes} {o : Nat} (h : Agree t t' o 2) :
    u16 le t' o = u16 le t o := by
  unfold u16; rw [h o (by omega) (by omega), h (o + 1) (by omega) (by omega)]

/-- A four-byte read depends only on its four bytes. -/
theorem u32_congr {le : Bool} {t t' : Bytes} {o : Nat} (h : Agree t t' o 4) :
    u32 le t' o = u32 le t o := by
  unfold u32
  rw [u16_congr (h.mono (Nat.le_refl _) (by omega)), u16_congr (h.mono (by omega) (by omega))]

/-- A window depends only on the bytes in its range. -/
theorem slice_congr {t t' : Bytes} {r : Nat × Nat} (h : Agree t t' r.1 r.2) :
    slice t' r = slice t r := by
  apply List.ext_getElem?
  intro j
  rw [slice_getElem?, slice_getElem?]
  split
  · exact h _ (by omega) (by omega)
  · rfl

/-- Reading an entry depends only on the length of the block and the entry's 12 bytes (the value bytes are not read here). -/
theorem readEntry_congr {le : Bool} {t t' : Bytes} {e : Nat} (hl : t'.length = t.length)
    (h : Agree t t' e 12) : readEntry le t' e = readEntry le t e := by
  have h1 : u16 le t' e = u16 le t e := u16_congr (h.mono (Nat.le_refl _) (by omega))
  have h2 : u16 le t' (e + 2) = u16 le t (e + 2) := u16_congr (h.mono (by omega) (by omega))
  have h3 : u32 le t' (e + 4) = u32 le t (e + 4) := u32_congr (h.mono (by omega) (by omega))
  have h4 : u32 le t' (e + 8) = u32 le t (e + 8) := u32_congr (h.mono (by omega) (by omega))
  simp only [readEntry, h1, h2, h3, h4, hl]

/-- `filterMap` gives the same list for two functions that agree on the list's elements. -/
theorem filterMap_congr_mem {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h a (by simp),
      filterMap_congr_mem (fun b hb => h b (by simp [hb]))]

/-- Reading an IFD depends only on the length of the block and the bytes of its count and table. -/
theorem readIfd_congr {le : Bool} {t t' : Bytes} {off : Nat} (hl : t'.length = t.length)
    (h : Agree t t' (tableAt le t off).1 (tableAt le t off).2) :
    readIfd le t' off = readIfd le t off := by
  simp only [tableAt] at h
  have h0 : u16 le t' off = u16 le t off := u16_congr (h.mono (Nat.le_refl _) (by omega))
  unfold readIfd
  rw [h0]
  cases hn : u16 le t off with
  | none => rfl
  | some n =>
    rw [hn] at h
    simp only [Option.getD_some] at h
    simp only
    split
    · rfl
    · congr 2
      apply filterMap_congr_mem
      intro i hi
      have hi' := List.mem_range.mp hi
      exact readEntry_congr hl (h.mono (by omega) (by omega))

/-- The entries' windows depend only on the bytes in the windows. -/
theorem view_congr {t t' : Bytes} {g : Ifd}
    (h : ∀ x ∈ g.entries, Agree t t' (winRange x).1 (winRange x).2) : view t' g = view t g := by
  unfold view
  apply List.map_congr_left
  intro x hx
  simp only [win, slice_congr (h x hx)]

/-- The header check depends only on the length and the first 8 bytes. -/
theorem header_congr {t t' : Bytes} (hl : t'.length = t.length) (h : Agree t t' 0 8) :
    header t' = header t := by
  have e0 := h 0 (by omega) (by omega)
  have e1 := h 1 (by omega) (by omega)
  have e2 : ∀ le, u16 le t' 2 = u16 le t 2 := fun _ => u16_congr (h.mono (by omega) (by omega))
  simp only [header, hl, e0, e1, e2]

/-! ## Zeroing -/

theorem getElem?_zeroAt (rs : List (Nat × Nat)) (t : Bytes) (i : Nat) :
    (zeroAt rs t)[i]? = t[i]?.map fun b => if inRanges rs i then 0 else b := by
  simp [zeroAt, List.getElem?_mapIdx]

/-- Zeroing keeps the length. -/
theorem length_zeroAt (rs : List (Nat × Nat)) (t : Bytes) : (zeroAt rs t).length = t.length := by
  simp [zeroAt]

/-- Zeroing no ranges changes nothing. -/
theorem zeroAt_nil (t : Bytes) : zeroAt [] t = t := by
  apply List.ext_getElem?; intro i
  rw [getElem?_zeroAt]; cases t[i]? <;> simp [inRanges]

/-- Zeroing a sub-range of what was already zeroed changes nothing. -/
theorem zeroAt_zeroAt_sub {rs rs' : List (Nat × Nat)} (t : Bytes)
    (hsub : ∀ i, inRanges rs' i = true → inRanges rs i = true) :
    zeroAt rs' (zeroAt rs t) = zeroAt rs t := by
  apply List.ext_getElem?; intro i
  rw [getElem?_zeroAt, getElem?_zeroAt]
  cases t[i]? with
  | none => rfl
  | some b =>
    by_cases h : inRanges rs' i = true
    · simp [h, hsub i h]
    · simp at h; simp [h]

/-- An index inside a range that is apart from every zero range is not zeroed. -/
theorem inRanges_false_of_apart {zs : List (Nat × Nat)} {r : Nat × Nat}
    (h : ∀ z ∈ zs, apart r z = true) {i : Nat} (h1 : r.1 ≤ i) (h2 : i < r.1 + r.2) :
    inRanges zs i = false := by
  unfold inRanges
  cases hz : zs.any (fun r => r.1 ≤ i && i < r.1 + r.2) with
  | false => rfl
  | true =>
    obtain ⟨z, hz, hin⟩ := List.any_eq_true.mp hz
    have ha := h z hz
    simp only [apart, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    omega

/-- Emptying keeps the length. -/
theorem emptyGps_length (t : Bytes) : (emptyGps t).length = t.length := length_zeroAt _ _

/-- Emptying changes only the bytes in the zero ranges, and sets them to 0.
This holds for every input. -/
theorem getElem?_emptyGps (t : Bytes) (i : Nat) :
    (emptyGps t)[i]? = if inRanges (zeroRanges t) i then t[i]?.map (fun _ => 0) else t[i]? := by
  rw [emptyGps, getElem?_zeroAt]
  split <;> simp_all

/-- When the reader finds no GPS IFD, emptying changes nothing. -/
theorem emptyGps_of_none {t : Bytes} (h : gpsIfd t = none) : emptyGps t = t := by
  simp [emptyGps, zeroRanges, h, zeroAt_nil]

/-- Under `disjoint`, emptying keeps every byte in every keep range. -/
theorem agree_of_disjoint {t : Bytes} (hd : disjoint t = true) {r : Nat × Nat}
    (hr : r ∈ keepRanges t) : Agree t (emptyGps t) r.1 r.2 := by
  intro i h1 h2
  have hz : inRanges (zeroRanges t) i = false := by
    unfold disjoint at hd
    exact inRanges_false_of_apart (fun z hz => List.all_eq_true.mp (List.all_eq_true.mp hd r hr) z hz) h1 h2
  rw [getElem?_emptyGps, hz]; rfl

/-! ## The structure is read the same after emptying (under `disjoint`) -/

theorem scan_some {t : Bytes} {le : Bool} {g : Ifd} {s : Scan} (h : scan t = some (le, g, s)) :
    ifd0 t = some (le, g) ∧ (view t g).foldl (scan0 le) {} = s := by
  unfold scan at h
  cases h0 : ifd0 t with
  | none => rw [h0] at h; simp at h
  | some p => rw [h0] at h; simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- The header is a keep range. -/
theorem keep_head {t : Bytes} : (0, 8) ∈ keepRanges t := by
  unfold keepRanges; split <;> simp

/-- IFD0's count and table are a keep range. -/
theorem keep_table {t : Bytes} {le : Bool} {g : Ifd} (h : ifd0 t = some (le, g)) :
    tableAt le t g.off ∈ keepRanges t := by
  simp [keepRanges, h]

/-- Each IFD0 entry's value window is a keep range. -/
theorem keep_win {t : Bytes} {le : Bool} {g : Ifd} (h : ifd0 t = some (le, g)) {x : Entry}
    (hx : x ∈ g.entries) : winRange x ∈ keepRanges t := by
  simp only [keepRanges, h]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hx)))

/-- The Exif IFD's count and table are a keep range. -/
theorem keep_exifTable {t : Bytes} {le : Bool} {g : Ifd} {eo : Nat} (h : ifd0 t = some (le, g))
    (he : ((view t g).foldl (scan0 le) {}).exifOff = some eo) : tableAt le t eo ∈ keepRanges t := by
  simp only [keepRanges, h, he]
  simp

/-- Each Exif IFD entry's value window is a keep range. -/
theorem keep_exifWin {t : Bytes} {le : Bool} {g e : Ifd} {eo : Nat} (h : ifd0 t = some (le, g))
    (he : ((view t g).foldl (scan0 le) {}).exifOff = some eo) (hr : readIfd le t eo = some e)
    {x : Entry} (hx : x ∈ e.entries) : winRange x ∈ keepRanges t := by
  simp only [keepRanges, h, he, hr]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_cons_of_mem _ (List.mem_map_of_mem hx))))

/-- Under `disjoint`, IFD0 is read the same after emptying. -/
theorem ifd0_emptyGps {t : Bytes} (hd : disjoint t = true) {le : Bool} {g : Ifd}
    (h : ifd0 t = some (le, g)) : ifd0 (emptyGps t) = some (le, g) := by
  have hl := emptyGps_length t
  have hh := header_congr hl (agree_of_disjoint hd keep_head)
  unfold ifd0 at h ⊢
  rw [hh]
  cases hhd : header t with
  | none => rw [hhd] at h; simp at h
  | some le' =>
    rw [hhd] at h
    simp only at h ⊢
    have h4 : u32 le' (emptyGps t) 4 = u32 le' t 4 :=
      u32_congr ((agree_of_disjoint hd keep_head).mono (by omega) (by omega))
    rw [h4]
    cases ho : u32 le' t 4 with
    | none => rw [ho] at h; simp at h
    | some o =>
      rw [ho] at h
      simp only at h ⊢
      cases hr : readIfd le' t o with
      | none => rw [hr] at h; simp at h
      | some g' =>
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hoff := (readIfd_some hr).1
        have hi0 : ifd0 t = some (le', g') := by simp [ifd0, hhd, ho, hr]
        have := agree_of_disjoint hd (keep_table hi0)
        rw [hoff] at this
        rw [readIfd_congr hl this, hr]; rfl

/-- Under `disjoint`, the IFD0 loop gives the same fields and pointers after emptying. -/
theorem scan_emptyGps {t : Bytes} (hd : disjoint t = true) {le : Bool} {g : Ifd} {s : Scan}
    (h : scan t = some (le, g, s)) : scan (emptyGps t) = some (le, g, s) := by
  obtain ⟨hi, hs⟩ := scan_some h
  have hv : view (emptyGps t) g = view t g :=
    view_congr fun x hx => agree_of_disjoint hd (keep_win hi hx)
  simp [scan, ifd0_emptyGps hd hi, hv, hs]

/-- Under `disjoint`, the Exif IFD is read the same after emptying. -/
theorem exifIfd_emptyGps {t : Bytes} (hd : disjoint t = true) :
    exifIfd (emptyGps t) = exifIfd t := by
  cases hs : scan t with
  | none =>
    have : gpsIfd t = none := by simp [gpsIfd, hs]
    rw [emptyGps_of_none this]
  | some p =>
    obtain ⟨le, g, s⟩ := p
    obtain ⟨hi, hsf⟩ := scan_some hs
    simp only [exifIfd, scan_emptyGps hd hs, hs]
    cases he : s.exifOff with
    | none => rfl
    | some eo =>
      simp only [Option.bind_some]
      rw [← hsf] at he
      exact readIfd_congr (emptyGps_length t) (agree_of_disjoint hd (keep_exifTable hi he))

/-- A two-byte read of 0 means both bytes are 0. -/
theorem u16_zero {le : Bool} {t : Bytes} {o : Nat} (h : u16 le t o = some 0) :
    t[o]? = some 0 ∧ t[o + 1]? = some 0 := by
  unfold u16 at h
  cases ha : t[o]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    cases hb : t[o + 1]? with
    | none => rw [ha, hb] at h; simp at h
    | some b =>
      rw [ha, hb] at h
      simp only [Option.some.injEq] at h
      have h' : a.toNat = 0 ∧ b.toNat = 0 := by split at h <;> omega
      have ha0 : a = 0 := UInt8.toNat_inj.mp (by rw [h'.1]; rfl)
      have hb0 : b = 0 := UInt8.toNat_inj.mp (by rw [h'.2]; rfl)
      exact ⟨by rw [ha0], by rw [hb0]⟩

/-- After emptying (under `disjoint`), the reader still finds the GPS IFD
at the same offset, now with count 0 and no entries. -/
theorem readTiff_emptyGps_gps {t : Bytes} (hd : disjoint t = true) {gg : Ifd}
    (h : gpsIfd t = some gg) : gpsIfd (emptyGps t) = some { off := gg.off, n := 0, entries := [] } := by
  cases hs : scan t with
  | none => simp [gpsIfd, hs] at h
  | some p =>
    obtain ⟨le, g, s⟩ := p
    have h' := h
    simp only [gpsIfd, hs] at h'
    cases ho : s.gpsOff with
    | none => rw [ho] at h'; simp at h'
    | some o =>
      rw [ho] at h'
      simp only [Option.bind_some] at h'
      obtain ⟨hoff, hn, -, -, -⟩ := readIfd_some h'
      have hb := u16_some hn
      have hz : ∀ i, o ≤ i → i < o + 2 → (emptyGps t)[i]? = some 0 := by
        intro i h1 h2
        have hin : inRanges (zeroRanges t) i = true := by
          simp only [zeroRanges, h, inRanges, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
            decide_eq_true_eq]
          left; omega
        rw [getElem?_emptyGps, hin]
        simp only
        rw [List.getElem?_eq_getElem (by omega)]; rfl
      have h16 : u16 le (emptyGps t) o = some 0 := by
        simp [u16, hz o (by omega) (by omega), hz (o + 1) (by omega) (by omega)]
      simp only [gpsIfd, scan_emptyGps hd hs, ho, Option.bind_some, readIfd, h16]
      simp [maxEntries, hoff]

/-- A GPS IFD with no entries gives no location. -/
theorem location_nil (le : Bool) : location le [] = none := by
  simp [location, deg, findTag]

/-- **No place after emptying** (under `disjoint`): the reader finds no
location in the emptied block, whatever location the input had. -/
theorem readTiff_emptyGps_location {t : Bytes} (hd : disjoint t = true) :
    (readTiff (emptyGps t)).location = none := by
  cases hg : gpsIfd t with
  | none =>
    rw [emptyGps_of_none hg]
    unfold readTiff; split
    · rfl
    · simp [hg]
  | some gg =>
    have := readTiff_emptyGps_gps hd hg
    unfold readTiff; split
    · rfl
    · simp [this, view, location_nil]

/-- **Other fields kept** (under `disjoint`): every field other than the
location (make, model, orientation, dates, width, height) is read the same
from the emptied block as from the input. -/
theorem readTiff_emptyGps_fields {t : Bytes} (hd : disjoint t = true) :
    (readTiff (emptyGps t)).fields = (readTiff t).fields := by
  cases hs : scan t with
  | none =>
    have : gpsIfd t = none := by simp [gpsIfd, hs]
    rw [emptyGps_of_none this]
  | some p =>
    obtain ⟨le, g, s⟩ := p
    obtain ⟨hi, hsf⟩ := scan_some hs
    simp only [readTiff, scan_emptyGps hd hs, hs, exifIfd_emptyGps hd]
    cases he : exifIfd t with
    | none => rfl
    | some e =>
      simp only
      congr 2
      apply view_congr
      intro x hx
      simp only [exifIfd, hs] at he
      cases heo : s.exifOff with
      | none => rw [heo] at he; simp at he
      | some eo =>
        rw [heo] at he
        simp only [Option.bind_some] at he
        rw [← hsf] at heo
        exact agree_of_disjoint hd (keep_exifWin hi heo he hx)

/-- **Idempotent** (under `disjoint`): emptying an emptied block changes
nothing. -/
theorem emptyGps_idem {t : Bytes} (hd : disjoint t = true) :
    emptyGps (emptyGps t) = emptyGps t := by
  cases hg : gpsIfd t with
  | none => rw [emptyGps_of_none hg, emptyGps_of_none hg]
  | some gg =>
    have h2 := readTiff_emptyGps_gps hd hg
    have hz : zeroRanges (emptyGps t) = [(gg.off, 2)] := by simp [zeroRanges, h2]
    show zeroAt (zeroRanges (emptyGps t)) (emptyGps t) = emptyGps t
    rw [hz]
    unfold emptyGps
    apply zeroAt_zeroAt_sub
    intro i hi
    simp only [inRanges, List.any_cons, List.any_nil, Bool.or_false, Bool.and_eq_true,
      decide_eq_true_eq] at hi
    simp only [zeroRanges, hg, inRanges, List.any_cons, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    left; omega

/-! ## The checked variant: no hypothesis -/

/-- After emptying, is the block quiet: no GPS IFD is found, or the one
found declares 0 entries? -/
def quiet (t : Bytes) : Bool :=
  match gpsIfd t with
  | none => true
  | some g => g.n == 0

/-- A GPS IFD that is found was read by `readIfd` at some offset and byte order. -/
theorem gpsIfd_some {t : Bytes} {g : Ifd} (h : gpsIfd t = some g) :
    ∃ le o, readIfd le t o = some g := by
  unfold gpsIfd at h
  split at h
  · rename_i le _ s _
    cases ho : s.gpsOff with
    | none => rw [ho] at h; simp at h
    | some o => rw [ho] at h; exact ⟨le, o, h⟩
  · simp at h

/-- A quiet block has no location. -/
theorem quiet_location {t : Bytes} (hq : quiet t = true) : (readTiff t).location = none := by
  unfold readTiff; split
  · rfl
  · simp only
    cases hg : gpsIfd t with
    | none => rfl
    | some g =>
      simp only [quiet, hg, beq_iff_eq] at hq
      obtain ⟨le, o, hr⟩ := gpsIfd_some hg
      have hlen := (readIfd_some hr).2.2.2.1
      have : g.entries = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [view, this, location_nil]

/-- Emptying a quiet block changes nothing. -/
theorem emptyGps_quiet {t : Bytes} (hq : quiet t = true) : emptyGps t = t := by
  cases hg : gpsIfd t with
  | none => exact emptyGps_of_none hg
  | some g =>
    simp only [quiet, hg, beq_iff_eq] at hq
    obtain ⟨le, o, hr⟩ := gpsIfd_some hg
    obtain ⟨hoff, hn, -, hlen, -⟩ := readIfd_some hr
    have he : g.entries = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hq] at hn
    obtain ⟨z0, z1⟩ := u16_zero hn
    apply List.ext_getElem?; intro i
    rw [getElem?_emptyGps]
    split
    · rename_i hin
      simp only [zeroRanges, hg, he, hq, List.map_nil, inRanges, List.any_cons, List.any_nil,
        Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at hin
      rw [hoff] at hin
      have : i = o ∨ i = o + 1 := by omega
      rcases this with rfl | rfl
      · rw [z0]; rfl
      · rw [z1]; rfl
    · rfl

/-- Under `disjoint`, the emptied block is quiet. -/
theorem quiet_emptyGps {t : Bytes} (hd : disjoint t = true) : quiet (emptyGps t) = true := by
  cases hg : gpsIfd t with
  | none => rw [emptyGps_of_none hg]; simp [quiet, hg]
  | some gg => simp [quiet, readTiff_emptyGps_gps hd hg]

/-! ## Files -/

/-- The kinds `withoutLocation` treats: JPEG, PNG, and everything else
(copied unchanged). -/
inductive Kind
  | jpeg | png | other
  deriving DecidableEq, Repr

/-- A segment of a JPEG (up to the image data) or a chunk of a PNG. -/
inductive Seg
  /-- EXIF: JPEG APP1 starting `Exif\0\0`, or PNG `eXIf` (with its CRC). -/
  | exif (tiff : Bytes) (crc : Option UInt32)
  /-- XMP: JPEG APP1 with the XMP header, or PNG `iTXt`/`tEXt` keyed
  `XML:com.adobe.xmp`. -/
  | xmp (body : Bytes)
  /-- Anything else, byte for byte: image data, SOF, IHDR, other text. -/
  | other (tag : Nat) (body : Bytes)
  deriving DecidableEq, Repr

/-- Is this an XMP segment? -/
def Seg.isXmp : Seg → Bool
  | .xmp _ => true
  | _ => false

/-- Is this an EXIF segment? -/
def Seg.isExif : Seg → Bool
  | .exif _ _ => true
  | _ => false

/-- Is this a segment that is neither EXIF nor XMP? -/
def Seg.isOther : Seg → Bool
  | .other _ _ => true
  | _ => false

/-- A file: its kind (from its first bytes) and its segments in order. -/
structure File where
  kind : Kind
  segs : List Seg
  deriving DecidableEq, Repr

/-- One CRC-32 bit step (polynomial 0xEDB88320). -/
def crcStep (c : UInt32) : UInt32 := if c &&& 1 = 1 then (0xedb88320 : UInt32) ^^^ (c >>> 1) else c >>> 1

/-- CRC-32 of a byte list, as PNG uses (the JS `crc32`, bit by bit instead of
by table). -/
def crc32 (bs : Bytes) : UInt32 :=
  (bs.foldl (fun c b => (List.range 8).foldl (fun c _ => crcStep c) (c ^^^ b.toUInt32))
    (0xffffffff : UInt32)) ^^^ 0xffffffff

/-- The CRC of a PNG `eXIf` chunk: over the type and the data. -/
def exifCrc (t : Bytes) : UInt32 := crc32 ([0x65, 0x58, 0x49, 0x66] ++ t)

/-- `withoutLocation` on one segment: EXIF emptied (and a PNG CRC
recomputed), XMP dropped, everything else kept. -/
def stripSeg : Seg → Option Seg
  | .exif t c => some (.exif (emptyGps t) (c.map fun _ => exifCrc (emptyGps t)))
  | .xmp _ => none
  | .other k b => some (.other k b)

/-- The JS `withoutLocation`. -/
def strip (f : File) : File :=
  if f.kind = .other then f else { f with segs := f.segs.filterMap stripSeg }

/-- The checked variant on one segment: an EXIF segment that is not quiet
after emptying is dropped whole. -/
def stripCheckedSeg : Seg → Option Seg
  | .exif t c =>
    if quiet (emptyGps t) then some (.exif (emptyGps t) (c.map fun _ => exifCrc (emptyGps t)))
    else none
  | .xmp _ => none
  | .other k b => some (.other k b)

/-- The checked variant of `withoutLocation` (not in the JS). -/
def stripChecked (f : File) : File :=
  if f.kind = .other then f else { f with segs := f.segs.filterMap stripCheckedSeg }

/-- Fields from a segment that is not EXIF or XMP (SOF, IHDR, PNG text, ID3
frames, a PDF Info dictionary): any function of its tag and bytes. -/
abbrev Decoder := Nat → Bytes → List (String × Val)

/-- The fields one segment gives. The reader takes none from XMP. -/
def segFields (dec : Decoder) : Seg → List (String × Val)
  | .exif t _ => (readTiff t).fields
  | .xmp _ => []
  | .other k b => dec k b

/-- The location one segment gives. -/
def segLoc : Seg → Option Loc
  | .exif t _ => (readTiff t).location
  | _ => none

/-- PNG merges EXIF fields with `??=` (earlier fields win); everything else
with `=` / `Object.assign` (later fields win). -/
def keepOld (k : Kind) (s : Seg) : Bool := k == .png && s.isExif

/-- Merge one segment's fields into the fields so far. -/
def merge (old : Bool) (acc new : List (String × Val)) : List (String × Val) :=
  if old then acc ++ new.filter fun p => !(acc.any fun q => q.1 == p.1)
  else new ++ acc.filter fun p => !(new.any fun q => q.1 == p.1)

/-- What a file says about itself: fields and location (the JS
`readMetadata`; the location is the first one found, `??=`). -/
structure FileMeta where
  fields : List (String × Val)
  location : Option Loc

/-- The JS `readMetadata`, on the segment model. -/
def readFile (dec : Decoder) (f : File) : FileMeta :=
  { fields := f.segs.foldl (fun acc s => merge (keepOld f.kind s) acc (segFields dec s)) []
    location := if f.kind = .other then none else (f.segs.filterMap segLoc).head? }

/-- Every EXIF segment of the file satisfies `disjoint`. -/
def WellFormed (f : File) : Prop := ∀ t c, Seg.exif t c ∈ f.segs → disjoint t = true

/-- Folding over `filterMap g l` is folding over `l` when each dropped element is a no-op step and each changed element is an equal step. -/
theorem foldl_filterMap_mem {α β : Type} {step : β → α → β} {g : α → Option α} :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, match g a with
      | none => step b a = b | some a' => step b a' = step b a) →
      ∀ (b : β), (l.filterMap g).foldl step b = l.foldl step b
  | [], _, _ => rfl
  | a :: l, hs, b => by
    have h := hs a (by simp) b
    have ih := foldl_filterMap_mem l (fun x hx => hs x (by simp [hx]))
    rw [List.filterMap_cons]
    revert h
    cases g a with
    | none => intro h; simp only [List.foldl_cons, h]; exact ih b
    | some a' => intro h; simp only [List.foldl_cons, h]; exact ih _

/-- Merging no fields changes nothing (so a dropped XMP segment does not change the fields). -/
theorem merge_nil (old : Bool) (acc : List (String × Val)) : merge old acc [] = acc := by
  cases old <;> simp [merge]

/-- **No place after stripping** (under `disjoint` for each EXIF segment):
the reader finds no location in `strip f`. -/
theorem strip_no_location (dec : Decoder) {f : File} (hw : WellFormed f) :
    (readFile dec (strip f)).location = none := by
  unfold strip
  split
  · simp [readFile, *]
  · rename_i hk
    simp only [readFile, hk, if_false]
    rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]
    intro s hs
    obtain ⟨s0, hs0, he⟩ := List.mem_filterMap.mp hs
    cases s0 with
    | exif t c =>
      simp only [stripSeg, Option.some.injEq] at he; subst he
      exact readTiff_emptyGps_location (hw t c hs0)
    | xmp b => simp [stripSeg] at he
    | other k b => simp only [stripSeg, Option.some.injEq] at he; subst he; rfl

/-- **Other fields kept** (under `disjoint` for each EXIF segment): `strip f`
gives the same fields as `f`. -/
theorem strip_keeps_fields (dec : Decoder) {f : File} (hw : WellFormed f) :
    (readFile dec (strip f)).fields = (readFile dec f).fields := by
  unfold strip
  split
  · rfl
  · simp only [readFile]
    apply foldl_filterMap_mem
    intro s hs b
    cases s with
    | exif t c =>
      simp only [stripSeg, keepOld, Seg.isExif, segFields, readTiff_emptyGps_fields (hw t c hs)]
    | xmp x => simp [stripSeg, segFields, merge_nil]
    | other k x => simp [stripSeg]

/-- **Idempotent** (under `disjoint` for each EXIF segment). -/
theorem strip_idem {f : File} (hw : WellFormed f) : strip (strip f) = strip f := by
  unfold strip
  split
  · simp [*]
  · rename_i hk
    simp only [File.mk.injEq, true_and]
    rw [List.filterMap_filterMap]
    apply filterMap_congr_mem
    intro s hs
    cases s with
    | exif t c => simp [stripSeg, emptyGps_idem (hw t c hs), Option.map_map, Function.comp_def]
    | xmp x => simp [stripSeg]
    | other k x => simp [stripSeg]

/-- **No XMP left** (every input): a stripped JPEG or PNG has no XMP segment. -/
theorem strip_no_xmp {f : File} (hk : f.kind ≠ .other) : ∀ s ∈ (strip f).segs, s.isXmp = false := by
  intro s hs
  simp only [strip, hk, if_false] at hs
  obtain ⟨s0, -, he⟩ := List.mem_filterMap.mp hs
  cases s0 <;> simp [stripSeg] at he <;> subst he <;> rfl

/-- **Image data untouched** (every input): the segments that are neither
EXIF nor XMP are the same, in the same order, byte for byte. -/
theorem strip_keeps_other (f : File) : (strip f).segs.filter Seg.isOther = f.segs.filter Seg.isOther := by
  unfold strip
  split
  · rfl
  · simp only
    induction f.segs with
    | nil => rfl
    | cons s ss ih => cases s <;> simp [List.filterMap_cons, List.filter_cons, stripSeg, Seg.isOther, ih]

/-- **PNG CRC** (every input): each EXIF segment with a CRC in a stripped
JPEG or PNG has the CRC of its new bytes. -/
theorem strip_png_crc {f : File} (hk : f.kind ≠ .other) :
    ∀ t c, Seg.exif t (some c) ∈ (strip f).segs → c = exifCrc t := by
  intro t c hs
  simp only [strip, hk, if_false] at hs
  obtain ⟨s0, -, he⟩ := List.mem_filterMap.mp hs
  cases s0 with
  | exif t0 c0 =>
    simp only [stripSeg, Option.some.injEq, Seg.exif.injEq] at he
    obtain ⟨rfl, h2⟩ := he
    cases c0 <;> simp_all
  | xmp _ => simp [stripSeg] at he
  | other _ _ => simp [stripSeg] at he

/-- A file of another kind (MP3, PDF, unknown) is copied unchanged. -/
theorem strip_other_kind {f : File} (hk : f.kind = .other) : strip f = f := by
  simp [strip, hk]

/-- **No place after the checked strip**, for every input, crafted or not. -/
theorem stripChecked_no_location (dec : Decoder) (f : File) :
    (readFile dec (stripChecked f)).location = none := by
  unfold stripChecked
  split
  · simp [readFile, *]
  · rename_i hk
    simp only [readFile, hk, if_false]
    rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]
    intro s hs
    obtain ⟨s0, -, he⟩ := List.mem_filterMap.mp hs
    cases s0 with
    | exif t c =>
      simp only [stripCheckedSeg] at he
      split at he
      · rename_i hq; simp only [Option.some.injEq] at he; subst he; exact quiet_location hq
      · simp at he
    | xmp b => simp [stripCheckedSeg] at he
    | other k b => simp only [stripCheckedSeg, Option.some.injEq] at he; subst he; rfl

/-- **The checked strip is idempotent**, for every input. -/
theorem stripChecked_idem (f : File) : stripChecked (stripChecked f) = stripChecked f := by
  unfold stripChecked
  split
  · simp [*]
  · rename_i hk
    simp only [File.mk.injEq, true_and]
    rw [List.filterMap_filterMap]
    apply filterMap_congr_mem
    intro s _
    cases s with
    | exif t c =>
      simp only [stripCheckedSeg]
      split
      · rename_i hq
        simp [stripCheckedSeg, emptyGps_quiet hq, hq, Option.map_map, Function.comp_def]
      · rfl
    | xmp x => simp [stripCheckedSeg]
    | other k x => simp [stripCheckedSeg]

/-- Under `disjoint`, the checked strip is the JS strip: the check never
drops a segment of a file that satisfies it. -/
theorem stripChecked_eq_strip {f : File} (hw : WellFormed f) : stripChecked f = strip f := by
  unfold stripChecked strip
  split
  · rfl
  · simp only [File.mk.injEq, true_and]
    apply filterMap_congr_mem
    intro s hs
    cases s with
    | exif t c => simp [stripCheckedSeg, stripSeg, quiet_emptyGps (hw t c hs)]
    | xmp x => rfl
    | other k x => rfl

/-- The checked strip leaves no XMP segment in a JPEG or PNG. -/
theorem stripChecked_no_xmp {f : File} (hk : f.kind ≠ .other) :
    ∀ s ∈ (stripChecked f).segs, s.isXmp = false := by
  intro s hs
  simp only [stripChecked, hk, if_false] at hs
  obtain ⟨s0, -, he⟩ := List.mem_filterMap.mp hs
  cases s0 with
  | exif t c =>
    simp only [stripCheckedSeg] at he
    split at he
    · simp only [Option.some.injEq] at he; subst he; rfl
    · simp at he
  | xmp _ => simp [stripCheckedSeg] at he
  | other _ _ => simp only [stripCheckedSeg, Option.some.injEq] at he; subst he; rfl

/-- The checked strip keeps the segments that are neither EXIF nor XMP,
byte for byte, in order. -/
theorem stripChecked_keeps_other (f : File) :
    (stripChecked f).segs.filter Seg.isOther = f.segs.filter Seg.isOther := by
  unfold stripChecked
  split
  · rfl
  · simp only
    induction f.segs with
    | nil => rfl
    | cons s ss ih =>
      cases s with
      | exif t c =>
        by_cases hq : quiet (emptyGps t) = true <;>
          simp [stripCheckedSeg, hq, Seg.isOther, ih]
      | xmp _ => simp [List.filterMap_cons, stripCheckedSeg, Seg.isOther, ih]
      | other _ _ => simp [List.filter_cons, stripCheckedSeg, Seg.isOther, ih]

/-! ## The share rule -/

/-- A share: the one path it reaches, and whether it may write. -/
structure Share where
  path : String
  write : Bool

/-- Who reads: the owner, or an app through a share. -/
inductive Who
  | owner
  | share (sh : Share)

/-- The owner's stored files, by path. -/
abbrev Store := List (String × File)

/-- The file stored at `p`. -/
def lookup (s : Store) (p : String) : Option File := (s.find? fun e => e.1 == p).map (·.2)

/-- Store `f` at `p`, replacing what was there. -/
def store (s : Store) (p : String) (f : File) : Store := (p, f) :: s.filter fun e => e.1 != p

/-- The path a request reaches: a share reaches its own path, whatever path
the app sends. -/
def target : Who → String → String
  | .owner, p => p
  | .share sh, _ => sh.path

/-- What a reader is given from a stored file. -/
def shown : Who → File → File
  | .owner, f => f
  | .share _, f => strip f

/-- The owner is shown the file as stored. -/
theorem shown_owner : shown .owner = id := funext fun _ => rfl
/-- A share is shown `strip` of the file. -/
theorem shown_share (sh : Share) : shown (.share sh) = strip := funext fun _ => rfl

/-- What a reader is given from a file's metadata. -/
def hide : Who → FileMeta → FileMeta
  | .owner, m => m
  | .share _, m => { m with location := none }

/-- A request: `pod.get`, `pod.meta` (here `describe`), `pod.put`. -/
inductive Req
  | get (p : String)
  | describe (p : String)
  | put (p : String) (f : File)

/-- Is this a read? -/
def Req.isRead : Req → Bool
  | .put _ _ => false
  | _ => true

/-- A response. -/
inductive Resp
  | file (f : Option File)
  | info (m : Option FileMeta)
  | done
  | refused

/-- Serve one request: the new store and the response. -/
def handle (dec : Decoder) (s : Store) (who : Who) : Req → Store × Resp
  | .get p => (s, .file ((lookup s (target who p)).map (shown who)))
  | .describe p => (s, .info ((lookup s (target who p)).map fun f => hide who (readFile dec f)))
  | .put p f =>
    match who with
    | .owner => (store s p f, .done)
    | .share sh => if sh.write then (store s sh.path f, .done) else (s, .refused)

/-- Serve requests in order; the store at the end. -/
def run (dec : Decoder) (s : Store) (rs : List (Who × Req)) : Store :=
  rs.foldl (fun s r => (handle dec s r.1 r.2).1) s

/-- The owner reads the stored file as it is. -/
theorem owner_get (dec : Decoder) (s : Store) (p : String) :
    (handle dec s .owner (.get p)).2 = .file (lookup s p) := by
  simp [handle, target, shown_owner]

/-- A read through a share gives `strip` of the stored file at the shared
path, whatever path the app asked for. -/
theorem share_get (dec : Decoder) (s : Store) (sh : Share) (p : String) :
    (handle dec s (.share sh) (.get p)).2 = .file ((lookup s sh.path).map strip) := by
  simp [handle, target, shown_share]

/-- A file read through a share has no location (under `disjoint` for the
stored file's EXIF segments). -/
theorem share_get_no_location (dec : Decoder) {s : Store} {sh : Share} {p : String} {f' : File}
    (hw : ∀ f, lookup s sh.path = some f → WellFormed f)
    (h : (handle dec s (.share sh) (.get p)).2 = .file (some f')) :
    (readFile dec f').location = none := by
  rw [share_get] at h
  simp only [Resp.file.injEq] at h
  cases hl : lookup s sh.path with
  | none => rw [hl] at h; simp at h
  | some f =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact strip_no_location dec (hw f hl)

/-- `pod.meta` through a share gives no location, for every file. -/
theorem share_meta_no_location (dec : Decoder) {s : Store} {sh : Share} {p : String} {m : FileMeta}
    (h : (handle dec s (.share sh) (.describe p)).2 = .info (some m)) : m.location = none := by
  simp only [handle, target, Resp.info.injEq] at h
  cases hl : lookup s sh.path with
  | none => rw [hl] at h; simp at h
  | some f => rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; rfl

/-- `pod.meta` through a share gives the owner's fields for the shared path
and no location. -/
theorem share_meta_fields (dec : Decoder) (s : Store) (sh : Share) (p : String) :
    (handle dec s (.share sh) (.describe p)).2 =
      .info ((lookup s sh.path).map fun f => { readFile dec f with location := none }) := by
  simp [handle, target, hide]

/-- A read (by anyone) does not change the store. -/
theorem read_keeps (dec : Decoder) (s : Store) (who : Who) {r : Req} (hr : r.isRead = true) :
    (handle dec s who r).1 = s := by
  cases r <;> simp_all [handle, Req.isRead]

/-- Any sequence of reads leaves the store, and so the owner's files, as it
was. -/
theorem reads_keep (dec : Decoder) :
    ∀ (rs : List (Who × Req)) (s : Store), (∀ x ∈ rs, x.2.isRead = true) → run dec s rs = s
  | [], _, _ => rfl
  | x :: rs, s, h => by
    simp only [run, List.foldl_cons]
    rw [read_keeps dec s x.1 (h x (by simp))]
    exact reads_keep dec rs s (fun y hy => h y (by simp [hy]))

/-- The model is not read-only by refusing everything: the owner's write is
then read back. -/
theorem owner_put_get (dec : Decoder) (s : Store) (p : String) (f : File) :
    (handle dec (handle dec s .owner (.put p f)).1 .owner (.get p)).2 = .file (some f) := by
  simp [handle, target, shown, lookup, store]

/-- A read-only share may not write. -/
theorem share_put_readonly (dec : Decoder) (s : Store) {sh : Share} (hw : sh.write = false)
    (p : String) (f : File) : handle dec s (.share sh) (.put p f) = (s, .refused) := by
  simp [handle, hw]

/-! ## Examples -/

/-- Two bytes, little-endian. -/
def le16 (v : Nat) : Bytes := [v.toUInt8, (v / 256).toUInt8]
/-- Four bytes, little-endian. -/
def le32 (v : Nat) : Bytes := le16 (v % 65536) ++ le16 (v / 65536)
/-- A 12-byte IFD entry, little-endian. -/
def ent (tag type count val : Nat) : Bytes := le16 tag ++ le16 type ++ le32 count ++ le32 val
/-- Three rationals. -/
def rat3 (a b c : Nat) : Bytes := le32 a ++ le32 1 ++ le32 b ++ le32 1 ++ le32 c ++ le32 1

/-- A TIFF block as a camera writes it: IFD0 with make "Cam" and a GPS
pointer; a GPS IFD at 38 with N 51° 30′ 0″, E 0° 7′ 0″. -/
def cameraTiff : Bytes :=
  [0x49, 0x49] ++ le16 42 ++ le32 8 ++
  le16 2 ++ ent 0x010f 2 4 0x006d6143 ++ ent 0x8825 4 1 38 ++ le32 0 ++
  le16 4 ++ ent 1 2 2 0x4e ++ ent 2 5 3 92 ++ ent 3 2 2 0x45 ++ ent 4 5 3 116 ++ le32 0 ++
  rat3 51 30 0 ++ rat3 0 7 0

#guard cameraTiff.length == 140
#guard disjoint cameraTiff
#guard (readTiff cameraTiff).location.isSome
#guard (readTiff cameraTiff).fields == [("make", .text [0x43, 0x61, 0x6d, 0])]
-- A file with GPS: no location after emptying, the make is kept.
#guard (readTiff (emptyGps cameraTiff)).location.isNone
#guard (readTiff (emptyGps cameraTiff)).fields == (readTiff cameraTiff).fields
-- Emptying twice is emptying once.
#guard emptyGps (emptyGps cameraTiff) == emptyGps cameraTiff
-- The lat/lon rationals (bytes 92..139) are now zero; the make (bytes 18..21) is not.
#guard ((emptyGps cameraTiff).drop 92).all (· == 0)
#guard slice (emptyGps cameraTiff) (18, 4) == [0x43, 0x61, 0x6d, 0]

/-- A JPEG: APP0, EXIF, XMP, then the image data. -/
def cameraJpeg : File :=
  { kind := .jpeg,
    segs := [.other 0xe0 [0x4a, 0x46], .exif cameraTiff none, .xmp [0x3c, 0x78], .other 0xda [1, 2, 3]] }

/-- A decoder for the examples: no fields from other segments. -/
def noDec : Decoder := fun _ _ => []

#guard (readFile noDec cameraJpeg).location.isSome
#guard (readFile noDec (strip cameraJpeg)).location.isNone
#guard (strip cameraJpeg).segs.length == 3
#guard (strip cameraJpeg).segs.all (!·.isXmp)
#guard (strip cameraJpeg).segs.filter Seg.isOther == cameraJpeg.segs.filter Seg.isOther
#guard strip (strip cameraJpeg) == strip cameraJpeg
#guard stripChecked cameraJpeg == strip cameraJpeg

-- The PNG CRC: CRC-32 of "IEND" is 0xAE426082.
#guard crc32 [0x49, 0x45, 0x4e, 0x44] == 0xae426082
/-- The same EXIF block as a PNG `eXIf` chunk, with a wrong CRC. -/
def cameraPng : File := { kind := .png, segs := [.other 0 [], .exif cameraTiff (some 0)] }
#guard (strip cameraPng).segs == [.other 0 [], .exif (emptyGps cameraTiff) (some (exifCrc (emptyGps cameraTiff)))]

-- An entry whose value would lie past the end of the block is skipped.
#guard readEntry true (ent 2 5 3 1000) 0 == none
#guard (readIfd true (le16 1 ++ ent 2 5 3 1000) 0).map (·.entries) == some []
-- A count over 512 is refused; a block that is too short gives nothing.
#guard readIfd true (le16 600) 0 == none
#guard (readTiff [0x49, 0x49, 42]).location.isNone

/-- A crafted TIFF block whose zero ranges overlap IFD0 (the same bytes
were run through `metadata.mjs`, see the module docstring). IFD0 has two GPS
pointers: to A at 56 (with a position) and to B at 38 (none). B's one entry
has its 5 value bytes at 22..26, over the second pointer's tag. -/
def overlapTiff : Bytes :=
  [0x49, 0x49] ++ le16 42 ++ le32 8 ++
  le16 2 ++ ent 0x8825 4 1 56 ++ ent 0x8825 4 1 38 ++ le32 0 ++
  le16 1 ++ ent 0 1 5 22 ++ le32 0 ++
  le16 4 ++ ent 1 2 2 0x4e ++ ent 2 5 3 110 ++ ent 3 2 2 0x45 ++ ent 4 5 3 134 ++ le32 0 ++
  rat3 51 0 0 ++ rat3 1 0 0

#guard overlapTiff.length == 158
#guard !disjoint overlapTiff
-- No location before; a location after `strip`; `strip` twice differs from once.
#guard (readTiff overlapTiff).location.isNone
#guard (readTiff (emptyGps overlapTiff)).location.isSome
#guard emptyGps (emptyGps overlapTiff) != emptyGps overlapTiff
-- The checked strip drops the segment, so no location.
#guard (stripChecked { kind := .jpeg, segs := [.exif overlapTiff none] }).segs == []
#guard (readFile noDec (stripChecked { kind := .jpeg, segs := [.exif overlapTiff none] })).location.isNone

end L4Factoidal.LWS.PodMetadata
