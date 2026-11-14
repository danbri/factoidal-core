import L4Factoidal.Codec.Inflate
import L4Factoidal.Codec.Crc32

/-!
# Compression Standard: the formats of CompressionStream and DecompressionStream

https://compression.spec.whatwg.org/. The two classes are TransformStreams of the page script
layer (`tools/wasmvm/quickjs/prelude.js`, section "Streams Standard"); what they decide is here:

- `Format.ofName?`: the CompressionFormat enumeration (§3): `deflate` (the zlib format, RFC
  1950), `deflate-raw` (RFC 1951) and `gzip` (RFC 1952). Other names (`brotli` too) are refused.
- `compress`: the bytes of a whole input in a format. The DEFLATE data is stored blocks
  (`Codec.deflateStored`): every inflater reads them; they do not make the data smaller.
- `decompress`: what the bytes received so far are: a whole stream (`done`, with whether bytes
  follow its end: the Standard's TypeError for "trailing data", after the output), a prefix of
  one (`more`), or not a stream of the format (`bad`). The header and trailer checks are RFC
  1950 §2.2 (CM 8, CINFO at most 7, FCHECK, no preset dictionary, the Adler-32 of the output)
  and RFC 1952 §2.3 (ID, CM 8, no reserved flag, the optional fields, FHCRC, CRC-32 and ISIZE).

Theorems: the name of a format reads back (`ofName_name`), `brotli` is refused, a header that
passes `zlibHeaderOk` has its check bits right (`zlibHeaderOk_fcheck`) and no dictionary, and a
`done` answer for `deflate-raw` is the inflater's answer for the whole input with nothing after
it (`decompress_raw_done`, `decompress_raw_extra`). Tested only (`#guard`): the round trip of
`compress` and `decompress` for each format, the WPT cases of corrupt and truncated input.
Not proved: anything about `Codec.inflateAt` itself.
-/
namespace L4Factoidal.WHATWG.Compression

open L4Factoidal.Codec

inductive Format where
  | deflate | deflateRaw | gzip
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The CompressionFormat enumeration value of a format. -/
def Format.name : Format → String
  | .deflate => "deflate" | .deflateRaw => "deflate-raw" | .gzip => "gzip"

def Format.ofName? : String → Option Format
  | "deflate" => some .deflate
  | "deflate-raw" => some .deflateRaw
  | "gzip" => some .gzip
  | _ => none

/-- Kind: a round trip. Says: the name of every format reads back as that format. -/
theorem ofName_name (f : Format) : Format.ofName? f.name = some f := by
  cases f <;> rfl

/-- Kind: a refusal. Says: brotli is not a format this engine has (the constructor throws). -/
theorem ofName_brotli : Format.ofName? "brotli" = none := rfl

/-- Adler-32 (RFC 1950 §8.2). -/
def adler32 (b : ByteArray) : Nat := Id.run do
  let mut a := 1
  let mut s := 0
  for x in b.data do
    a := (a + x.toNat) % 65521
    s := (s + a) % 65521
  return s * 65536 + a

def be32 (n : Nat) : ByteArray :=
  ⟨#[(n / 16777216 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 256 % 256).toUInt8, (n % 256).toUInt8]⟩

def le32 (n : Nat) : ByteArray :=
  ⟨#[(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8, (n / 16777216 % 256).toUInt8]⟩

def byteAt (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

def rd32be (b : ByteArray) (i : Nat) : Nat :=
  ((byteAt b i * 256 + byteAt b (i + 1)) * 256 + byteAt b (i + 2)) * 256 + byteAt b (i + 3)

def rd32le (b : ByteArray) (i : Nat) : Nat :=
  ((byteAt b (i + 3) * 256 + byteAt b (i + 2)) * 256 + byteAt b (i + 1)) * 256 + byteAt b i

/-- The whole input in the format. -/
def compress : Format → ByteArray → ByteArray
  | .deflateRaw, b => deflateStored b
  | .deflate, b => ByteArray.mk #[0x78, 0x01] ++ deflateStored b ++ be32 (adler32 b)
  | .gzip, b => ByteArray.mk #[0x1f, 0x8b, 8, 0, 0, 0, 0, 0, 0, 0xff] ++ deflateStored b ++
      le32 (crc32 b).toNat ++ le32 (b.size % 4294967296)

/-- RFC 1950 §2.2: compression method 8, a window of at most 32 KiB (CINFO ≤ 7), the check
bits (FCHECK: CMF·256 + FLG is a multiple of 31), and no preset dictionary (FDICT). -/
def zlibHeaderOk (cmf flg : Nat) : Bool :=
  cmf % 16 == 8 && cmf / 16 ≤ 7 && (cmf * 256 + flg) % 31 == 0 && flg / 32 % 2 == 0

/-- Kind: a refusal. Says: a header that passes has its check bits right and asks for no
preset dictionary. -/
theorem zlibHeaderOk_fcheck (cmf flg : Nat) (h : zlibHeaderOk cmf flg = true) :
    (cmf * 256 + flg) % 31 = 0 ∧ flg / 32 % 2 = 0 := by
  simp [zlibHeaderOk] at h
  exact ⟨h.1.2, h.2⟩

/-- What the bytes received so far are. -/
inductive Outcome where
  /-- A whole stream: its output, and whether bytes follow its end. -/
  | done (out : ByteArray) (extra : Bool)
  /-- A prefix of a stream: more input is needed. -/
  | more
  /-- Not a stream of the format. -/
  | bad (why : String)
  deriving Inhabited

/-- The inflater's answers that mean the input stopped inside the stream. -/
def truncation (msg : String) : Bool :=
  msg == "unexpected end of compressed data" || msg == "stored block runs past the end of the data"

/-- The DEFLATE stream at `start`, then a trailer of `trailer` bytes that `check` accepts. -/
def body (b : ByteArray) (start trailer : Nat) (check : ByteArray → Nat → Bool) : Outcome :=
  match inflateAt b start with
  | .error m => if truncation m then .more else .bad m
  | .ok (out, e) =>
    if e + trailer > b.size then .more
    else if !check out e then .bad "the trailer does not match the data"
    else .done out (e + trailer != b.size)

/-- The end of a gzip header (RFC 1952 §2.3.1), or `none` when the input stops inside it. -/
def gzipHeaderEnd (b : ByteArray) : Except String (Option Nat) := Id.run do
  if b.size < 10 then return .ok none
  if byteAt b 0 != 0x1f || byteAt b 1 != 0x8b then return .error "not a gzip stream"
  if byteAt b 2 != 8 then return .error "the gzip compression method is not deflate"
  let flg := byteAt b 3
  if flg / 32 != 0 then return .error "reserved gzip flags are set"
  let mut i := 10
  if flg / 4 % 2 == 1 then
    if i + 2 > b.size then return .ok none
    i := i + 2 + byteAt b i + 256 * byteAt b (i + 1)
  -- FNAME and FCOMMENT: zero-terminated
  for bit in [8, 16] do
    if flg / bit % 2 == 1 then
      let mut j := i
      let mut found := false
      for _ in [0:b.size] do
        if j ≥ b.size then break
        if byteAt b j == 0 then
          found := true
          break
        j := j + 1
      if !found then return .ok none
      i := j + 1
  if flg / 2 % 2 == 1 then
    if i + 2 > b.size then return .ok none
    -- FHCRC: the two low bytes of the CRC-32 of the header before it
    let crc := (crc32 (b.extract 0 i)).toNat % 65536
    if byteAt b i + 256 * byteAt b (i + 1) != crc then return .error "the gzip header CRC does not match"
    i := i + 2
  if i > b.size then return .ok none
  return .ok (some i)

/-- The bytes received so far, in the format. -/
def decompress (f : Format) (b : ByteArray) : Outcome :=
  match f with
  | .deflateRaw => body b 0 0 (fun _ _ => true)
  | .deflate =>
    if b.size < 2 then .more
    else if !zlibHeaderOk (byteAt b 0) (byteAt b 1) then .bad "not a zlib stream"
    else body b 2 4 (fun out e => rd32be b e == adler32 out)
  | .gzip =>
    match gzipHeaderEnd b with
    | .error m => .bad m
    | .ok none => .more
    | .ok (some i) => body b i 8 (fun out e =>
        rd32le b e == (crc32 out).toNat && rd32le b (e + 4) == out.size % 4294967296)

/-- Kind: a specification. Says: a `deflate-raw` input is a whole stream with nothing after it
exactly when the inflater decodes it to its last byte. -/
theorem decompress_raw_done (b out : ByteArray) (h : decompress .deflateRaw b = .done out false) :
    inflateAt b 0 = .ok (out, b.size) := by
  simp only [decompress, body] at h
  split at h
  · split at h <;> cases h
  · rename_i out' e he
    split at h
    · cases h
    · simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      rw [he]
      have : e = b.size := by omega
      rw [this]

/-- Kind: a specification. Says: a `deflate-raw` answer with bytes after the stream is the
inflater's output for a stream that ends before the input does. -/
theorem decompress_raw_extra (b out : ByteArray) (h : decompress .deflateRaw b = .done out true) :
    ∃ e, inflateAt b 0 = .ok (out, e) ∧ e < b.size := by
  simp only [decompress, body] at h
  split at h
  · split at h <;> cases h
  · rename_i out' e he
    split at h
    · cases h
    · simp at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      exact ⟨e, he, by omega⟩

/-! ## How often a DecompressionStream decodes (a work bound)

A DecompressionStream keeps the bytes it has received and asks `decompress` whether they hold a
whole stream. Asking after every chunk costs the square of the input (a page that writes one
byte at a time). It asks only when the bytes received are at least twice what it last asked
about (`askAgain`), and once more when it is closed: the bytes decoded in all are then at most
three times the input (`askLoop_work`, plus the last ask). -/

/-- Ask again: never asked yet, or the input has at least doubled since. -/
def askAgain (asked size : Nat) : Bool := asked == 0 || size ≥ 2 * asked

/-- The asks for running totals `sizes`: the bytes decoded in all, and the size last asked about. -/
def askLoop : List Nat → Nat → Nat → Nat × Nat
  | [], work, asked => (work, asked)
  | s :: ss, work, asked =>
    if askAgain asked s then askLoop ss (work + s) s else askLoop ss work asked

/-- Kind: a resource bound. Says: the bytes decoded by the asks are at most twice the size last
asked about (so at most twice the input), whatever the chunks. -/
theorem askLoop_work (sizes : List Nat) (work asked : Nat) (h : work ≤ 2 * asked) :
    (askLoop sizes work asked).1 ≤ 2 * (askLoop sizes work asked).2 := by
  induction sizes generalizing work asked with
  | nil => simpa [askLoop] using h
  | cons s ss ih =>
    simp only [askLoop]
    split
    · rename_i hs
      apply ih
      simp [askAgain] at hs
      rcases hs with h0 | h2
      · subst h0; omega
      · omega
    · exact ih work asked h

/-- Kind: a resource bound. Says: the size last asked about is never more than the largest
running total (nor the size asked before). -/
theorem askLoop_asked (sizes : List Nat) (work asked b : Nat) (hb : asked ≤ b) (hs : ∀ s ∈ sizes, s ≤ b) :
    (askLoop sizes work asked).2 ≤ b := by
  induction sizes generalizing work asked with
  | nil => simpa [askLoop] using hb
  | cons s ss ih =>
    simp only [askLoop]
    split
    · exact ih _ _ (hs s (by simp)) (fun x hx => hs x (by simp [hx]))
    · exact ih _ _ hb (fun x hx => hs x (by simp [hx]))

#guard (askLoop ((List.range 1000).map (· + 1)) 0 0).1 ≤ 2 * 1000
#guard (askLoop ((List.range 1000).map (· + 1)) 0 0).1 == 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 + 256 + 512

/-- The page's `web_api` operations (Hosts/WebApi.lean): 52 `(name)` the format's name, or -2
(the constructors' TypeError); 50 `(name, bytes)` the compressed bytes; 51 `(name, bytes)`
one status byte (0 a whole stream, 1 a whole stream with bytes after it, 2 more input
needed) and the output, or -20 for input that is not a stream of the format. -/
def op (code : Nat) (name : String) (bytes : ByteArray) : Except Int ByteArray :=
  match Format.ofName? name with
  | none => .error (-2)
  | some f =>
    match code with
    | 52 => .ok f.name.toUTF8
    -- 53 `(name, "asked size")`: does a DecompressionStream that last asked about `asked`
    -- bytes and now has `size` ask again (`askAgain`)
    | 53 =>
      let parts := ((String.fromUTF8? bytes).getD "").splitOn " "
      let asked := (parts.getD 0 "").toNat?.getD 0
      let size := (parts.getD 1 "").toNat?.getD 0
      .ok (if askAgain asked size then "1" else "0").toUTF8
    | 50 => .ok (compress f bytes)
    | 51 =>
      match decompress f bytes with
      | .done out extra => .ok (ByteArray.mk #[if extra then 1 else 0] ++ out)
      | .more => .ok (ByteArray.mk #[2])
      | .bad _ => .error (-20)
    | _ => .error (-2)

/-- Kind: a refusal. Says: every operation refuses a name that is not a format. -/
theorem op_refuses (code : Nat) (name : String) (bytes : ByteArray) (h : Format.ofName? name = none) :
    op code name bytes = .error (-2) := by
  simp [op, h]

/-! ## Checks (the WPT compression cases) -/

def outcomeStr : Outcome → String
  | .done out extra => s!"done {out.toList} {extra}"
  | .more => "more"
  | .bad _ => "bad"

private def hello : ByteArray := "expected output".toUTF8

#guard (Format.ofName? "deflate-raw").map Format.name == some "deflate-raw"
#guard Format.ofName? "Deflate" == none && Format.ofName? "" == none
#guard (match op 51 "gzip" ByteArray.empty with | .ok b => b.toList == [2] | _ => false)
#guard (match op 50 "brotli" ByteArray.empty with | .error e => e == -2 | _ => false)
-- round trips
#guard [Format.deflate, .deflateRaw, .gzip].all fun f =>
  outcomeStr (decompress f (compress f hello)) == outcomeStr (.done hello false)
#guard [Format.deflate, .deflateRaw, .gzip].all fun f =>
  outcomeStr (decompress f (compress f ByteArray.empty)) == outcomeStr (.done ByteArray.empty false)
-- decompression-input.js: zlib and gzip of "expected output" made by zlib with compression
private def deflateValue : ByteArray := ⟨#[120, 156, 75, 173, 40, 72, 77, 46, 73, 77, 81, 200, 47, 45, 41, 40, 45, 1, 0, 48, 173, 6, 36]⟩
private def gzipValue : ByteArray := ⟨#[31, 139, 8, 0, 0, 0, 0, 0, 0, 3, 75, 173, 40, 72, 77, 46, 73, 77, 81, 200, 47, 45, 41, 40, 45, 1, 0, 176, 1, 57, 179, 15, 0, 0, 0]⟩
private def rawValue : ByteArray := ⟨#[75, 173, 40, 72, 77, 46, 73, 77, 81, 200, 47, 45, 41, 40, 45, 1, 0]⟩
#guard outcomeStr (decompress .deflate deflateValue) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .gzip gzipValue) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .deflateRaw rawValue) == outcomeStr (.done hello false)
-- decompression-extra-input: the output, then the error for the extra byte
#guard outcomeStr (decompress .deflate (deflateValue.push 0)) == outcomeStr (.done hello true)
#guard outcomeStr (decompress .gzip (gzipValue.push 0)) == outcomeStr (.done hello true)
#guard outcomeStr (decompress .deflateRaw (rawValue.push 0)) == outcomeStr (.done hello true)
-- every proper prefix needs more input (decompression-split-chunk, a truncated stream)
#guard (List.range deflateValue.size).all fun k => outcomeStr (decompress .deflate (deflateValue.extract 0 k)) == "more"
#guard (List.range gzipValue.size).all fun k => outcomeStr (decompress .gzip (gzipValue.extract 0 k)) == "more"
#guard (List.range rawValue.size).all fun k => outcomeStr (decompress .deflateRaw (rawValue.extract 0 k)) == "more"
-- decompression-empty-input: the empty streams of each format
#guard outcomeStr (decompress .gzip ⟨#[31, 139, 8, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩) == "done [] false"
#guard outcomeStr (decompress .deflate ⟨#[120, 156, 3, 0, 0, 0, 0, 1]⟩) == "done [] false"
#guard outcomeStr (decompress .deflateRaw ⟨#[1, 0, 0, 255, 255]⟩) == "done [] false"
-- decompression-corrupt-input: one field changed
private def setAt (b : ByteArray) (i : Nat) (v : UInt8) : ByteArray := b.set! i v
#guard outcomeStr (decompress .deflate (setAt deflateValue 0 0)) == "bad"
#guard [218, 1, 94].all fun v => outcomeStr (decompress .deflate (setAt deflateValue 1 v)) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .deflate (setAt deflateValue 1 157)) == "bad"
#guard outcomeStr (decompress .deflate (setAt deflateValue 22 255)) == "bad"
#guard outcomeStr (decompress .gzip (setAt gzipValue 0 255)) == "bad"
#guard outcomeStr (decompress .gzip (setAt gzipValue 2 0)) == "bad"
#guard outcomeStr (decompress .gzip (setAt gzipValue 3 1)) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .gzip (setAt gzipValue 3 2)) != outcomeStr (.done hello false)
#guard [4, 8, 9].all fun i => outcomeStr (decompress .gzip (setAt gzipValue i 255)) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .gzip (setAt gzipValue 27 255)) == "bad"
#guard outcomeStr (decompress .gzip (setAt gzipValue 31 255)) == "bad"
#guard outcomeStr (decompress .deflate (setAt deflateValue 18 4)) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .deflate (setAt deflateValue 18 5)) == "bad"
#guard outcomeStr (decompress .gzip (setAt gzipValue 26 4)) == outcomeStr (.done hello false)
#guard outcomeStr (decompress .gzip (setAt gzipValue 26 3)) == "bad"
-- decompression-bad-chunks: the invalid deflate and gzip bytes
#guard outcomeStr (decompress .deflate (setAt deflateValue 0 0)) == "bad"
#guard outcomeStr (decompress .gzip (setAt gzipValue 0 0)) == "bad"

end L4Factoidal.WHATWG.Compression
