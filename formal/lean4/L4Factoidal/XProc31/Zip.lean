import L4Factoidal.Codec.Archive

/-! Multi-entry ZIP for XProc. Central-directory order is preserved. Methods
0 (stored) and 8 (DEFLATE) are supported, including streamed data descriptors.
ZIP64, encryption, multi-disk archives and legacy non-ASCII name encodings are
explicitly unsupported. Other extra fields are checked structurally but are
not retained by the writer. No archive member is extracted to the filesystem. -/
namespace L4Factoidal.XProc31.Zip

inductive Error where
  | malformed (message : String)
  | unsupported (message : String)
  deriving Repr, BEq

instance : ToString Error := ⟨fun e => match e with
  | .malformed message => message
  | .unsupported message => "unsupported: " ++ message⟩

structure Entry where
  name : String
  bytes : ByteArray
  method : Nat := 8
  comment : String := ""
  dosTime : Nat := 0
  dosDate : Nat := 33
  externalAttributes : Nat := 0
  internalAttributes : Nat := 0
  versionMadeBy : Nat := 20
  deriving BEq, Inhabited

structure Archive where
  entries : List Entry := []
  comment : String := ""
  deriving BEq, Inhabited

def Entry.isDirectory (entry : Entry) : Bool :=
  entry.name.endsWith "/" || entry.externalAttributes &&& 0x10 != 0

private def u16 (bytes : ByteArray) (i : Nat) : Nat :=
  (bytes.get! i).toNat + 256 * (bytes.get! (i+1)).toNat

private def u32 (bytes : ByteArray) (i : Nat) : Nat :=
  u16 bytes i + 65536 * u16 bytes (i+2)

private def le16 (n : Nat) : ByteArray :=
  ⟨#[(n % 256).toUInt8, (n / 256 % 256).toUInt8]⟩

private def le32 (n : Nat) : ByteArray := le16 n ++ le16 (n / 65536)

private def hasBytes (bytes : ByteArray) (i count : Nat) : Bool := i + count <= bytes.size

private def findEnd (bytes : ByteArray) : Option Nat := Id.run do
  if bytes.size < 22 then return none
  let mut i := bytes.size - 22
  for _ in [0:min (bytes.size - 21) 65536] do
    if u32 bytes i == 0x06054b50 && i + 22 + u16 bytes (i+20) == bytes.size then return some i
    if i == 0 then return none
    i := i - 1
  return none

private def textField (bytes : ByteArray) (utf8 : Bool) : Except Error String := do
  if !utf8 && bytes.toList.any (fun b => b.toNat >= 128) then
    throw (.unsupported "legacy non-ASCII ZIP name/comment encoding")
  match String.fromUTF8? bytes with
  | some text => pure text
  | none => throw (.malformed "invalid UTF-8 ZIP name/comment")

private def checkExtra (bytes : ByteArray) (start count : Nat) : Except Error Unit := do
  if !hasBytes bytes start count then throw (.malformed "truncated ZIP extra field")
  let mut cursor := start
  let stop := start + count
  for _ in [0:count] do
    if cursor == stop then break
    if cursor + 4 > stop then throw (.malformed "truncated ZIP extra-field header")
    let tag := u16 bytes cursor
    let size := u16 bytes (cursor+2)
    if cursor + 4 + size > stop then throw (.malformed "truncated ZIP extra-field value")
    if tag == 1 then throw (.unsupported "ZIP64 extra field")
    if tag == 0x9901 then throw (.unsupported "encrypted ZIP entry")
    cursor := cursor + 4 + size

/-- Decode all entries using central-directory sizes, including entries whose
local headers defer those sizes to a data descriptor. The aggregate expanded
size is bounded before decompression. -/
def read (bytes : ByteArray) (maxBytes : Nat := Codec.maxInflated) : Except Error Archive := do
  let some ending := findEnd bytes | throw (.malformed "ZIP end of central directory not found")
  if ending >= 20 && u32 bytes (ending-20) == 0x07064b50 then throw (.unsupported "ZIP64 archive")
  let count := u16 bytes (ending+10)
  let centralSize := u32 bytes (ending+12)
  let centralStart := u32 bytes (ending+16)
  if count == 65535 || centralSize == 4294967295 || centralStart == 4294967295 then
    throw (.unsupported "ZIP64 archive")
  if u16 bytes (ending+4) != 0 || u16 bytes (ending+6) != 0 || u16 bytes (ending+8) != count then
    throw (.unsupported "multi-disk ZIP archive")
  if centralStart + centralSize > ending then throw (.malformed "ZIP central directory exceeds archive bounds")
  -- The archive comment has no UTF-8 flag; accept ASCII conservatively.
  let comment ← textField (bytes.extract (ending+22) bytes.size) false
  let mut cursor := centralStart
  let mut total := 0
  let mut entries : List Entry := []
  for _ in [0:count] do
    if cursor + 46 > centralStart + centralSize || u32 bytes cursor != 0x02014b50 then
      throw (.malformed "invalid ZIP central-directory entry")
    let flags := u16 bytes (cursor+8)
    let method := u16 bytes (cursor+10)
    let crc := u32 bytes (cursor+16)
    let compressedSize := u32 bytes (cursor+20)
    let expandedSize := u32 bytes (cursor+24)
    let nameSize := u16 bytes (cursor+28)
    let extraSize := u16 bytes (cursor+30)
    let commentSize := u16 bytes (cursor+32)
    let localStart := u32 bytes (cursor+42)
    if compressedSize == 4294967295 || expandedSize == 4294967295 || localStart == 4294967295 then
      throw (.unsupported "ZIP64 entry")
    if u16 bytes (cursor+34) != 0 then throw (.unsupported "multi-disk ZIP entry")
    if flags &&& 0x41 != 0 then throw (.unsupported "encrypted ZIP entry")
    if flags &&& 0xf7f1 != 0 then throw (.unsupported "ZIP general-purpose flag")
    if u16 bytes (cursor+6) > 20 then throw (.unsupported "ZIP entry requires a newer feature version")
    if method != 0 && method != 8 then throw (.unsupported ("ZIP compression method " ++ toString method))
    if total + expandedSize > maxBytes then throw (.unsupported "ZIP expanded-size limit")
    total := total + expandedSize
    let next := cursor + 46 + nameSize + extraSize + commentSize
    if next > centralStart + centralSize then throw (.malformed "truncated ZIP central-directory fields")
    if nameSize == 0 then throw (.malformed "empty ZIP entry name")
    let nameBytes := bytes.extract (cursor+46) (cursor+46+nameSize)
    let name ← textField nameBytes (flags &&& 0x800 != 0)
    let entryComment ← textField (bytes.extract (cursor+46+nameSize+extraSize) next) (flags &&& 0x800 != 0)
    checkExtra bytes (cursor+46+nameSize) extraSize
    if localStart + 30 > centralStart || u32 bytes localStart != 0x04034b50 then
      throw (.malformed "invalid ZIP local header")
    if u16 bytes (localStart+6) != flags || u16 bytes (localStart+8) != method then
      throw (.malformed "ZIP local/central flags or method disagree")
    let localNameSize := u16 bytes (localStart+26)
    let localExtraSize := u16 bytes (localStart+28)
    let dataStart := localStart + 30 + localNameSize + localExtraSize
    if dataStart + compressedSize > centralStart then throw (.malformed "ZIP entry data exceeds archive bounds")
    if bytes.extract (localStart+30) (localStart+30+localNameSize) != nameBytes then
      throw (.malformed "ZIP local/central names disagree")
    checkExtra bytes (localStart+30+localNameSize) localExtraSize
    if flags &&& 8 == 0 then
      if u32 bytes (localStart+14) != crc || u32 bytes (localStart+18) != compressedSize ||
          u32 bytes (localStart+22) != expandedSize then
        throw (.malformed "ZIP local/central CRC or sizes disagree")
    else
      let descriptor := dataStart + compressedSize
      if descriptor + 12 > centralStart then throw (.malformed "truncated ZIP data descriptor")
      let descriptorMatches (offset : Nat) := offset + 12 <= centralStart && u32 bytes offset == crc &&
        u32 bytes (offset+4) == compressedSize && u32 bytes (offset+8) == expandedSize
      -- A signature-free descriptor's CRC can itself equal the signature.
      if !descriptorMatches descriptor && !(u32 bytes descriptor == 0x08074b50 && descriptorMatches (descriptor+4)) then
        throw (.malformed "ZIP data descriptor disagrees with central directory")
    let raw := bytes.extract dataStart (dataStart+compressedSize)
    let data ← if method == 0 then pure raw else do
      let (decoded, consumed) ← (Codec.inflateAt raw 0).mapError Error.malformed
      if consumed != raw.size then throw (.malformed "trailing bytes in ZIP DEFLATE stream")
      pure decoded
    if data.size != expandedSize then throw (.malformed "ZIP expanded size mismatch")
    if (Codec.crc32 data).toNat != crc then throw (.malformed "ZIP CRC-32 mismatch")
    let entry : Entry := {
      name := name
      bytes := data
      method := method
      comment := entryComment
      dosTime := u16 bytes (cursor+12)
      dosDate := u16 bytes (cursor+14)
      externalAttributes := u32 bytes (cursor+38)
      internalAttributes := u16 bytes (cursor+36)
      versionMadeBy := u16 bytes (cursor+4) }
    entries := entry :: entries
    cursor := next
  if cursor != centralStart + centralSize then throw (.unsupported "additional ZIP central-directory records")
  return {entries := entries.reverse, comment}

/-- Write ordinary single-disk ZIP. DEFLATE output uses valid stored blocks;
method numbers, comments, DOS times and external attributes are preserved.
UTF-8 entry names/comments use the UTF-8 general-purpose flag. -/
def write (archive : Archive) : Except Error ByteArray := do
  if archive.entries.length >= 65535 then throw (.unsupported "ZIP64 entry count")
  let comment := archive.comment.toUTF8
  if comment.size > 65535 then throw (.malformed "ZIP archive comment is too long")
  if comment.toList.any (fun b => b.toNat >= 128) then throw (.unsupported "non-ASCII ZIP archive comment")
  let mut body := ByteArray.empty
  let mut central := ByteArray.empty
  for entry in archive.entries do
    if entry.method != 0 && entry.method != 8 then throw (.unsupported ("ZIP compression method " ++ toString entry.method))
    let name := entry.name.toUTF8
    let note := entry.comment.toUTF8
    if name.isEmpty || name.size > 65535 || note.size > 65535 then throw (.malformed "invalid ZIP entry name/comment length")
    if entry.dosTime > 65535 || entry.dosDate > 65535 || entry.versionMadeBy > 65535 ||
        entry.internalAttributes > 65535 || entry.externalAttributes >= 4294967296 then
      throw (.malformed "ZIP entry metadata exceeds field width")
    let compressed := if entry.method == 0 then entry.bytes else Codec.deflateStored entry.bytes
    if compressed.size >= 4294967295 || entry.bytes.size >= 4294967295 || body.size >= 4294967295 then
      throw (.unsupported "ZIP64 entry size or offset")
    let crc := (Codec.crc32 entry.bytes).toNat
    let localHeader := le32 0x04034b50 ++ le16 20 ++ le16 0x800 ++ le16 entry.method ++
      le16 entry.dosTime ++ le16 entry.dosDate ++ le32 crc ++ le32 compressed.size ++ le32 entry.bytes.size ++
      le16 name.size ++ le16 0 ++ name
    let centralHeader := le32 0x02014b50 ++ le16 entry.versionMadeBy ++ le16 20 ++ le16 0x800 ++ le16 entry.method ++
      le16 entry.dosTime ++ le16 entry.dosDate ++ le32 crc ++ le32 compressed.size ++ le32 entry.bytes.size ++
      le16 name.size ++ le16 0 ++ le16 note.size ++ le16 0 ++ le16 entry.internalAttributes ++ le32 entry.externalAttributes ++
      le32 body.size ++ name ++ note
    body := body ++ localHeader ++ compressed
    central := central ++ centralHeader
  if body.size >= 4294967295 || central.size >= 4294967295 then throw (.unsupported "ZIP64 central directory")
  let count := archive.entries.length
  return body ++ central ++ le32 0x06054b50 ++ le16 0 ++ le16 0 ++ le16 count ++ le16 count ++
    le32 central.size ++ le32 body.size ++ le16 comment.size ++ comment

private def sample : Archive :=
  {entries := [{name := "one.xml", bytes := "<one/>".toUTF8, method := 0, comment := "stored"},
               {name := "folder/twó.txt", bytes := "two".toUTF8, method := 8, comment := "deflated"},
               {name := "folder/", bytes := ByteArray.empty, method := 0}], comment := "archive"}

#guard ((write sample).bind fun bytes => read bytes).toOption == some sample
#guard ((write {}).bind fun bytes => read bytes).toOption == some {}
#guard (read "not a zip".toUTF8).toBool == false
#guard (write {entries := [{name := "x", bytes := ByteArray.empty, method := 99}]}).toBool == false
#guard ({name := "folder/", bytes := ByteArray.empty} : Entry).isDirectory
#guard !(sample.entries.head!).isDirectory

private def crcRegression : Bool :=
  match write sample with
  | .error _ => false
  | .ok bytes =>
    let start := 30 + "one.xml".toUTF8.size
    let damaged := bytes.extract 0 start ++ ByteArray.mk #[0] ++ bytes.extract (start+1) bytes.size
    match read damaged with
    | .error (.malformed message) => message == "ZIP CRC-32 mismatch"
    | _ => false

#guard crcRegression
#guard match write {entries := [{name := "x", bytes := ByteArray.empty, method := 99}]} with
  | .error (.unsupported _) => true | _ => false

/-- Read both vendored ZIP fixtures, including data descriptors, then round-trip
all entries and metadata through the writer. The caller supplies the documents
folder so this regression does not depend on the build process's directory. -/
def fixtureRegression (documents : System.FilePath) : IO (Except String Unit) := do
  for (name, files) in [("archive.zip", 10), ("ab-doc.zip", 2)] do
    let bytes ← IO.FS.readBinFile (documents / name)
    let archive ← match read bytes with
      | .error e => return .error (name ++ ": " ++ toString e)
      | .ok archive => pure archive
    if (archive.entries.filter (fun e => !e.isDirectory)).length != files then
      return .error (name ++ ": unexpected file count")
    let encoded ← match write archive with
      | .error e => return .error (name ++ ": " ++ toString e)
      | .ok encoded => pure encoded
    match read encoded with
    | .error e => return .error (name ++ ": " ++ toString e)
    | .ok decoded => if decoded != archive then return .error (name ++ ": round-trip differs")
  return .ok ()

end L4Factoidal.XProc31.Zip
