import L4Factoidal.Storage.IndexedBlockWireV3

namespace L4Factoidal.Storage.IndexedBlockWireV3Tests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.IndexedBlock
open L4Factoidal.Storage.IndexedBlockWireV3

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pAge : WfIri := ⟨"http://example.org/age", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def names : Graph :=
  [{ s := alice, p := pName, o := .literal (Literal.langString "Alice" "en") },
   { s := bob, p := pName, o := .literal (Literal.langString "Bob" "en") }]
private def mixed : Graph :=
  names ++ [{ s := alice, p := pAge, o := .literal (Literal.string "30") }]

private def block := fromGraph names
private def bytes : ByteArray := (encode? block).getD ByteArray.empty
private def corrupt : ByteArray := ByteArray.mk ((encodeList block).drop 1 |>.toArray)

private def pagePlanWorks : Bool :=
  match decodePrefix bytes with
  | none => false
  | some header =>
      match dictionaryPrefixRange header with
      | none => false
      | some ptdPrefixRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => false
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rows := rowsRange header
              let rowPrefix := bytes.extract rows.offset (rows.offset + rowBytes)
              match dictionaryPagesForRowPrefix? header ptdPrefix directory rowPrefix with
              | some [page] => page.offset >= (dictionaryRange header).offset &&
                  page.offset + page.length <= (dictionaryRange header).offset + (dictionaryRange header).length
              | _ => false

private def rangeScan : List Triple :=
  match decodePrefix bytes with
  | none => []
  | some header =>
      match dictionaryPrefixRange header with
      | none => []
      | some ptdPrefixRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => []
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rows := rowsRange header
              let rowPrefix := bytes.extract rows.offset (rows.offset + rows.length)
              match dictionaryPagesForRowPrefix? header ptdPrefix directory rowPrefix with
              | none => []
              | some ranges =>
                  let pages := ranges.map fun range =>
                    (range, bytes.extract range.offset (range.offset + range.length))
                  (scanRowPrefixPages { p := some pName }
                    (bytes.extract 0 prefixBytes) rowPrefix ptdPrefix directory pages).getD []

private def secondRowRangeScan : List Triple :=
  match decodePrefix bytes with
  | none => []
  | some header =>
      match dictionaryPrefixRange header, rowRange? header 1 1 with
      | some ptdPrefixRange, some rowRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => []
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rowBytes := bytes.extract rowRange.offset (rowRange.offset + rowRange.length)
              match dictionaryPagesForRowRange? header 1 ptdPrefix directory rowBytes with
              | none => []
              | some ranges =>
                  let pages := ranges.map fun range =>
                    (range, bytes.extract range.offset (range.offset + range.length))
                  (scanRowRangePages { p := some pName }
                    (bytes.extract 0 prefixBytes) 1 rowBytes ptdPrefix directory pages).getD []
      | _, _ => []

private def missingPageRejected : Bool :=
  match decodePrefix bytes with
  | none => false
  | some header =>
      match dictionaryPrefixRange header with
      | none => false
      | some ptdPrefixRange =>
          let ptdPrefix := bytes.extract ptdPrefixRange.offset (ptdPrefixRange.offset + ptdPrefixRange.length)
          match dictionaryDirectoryRange? header ptdPrefix with
          | none => false
          | some directoryRange =>
              let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
              let rows := rowsRange header
              let rowPrefix := bytes.extract rows.offset (rows.offset + rows.length)
              (scanRowPrefixPages { p := some pName }
                (bytes.extract 0 prefixBytes) rowPrefix ptdPrefix directory []).isNone

private structure RangeInputs where
  header : Prefix
  ptdPrefix : ByteArray
  directory : ByteArray
  rows : ByteArray
  pages : List (ByteRange × ByteArray)

private def rangeInputs : Option RangeInputs := do
  let header ← decodePrefix bytes
  let prefixRange ← dictionaryPrefixRange header
  let ptdPrefix := bytes.extract prefixRange.offset (prefixRange.offset + prefixRange.length)
  let directoryRange ← dictionaryDirectoryRange? header ptdPrefix
  let directory := bytes.extract directoryRange.offset (directoryRange.offset + directoryRange.length)
  let rowsRange := rowsRange header
  let rows := bytes.extract rowsRange.offset (rowsRange.offset + rowsRange.length)
  let ranges ← dictionaryPagesForRowPrefix? header ptdPrefix directory rows
  let pages := ranges.map fun range =>
    (range, bytes.extract range.offset (range.offset + range.length))
  some { header, ptdPrefix, directory, rows, pages }

private def headerBytes (header : Prefix) : ByteArray :=
  let writeU32LE := L4Factoidal.Storage.writeU32LE
  byteArrayOfList (writeU32LE magic ++ [version] ++
    writeU32LE (UInt32.ofNat header.rowCount) ++
    writeU32LE (UInt32.ofNat header.dictionaryBytes))

#guard match rangeInputs with
  | some inputs =>
      (scanRowRangePages { p := some pName } (headerBytes inputs.header) 1
        (inputs.rows.extract 0 rowBytes) inputs.ptdPrefix inputs.directory inputs.pages).isNone
  | none => false
#guard match rangeInputs with
  | some inputs =>
      (dictionaryPagesForRowRange? inputs.header 1 inputs.ptdPrefix inputs.directory
        (inputs.rows.extract 0 rowBytes)).isNone
  | none => false
#guard match rangeInputs with
  | some inputs =>
      let malformed := { inputs.header with dictionaryBytes := 0 }
      (scanRowPrefixPages { p := some pName } (headerBytes malformed)
        inputs.rows inputs.ptdPrefix inputs.directory inputs.pages).isNone
  | none => false
#guard match rangeInputs with
  | some inputs =>
      let malformed := { inputs.header with dictionaryBytes := inputs.header.dictionaryBytes + 1 }
      (scanRowRangePages { p := some pName } (headerBytes malformed) 0
        inputs.rows inputs.ptdPrefix inputs.directory inputs.pages).isNone
  | none => false
#guard match rangeInputs with
  | some inputs =>
      let malformed := { inputs.header with dictionaryBytes := inputs.header.dictionaryBytes + 1 }
      (dictionaryPagesForRowPrefix? malformed inputs.ptdPrefix inputs.directory inputs.rows).isNone
  | none => false
#guard match rangeInputs with
  | some inputs =>
      (dictionaryPagesForRowPrefix? { inputs.header with rowCount := 1 }
        inputs.ptdPrefix inputs.directory inputs.rows).isNone
  | none => false

#guard supported block
#guard !(supported (fromGraph mixed))
#guard match decodePrefix bytes with
  | some header => header.rowCount == block.rows.size &&
      rowsRange header == { offset := prefixBytes, length := block.rows.size * rowBytes } &&
      (dictionaryRange header).offset == prefixBytes + block.rows.size * rowBytes
  | none => false
#guard match decode bytes with
  | some decoded => decoded.denotes == names &&
      scanBound { p := some pName } decoded == tripleMatchesBound { p := some pName } names
  | none => false
#guard pagePlanWorks
#guard rangeScan == tripleMatchesBound { p := some pName } names
#guard secondRowRangeScan == names.drop 1
#guard match decodePrefix bytes with
  | some header => rowRange? header 1 1 == some { offset := prefixBytes + rowBytes, length := rowBytes } &&
      (rowRange? header header.rowCount 1).isNone
  | none => false
#guard missingPageRejected
#guard match decodePrefix bytes with
  | some header =>
      let rows := rowsRange header
      let rowBytes := bytes.extract rows.offset (rows.offset + rows.length)
      match dictionaryPrefixRange header with
      | some dictionaryPrefix =>
          match L4Factoidal.Storage.PagedTermDictionary.decodePrefix
              (bytes.extract dictionaryPrefix.offset (dictionaryPrefix.offset + dictionaryPrefix.length)) with
          | some ptd => (validatedRowPredicate? ptd.termCount rowBytes).isSome
          | none => false
      | none => false
  | none => false
#guard (validatedRowPredicate? 1 ByteArray.empty).isNone
#guard (scanRowPrefixPages {} ByteArray.empty ByteArray.empty ByteArray.empty ByteArray.empty []).isNone
#guard (decode corrupt).isNone

end L4Factoidal.Storage.IndexedBlockWireV3Tests
