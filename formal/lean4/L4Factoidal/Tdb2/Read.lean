/-
L4Factoidal.Tdb2.Read — read the quads of an Apache Jena TDB2 database
(read only; https://github.com/danbri/factoidal/issues/834).

Format record: docs/designissues/2026-10-13-tdb2-format.md. Summary:

* A database directory holds generations `Data-0001`, `Data-0002`, ...; the
  highest one is current. A non-empty `journal.jrnl` means a commit that Jena
  has not replayed: the reader refuses it.
* `SPO` (default graph, 24-byte records) and `GSPO` (named graphs, 32-byte
  records) are B+trees of NodeIds. `X.bpt` holds three big-endian longs (root
  block id, ...). `X.idn` holds 8192-byte tree nodes: an int (block type 6
  branch / 7 leaf in the high byte, key count in the low 24 bits), `MaxRec`
  records, then `count+1` int pointers. Children of a leaf node (type 7) are
  record blocks of `X.dat`: int count, int link, records.
* A NodeId is a big-endian 64-bit word. Bit 63 clear: a byte offset into
  `nodes-data.obj`, where one Thrift compact-protocol `RDF_Term` is stored.
  Bits 63 and 62 set: an inline xsd:double (62 bits). Bit 63 set, 62 clear:
  type in bits 62..56, value in bits 55..0 (integers, decimal, float,
  dateTime, date, boolean).

Every loop over input-proportional data is a `for` over a range with
mutable state (no recursion per item). The one recursive function,
`readStruct`, recurses once per NESTING level of a Thrift struct and is
bounded by its `depth` argument (RDF_Term nests at most three deep).
-/
import Std.Data.HashMap
import L4Factoidal.Tdb2.Format

namespace L4Factoidal.Tdb2

def blockSize : Nat := 8192
def ptrLen : Nat := 4

@[inline] def u8 (d : ByteArray) (i : Nat) : Nat :=
  if h : i < d.size then d[i].toNat else 0

def be32 (d : ByteArray) (i : Nat) : Nat :=
  (u8 d i <<< 24) ||| (u8 d (i+1) <<< 16) ||| (u8 d (i+2) <<< 8) ||| u8 d (i+3)

def be64 (d : ByteArray) (i : Nat) : Nat :=
  (be32 d i <<< 32) ||| be32 d (i+4)

def le64 (d : ByteArray) (i : Nat) : Nat := Id.run do
    let mut v := 0
    for j in [0:8] do
      v := v ||| (u8 d (i + j) <<< (8 * j))
    return v

/-- Two's complement value of the low `bits` bits of `v`. -/
def signExtend (v bits : Nat) : Int :=
  let x := v % 2 ^ bits
  if x ≥ 2 ^ (bits - 1) then (x : Int) - (2 ^ bits : Nat) else x

/-- `BPlusTreeParams.calcOrder(8192, recordLength)` with `Gap = 0`. -/
def treeOrder (recordLen : Nat) : Nat :=
  ((blockSize - 4 - recordLen) / (recordLen + ptrLen) + 1) / 2

/-- The files of one B+tree. -/
structure Tree where
  bpt : ByteArray
  idn : ByteArray
  dat : ByteArray

/-- Every record of a tree in key order: a depth-first walk from the root
    with an explicit stack (TDB2 trees are copy on write; record-block links
    are not followed). `fuel` bounds the number of blocks visited, so a
    malformed tree with a pointer cycle stops with an error. -/
def treeRecords (t : Tree) (recordLen : Nat) : Except String (Array ByteArray) := Id.run do
  if t.bpt.size < 24 then return .error "B+tree state file shorter than 24 bytes"
  let root := be64 t.bpt 0
  let maxRec := 2 * treeOrder recordLen - 1
  let fuel := t.idn.size / blockSize + t.dat.size / blockSize + 1
  -- stack entries: (isRecordBlock, block id)
  let mut stack : Array (Bool × Nat) := #[(false, root)]
  let mut out : Array ByteArray := #[]
  for _ in [0:fuel] do
    match stack.back? with
    | none => break
    | some (isRec, bid) =>
      stack := stack.pop
      let base := bid * blockSize
      if isRec then
        if base + blockSize > t.dat.size then
          return .error s!"record block {bid} outside the .dat file"
        let count := be32 t.dat base
        if 8 + count * recordLen > blockSize then
          return .error s!"record block {bid}: count {count} too large"
        for i in [0:count] do
          let s := base + 8 + i * recordLen
          out := out.push (t.dat.extract s (s + recordLen))
      else
        if base + blockSize > t.idn.size then
          return .error s!"tree node {bid} outside the .idn file"
        let head := be32 t.idn base
        let btype := head >>> 24
        let count := head % 2 ^ 24
        if btype != 6 && btype != 7 then
          return .error s!"tree node {bid}: block type {btype}, expected 6 or 7"
        if count > maxRec then
          return .error s!"tree node {bid}: count {count} above {maxRec}"
        let pstart := base + 4 + maxRec * recordLen
        -- push children right to left so the leftmost is popped first
        for j in [0:count + 1] do
          let i := count - j
          stack := stack.push (btype == 7, be32 t.idn (pstart + ptrLen * i))
  if !stack.isEmpty then return .error "B+tree walk did not finish (pointer cycle?)"
  return .ok out

/-! ## Thrift compact protocol (the subset `RDF_Term` uses) -/

inductive TVal where
  | bool (b : Bool)
  | int (i : Int)
  | dbl (bits : UInt64)
  | str (s : String)
  | strct (fields : Array (Nat × TVal))
  deriving Inhabited

/-- Unsigned varint at `pos`: (value, next position). -/
def varint (d : ByteArray) (pos : Nat) : Except String (Nat × Nat) := Id.run do
  let mut v := 0
  let mut p := pos
  for i in [0:10] do
    if p ≥ d.size then return .error "varint runs past the end"
    let b := u8 d p
    p := p + 1
    v := v ||| ((b % 128) <<< (7 * i))
    if b < 128 then return .ok (v, p)
  return .error "varint longer than 10 bytes"

def zigzag (v : Nat) : Int := if v % 2 == 0 then (v / 2 : Nat) else -((v / 2 : Nat) : Int) - 1

/-- A struct at `pos` (fields up to the STOP byte), nested at most `depth`
    levels. Returns the fields and the next position. -/
def readStruct (d : ByteArray) : Nat → Nat → Except String (Array (Nat × TVal) × Nat)
  | 0, _ => .error "Thrift struct nested too deep"
  | depth + 1, pos => Id.run do
    let mut p := pos
    let mut last := 0
    let mut fields : Array (Nat × TVal) := #[]
    for _ in [0:d.size + 1] do
      if p ≥ d.size then return .error "Thrift struct runs past the end"
      let h := u8 d p
      p := p + 1
      if h == 0 then return .ok (fields, p)
      let delta := h >>> 4
      let ty := h % 16
      let mut fid := last + delta
      if delta == 0 then
        match varint d p with
        | .error e => return .error e
        | .ok (v, q) => p := q; fid := (zigzag v).toNat
      last := fid
      if ty == 1 || ty == 2 then
        fields := fields.push (fid, .bool (ty == 1))
      else if ty == 3 then
        fields := fields.push (fid, .int (signExtend (u8 d p) 8)); p := p + 1
      else if ty == 4 || ty == 5 || ty == 6 then
        match varint d p with
        | .error e => return .error e
        | .ok (v, q) => p := q; fields := fields.push (fid, .int (zigzag v))
      else if ty == 7 then
        if p + 8 > d.size then return .error "double runs past the end"
        fields := fields.push (fid, .dbl (le64 d p).toUInt64); p := p + 8
      else if ty == 8 then
        match varint d p with
        | .error e => return .error e
        | .ok (n, q) =>
          if q + n > d.size then return .error "string runs past the end"
          match String.fromUTF8? (d.extract q (q + n)) with
          | none => return .error "string is not UTF-8"
          | some s => fields := fields.push (fid, .str s); p := q + n
      else if ty == 12 then
        match readStruct d depth p with
        | .error e => return .error e
        | .ok (fs, q) => fields := fields.push (fid, .strct fs); p := q
      else return .error s!"Thrift type {ty} is not used by RDF_Term"
    return .error "Thrift struct has no STOP byte"

def field? (fs : Array (Nat × TVal)) (id : Nat) : Option TVal :=
  (fs.find? (·.1 == id)).map (·.2)

def strField? (fs : Array (Nat × TVal)) (id : Nat) : Option String :=
  match field? fs id with
  | some (.str s) => some s
  | _ => none

/-! ## Terms in N-Quads form, as `tdb2.tdbdump` prints them -/

def xsd (local_ : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ local_

/-- N-Triples string escaping as Jena's writer applies it. -/
def escapeLex (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    out := match c with
      | '\\' => out ++ "\\\\"
      | '"' => out ++ "\\\""
      | '\n' => out ++ "\\n"
      | '\r' => out ++ "\\r"
      | '\t' => out ++ "\\t"
      | c => out.push c
  return out

def literal (lex : String) (dt : String) : String :=
  if dt == xsd "string" then "\"" ++ escapeLex lex ++ "\""
  else "\"" ++ escapeLex lex ++ "\"^^<" ++ dt ++ ">"

/-- An `RDF_Term` (`ThriftConvert.convert(RDF_Term)`). -/
def termOfThrift (fs : Array (Nat × TVal)) : Except String String :=
  match field? fs 1, field? fs 2, field? fs 3 with
  | some (.strct f), _, _ =>
      match strField? f 1 with | some i => .ok ("<" ++ i ++ ">") | none => .error "RDF_IRI without iri"
  | _, some (.strct f), _ =>
      match strField? f 1 with | some l => .ok ("_:B" ++ l) | none => .error "RDF_BNode without label"
  | _, _, some (.strct f) =>
      let lex := (strField? f 1).getD ""
      match strField? f 2, strField? f 5 with
      | some lang, dir =>
          if lang.isEmpty then
            .ok (literal lex ((strField? f 3).getD (xsd "string")))
          else
            .ok ("\"" ++ escapeLex lex ++ "\"@" ++ lang ++
                 (match dir with | some d => if d.isEmpty then "" else "--" ++ d | none => ""))
      | none, _ =>
          match strField? f 3 with
          | some dt => .ok (literal lex dt)
          | none => if (field? f 4).isSome then .error "RDF_Literal with a prefixed datatype"
                    else .ok (literal lex (xsd "string"))
  | _, _, _ =>
    match field? fs 10, field? fs 11, field? fs 12 with
    | some (.int v), _, _ => .ok (literal (toString v) (xsd "integer"))
    | _, some (.dbl b), _ => .ok (literal (javaDoubleString b) (xsd "double"))
    | _, _, some (.strct f) =>
        match field? f 1, field? f 2 with
        | some (.int v), sc =>
            let scale := match sc with | some (.int s) => s | _ => 0
            .ok (literal (plainDecimalInt v scale) (xsd "decimal"))
        | _, _ => .error "RDF_Decimal without value"
    | _, _, _ => .error s!"RDF_Term field {fs.map (·.1)} not supported (variable, triple term or prefix name)"

/-- Datatype local name of an inline integer NodeId type (`NodeIdType`). -/
def integerType (ty : Nat) : Option String :=
  match ty with
  | 1 => some "integer" | 10 => some "positiveInteger" | 11 => some "negativeInteger"
  | 12 => some "nonNegativeInteger" | 13 => some "nonPositiveInteger" | 14 => some "long"
  | 15 => some "int" | 16 => some "short" | 17 => some "byte" | 18 => some "unsignedLong"
  | 19 => some "unsignedInt" | 20 => some "unsignedShort" | 21 => some "unsignedByte"
  | _ => none

/-- The term a NodeId stands for (`NodeIdFactory.create64`,
    `NodeIdInline.extract`, `NodeTableTRDF.readNodeFromTable`). -/
def nodeOf (obj : ByteArray) (nid : Nat) : Except String String :=
  if nid >>> 63 == 0 then
    match readStruct obj 4 nid with
    | .ok (fs, _) => termOfThrift fs
    | .error e => .error s!"node table offset {nid}: {e}"
  else if (nid >>> 62) % 2 == 1 then
    -- DoubleNode62.unpack: sign bit 61, 9-bit exponent 60..52, significand.
    let x := nid % 2 ^ 62
    let sign := (x >>> 61) % 2
    let exp9 := (x >>> 52) % 512
    let sig := x % 2 ^ 52
    let exp11 := if exp9 == 0 then 0 else if exp9 == 0x1FF then 0x7FF else exp9 + 1023 - 255
    .ok (literal (xsdDoubleString ((sign <<< 63) ||| (exp11 <<< 52) ||| sig).toUInt64) (xsd "double"))
  else
    let ty := (nid >>> 56) % 128
    let v := nid % 2 ^ 56
    match integerType ty with
    | some local_ => .ok (literal (toString (signExtend v 56)) (xsd local_))
    | none =>
      match ty with
      | 2 => .ok (literal (canonicalDecimalWithDot (signExtend (v % 2 ^ 48) 48) ((v >>> 48) % 256))
                  (xsd "decimal"))
      | 3 => .ok (literal (xsdFloatString (v % 2 ^ 32).toUInt32) (xsd "float"))
      | 5 => .ok (literal (dateTimeLex v true) (xsd "dateTime"))
      | 6 => .ok (literal (dateTimeLex v true) (xsd "dateTimeStamp"))
      | 7 => .ok (literal (dateTimeLex v false) (xsd "date"))
      | 8 => if v == 0 then .ok (literal "false" (xsd "boolean"))
             else if v == 1 then .ok (literal "true" (xsd "boolean"))
             else .error s!"boolean NodeId value {v}"
      | _ => .error s!"inline NodeId type {ty} not known"

/-- The files a quad listing needs. -/
structure Database where
  spo : Tree
  gspo : Tree
  obj : ByteArray

/-- N-Quads lines of every quad: default graph from SPO, then named graphs
    from GSPO, each in index order. -/
def quadLines (db : Database) : Except String (Array String) := Id.run do
  let spo ← match treeRecords db.spo 24 with
    | .ok r => pure r | .error e => return .error s!"SPO: {e}"
  let gspo ← match treeRecords db.gspo 32 with
    | .ok r => pure r | .error e => return .error s!"GSPO: {e}"
  let mut cache : Std.HashMap Nat String := {}
  let mut out : Array String := Array.mkEmpty (spo.size + gspo.size)
  for (recs, width) in [(spo, 3), (gspo, 4)] do
    for r in recs do
      let mut terms : Array String := #[]
      for i in [0:width] do
        let nid := be64 r (8 * i)
        match cache.get? nid with
        | some s => terms := terms.push s
        | none =>
          match nodeOf db.obj nid with
          | .ok s => cache := cache.insert nid s; terms := terms.push s
          | .error e => return .error e
      out := out.push <|
        if width == 3 then s!"{terms[0]!} {terms[1]!} {terms[2]!} ."
        else s!"{terms[1]!} {terms[2]!} {terms[3]!} {terms[0]!} ."
  return .ok out

/-! ## Reading a database directory -/

def readTree (gen : System.FilePath) (name : String) : IO Tree := do
  pure { bpt := ← IO.FS.readBinFile (gen / s!"{name}.bpt")
         idn := ← IO.FS.readBinFile (gen / s!"{name}.idn")
         dat := ← IO.FS.readBinFile (gen / s!"{name}.dat") }

/-- The current generation directory: `dir` itself when it is a `Data-NNNN`
    directory, else its highest-numbered `Data-NNNN` child. -/
def generation (dir : System.FilePath) : IO (Except String System.FilePath) := do
  if (dir.fileName.getD "").startsWith "Data-" then return .ok dir
  let entries ← dir.readDir
  let gens := (entries.filter (·.fileName.startsWith "Data-")).map (·.fileName)
  match gens.toList.mergeSort (· ≥ ·) with
  | g :: _ => return .ok (dir / g)
  | [] => return .error s!"{dir}: no Data-NNNN generation directory (not a TDB2 database)"

/-- Every quad of the TDB2 database at `dir`, as N-Quads text. -/
def readDatabaseNQuads (dir : System.FilePath) : IO (Except String String) := do
  try
    match ← generation dir with
    | .error e => return .error e
    | .ok gen =>
      let jrnl := gen / "journal.jrnl"
      if ← jrnl.pathExists then
        if (← jrnl.metadata).byteSize != 0 then
          return .error s!"{jrnl}: journal is not empty; open the database with Jena once to replay it"
      let db : Database := { spo := ← readTree gen "SPO", gspo := ← readTree gen "GSPO",
                             obj := ← IO.FS.readBinFile (gen / "nodes-data.obj") }
      match quadLines db with
      | .error e => return .error e
      | .ok lines => return .ok (String.join (lines.toList.map (· ++ "\n")))
  catch e => return .error s!"{dir}: {e}"

/-! ## Checks on built byte strings -/

private def bytes (l : List Nat) : ByteArray := ⟨l.toArray.map (·.toUInt8)⟩

-- RDF_Term{iri: RDF_IRI{iri: "a"}} in compact protocol: field 1 struct (0x1C),
-- field 1 binary (0x18), length 1, 'a', STOP, STOP.
#guard (match readStruct (bytes [0x1C, 0x18, 1, 0x61, 0, 0]) 4 0 with
        | .ok (fs, p) => (termOfThrift fs).toOption == some "<a>" && p == 6 | _ => false)
-- valInteger = -3 (field 10, i64, zigzag 5): delta 10 type 6 = 0xA6.
#guard (match readStruct (bytes [0xA6, 5, 0]) 4 0 with
        | .ok (fs, _) => (termOfThrift fs).toOption ==
            some "\"-3\"^^<http://www.w3.org/2001/XMLSchema#integer>" | _ => false)
-- A struct without a STOP byte is refused.
#guard (readStruct (bytes [0x1C, 0x18, 1, 0x61]) 4 0).toOption.isNone
-- Inline integer NodeId: type 1, value -1 (56 one bits).
#guard (nodeOf ByteArray.empty ((1 <<< 63) ||| (1 <<< 56) ||| (2 ^ 56 - 1))).toOption ==
  some "\"-1\"^^<http://www.w3.org/2001/XMLSchema#integer>"
-- Inline boolean NodeId: type 8.
#guard (nodeOf ByteArray.empty ((1 <<< 63) ||| (8 <<< 56) ||| 1)).toOption ==
  some "\"true\"^^<http://www.w3.org/2001/XMLSchema#boolean>"
#guard (nodeOf ByteArray.empty ((1 <<< 63) ||| (8 <<< 56) ||| 2)).toOption.isNone
-- Inline decimal 1.50 (value 150, scale 2) prints Jena's form "1.5".
#guard (nodeOf ByteArray.empty ((1 <<< 63) ||| (2 <<< 56) ||| (2 <<< 48) ||| 150)).toOption ==
  some "\"1.5\"^^<http://www.w3.org/2001/XMLSchema#decimal>"
-- A tree with an empty state file is refused.
#guard (treeRecords { bpt := ByteArray.empty, idn := ByteArray.empty, dat := ByteArray.empty } 24
  |>.toOption.isNone)

end L4Factoidal.Tdb2
