/-
L4Factoidal.XPath4.Csv — CSV in XPath 4.0: `fn:parse-csv`, `fn:csv-doc`,
`fn:csv-to-xml` (F&O 4.0 §17.5), with the record
`fn:parsed-csv-structure-record` (§17.5.6) and the XML representation of
§17.5.9.

Spec: F&O 4.0 editor's draft, qtspecs commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c, `function-catalog.xml`. The
draft has dropped `fn:csv-to-arrays` (its rules are absorbed by
`fn:parse-csv`), so there is no such function here.

The parser is one loop over the characters with an index (no recursion
per character or row), so a CSV of 100 000 rows is parsed in constant
stack. Line endings are normalised first (CR LF and CR to LF), also inside
quoted fields. A quote character starts a quoted field only as the first
character of the field; in an unquoted field it is an ordinary character.
After the closing quote only a separator, a newline or the end of the
input is allowed (`FOCV0001`).

A row that is empty after trimming and is ended by a newline is a blank
row (`[]`); an unterminated last line that is empty after trimming is not
a row. A comment row (first character is the comment marker) is dropped
up to and including the next newline, before the header is looked for.

The `get` entry of the record is an inline function item whose body is
XPath text, parsed by `XPath4.Parser`, closing over the rows and the
column index.

`fn:csv-doc` reads a resource that the caller read in advance
(`Env.resources`, as for `fn:unparsed-text`); the evaluator does no I/O.
-/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.XPath4.Parser

namespace L4Factoidal.XPath4

/-! ## Options -/

structure CsvOpts where
  sep : Char := ','
  quote : Char := '"'
  comment : Option Char := none
  trim : Bool := false
  header : Bool := false
  names : Option (List String) := none
  select : List Int := []
  trimRows : Bool := false

def csvOptionNames : List String :=
  ["separator", "quote-character", "comment-marker", "trim-whitespace", "header",
   "select-columns", "trim-rows"]

def isStringy (a : Atomic) : Bool := a.is .string || a.is .anyURI || a.ty == .untyped

/-- A single-character option: `FOCV0002` for any other length. -/
def csvCharOpt (opts : Seq) (key : String) : M (Option Char) := do
  match optLookup opts key with
  | none => pure none
  | some [] => if key == "comment-marker" then pure none else err "XPTY0004" (key ++ " must be a string")
  | some [.atom a] =>
    if !isStringy a then err "XPTY0004" (key ++ " must be a string")
    else
      match a.str.toList with
      | [c] => pure (some c)
      | _ => err "FOCV0002" (key ++ " must be a single character")
  | some _ => err "XPTY0004" (key ++ " must be a single string")

def csvOpts (opts : Seq) : M CsvOpts := do
  checkOptionKeys opts csvOptionNames
  let sep ← csvCharOpt opts "separator"
  let quote ← csvCharOpt opts "quote-character"
  let comment ← csvCharOpt opts "comment-marker"
  let o : CsvOpts := { sep := sep.getD ',', quote := quote.getD '"', comment }
  if o.sep == '\n' || o.quote == '\n' || comment == some '\n' then
    err "FOCV0002" "a newline cannot be a separator, quote character or comment marker"
  if o.sep == o.quote || comment == some o.sep || comment == some o.quote then
    err "FOCV0002" "the same character is used in several roles"
  let trim ← optBool opts "trim-whitespace" false
  let trimRows ← optBool opts "trim-rows" false
  let (header, names) ← match optLookup opts "header" with
    | none => pure (false, none)
    | some [.atom ⟨_, .bool b⟩] => pure (b, none)
    | some s =>
      let ns ← s.mapM (fun i => match i with
        | .atom a => if isStringy a then pure a.str else err "XPTY0004" "header must be a boolean or strings"
        | _ => err "XPTY0004" "header must be a boolean or strings")
      pure (false, some ns)
  let select ← match optLookup opts "select-columns" with
    | none => pure []
    | some s => s.mapM (fun i => match i with
        | .atom ⟨_, .int k⟩ => pure k
        | _ => err "XPTY0004" "select-columns must be integers")
  pure { o with trim, trimRows, header, names, select }

/-! ## The parser -/

/-- Rows of fields. See the module comment for the blank-row and comment rules. -/
def parseRows (o : CsvOpts) (text : String) : M (Array (Array String)) := do
  let text := (text.replace "\r\n" "\n").replace "\r" "\n"
  let cs := text.toList.toArray
  let n := cs.size
  let mut rows : Array (Array String) := #[]
  let mut i := 0
  while i < n do
    if o.comment == some cs[i]! then
      while i < n && cs[i]! != '\n' do i := i + 1
      i := i + 1
      continue
    let mut fields : Array String := #[]
    let mut anyQuoted := false
    let mut done := false
    let mut terminated := false
    while !done do
      if i < n && cs[i]! == o.quote then
        anyQuoted := true
        i := i + 1
        let mut buf := ""
        let mut closed := false
        while !closed do
          if i ≥ n then err "FOCV0001" "a quoted field is not closed"
          let c := cs[i]!
          if c == o.quote then
            if i + 1 < n && cs[i + 1]! == o.quote then
              buf := buf.push c
              i := i + 2
            else
              i := i + 1
              closed := true
          else
            buf := buf.push c
            i := i + 1
        fields := fields.push buf
        if i ≥ n then done := true
        else if cs[i]! == o.sep then i := i + 1
        else if cs[i]! == '\n' then
          i := i + 1
          done := true
          terminated := true
        else err "FOCV0001" "a closing quote must be followed by a separator or a newline"
      else
        let start := i
        while i < n && cs[i]! != o.sep && cs[i]! != '\n' do i := i + 1
        let raw := String.ofList (cs.extract start i).toList
        fields := fields.push (if o.trim then trimWs raw else raw)
        if i ≥ n then done := true
        else if cs[i]! == o.sep then i := i + 1
        else
          i := i + 1
          done := true
          terminated := true
    if fields.size == 1 && !anyQuoted && fields[0]! == "" then
      if terminated then rows := rows.push #[]
    else rows := rows.push fields
  pure rows

/-! ## The parsed record -/

structure CsvData where
  columns : List String
  index : List (String × Nat)
  rows : Array (Array String)

def selectCols (sel : List Int) (row : Array String) : Array String :=
  (sel.toArray).map (fun k => if k ≥ 1 && k ≤ (row.size : Int) then row[(k - 1).toNat]! else "")

def fitRow (w : Nat) (row : Array String) : Array String :=
  if row.size ≥ w then row.extract 0 w else row ++ Array.replicate (w - row.size) ""

def indexOfNames (names : List String) : List (String × Nat) :=
  (names.foldl (fun (acc : List (String × Nat) × Nat) nm =>
    let (l, k) := acc
    if nm != "" && !l.any (·.1 == nm) then (l ++ [(nm, k + 1)], k + 1) else (l, k + 1)) ([], 0)).1

def csvData (o : CsvOpts) (all : Array (Array String)) : CsvData :=
  let width := (all[0]?).map (·.size)
  let (hdr, body) : Option (Array String) × Array (Array String) :=
    if o.header && all.size > 0 then (some (all[0]!.map trimWs), all.extract 1 all.size) else (none, all)
  let (hdr, body) :=
    if !o.select.isEmpty then (hdr.map (selectCols o.select), body.map (selectCols o.select))
    else if o.trimRows then
      match width with
      | some w => (hdr, body.map (fitRow w))
      | none => (hdr, body)
    else (hdr, body)
  let columns : List String := match o.names, hdr with
    | some ns, _ => ns
    | none, some h => h.toList
    | none, none => []
  { columns, index := indexOfNames columns, rows := body }

def strItems (l : List String) : Seq := l.map (fun s => Item.atom (Atomic.ofStr s))

def csvGetBody : String :=
  "let $col := (if ($c instance of xs:string) then " ++
  "(if (map:contains($ci, $c)) then map:get($ci, $c) else " ++
  "error(QName('http://www.w3.org/2005/xqt-errors', 'FOCV0004'), 'no such column')) else $c) " ++
  "return (if ($r lt 1 or $r gt count($rows) or $col lt 1) then '' else " ++
  "(let $row := $rows[$r] return " ++
  "if ($col gt array:size($row)) then '' else array:get($row, $col)))"

def csvRecord (d : CsvData) : M Seq := do
  let rowsSeq : Seq := d.rows.toList.map (fun r => Item.arr (r.toList.map (fun s => sStr s)))
  let indexMap : Seq := [.map (d.index.map (fun (k, v) => (Atomic.ofStr k, sInt (Int.ofNat v))))]
  let body ← parseXPath csvGetBody
  let tr ← parseSeqType "xs:integer"
  let tc ← parseSeqType "(xs:integer | xs:string)"
  let tret ← parseSeqType "xs:string"
  let qn (s : String) : QN := { uri := "", loc := s }
  let get : Item := .fn (.inline [(qn "r", tr), (qn "c", tc)] tret body false
    [(qn "rows", rowsSeq), (qn "ci", indexMap)])
  pure [.map [
    (Atomic.ofStr "columns", strItems d.columns),
    (Atomic.ofStr "column-index", indexMap),
    (Atomic.ofStr "rows", rowsSeq),
    (Atomic.ofStr "get", [get])]]

def parseCsvText (text : String) (opts : Seq) : M CsvData := do
  let o ← csvOpts opts
  let rows ← parseRows o text
  pure (csvData o rows)

def parseCsvFn : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v => csvRecord (← parseCsvText v.str (argN a 1))

def csvDocFn : LibFn := fun _ e a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some h =>
    let text ← textResource e h.str
    csvRecord (← parseCsvText text (argN a 1))

/-! ## fn:csv-to-xml -/

def csvScope : List (String × String) := [("", nsFN), ("xml", nsXML)]

def fnName (l : String) : QN := { uri := nsFN, loc := l, pfx := "" }

/-- Append an element with an optional `column` attribute and optional
    text; the children (given by `kids`) are filled in by the caller. Returns the
    array and the index of the element. -/
def pushEl (ns : Array NRec) (loc : String) (par : Nat) : Array NRec × Nat :=
  let i := ns.size
  (ns.push { kind := .element, name := fnName loc, parent := some par, inscope := csvScope }, i)

def pushLeaf (ns : Array NRec) (loc : String) (par : Nat) (col : Option String) (txt : String) :
    Array NRec × Nat := Id.run do
  let (ns0, el) := pushEl ns loc par
  let mut ns := ns0
  let mut ats : Array Nat := #[]
  if let some c := col then
    ats := ats.push ns.size
    ns := ns.push { kind := .attribute, name := { uri := "", loc := "column", pfx := "" }, value := c,
                    parent := some el, last := ns.size }
  let mut kids : Array Nat := #[]
  if txt != "" then
    kids := kids.push ns.size
    ns := ns.push { kind := .text, value := txt, parent := some el, last := ns.size }
  let sz := ns.size
  ns := ns.modify el (fun r => { r with attrs := ats, children := kids, last := sz - 1 })
  (ns, el)

def csvDoc (d : CsvData) : Doc := Id.run do
  let mut ns : Array NRec := #[{ kind := .document }]
  let (ns1, csv) := pushEl ns "csv" 0
  ns := ns1
  let mut csvKids : Array Nat := #[]
  let colArr := d.columns.toArray
  let lastCol := (List.range colArr.size).foldl (fun acc k => if colArr[k]! != "" then some k else acc) none
  if let some lc := lastCol then
    let (ns2, cols) := pushEl ns "columns" csv
    ns := ns2
    csvKids := csvKids.push cols
    let mut ckids : Array Nat := #[]
    for k in [0:lc + 1] do
      let (ns3, c) := pushLeaf ns "column" cols none colArr[k]!
      ns := ns3
      ckids := ckids.push c
    let sz := ns.size
    ns := ns.modify cols (fun r => { r with children := ckids, last := sz - 1 })
  let (ns2, rowsEl) := pushEl ns "rows" csv
  ns := ns2
  csvKids := csvKids.push rowsEl
  let mut rkids : Array Nat := #[]
  for row in d.rows do
    let (ns3, re) := pushEl ns "row" rowsEl
    ns := ns3
    rkids := rkids.push re
    let mut fkids : Array Nat := #[]
    let mut k := 0
    for f in row do
      let nm := (colArr[k]?).getD ""
      let (ns4, fe) := pushLeaf ns "field" re (if nm != "" then some nm else none) f
      ns := ns4
      fkids := fkids.push fe
      k := k + 1
    let sz := ns.size
    ns := ns.modify re (fun r => { r with children := fkids, last := sz - 1 })
  let sz := ns.size
  ns := ns.modify rowsEl (fun r => { r with children := rkids, last := sz - 1 })
  let sz := ns.size
  ns := ns.modify csv (fun r => { r with children := csvKids, last := sz - 1 })
  let sz := ns.size
  ns := ns.modify 0 (fun r => { r with children := #[csv], last := sz - 1 })
  { nodes := ns }

def csvToXmlFn : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    let d ← parseCsvText v.str (argN a 1)
    let sig := v.str ++ "\x00" ++ toString d.columns ++ "\x00" ++ toString d.rows.size
    pure [(csvDoc d).rootItem (runtimeDocId "csv-to-xml" sig)]

def csvTable : List (String × LibFn) := [
  ent "parse-csv" parseCsvFn,
  ent "csv-doc" csvDocFn,
  ent "csv-to-xml" csvToXmlFn
]

end L4Factoidal.XPath4
