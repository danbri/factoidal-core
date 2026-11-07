import L4Factoidal.Rendering.Style

/-! Table structure and the table width and height algorithms, as pure functions of
the DOM arena, the computed styles and the cell measurements that `Layout` gives.

* The table box tree (CSS 2.1 §17.2.1, the anonymous table objects): internal table
  boxes outside a table are wrapped in an anonymous table (`segments`); rows and cells
  that are missing are made anonymous (`build`): a cell that is not in a row gets an
  anonymous row, and content that is not a cell gets an anonymous cell. Header and
  footer groups move to the top and the bottom (CSS 2.1 §17.2).
* The slots of the grid (HTML §4.9.12, the table processing model): `colspan`
  (1 to 1000) and `rowspan` (0 to 65534, 0 means the end of the row group), and the
  slots that a row span covers in the rows below.
* Column widths, automatic layout: the min-content and max-content widths of each
  column from its cells, spanning cells spread over their columns (CSS 2.1 §17.5.2.2),
  and the distribution of the table width over the columns by the four guesses of
  CSS Tables 3 §3.9.3 (min-content; percentages; specified widths; max-content), with
  the width over the last guess given to automatic columns first.
* Fixed layout (`table-layout: fixed`, CSS 2.1 §17.5.2.1): widths from the column
  elements and the first row only.
* Row heights (CSS 2.1 §17.5.3): the tallest cell of a row, row spans spread over
  their rows, the rest of a specified table height spread over the rows.

The cell measurements come from `Layout`, through the inline layout that draws the
same text, so that line breaking and fonts are the same in both. Not done here:
`border-collapse: collapse` borders (there are no borders in this profile,
https://github.com/danbri/factoidal/issues/1273), `visibility: collapse`, baseline
alignment of cells (a baseline cell is placed as a top cell), and `inline-table` as an
atomic inline (https://github.com/danbri/factoidal/issues/1272). -/
namespace L4Factoidal.Rendering.Table
open DOM CSS

/-- The content of a cell: an element, or the anonymous cell made for other content. -/
inductive Source where
  | element (id : Nat)
  /-- Content of `parent` that is not in a cell: those children, in an anonymous cell. -/
  | anonymous (parent : Nat) (kids : Array Nat)
  deriving Repr, BEq, Inhabited

structure Cell where
  source : Source
  row : Nat
  col : Nat
  rowSpan : Nat := 1
  colSpan : Nat := 1
  deriving Repr, Inhabited

structure Row where
  /-- The row element, `none` for an anonymous row. -/
  element : Option Nat
  /-- The row group element, `none` for an anonymous row group. -/
  group : Option Nat
  deriving Repr, Inhabited

def columnCount (cells : List Cell) : Nat :=
  cells.foldl (fun m c => max m (c.col+c.colSpan)) 0

structure Grid where
  rows : Array Row := #[]
  cells : Array Cell := #[]
  columns : Nat := 0
  captions : Array Nat := #[]
  /-- The `col` or `colgroup` element of each column that has one, by column index. -/
  columnElements : Array (Option Nat) := #[]
  deriving Repr, Inhabited

/-- The grid of these rows and cells. Its column count is the end of the last cell, or the
number of columns that `col` and `colgroup` elements make when that is more (HTML §4.9.12). -/
def Grid.ofCells (rows : Array Row) (cells : Array Cell) (captions : Array Nat)
    (columnElements : Array (Option Nat)) : Grid :=
  {rows, cells, captions, columnElements, columns := max (columnCount cells.toList) columnElements.size}

private theorem le_foldl_max (l : List Cell) (init : Nat) :
    init ≤ l.foldl (fun m c => max m (c.col+c.colSpan)) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons c rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem mem_le_foldl_max (l : List Cell) (init : Nat) (c : Cell) (h : c ∈ l) :
    c.col+c.colSpan ≤ l.foldl (fun m c => max m (c.col+c.colSpan)) init := by
  induction l generalizing init with
  | nil => cases h
  | cons d rest ih =>
    simp only [List.foldl_cons]
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max rest _)
    | tail _ h => exact ih _ h

/-- Every cell of a grid ends at or before the last column: the column count is the
end of the cell that ends last. -/
theorem Grid.ofCells_cells_within (rows : Array Row) (cells : Array Cell) (captions : Array Nat)
    (columnElements : Array (Option Nat)) (c : Cell) (h : c ∈ cells.toList) :
    c.col+c.colSpan ≤ (Grid.ofCells rows cells captions columnElements).columns :=
  Nat.le_trans (mem_le_foldl_max cells.toList 0 c h) (Nat.le_max_left _ _)

/-- Text that is only white space, comments and processing instructions do not make
anonymous cells between table boxes (CSS 2.1 §17.2.1 rule 1). -/
def ignorable (dom : Dom) (styles : Array Computed) (id : Nat) : Bool :=
  let n := dom.get id
  (styles[id]?.map (·.display == .none)).getD false ||
  n.type == .comment || n.type == .pi || n.type == .doctype ||
  (n.type == .text && n.data.all fun c => c == ' ' || c == '\n' || c == '\t' || c == '\r' || c.toNat == 12)

private def displayOf (styles : Array Computed) (id : Nat) : Display :=
  (styles[id]?.map (·.display)).getD .inline

/-- The children of a block container, with each run of internal table boxes
(and the white space between them) as one anonymous table (CSS 2.1 §17.2.1 rule 3). -/
inductive Segment where
  | node (id : Nat)
  | run (kids : Array Nat)
  deriving Repr, BEq

def segments (dom : Dom) (styles : Array Computed) (kids : Array Nat) : Array Segment := Id.run do
  let mut out : Array Segment := #[]
  let mut run : Array Nat := #[]
  let mut held : Array Nat := #[]
  for k in kids do
    if (displayOf styles k).isTableInternal then
      run := run.push k
      held := #[]
    else if !run.isEmpty && ignorable dom styles k then held := held.push k
    else
      if !run.isEmpty then
        out := out.push (.run run)
        run := #[]
        out := out ++ held.map .node
        held := #[]
      out := out.push (.node k)
  if !run.isEmpty then
    out := out.push (.run run)
    out := out ++ held.map .node
  return out

/-- The cells of one row: cell children as they are, other content in anonymous cells. -/
def rowCells (dom : Dom) (styles : Array Computed) (row : Nat) (kids : Array Nat) : Array Source := Id.run do
  let mut out : Array Source := #[]
  let mut run : Array Nat := #[]
  for k in kids do
    if displayOf styles k == .tableCell then
      if !run.isEmpty then
        out := out.push (.anonymous row run)
        run := #[]
      out := out.push (.element k)
    else if displayOf styles k == .none then pure ()
    else if !(run.isEmpty && ignorable dom styles k) then run := run.push k
  if run.any (fun k => !ignorable dom styles k) then out := out.push (.anonymous row run)
  return out

structure RowSpec where
  element : Option Nat
  cells : Array Source
  deriving Repr, Inhabited
structure GroupSpec where
  element : Option Nat
  rows : Array RowSpec
  deriving Repr, Inhabited

/-- The rows of a row group's children: row children as they are, and each run of
other content (cells and anything else) in one anonymous row. -/
def groupRows (dom : Dom) (styles : Array Computed) (group : Nat) (kids : Array Nat) : Array RowSpec := Id.run do
  let mut out : Array RowSpec := #[]
  let mut run : Array Nat := #[]
  for k in kids do
    let d := displayOf styles k
    if d == .tableRow then
      if !run.isEmpty then
        let cells := rowCells dom styles group run
        if !cells.isEmpty then out := out.push ⟨none,cells⟩
        run := #[]
      out := out.push ⟨some k,rowCells dom styles k (dom.get k).kids⟩
    else if d == .none || d == .tableCaption || d == .tableColumn || d == .tableColumnGroup then pure ()
    else run := run.push k
  if !run.isEmpty then
    let cells := rowCells dom styles group run
    if !cells.isEmpty then out := out.push ⟨none,cells⟩
  return out

/-- An HTML integer attribute (HTML §2.3.4.1, the leading digits), or `none`. -/
private def integerAttribute (n : DOM.Node) (key : String) : Option Nat :=
  let digits := (attrValue n key).trimAscii.toString.toList.takeWhile Char.isDigit
  if digits.isEmpty then none else some (String.ofList digits).toNat!

/-- `colspan`, 1 to 1000; 0 or a value that is not a number is 1 (HTML §4.9.11). -/
def colSpanOf (dom : Dom) : Source → Nat
  | .element id => match integerAttribute (dom.get id) "colspan" with
    | some n => if n == 0 then 1 else min n 1000
    | none => 1
  | .anonymous .. => 1
/-- `rowspan`, 0 to 65534; a value that is not a number is 1 (HTML §4.9.11). -/
def rowSpanOf (dom : Dom) : Source → Nat
  | .element id => match integerAttribute (dom.get id) "rowspan" with
    | some n => min n 65534
    | none => 1
  | .anonymous .. => 1

/-- The slots of each cell (HTML §4.9.12): a cell takes the first column of its row
that no row span from above covers. Row spans end at the end of their row group. -/
def place (dom : Dom) (groups : Array GroupSpec) : Array Row × Array Cell := Id.run do
  let mut rows : Array Row := #[]
  let mut cells : Array Cell := #[]
  for g in groups do
    let start := rows.size
    let count := g.rows.size
    -- cover[c]: the first row (absolute) that is not covered in column c.
    let mut cover : Array Nat := #[]
    for i in [0:count] do
      let r := g.rows[i]!
      let rowIndex := start+i
      rows := rows.push ⟨r.element,g.element⟩
      let mut c := 0
      for source in r.cells do
        for _ in [0:cover.size+1] do
          if cover.getD c 0 > rowIndex then c := c+1 else break
        let colSpan := colSpanOf dom source
        let wanted := rowSpanOf dom source
        let rowSpan := if wanted == 0 then count-i else min wanted (count-i)
        cells := cells.push {source,row := rowIndex,col := c,rowSpan,colSpan}
        if cover.size < c+colSpan then cover := cover ++ Array.replicate (c+colSpan-cover.size) 0
        for j in [c:c+colSpan] do cover := cover.set! j (rowIndex+rowSpan)
        c := c+colSpan
  return (rows,cells)

/-- The table grid of a table's children (a table element's, or an anonymous table's run). -/
def build (dom : Dom) (styles : Array Computed) (table : Nat) (kids : Array Nat) : Grid := Id.run do
  let mut header : Option GroupSpec := none
  let mut footer : Option GroupSpec := none
  let mut bodies : Array GroupSpec := #[]
  let mut captions : Array Nat := #[]
  let mut columns : Array (Option Nat) := #[]
  let mut run : Array Nat := #[]
  for k in kids do
    let d := displayOf styles k
    let structural := d == .tableCaption || d == .tableColumn || d == .tableColumnGroup ||
      d == .tableRowGroup || d == .tableHeaderGroup || d == .tableFooterGroup
    if structural && !run.isEmpty then
      let rows := groupRows dom styles table run
      if !rows.isEmpty then bodies := bodies.push ⟨none,rows⟩
      run := #[]
    match d with
    | .tableCaption => captions := captions.push k
    | .tableColumn =>
      let span := max 1 (min 1000 ((integerAttribute (dom.get k) "span").getD 1))
      columns := columns ++ Array.replicate span (some k)
    | .tableColumnGroup =>
      let cols := (dom.get k).kids.filter fun c => displayOf styles c == .tableColumn
      if cols.isEmpty then
        let span := max 1 (min 1000 ((integerAttribute (dom.get k) "span").getD 1))
        columns := columns ++ Array.replicate span (some k)
      else
        for c in cols do
          let span := max 1 (min 1000 ((integerAttribute (dom.get c) "span").getD 1))
          columns := columns ++ Array.replicate span (some c)
    | .tableHeaderGroup =>
      let g : GroupSpec := ⟨some k,groupRows dom styles k (dom.get k).kids⟩
      if header.isNone then header := some g else bodies := bodies.push g
    | .tableFooterGroup =>
      let g : GroupSpec := ⟨some k,groupRows dom styles k (dom.get k).kids⟩
      if footer.isNone then footer := some g else bodies := bodies.push g
    | .tableRowGroup => bodies := bodies.push ⟨some k,groupRows dom styles k (dom.get k).kids⟩
    | .none => pure ()
    | _ => if !(run.isEmpty && ignorable dom styles k) then run := run.push k
  if !run.isEmpty then
    let rows := groupRows dom styles table run
    if !rows.isEmpty then bodies := bodies.push ⟨none,rows⟩
  let groups := (header.toArray ++ bodies ++ footer.toArray)
  let (rows,cells) := place dom groups
  return Grid.ofCells rows cells captions columns

/-! ### Widths -/

/-- What a cell or a column element asks of its columns: outer widths (padding included). -/
structure Measure where
  min : Float := 0
  max : Float := 0
  /-- A specified width in pixels, padding included. -/
  fixed : Option Float := none
  /-- A specified percentage of the table width, as a fraction. -/
  percent : Option Float := none
  deriving Repr, Inhabited

abbrev Column := Measure

def total (xs : Array Float) : Float := xs.foldl (·+·) 0

/-- Add `extra` to the entries `start ..< start+count` of `xs`, in proportion to
`weights` (equal shares when the weights add up to zero). -/
def spread (xs weights : Array Float) (start count : Nat) (extra : Float) : Array Float := Id.run do
  let mut sum : Float := 0
  for j in [start:start+count] do sum := sum+weights.getD j 0
  let mut out := xs
  for j in [start:start+count] do
    let share := if sum > 0 then weights.getD j 0/sum else 1/Float.ofNat count
    out := out.modify j (·+extra*share)
  return out

/-- Column measures from the cells (CSS 2.1 §17.5.2.2 steps 1 to 3): single-column
cells first, then spanning cells from the narrowest span up, each giving what its
columns lack in proportion to their max-content widths. `hs` is the horizontal border
spacing, which a spanning cell also covers. -/
def columns (count : Nat) (cells : Array Cell) (measures : Array Measure)
    (elements : Array Measure) (hs : Float) : Array Column := Id.run do
  let mut cols : Array Column := Array.replicate count {}
  for j in [0:min count elements.size] do
    let e := elements[j]!
    cols := cols.modify j fun c => {c with fixed := e.fixed, percent := e.percent, max := max c.max (e.fixed.getD 0)}
  for (cell,m) in cells.zip measures do
    if cell.colSpan == 1 && cell.col < count then
      cols := cols.modify cell.col fun c =>
        {min := max c.min m.min, max := max c.max (max m.max (m.fixed.getD 0)),
         fixed := match c.fixed,m.fixed with | some a,some b => some (max a b) | a,b => a.orElse fun _ => b,
         percent := match c.percent,m.percent with | some a,some b => some (max a b) | a,b => a.orElse fun _ => b}
  let spanning := (cells.zip measures).filter (·.1.colSpan > 1) |>.qsort (fun a b => a.1.colSpan < b.1.colSpan)
  for (cell,m) in spanning do
    let count' := min cell.colSpan (count-cell.col)
    if count' == 0 then continue
    let gaps := hs*Float.ofNat (count'-1)
    let mins := cols.map (·.min)
    let maxs := cols.map (·.max)
    let sumMin := (mins.extract cell.col (cell.col+count')).foldl (·+·) 0
    let sumMax := (maxs.extract cell.col (cell.col+count')).foldl (·+·) 0
    let needMin := m.min-gaps-sumMin
    let newMins := if needMin > 0 then spread mins maxs cell.col count' needMin else mins
    let wantMax := max m.max (m.fixed.getD 0)
    let needMax := wantMax-gaps-sumMax
    let newMaxs := if needMax > 0 then spread maxs maxs cell.col count' needMax else maxs
    cols := cols.mapIdx fun j c => {c with min := newMins[j]!, max := newMaxs[j]!}
  return cols.map fun c =>
    let max' := max c.min (match c.fixed with | some f => max f c.min | none => c.max)
    {c with max := max'}

/-- The four width guesses of CSS Tables 3 §3.9.3 for a table width `target`. -/
def guesses (cols : Array Column) (target : Float) : Array (Array Float) :=
  let pct (c : Column) : Option Float := c.percent.map fun p => max c.min (p*target)
  #[cols.map (·.min),
    cols.map (fun c => (pct c).getD c.min),
    cols.map (fun c => (pct c).getD (match c.fixed with | some f => max c.min f | none => c.min)),
    cols.map (fun c => (pct c).getD (match c.fixed with | some f => max c.min f | none => c.max))]

/-- The width of each column for a sum of column widths `target` (CSS Tables 3 §3.9.3):
between two neighbouring guesses, the columns move from the one to the other by the same
fraction; past the max-content guess, the rest goes to automatic columns in proportion to
their max-content widths, else to columns with a specified width, else to percentage
columns, else equally. Below the min-content guess, every column has its min-content width. -/
def distribute (cols : Array Column) (target : Float) : Array Float := Id.run do
  let gs := guesses cols target
  let g0 := gs[0]!
  if cols.isEmpty || target <= total g0 then return g0
  for i in [0:3] do
    let a := gs[i]!
    let b := gs[i+1]!
    let sa := total a
    let sb := total b
    if target <= sb then
      if sb <= sa then return b
      let t := (target-sa)/(sb-sa)
      return a.mapIdx fun j x => x+t*(b[j]!-x)
  let top := gs[3]!
  let extra := target-total top
  let auto := cols.map fun c => c.fixed.isNone && c.percent.isNone
  let weighted (w : Column → Float) (keep : Column → Bool) : Array Float :=
    cols.map fun c => if keep c then w c else 0
  let autoMax := weighted (·.max) (fun c => c.fixed.isNone && c.percent.isNone)
  let weights :=
    if total autoMax > 0 then autoMax
    else if auto.any id then weighted (fun _ => 1) (fun c => c.fixed.isNone && c.percent.isNone)
    else
      let fixed := weighted (fun c => c.fixed.getD 0) (fun c => c.percent.isNone)
      if total fixed > 0 then fixed
      else
        let pct := weighted (fun c => c.percent.getD 0) (fun _ => true)
        if total pct > 0 then pct else cols.map fun _ => 1
  return spread top weights 0 cols.size extra

/-- Fixed table layout (CSS 2.1 §17.5.2.1): a column takes the width of its column
element, else of the first-row cell that starts in it (a spanning cell's width is
divided equally); percentages are of `target`; the columns with no width share what
is left equally. The table is wider than `target` when the widths need it. -/
def fixedWidths (count : Nat) (firstRow : Array (Cell × Measure)) (elements : Array Measure)
    (target hs : Float) : Array Float := Id.run do
  let asked (m : Measure) : Option Float :=
    (m.percent.map (·*target)).orElse fun _ => m.fixed
  let mut widths : Array (Option Float) := Array.replicate count none
  for j in [0:min count elements.size] do widths := widths.set! j (asked elements[j]!)
  for (cell,m) in firstRow do
    if let some w := asked m then
      let span := min cell.colSpan (count-cell.col)
      if span > 0 then
        let each := max 0 (w-hs*Float.ofNat (span-1))/Float.ofNat span
        for j in [cell.col:cell.col+span] do
          if widths[j]!.isNone then widths := widths.set! j (some each)
  let given := widths.foldl (fun s w => s+w.getD 0) 0
  let unset := (widths.filter Option.isNone).size
  let rest := if unset == 0 then 0 else max 0 (target-given)/Float.ofNat unset
  let out := widths.map (·.getD rest)
  let sum := total out
  -- All columns specified and narrower than the table: they grow in proportion.
  if unset == 0 && sum < target && count > 0 then return spread out out 0 count (target-sum)
  return out

/-- The start of each track after spacing `gap` before it: gap, then each size and gap. -/
def offsets (sizes : Array Float) (gap : Float) : Array Float := Id.run do
  let mut pos := gap
  let mut out : Array Float := #[]
  for s in sizes do
    out := out.push pos
    pos := pos+s+gap
  return out

/-- The size of `count` tracks from `start`, with the gaps between them. -/
def spanSize (sizes : Array Float) (start count : Nat) (gap : Float) : Float :=
  let n := min count (sizes.size-start)
  (sizes.extract start (start+n)).foldl (·+·) 0 + gap*Float.ofNat (n-1)

/-- The sum of the tracks and of the gaps around and between them (no gaps when there are no tracks). -/
def extent (sizes : Array Float) (gap : Float) : Float :=
  if sizes.isEmpty then 0 else total sizes+gap*Float.ofNat (sizes.size+1)

/-! ### Heights -/

/-- Row heights (CSS 2.1 §17.5.3): at least the row's own height, the tallest cell
that is in that row only, then each spanning cell (from the shortest span up) adds what
its rows lack equally to them. -/
def rowHeights (minimum : Array Float) (cells : Array Cell) (heights : Array Float) (vs : Float) : Array Float := Id.run do
  let mut rows := minimum
  for (cell,h) in cells.zip heights do
    if cell.rowSpan <= 1 && cell.row < rows.size then rows := rows.modify cell.row (max · h)
  let spanning := (cells.zip heights).filter (·.1.rowSpan > 1) |>.qsort (fun a b => a.1.rowSpan < b.1.rowSpan)
  for (cell,h) in spanning do
    let n := min cell.rowSpan (rows.size-cell.row)
    if n == 0 then continue
    let need := h-spanSize rows cell.row n vs
    if need > 0 then rows := spread rows (Array.replicate rows.size 0) cell.row n need
  return rows

/-- The rest of a specified table height, given to the rows in proportion to their heights. -/
def stretch (rows : Array Float) (extra : Float) : Array Float :=
  if extra <= 0 || rows.isEmpty then rows else spread rows rows 0 rows.size extra

/-- The offset of a cell's content in its slot for its `vertical-align`. A baseline
cell is placed as a top cell. -/
def alignOffset (align : VerticalAlign) (slot content : Float) : Float :=
  let free := max 0 (slot-content)
  match align with
  | .middle => free/2
  | .bottom => free
  | .top | .baseline => 0

/-! ### Checks -/

private def near (a b : Float) : Bool := (a-b).abs < 0.0001
private def nearAll (a b : Array Float) : Bool := a.size == b.size && (a.zip b).all fun (x,y) => near x y

-- Wide enough: each column gets its max-content width and the rest in proportion.
#guard nearAll (distribute #[{min := 10,max := 30},{min := 20,max := 10}] 80) #[60,20]
-- Between min-content and max-content: the same fraction of the way for each column.
#guard nearAll (distribute #[{min := 10,max := 30},{min := 20,max := 40}] 50) #[20,30]
-- Narrower than min-content: min-content widths (the table overflows).
#guard nearAll (distribute #[{min := 10,max := 30},{min := 20,max := 40}] 5) #[10,20]
-- A percentage column takes its share first.
#guard nearAll (distribute #[{min := 0,max := 10,percent := some 0.5},{min := 0,max := 10}] 100) #[50,50]
-- A specified width is kept while an automatic column takes the rest.
#guard nearAll (distribute #[{min := 5,max := 40,fixed := some 40},{min := 5,max := 20}] 100) #[40,60]
-- The columns add up to the target whenever the target is at least the min-content sum.
#guard near (total (distribute #[{min := 3,max := 7},{min := 1,max := 50,fixed := some 9},{min := 2,max := 2,percent := some 0.25}] 77)) 77
-- A spanning cell's min-content width is spread over its columns by their max-content widths.
#guard nearAll ((columns 2 #[{source := .element 1,row := 0,col := 0},{source := .element 2,row := 1,col := 0,colSpan := 2}]
    #[{min := 10,max := 10},{min := 50,max := 50}] #[] 0).map (·.min)) #[50,0]
#guard nearAll ((columns 2 #[{source := .element 1,row := 0,col := 0},{source := .element 3,row := 0,col := 1},
    {source := .element 2,row := 1,col := 0,colSpan := 2}]
    #[{min := 10,max := 10},{min := 10,max := 30},{min := 60,max := 60}] #[] 0).map (·.max)) #[20,45]
-- A row span adds what its rows lack equally.
#guard nearAll (rowHeights #[0,0] #[{source := .element 1,row := 0,col := 0},{source := .element 2,row := 0,col := 1,rowSpan := 2}] #[10,30] 2) #[19,9]
#guard nearAll (offsets #[10,20,30] 2) #[2,14,36]
#guard near (spanSize #[10,20,30] 1 2 2) 52
#guard near (extent #[10,20,30] 2) 68
#guard nearAll (fixedWidths 3 #[({source := .element 1,row := 0,col := 0},{fixed := some 50})] #[] 200 0) #[50,75,75]

end L4Factoidal.Rendering.Table
