import L4Factoidal.Rendering.BoxAlign
import L4Factoidal.Rendering.Grid.Template

/-! Computed values of grid containers and grid items (CSS Grid Layout 2 §7 and §8):
`Computed.grid`. Every value is read through the property table (`CssValues`): the table
decides what is a value of a property and computes its lengths; this module turns the
components of that computed value into the structures grid layout works on
(`Grid.TrackList`, `Grid.Line`), with lengths in layout units, percentages in parts per
million and flex factors in 1/65536 fr. The gaps, `order` and the alignment properties
are in `Computed.align` (`Rendering/BoxAlign.lean`). -/
namespace L4Factoidal.Rendering.CSS
open L4Factoidal.Rendering

/-- The grid values of an element. `templateAreas` holds the cell names of each row
string (none: no rows). -/
structure GridStyle where
  templateColumns : Grid.TrackList := {}
  templateRows : Grid.TrackList := {}
  templateAreas : List (List String) := []
  autoColumns : List Grid.TrackSize := []
  autoRows : List Grid.TrackSize := []
  /-- `grid-auto-flow: column`. -/
  flowColumn : Bool := false
  /-- `grid-auto-flow: dense`. -/
  dense : Bool := false
  rowStart : Grid.Line := .auto
  rowEnd : Grid.Line := .auto
  columnStart : Grid.Line := .auto
  columnEnd : Grid.Line := .auto
  deriving Repr, BEq

instance : Inhabited GridStyle := ⟨{}⟩

/-- Every field equal: the two lay out the same. -/
def GridStyle.same (a b : GridStyle) : Bool := a == b

/-- A px value in layout units, to the nearest unit; a negative value is 0. -/
def gridUnitsOf (px : Rat) : Nat := ((px * 64 + (1 : Rat) / 2).floor).toNat

/-- A percentage in parts per million. -/
def gridPpmOf (percent : Rat) : Nat := ((percent * 10000 + (1 : Rat) / 2).floor).toNat

/-- A flex factor in 1/65536 fr. -/
def gridFrOf (fr : Rat) : Nat := ((fr * 65536 + (1 : Rat) / 2).floor).toNat

/-- The px and percent parts of a sum `a + b - c …` of px lengths and percentages (the
computed form of a `calc()` that mixes them). -/
def calcParts (cvs : List CssValues.CV) : Option (Rat × Rat) :=
  (cvs.foldl (fun (acc : Option (Rat × Rat × Rat)) cv =>
    match acc with
    | none => none
    | some (px, pct, sign) =>
      match cv with
      | .tok (.dim v _ "px") => some (px + sign * v, pct, 1)
      | .tok (.pct v) => some (px, pct + sign * v, 1)
      | .tok (.num v _) => if v == 0 then some (px, pct, 1) else none
      | .tok (.delim '+') => some (px, pct, 1)
      | .tok (.delim '-') => some (px, pct, -1)
      | _ => none) (some (0, 0, 1))).map fun (px, pct, _) => (px, pct)

/-- A `<length-percentage>` component of a computed value: units and parts per million. -/
def lengthPercentOf : CssValues.CV → Option (Nat × Nat)
  | .tok (.dim v _ "px") => some (gridUnitsOf v, 0)
  | .tok (.pct v) => some (0, gridPpmOf v)
  | .tok (.num v _) => if v == 0 then some (0, 0) else none
  | .fn name args =>
    if CssValues.lower name == "calc" then
      (calcParts (CssValues.stripWs args)).map fun (px, pct) => (gridUnitsOf px, gridPpmOf pct)
    else none
  | _ => none

def breadthOf : CssValues.CV → Option Grid.Breadth
  | .tok (.ident s) =>
    match CssValues.lower s with
    | "auto" => some .auto
    | "min-content" => some .minContent
    | "max-content" => some .maxContent
    | _ => none
  | .tok (.dim v i unit) =>
    if CssValues.lower unit == "fr" then some (.fr (gridFrOf v))
    else (lengthPercentOf (.tok (.dim v i unit))).map fun (u, p) => .length u p
  | cv => (lengthPercentOf cv).map fun (u, p) => .length u p

/-- A `<track-size>` component (§7.2.1). -/
def trackSizeOf : CssValues.CV → Option Grid.TrackSize
  | .fn name args =>
    match CssValues.lower name with
    | "minmax" =>
      match (CssValues.splitCommas args).map CssValues.stripWs with
      | [[a], [b]] =>
        match breadthOf a, breadthOf b with
        | some lo, some hi => some (.minmax lo hi)
        | _, _ => none
      | _ => none
    | "fit-content" =>
      match CssValues.stripWs args with
      | [a] => (lengthPercentOf a).map fun (u, p) => .fitContent u p
      | _ => none
    | _ => (breadthOf (.fn name args)).map .breadth
  | cv => (breadthOf cv).map .breadth

/-- Line names `[a b]`, or a track size. -/
def trackPartOf : CssValues.CV → Option Grid.Part
  | .block '[' body =>
    some (.names (body.filterMap fun cv => match cv with
      | .tok (.ident s) => some s
      | _ => none))
  | cv => (trackSizeOf cv).map .track

/-- An entry of a track list: a part, or `repeat(count, parts)` (§7.2.3). -/
def trackEntryOf : CssValues.CV → Option Grid.Entry
  | .fn name args =>
    if CssValues.lower name == "repeat" then
      match (CssValues.splitCommas args).map CssValues.stripWs with
      | [[count], body] =>
        let count? : Option Grid.RepeatCount := match count with
          | .tok (.num n _) => some (.times n.floor.toNat)
          | .tok (.ident s) =>
            if CssValues.lower s == "auto-fill" then some .autoFill
            else if CssValues.lower s == "auto-fit" then some .autoFit else none
          | _ => none
        match count?, body.mapM trackPartOf with
        | some c, some parts => some (.repeat c parts)
        | _, _ => none
      | _ => none
    else (trackPartOf (.fn name args)).map .part
  | cv => (trackPartOf cv).map .part

/-- The value of `grid-template-columns` or `grid-template-rows` from its components. -/
def trackListOf (cvs : List CssValues.CV) : Option Grid.TrackList :=
  match cvs with
  | [.tok (.ident "none")] => some {}
  | .tok (.ident "subgrid") :: rest =>
    some {subgrid := true, entries := rest.filterMap trackEntryOf}
  | _ => (cvs.mapM trackEntryOf).map fun entries => {entries}

/-- The value of `grid-auto-columns` or `grid-auto-rows`: track sizes. -/
def autoTracksOf (cvs : List CssValues.CV) : Option (List Grid.TrackSize) := cvs.mapM trackSizeOf

/-- A `<grid-line>` (§8.3) from its components. -/
def gridLineOf (cvs : List CssValues.CV) : Option Grid.Line :=
  let idents := cvs.filterMap fun cv => match cv with
    | .tok (.ident s) => some s
    | _ => none
  let number := (cvs.filterMap fun cv => match cv with
    | .tok (.num n _) => some n.floor
    | _ => none).head?
  let span := idents.any fun s => CssValues.lower s == "span"
  let name := (idents.filter fun s => CssValues.lower s != "span").head?
  if span then
    -- `span` alone is not a grid line (§8.3: a number or a name follows)
    if number.isNone && name.isNone then none else some (.span (number.getD 1).toNat name)
  else match number, name with
    | some n, _ => some (.index n name)
    | none, some s => if CssValues.lower s == "auto" then some .auto else some (.ident s)
    | none, none => none

/-- The rows of `grid-template-areas`: the cell names of each string. -/
def areaRowsOf (cvs : List CssValues.CV) : Option (List (List String)) :=
  match cvs with
  | [.tok (.ident "none")] => some []
  | _ =>
    let rows := cvs.filterMap fun cv => match cv with
      | .tok (.str s) => some ((((s.replace "\t" " ").replace "\n" " ").splitOn " ").filter (· != ""))
      | _ => none
    -- a value that is not a rectangle of names is invalid (§7.3)
    if rows.length == cvs.length && (Grid.parseAreas rows).isSome then some rows else none

/-- The property names this module reads. -/
def gridProperties : List String :=
  ["grid-template-columns", "grid-template-rows", "grid-template-areas", "grid-auto-columns",
   "grid-auto-rows", "grid-auto-flow", "grid-row-start", "grid-row-end", "grid-column-start",
   "grid-column-end"]

/-- `g` with the declaration `property: value` applied, when `property` is one of
`gridProperties` and `value` is a value of it; else `none`. The check of the name comes
first, so a declaration of any other property costs a few string comparisons. -/
def GridStyle.set (fontSize : Float) (g : GridStyle) (property value : String) : Option GridStyle :=
  if !gridProperties.contains property then none else
  match CssValues.specified property value with
  | none => none
  | some v =>
    if resetsToInitial v then
      some (match property with
        | "grid-template-columns" => {g with templateColumns := {}}
        | "grid-template-rows" => {g with templateRows := {}}
        | "grid-template-areas" => {g with templateAreas := []}
        | "grid-auto-columns" => {g with autoColumns := []}
        | "grid-auto-rows" => {g with autoRows := []}
        | "grid-auto-flow" => {g with flowColumn := false, dense := false}
        | "grid-row-start" => {g with rowStart := .auto}
        | "grid-row-end" => {g with rowEnd := .auto}
        | "grid-column-start" => {g with columnStart := .auto}
        | _ => {g with columnEnd := .auto})
    else
      match tableComponents fontSize property value with
      | none => none
      | some cvs =>
        match property with
        | "grid-template-columns" => (trackListOf cvs).map fun x => {g with templateColumns := x}
        | "grid-template-rows" => (trackListOf cvs).map fun x => {g with templateRows := x}
        | "grid-template-areas" => (areaRowsOf cvs).map fun x => {g with templateAreas := x}
        | "grid-auto-columns" => (autoTracksOf cvs).map fun x => {g with autoColumns := x}
        | "grid-auto-rows" => (autoTracksOf cvs).map fun x => {g with autoRows := x}
        | "grid-auto-flow" =>
          let words := cvs.filterMap fun cv => match cv with
            | .tok (.ident s) => some (CssValues.lower s)
            | _ => none
          some {g with flowColumn := words.contains "column", dense := words.contains "dense"}
        | "grid-row-start" => (gridLineOf cvs).map fun x => {g with rowStart := x}
        | "grid-row-end" => (gridLineOf cvs).map fun x => {g with rowEnd := x}
        | "grid-column-start" => (gridLineOf cvs).map fun x => {g with columnStart := x}
        | "grid-column-end" => (gridLineOf cvs).map fun x => {g with columnEnd := x}
        | _ => none

/-! ### Shorthands (§7.4, §7.8, §8.4): their longhand declarations -/

/-- The components split at each top-level `/`. -/
def splitSlashes (cvs : List CssValues.CV) : List (List CssValues.CV) :=
  let (groups, last) := cvs.foldl (fun (acc : List (List CssValues.CV) × List CssValues.CV) cv =>
    match cv with
    | .tok (.delim '/') => (acc.1 ++ [acc.2], [])
    | _ => (acc.1, acc.2 ++ [cv])) ([], [])
  groups ++ [last]

/-- A grid line value is a `<custom-ident>` alone (§8.4: it then also stands for the
omitted values of the placement shorthands). -/
def isLineIdent (cvs : List CssValues.CV) : Bool :=
  match cvs with
  | [.tok (.ident s)] => CssValues.lower s != "auto" && CssValues.lower s != "span"
  | _ => false

/-- The text of an omitted line of a placement shorthand: the ident of `from`, else
`auto`. -/
def omittedLine (given : List CssValues.CV) : String :=
  if isLineIdent given then CssValues.serialize given else "auto"

/-- The longhands of `grid-template` (§7.4) from the components of its value. -/
def gridTemplateLonghands (cvs : List CssValues.CV) : Option (List (String × String)) :=
  let triple := fun (rows columns areas : String) =>
    some [("grid-template-rows", rows), ("grid-template-columns", columns), ("grid-template-areas", areas)]
  match cvs with
  | [.tok (.ident "none")] => triple "none" "none" "none"
  | _ =>
    let strings := cvs.filter fun cv => match cv with
      | .tok (.str _) => true
      | _ => false
    match splitSlashes cvs with
    | [rows, columns] =>
      if strings.isEmpty then triple (CssValues.serialize rows) (CssValues.serialize columns) "none"
      else
        -- [ <line-names>? <string> <track-size>? <line-names>? ]+ / <explicit-track-list>
        let rowTracks := rows.foldl (fun (acc : List CssValues.CV × Bool) cv =>
          match cv with
          | .tok (.str _) => (if acc.2 then acc.1 ++ [.tok (.ident "auto")] else acc.1, true)
          | .block '[' _ => (acc.1 ++ [cv], acc.2)
          | _ => (acc.1 ++ [cv], false)) ([], false)
        let rowTracks := if rowTracks.2 then rowTracks.1 ++ [.tok (.ident "auto")] else rowTracks.1
        triple (CssValues.serialize rowTracks) (CssValues.serialize columns) (CssValues.serialize strings)
    | [rows] =>
      if strings.isEmpty then none
      else
        let rowTracks := rows.foldl (fun (acc : List CssValues.CV × Bool) cv =>
          match cv with
          | .tok (.str _) => (if acc.2 then acc.1 ++ [.tok (.ident "auto")] else acc.1, true)
          | .block '[' _ => (acc.1 ++ [cv], acc.2)
          | _ => (acc.1 ++ [cv], false)) ([], false)
        let rowTracks := if rowTracks.2 then rowTracks.1 ++ [.tok (.ident "auto")] else rowTracks.1
        triple (CssValues.serialize rowTracks) "none" (CssValues.serialize strings)
    | _ => none

/-- The longhand declarations of a grid shorthand (`grid-row`, `grid-column`,
`grid-area`, `grid-template`, `grid`); `none` for any other property, or when the value is
not one of the shorthand's by the property table. -/
def gridShorthand (property value : String) : Option (List (String × String)) :=
  if !["grid-row", "grid-column", "grid-area", "grid-template", "grid"].contains property then none else
  match CssValues.specified property value with
  | none => none
  | some v =>
    let names := match property with
      | "grid-row" => ["grid-row-start", "grid-row-end"]
      | "grid-column" => ["grid-column-start", "grid-column-end"]
      | "grid-area" => ["grid-row-start", "grid-column-start", "grid-row-end", "grid-column-end"]
      | "grid-template" => ["grid-template-rows", "grid-template-columns", "grid-template-areas"]
      | _ => ["grid-template-rows", "grid-template-columns", "grid-template-areas", "grid-auto-rows",
              "grid-auto-columns", "grid-auto-flow"]
    if resetsToInitial v || v == "inherit" then some (names.map fun n => (n, v))
    else
      let cvs := CssValues.stripWs (CssValues.CV.parse v)
      let text := CssValues.serialize
      match property with
      | "grid-row" | "grid-column" =>
        match splitSlashes cvs with
        | [a] => some (names.zip [text a, omittedLine a])
        | [a, b] => some (names.zip [text a, text b])
        | _ => none
      | "grid-area" =>
        match splitSlashes cvs with
        | [a] => some (names.zip [text a, omittedLine a, omittedLine a, omittedLine a])
        | [a, b] => some (names.zip [text a, text b, omittedLine a, omittedLine b])
        | [a, b, c] => some (names.zip [text a, text b, text c, omittedLine b])
        | [a, b, c, d] => some (names.zip [text a, text b, text c, text d])
        | _ => none
      | "grid-template" => gridTemplateLonghands cvs
      | _ =>
        -- `grid` (§7.8): a `grid-template`, or one axis as a template and the other as
        -- auto-flow tracks; the other sub-properties are reset
        let flowWords := fun (side : List CssValues.CV) => side.filter fun cv => match cv with
          | .tok (.ident s) => CssValues.lower s == "auto-flow" || CssValues.lower s == "dense"
          | _ => false
        let withoutFlow := fun (side : List CssValues.CV) => side.filter fun cv => match cv with
          | .tok (.ident s) => CssValues.lower s != "auto-flow" && CssValues.lower s != "dense"
          | _ => true
        let autoText := fun (side : List CssValues.CV) =>
          if (withoutFlow side).isEmpty then "auto" else text (withoutFlow side)
        match splitSlashes cvs with
        | [rows, columns] =>
          if !(flowWords columns).isEmpty then
            some [("grid-template-rows", text rows), ("grid-template-columns", "none"),
                  ("grid-template-areas", "none"), ("grid-auto-rows", "auto"),
                  ("grid-auto-columns", autoText columns),
                  ("grid-auto-flow", if (flowWords columns).length > 1 then "column dense" else "column")]
          else if !(flowWords rows).isEmpty then
            some [("grid-template-rows", "none"), ("grid-template-columns", text columns),
                  ("grid-template-areas", "none"), ("grid-auto-rows", autoText rows),
                  ("grid-auto-columns", "auto"),
                  ("grid-auto-flow", if (flowWords rows).length > 1 then "row dense" else "row")]
          else (gridTemplateLonghands cvs).map (· ++
            [("grid-auto-rows", "auto"), ("grid-auto-columns", "auto"), ("grid-auto-flow", "row")])
        | _ => (gridTemplateLonghands cvs).map (· ++
            [("grid-auto-rows", "auto"), ("grid-auto-columns", "auto"), ("grid-auto-flow", "row")])

/-! ### Tests -/

private def gpx (n : Nat) : Grid.TrackSize := .breadth (.length (n * 64) 0)

#guard ((GridStyle.set 16 {} "grid-template-columns" "50px 100px").map (·.templateColumns.entries)) ==
  some [.part (.track (gpx 50)), .part (.track (gpx 100))]
#guard ((GridStyle.set 16 {} "grid-template-columns" "none").map (·.templateColumns.entries)) == some []
#guard ((GridStyle.set 10 {} "grid-template-rows" "2em 1fr auto").map (·.templateRows.entries)) ==
  some [.part (.track (gpx 20)), .part (.track (.breadth (.fr 65536))), .part (.track (.breadth .auto))]
#guard ((GridStyle.set 16 {} "grid-template-columns" "[a] 10px [b c] minmax(min-content, 2fr) [d]").map (·.templateColumns.entries)) ==
  some [.part (.names ["a"]), .part (.track (gpx 10)), .part (.names ["b", "c"]),
        .part (.track (.minmax .minContent (.fr 131072))), .part (.names ["d"])]
#guard ((GridStyle.set 16 {} "grid-template-columns" "repeat(2, 10px [x]) 50%").map (·.templateColumns.entries)) ==
  some [.repeat (.times 2) [.track (gpx 10), .names ["x"]], .part (.track (.breadth (.length 0 500000)))]
#guard ((GridStyle.set 16 {} "grid-template-columns" "repeat(auto-fill, 100px)").map (·.templateColumns.entries)) ==
  some [.repeat .autoFill [.track (gpx 100)]]
#guard ((GridStyle.set 16 {} "grid-template-columns" "fit-content(40px)").map (·.templateColumns.entries)) ==
  some [.part (.track (.fitContent (40 * 64) 0))]
#guard (GridStyle.set 16 {} "grid-template-columns" "bogus(1)").isNone
#guard (GridStyle.set 16 {} "width" "10px").isNone
#guard ((GridStyle.set 16 {} "grid-auto-rows" "10px 20px").map (·.autoRows)) == some [gpx 10, gpx 20]
#guard ((GridStyle.set 16 {} "grid-auto-flow" "column dense").map fun g => (g.flowColumn, g.dense)) == some (true, true)
#guard ((GridStyle.set 16 {} "grid-row-start" "2").map (·.rowStart)) == some (.index 2 none)
#guard ((GridStyle.set 16 {} "grid-row-start" "-1").map (·.rowStart)) == some (.index (-1) none)
#guard ((GridStyle.set 16 {} "grid-column-end" "span 3").map (·.columnEnd)) == some (.span 3 none)
#guard ((GridStyle.set 16 {} "grid-column-end" "span").map (·.columnEnd)) == none
#guard ((GridStyle.set 16 {} "grid-column-start" "foo").map (·.columnStart)) == some (.ident "foo")
#guard ((GridStyle.set 16 {} "grid-column-start" "2 foo").map (·.columnStart)) == some (.index 2 (some "foo"))
#guard ((GridStyle.set 16 {} "grid-column-start" "auto").map (·.columnStart)) == some .auto
#guard ((GridStyle.set 16 {} "grid-template-areas" "\"a a b\" \"c . b\"").map (·.templateAreas)) ==
  some [["a", "a", "b"], ["c", ".", "b"]]
#guard (GridStyle.set 16 {} "grid-template-areas" "\"a b\" \"b a\"").isNone
#guard gridShorthand "grid-row" "1 / 3" == some [("grid-row-start", "1"), ("grid-row-end", "3")]
#guard gridShorthand "grid-column" "2" == some [("grid-column-start", "2"), ("grid-column-end", "auto")]
#guard gridShorthand "grid-column" "foo" == some [("grid-column-start", "foo"), ("grid-column-end", "foo")]
#guard gridShorthand "grid-area" "1 / 2 / 3 / 4" ==
  some [("grid-row-start", "1"), ("grid-column-start", "2"), ("grid-row-end", "3"), ("grid-column-end", "4")]
#guard gridShorthand "grid-area" "a" ==
  some [("grid-row-start", "a"), ("grid-column-start", "a"), ("grid-row-end", "a"), ("grid-column-end", "a")]
#guard gridShorthand "grid-area" "2 / 3" ==
  some [("grid-row-start", "2"), ("grid-column-start", "3"), ("grid-row-end", "auto"), ("grid-column-end", "auto")]
#guard gridShorthand "grid-template" "10px 20px / 30px" ==
  some [("grid-template-rows", "10px 20px"), ("grid-template-columns", "30px"), ("grid-template-areas", "none")]
#guard gridShorthand "grid" "auto-flow 10px / 20px" ==
  some [("grid-template-rows", "none"), ("grid-template-columns", "20px"), ("grid-template-areas", "none"),
        ("grid-auto-rows", "10px"), ("grid-auto-columns", "auto"), ("grid-auto-flow", "row")]
#guard gridShorthand "color" "red" == none

end L4Factoidal.Rendering.CSS
