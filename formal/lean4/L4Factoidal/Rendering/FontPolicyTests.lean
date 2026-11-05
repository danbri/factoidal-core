import L4Factoidal.Rendering.FontPolicy

/-! Guards for `Rendering.FontPolicy` (https://github.com/danbri/factoidal/issues/1233). -/

namespace L4Factoidal.Rendering.FontPolicyTests
open L4Factoidal.Rendering.FontPolicy

private def be16 (n : Nat) : List UInt8 := [(n / 256 % 256).toUInt8, (n % 256).toUInt8]
private def be32 (n : Nat) : List UInt8 := be16 (n / 65536) ++ be16 n
private def tagBytes (t : String) : List UInt8 := t.toList.map (·.toNat.toUInt8)
/-- A minimal sfnt: header, n table records, each table 4 zero bytes after the directory. -/
private def sfnt (version : List UInt8) (tags : List String) : ByteArray :=
  let n := tags.length
  let dirEnd := 12 + 16 * n
  let recs := (tags.zip (List.range n)).flatMap fun (t, i) =>
    tagBytes t ++ be32 0 ++ be32 (dirEnd + 4 * i) ++ be32 4
  ⟨(version ++ be16 n ++ be16 0 ++ be16 0 ++ be16 0 ++ recs ++ List.replicate (4 * n) 0).toArray⟩
private def tt := be32 0x00010000
private def font : FontIdentity := ⟨"Example Sans", "example.ttf", String.ofList (List.replicate 64 'a')⟩
private def tagsOf (b : ByteArray) : Option (List String) := (readDirectory b).toOption.map (·.toList.map (·.tag))

-- directory reader
#guard tagsOf (sfnt tt ["cmap", "glyf", "GSUB"]) == some ["cmap", "glyf", "GSUB"]
#guard tagsOf (sfnt (tagBytes "OTTO") ["CFF "]) == some ["CFF "]
#guard (readDirectory (sfnt (tagBytes "wOF2") [])).toOption.isNone
#guard (readDirectory (sfnt tt ["cmap", "cmap"])).toOption.isNone
#guard (readDirectory ⟨#[0, 1, 0]⟩).toOption.isNone
-- truncated: directory claims 2 tables, bytes hold 1 record
#guard (readDirectory ⟨((sfnt tt ["cmap", "glyf"]).toList.take 28).toArray⟩).toOption.isNone
-- table out of bounds
#guard (readDirectory ⟨((sfnt tt ["cmap"]).toList.take 28).toArray⟩).toOption.isNone
#guard (readDirectory (sfnt tt ["cmap"]) (faceIndex := 1)).toOption.isNone
-- limits
#guard (readDirectory (sfnt tt ["cmap", "glyf"]) (limits := { tables := 1 })).toOption.isNone
#guard (readDirectory (sfnt tt ["cmap"]) (limits := { fontBytes := 10 })).toOption.isNone
-- TrueType Collection, face 0 at offset 16
private def ttc : ByteArray :=
  let inner := (sfnt tt ["cmap"]).toList
  -- shift the table offset by 16 (header of the collection)
  let fixed := inner.take 20 ++ be32 (28 + 16) ++ inner.drop 24
  ⟨(tagBytes "ttcf" ++ be32 0x00010000 ++ be32 1 ++ be32 16 ++ fixed).toArray⟩
#guard ((readDirectory ttc).toOption.map (·.toList.map (·.tag))) == some ["cmap"]
#guard (readDirectory ttc (faceIndex := 1)).toOption.isNone

-- classification
#guard classifyTag "Wasm" == .wasm
#guard classifyTag "fpgm" == .hinting
#guard classifyTag "morx" == .aat
#guard classifyTag "Silf" == .graphite
#guard classifyTag "GPOS" == .layout
#guard classifyTag "cmap" == .fontFiles
#guard classifyTag "feat" == .fontFiles   -- AAT feature names are data; Graphite is "Feat"

-- policy and modes
#guard Policy.standard.mode == .standard
#guard Policy.safe.mode == .safe
#guard (Policy.standard.set .wasm true (.option "--dangerously-allow-font-wasm")).toOption.isNone
#guard (Policy.standard.set .aat true .page).toOption.isNone
#guard ((Policy.standard.set .aat true (.option "--dangerously-allow-font-aat")).toOption.map (·.mode)) == some .custom
#guard ((Policy.standard.set .aat true (.option "--dangerously-allow-font-aat")).toOption.map (·.startWarnings.length)) == some 1
#guard (Policy.standard.set .hinting true (.option "--dangerously-allow-font-hinting")).toOption.isNone  -- adapter never hints
#guard Policy.standard.startWarnings.isEmpty
#guard !(Policy.standard.settings .svg).allowed           -- no implementation, so not allowed by standard
#guard (Policy.standard.set .svg true .page).toOption.isNone          -- no implementation
#guard ((Policy.standard.set .layout false .page).toOption.map (·.mode)) == some .custom
#guard (Policy.safe.set .cff true .page).toOption.isNone              -- safe reads no file

-- decisions
private def wasmFont := (readDirectory (sfnt tt ["cmap", "glyf", "GSUB", "Wasm", "fpgm", "DSIG"])).toOption.getD #[]
#guard (decide Policy.standard font wasmFont).fontUsed
#guard (decide Policy.standard font wasmFont).hasDsig
#guard ((decide Policy.standard font wasmFont).refusals.map (·.code)) == ["font.table.hinting", "font.table.wasm"]
#guard (decide Policy.standard font wasmFont).used == [.fontFiles, .layout]
#guard !(decide Policy.safe font wasmFont).fontUsed
#guard ((decide Policy.safe font wasmFont).refusals.map (·.code)) == ["font.file.refused"]
#guard ((decide Policy.standard font wasmFont).refusals.getLast?.map (·.render)) == some
  ("font.table.wasm: \"Example Sans\" (example.ttf, sha256 aaaaaaaaaaaa...) has Wasm.\n" ++
   "A Wasm table is a program that the font asks the text shaper to run.\n" ++
   "Risk: the program can do any computation and can change every glyph.\n" ++
   "Setting: font.wasm = refuse (default). A WebAssembly engine in Lean is planned (https://github.com/danbri/factoidal/issues/1244); until then it can not be allowed.\n" ++
   "Action: the font was used without this table.")
end L4Factoidal.Rendering.FontPolicyTests
