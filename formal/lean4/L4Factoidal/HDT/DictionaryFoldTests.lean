/-
L4Factoidal.HDT.DictionaryFoldTests — the HDT reader folds language tags
(https://github.com/danbri/factoidal/issues/977).

A synthetic Plain Front Coding section (one block) holds the sorted strings
`"x"@EN`, `"x"@de`, `"y"@en`, as a file from a tool that keeps the tag case
of its source would. The reader decodes `"x"@EN` as `"x"@en`; a lookup of
`"x"@en`, `"x"@EN` or `"x"@En` finds that id; `roundTripsAll` holds. A second
section holds both `"x"@EN` and `"x"@en`: the two ids decode to one term, and
`roundTripsAll` fails, so `DictionaryTheorems.hdt_dictInjective` does not
apply to that file.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.HDT.Dictionary

namespace L4Factoidal.HDT.DictionaryFoldTests

open L4Factoidal.RDF
open L4Factoidal.HDT

private def commonPrefixLen (acc : Nat) : List UInt8 → List UInt8 → Nat
  | a :: as, b :: bs => if a == b then commonPrefixLen (acc + 1) as bs else acc
  | _, _ => acc

/-- The packed bytes of one PFC block: the first string whole and NUL
    terminated, each later one as `vbyte(common prefix) suffix NUL`. -/
private def pfcBlockBytes : List String → List UInt8
  | [] => []
  | first :: rest =>
    let f := first.toUTF8.toList
    (rest.foldl (fun (acc : List UInt8 × List UInt8) s =>
      let b := s.toUTF8.toList
      let k := commonPrefixLen 0 acc.2 b
      (acc.1 ++ Storage.vbyteEncode k ++ b.drop k ++ [0], b)) (f ++ [0], f)).1

/-- A one-block section of `strs` (sorted), with an 8-bit block-start log
    array `[0, packed length]` in front of the packed bytes. -/
private def section1 (strs : List String) : Bytes × PfcSection :=
  let packed := pfcBlockBytes strs
  let bytes : List UInt8 := [0, UInt8.ofNat packed.length] ++ packed
  (⟨bytes.toArray⟩,
   { start := 0, numstrings := strs.length, packedBytes := packed.length, blocksize := 16,
     blocks := { start := 0, numbits := 8, numentries := 2, dataStart := 0, dataBytes := 2,
                 «end» := 2 },
     packedStart := 2, «end» := 2 + packed.length })

private def strs1 : List String := ["\"x\"@EN", "\"x\"@de", "\"y\"@en"]
private def a1 : Bytes := (section1 strs1).1
private def inv1 : Inventory := { (default : Inventory) with dictObjects := (section1 strs1).2 }

private def lit (lex tag : String) : Term := .literal (Literal.langString lex tag)

-- the section reads back as written
#guard pfcExtract a1 (section1 strs1).2 1 == some "\"x\"@EN"
#guard pfcExtract a1 (section1 strs1).2 3 == some "\"y\"@en"
-- the read-time fold
#guard idToTerm a1 inv1 .object 1 == some (lit "x" "en")
#guard idToTerm a1 inv1 .object 2 == some (lit "x" "de")
-- a lookup finds the stored `"x"@EN` for every case of the tag
#guard termToId a1 inv1 .object (lit "x" "en") == some 1
#guard termToId a1 inv1 .object (lit "x" "EN") == some 1
#guard termToId a1 inv1 .object (lit "x" "En") == some 1
#guard termToId a1 inv1 .object (lit "y" "EN") == some 3
#guard termToId a1 inv1 .object (lit "x" "fr") == none
#guard termToId a1 inv1 .object (lit "z" "en") == none
-- one id per RDF term in this role
#guard roundTripsAll a1 inv1 .object

-- a file with two spellings of one term: two ids, one decoded term
private def strs2 : List String := ["\"x\"@EN", "\"x\"@en"]
private def a2 : Bytes := (section1 strs2).1
private def inv2 : Inventory := { (default : Inventory) with dictObjects := (section1 strs2).2 }

#guard idToTerm a2 inv2 .object 1 == idToTerm a2 inv2 .object 2
#guard !roundTripsAll a2 inv2 .object

end L4Factoidal.HDT.DictionaryFoldTests
