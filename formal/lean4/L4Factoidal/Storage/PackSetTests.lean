/-
L4Factoidal.Storage.PackSetTests — build-time checks that the streaming packer
writes a set of rows (https://github.com/danbri/factoidal/issues/1006).

Each check runs the packer's own functions (`prepassFeed`, `ingestFeed`,
`ingestFinish` for IBK3; `quadIngestFeed`, `quadIngestFinish` for IBK5) on a
small Turtle source and reads `PackState.tripleCount`, the row count that
`packFinish` reports and the store answers to `COUNT(*)`. Before issue 1006
the counts were 4, 3 and 130 on IBK3 and 4, 3 and 130 on IBK5.

The third source states one triple 130 times and is fed one line per chunk, so
the IBK3 path runs three publication batches (one per 64 chunks): the seen
graph must carry across batches.
-/
import L4Factoidal.Storage.PackStream

namespace L4Factoidal.Storage.PackSetTests

open L4Factoidal.Storage.PackStream
open L4Factoidal.RDF

private def dup : String :=
  "@prefix ex: <http://example.org/> .\nex:alice ex:name \"Alice\" , \"Alice\" .\nex:alice ex:knows _:b0 .\n_:b0 ex:name \"Bob\" .\n"

private def tags : String :=
  "@prefix ex: <http://example.org/> .\nex:alice ex:name \"Alice\"@en .\nex:alice ex:name \"Alice\"@EN .\nex:alice ex:name \"Alice\"@en-GB .\n"

private def line : String := "<http://example.org/s> <http://example.org/p> \"v\" .\n"

private def many : List String := List.replicate 130 line

private def prepassOf (chunks : List String) : Except String SourcePrepass := do
  let st ← chunks.foldlM (fun st c => prepassFeed st c.toUTF8) (prepassInit)
  prepassFinish st

/-- IBK3: the rows the packer writes, one feed per chunk. -/
private def ibk3Rows (chunks : List String) : Except String Nat := do
  let pre ← prepassOf chunks
  let st ← ingestInit BlockMerkle.pureHasher .ibk3 pre none Crypto.pureBlockFold256 .turtle
  let st ← chunks.foldlM (fun st c => do let (st, _) ← ingestFeed st c.toUTF8; pure st) st
  let (packed, _) ← ingestFinish st
  pure packed.tripleCount

/-- IBK5: the rows the packer writes, one feed per chunk. -/
private def ibk5Rows (chunks : List String) : Except String Nat := do
  let pre ← prepassOf chunks
  let st ← quadIngestInit BlockMerkle.pureHasher .ibk5 .turtle {} pre none
  let st ← chunks.foldlM (fun st c => do let (st, _) ← quadIngestFeed st c.toUTF8; pure st) st
  let r ← quadIngestFinish st
  pure r.packed.tripleCount

#guard (ibk3Rows [dup]).toOption == some 3
#guard (ibk3Rows [tags]).toOption == some 2
#guard (ibk3Rows many).toOption == some 1
#guard (ibk5Rows [dup]).toOption == some 3
#guard (ibk5Rows [tags]).toOption == some 2
#guard (ibk5Rows many).toOption == some 1

/-- A source with no repeated triple keeps every row (and its order: the
    first occurrence fixes the place), so its generation is unchanged. -/
private def distinct : String :=
  "@prefix ex: <http://example.org/> .\nex:a ex:p ex:b .\nex:a ex:p ex:c .\nex:b ex:q \"x\"@en .\n"

#guard (ibk3Rows [distinct]).toOption == some 3
#guard (ibk5Rows [distinct]).toOption == some 3

end L4Factoidal.Storage.PackSetTests
