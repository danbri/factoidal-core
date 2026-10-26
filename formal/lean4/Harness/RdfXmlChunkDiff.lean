/-
Harness.RdfXmlChunkDiff — the RDF/XML reader of the source layer, read in
chunks, against the whole-document reader
(https://github.com/danbri/factoidal/issues/838).

`l4rdfxml-chunk-diff FILE...` reads each file, then for each base (none, and
`http://example.org/dir/doc.rdf`) compares

* the whole-document reader, `RdfXml.parseRdfXml` of the text, and
* `Source.Reader` for `.rdfxml` (`Syntax/RdfXmlChunkFold.lean`), fed with
  chunks of 1, 7, 64 and 65,536 characters (1 and 7 only for files under
  `smallLimit` characters).

A case agrees when both readers refuse the document, or both give the same
triples in the same order (blank-node labels included). Error messages are
not compared: the chunk fold can report another error first (module header
of `RdfXmlChunkFold`). The equality is not proved for the children phase;
this run is its measurement (row RX-1 of `tests/known-defects/run.sh`,
https://github.com/danbri/factoidal/issues/936).

Prints one DIFF line for each disagreement, then the counts; exit 0 when
every case agrees, 1 otherwise, 2 when no file was read.
-/
import L4Factoidal.RDF.Source

open L4Factoidal.Syntax
open L4Factoidal.RDF
open L4Factoidal.RDF.Source

/-- Files at least this long (in characters) are read in chunks of 64 and
65,536 characters only. -/
def smallLimit : Nat := 400000

/-- Cut a text into chunks of `n` characters. -/
def chunksOf (n : Nat) (text : String) : List String :=
  let rec go (fuel : Nat) (cs : List Char) (acc : List String) : List String :=
    match fuel, cs with
    | 0, _ => acc.reverse
    | _, [] => acc.reverse
    | f + 1, cs => go f (cs.drop n) (String.ofList (cs.take n) :: acc)
  go (text.length + 1) text.toList []

/-- The triples of the source-layer reader, in the order it gives them. -/
def readChunked (base : Option String) (chunks : List String) : Option (List Triple) :=
  match Reader.init ({} : Extra) .rdfxml .rdf11 base "" ([] : List Triple) with
  | .error _ => none
  | .ok r =>
    match r.readAll (fun a t _ => t :: a) chunks with
    | .ok ts => some ts.reverse
    | .error _ => none

def main (args : List String) : IO UInt32 := do
  let mut cases := 0
  let mut agree := 0
  let mut differ := 0
  let mut accepted := 0
  let mut files := 0
  for path in args do
    let text ← IO.FS.readFile path
    files := files + 1
    let sizes := if text.length < smallLimit then [1, 7, 64, 65536] else [64, 65536]
    for base in [none, some "http://example.org/dir/doc.rdf"] do
      let want := (RdfXml.parseRdfXml text base).toOption
      for n in sizes do
        let got := readChunked base (chunksOf n text)
        cases := cases + 1
        if got == want then
          agree := agree + 1
          if want.isSome then accepted := accepted + 1
        else
          differ := differ + 1
          let show1 (o : Option (List Triple)) : String :=
            match o with
            | none => "refused"
            | some ts => s!"{ts.length} triples"
          IO.println s!"DIFF {path} base={base.getD "-"} chunk={n}: whole {show1 want}, chunked {show1 got}"
  IO.println s!"l4rdfxml-chunk-diff: {files} files; {agree} agree ({accepted} accepted by both, {agree - accepted} refused by both), {differ} differ (out of {cases} cases)"
  if files == 0 then return 2
  return (if differ == 0 then 0 else 1)
