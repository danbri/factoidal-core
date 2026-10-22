/-
Harness.JsonLdChunkDiff — the JSON-LD reader of the source layer, read one
top-level node object at a time, against the whole-document reader
(https://github.com/danbri/factoidal/issues/839).

`l4jsonld-chunk-diff FILE...` reads each file as a JSON-LD document and, for
each base (none, and `http://example.org/dir/doc.jsonld`) and for each of four
texts built from the file's text T by text surgery:

* T itself,
* `[` T `]`   (shape A: an array of node objects),
* `{"@context":{},"@graph":[` T `]}`  (shape B),
* `{"@context":{},"@graph":[` T `,` T `]}`  (shape B, the object twice: the same
  blank-node labels are asked for twice, and the counter has to pass on),

it compares

* the whole-document reader, `Source.parseDocument` of the text, and
* `Source.Reader` for `.jsonld` (`Syntax/JsonLdChunkFold.lean`), started with
  the generated-prefix argument that `Source.Prepass.forFormat .jsonld` gives
  for the text, fed with chunks of 1, 7, 64 and 65,536 characters (1 and 7 only
  for texts under `smallLimit` characters).

A case agrees when both readers refuse the text, or both give the same quads:
the same list when the whole reader's dataset has no named graph, and the same
multiset when it has (the whole reader gives the default graph, then the named
graphs; the item reader gives each item's default graph and named graphs in
turn). Blank-node labels are compared as they are. Error messages are not
compared. The equality is not proved (row JS-1 of `tests/known-defects/run.sh`,
https://github.com/danbri/factoidal/issues/946); this run is its measurement.

Prints one DIFF line for each disagreement, then the counts, including how many
cases the item reader read item by item ("streamed"); exit 0 when every case
agrees, 1 otherwise, 2 when no file was read or no case was streamed.
-/
import L4Factoidal.RDF.SourceJsonLd

open L4Factoidal.Syntax
open L4Factoidal.RDF
open L4Factoidal.RDF.Source

def smallLimit : Nat := 100000

def chunksOf (n : Nat) (text : String) : List String :=
  let rec go (fuel : Nat) (cs : List Char) (acc : List String) : List String :=
    match fuel, cs with
    | 0, _ => acc.reverse
    | _, [] => acc.reverse
    | f + 1, cs => go f (cs.drop n) (String.ofList (cs.take n) :: acc)
  go (text.length + 1) text.toList []

abbrev Quad := Triple × Option Subject

def quadsOf (ds : Dataset) : List Quad :=
  (foldDataset (fun (a : List Quad) t g => (t, g) :: a) [] ds).reverse

def key (q : Quad) : String := reprStr q

/-- The quads as a multiset: the count of each quad's text. -/
def counts (qs : List Quad) : Std.HashMap String Nat :=
  qs.foldl (fun m q => m.insert (key q) (m.getD (key q) 0 + 1)) {}

def sameMultiset (a b : List Quad) : Bool :=
  let ca := counts a
  let cb := counts b
  ca.size == cb.size && a.length == b.length && ca.toList.all fun (k, n) => cb.getD k 0 == n

/-- The generated-prefix argument for a text. -/
def prefixOf (text : String) : String :=
  match (Prepass.forFormat .jsonld).feed text.toUTF8 with
  | .error _ => ""
  | .ok p => (p.finish).toOption.getD ""

def readChunked (base : Option String) (pfx : String) (chunks : List String) : Option (List Quad) :=
  match Reader.init withJsonLd .jsonld .rdf11 base pfx ([] : List Quad) with
  | .error _ => none
  | .ok r =>
    match r.readAll (fun a t g => (t, g) :: a) chunks with
    | .ok qs => some qs.reverse
    | .error _ => none

def main (args : List String) : IO UInt32 := do
  let mut cases := 0
  let mut agree := 0
  let mut differ := 0
  let mut accepted := 0
  let mut streamed := 0
  let mut streamedAccepted := 0
  let mut files := 0
  for path in args do
    let t ← IO.FS.readFile path
    files := files + 1
    let texts := [t, "[" ++ t ++ "]", "{\"@context\":{},\"@graph\":[" ++ t ++ "]}",
                  "{\"@context\":{},\"@graph\":[" ++ t ++ "," ++ t ++ "]}"]
    for text in texts do
      let pfx := prefixOf text
      let sizes := if text.length < smallLimit then [1, 7, 64, 65536] else [64, 65536]
      for base in [none, some "http://example.org/dir/doc.jsonld"] do
        let wantDs := (parseDocument withJsonLd .jsonld .rdf11 base text).toOption
        let want := wantDs.map quadsOf
        let hasNamed := match wantDs with | some ds => !ds.named.isEmpty | none => false
        for n in sizes do
          let got := readChunked base pfx (chunksOf n text)
          cases := cases + 1
          let ok :=
            match want, got with
            | none, none => true
            | some w, some g => if hasNamed then sameMultiset w g else w == g
            | _, _ => false
          if pfx == "_jld_anon" then
            streamed := streamed + 1
            if want.isSome then streamedAccepted := streamedAccepted + 1
          if ok then
            agree := agree + 1
            if want.isSome then accepted := accepted + 1
          else
            differ := differ + 1
            let show1 (o : Option (List Quad)) : String :=
              match o with
              | none => "refused"
              | some qs => s!"{qs.length} quads"
            IO.println s!"DIFF {path} base={base.getD "-"} chunk={n} streamed={pfx == "_jld_anon"} text={text.take 60}: whole {show1 want}, chunked {show1 got}"
  IO.println s!"l4jsonld-chunk-diff: {files} files; {agree} agree ({accepted} accepted by both, {agree - accepted} refused by both), {differ} differ (out of {cases} cases); {streamed} cases read item by item ({streamedAccepted} accepted)"
  if files == 0 || streamed == 0 then return 2
  return (if differ == 0 then 0 else 1)
