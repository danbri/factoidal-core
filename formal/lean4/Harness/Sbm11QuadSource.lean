/-
Harness/Sbm11QuadSource — `l4sbm11-quad-source`: tests of the producers of RDF
quads and of the packer entry `Sbm11Pack.packQuads`
(https://github.com/danbri/factoidal/issues/866; `tests/sbm11/quad_source.sh`
runs it). It is a HARNESS: it writes and reads files and prints.

  l4sbm11-quad-source selftest WORKDIR
      In process, with no document text. For every test dataset and every batch
      size: the batches of `QuadSource.ofDataset` and `QuadSource.ofArray` taken
      together are the quads of the dataset in order (`Dataset.quadList`); the
      graph names that `ofDataset` declares are the names of `Dataset.named`, in
      order (`QuadSourceTheorems.ofDataset_graphs`), and an array declares none;
      each batch has at least one quad or graph name and at most `max 1 batch` of
      them, they are the batches of the pure model (`Pull.batches`, the object of
      the theorems in `L4Factoidal/RDF/QuadSourceTheorems.lean`), and `next` gives
      `none` again after the end. A step that throws makes every later call throw.
      Then each dataset is packed by `packQuads` ten ways: from the dataset, from 1,
      2 and 5 producers (an array cut into slices), with batches of 1, 3 and 4,096
      quads, with term maps of 7, 40 and 262,144 terms, from the quads in reverse
      order, and with the default graph and the named graphs as two datasets. The
      array producers have one more producer that declares the named graphs of the
      dataset (`namesSource`): a named graph with no triple is in no quad. Every
      file of the nine generations, the manifest and the graph list included, is
      byte-identical to the file of the first. A pack of the array producers
      without the declarations differs from the first exactly when the dataset has
      a named graph with no triple (the declarations are not without effect).
      WORKDIR holds the generations (deleted as the run goes).
      Prints "quad source selftest: N pass, M fail (out of T)".
  l4sbm11-quad-source cases
      The test datasets: name, number of quads, `rdf11` or `rdf12` (the dataset has a
      triple term or a directional literal).
  l4sbm11-quad-source names CASE
      The distinct names of the named graphs of the test dataset CASE, empty graphs
      included, one term on each line (`<IRI>` or `_:label`), in the order of their
      first named graph: what `l4sbm11 graphs` of its pack must list.
  l4sbm11-quad-source pack-dataset CASE OUTDIR [--batch B] [--producers K]
                                   [--run-terms N] [--expected FILE]
      Pack the test dataset CASE from memory into OUTDIR with `packQuads`: K
      producers (default 1) of batches of B quads (default 4,096); for K > 1, an
      array cut into K slices and one producer that declares the named graphs. With
      `--expected FILE`, write the dataset as N-Quads text to FILE, for
      `l4sbm11-w3c compare` (the text is the expected side of a comparison; the
      pack does not read it).
  l4sbm11-quad-source hdt-dump FILE.hdt
      The triples of an HDT file as N-Quads, by the HDT store's own search
      (`HDT.searchTriples`), the dump that `l4sbm11 dump` of the packed HDT file
      is compared with.
  l4sbm11-quad-source hdt-errors FILE.hdt
      The error paths of the HDT producer, on a store that opened: an id of the
      subject, predicate or object role that is 0 or lies outside the dictionary
      gives an error and not a term, and so does a subject after the last subject of
      the triples section (the query decoders of `HDT/Store.lean` give a sentinel term
      for these; a pack would copy it into the generation). The subjects that the
      store has give no error. Prints "hdt errors: N pass, M fail (out of T)".

Exit 1 on any failed check or error.
-/
import Harness.Sbm11PackLib
import L4Factoidal.RDF.QuadSource
import L4Factoidal.RDF.Sink
import L4Factoidal.Qlvr.Sort
import L4Factoidal.HDT.QuadSource

open L4Factoidal.RDF
open L4Factoidal.RDF.QuadSource

namespace Sbm11QuadSource

/-! ## Test datasets -/

def iriOf (s : String) : WfIri :=
  if h : isIri s = true then ⟨s, h⟩ else ⟨"urn:invalid:iri", rfl⟩

def ex (s : String) : String := "http://example.org/" ++ s
def xsd (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

def sIri (s : String) : Subject := .iri (iriOf s)
def tIri (s : String) : Term := .iri (iriOf s)
def plain (lex : String) : Term := .literal (Literal.string lex)
def lang (lex tag : String) : Term := .literal (Literal.langString lex tag)
def typed (lex dt : String) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := iriOf dt, langTag := none, direction := none }
  if h : literalWf l = true then .literal ⟨l, h⟩ else plain lex
def tr (s : Subject) (p : String) (o : Term) : Triple := { s := s, p := iriOf p, o := o }

def caseDefault : Dataset :=
  { default := [
      tr (sIri (ex "s1")) (ex "p") (tIri (ex "o1")),
      tr (sIri (ex "s1")) (ex "name") (plain "Alice"),
      tr (sIri (ex "s1")) (ex "age") (typed "30" (xsd "integer")),
      tr (sIri (ex "s2")) (ex "label") (lang "hello" "en"),
      tr (sIri (ex "s2")) (ex "label") (lang "bonjour" "fr")],
    named := [] }

def caseNamed : Dataset :=
  { default := [],
    named := [
      { name := sIri (ex "g1"), graph := [
          tr (sIri (ex "a")) (ex "p") (tIri (ex "b")),
          tr (sIri (ex "a")) (ex "q") (plain "x")] },
      { name := sIri (ex "g2"), graph := [
          tr (sIri (ex "c")) (ex "p") (tIri (ex "d"))] }] }

/-- Default graph and named graphs, blank nodes as subject, object and graph name,
    a repeated triple, a triple in two graphs, a named graph with no triple. -/
def caseMixed : Dataset :=
  { default := [
      tr (sIri (ex "s")) (ex "p") (tIri (ex "o")),
      tr (sIri (ex "s")) (ex "p") (tIri (ex "o")),
      tr (.bnode "b1") (ex "p") (.bnode "b2"),
      tr (.bnode "b2") (ex "q") (plain "from a blank node")],
    named := [
      { name := sIri (ex "g1"), graph := [
          tr (sIri (ex "s")) (ex "p") (tIri (ex "o")),
          tr (.bnode "b1") (ex "p") (typed "7" (xsd "integer"))] },
      { name := .bnode "g", graph := [
          tr (.bnode "b2") (ex "r") (.bnode "b1")] },
      { name := sIri (ex "empty"), graph := [] },
      { name := sIri (ex "g1"), graph := [
          tr (sIri (ex "late")) (ex "p") (plain "a second block of the graph g1")] }] }

/-- Terms that stress the dictionary: Unicode, escapes, a long lexical form, an
    upper-case language tag (the packer folds it), integers (canonical and not),
    and other datatypes. All of them are RDF 1.1. -/
def caseTerms : Dataset :=
  let s := sIri (ex "terms")
  { default := [
      tr s (ex "unicode") (plain ("café 中文 " ++ String.singleton (Char.ofNat 0x1F600))),
      tr s (ex "escapes") (plain "line one\nline two\ttab \"quoted\" back\\slash"),
      tr s (ex "long") (plain (String.ofList (List.replicate 100000 'x'))),
      tr s (ex "tag") (lang "Colour" "EN-gb"),
      tr s (ex "int") (typed "42" (xsd "integer")),
      tr s (ex "intNeg") (typed "-17" (xsd "integer")),
      tr s (ex "intLeadingZero") (typed "007" (xsd "integer")),
      tr s (ex "intHuge") (typed "123456789012345678901234567890" (xsd "integer")),
      tr s (ex "bool") (typed "true" (xsd "boolean")),
      tr s (ex "boolOne") (typed "1" (xsd "boolean")),
      tr s (ex "dec") (typed "3.14" (xsd "decimal")),
      tr s (ex "dbl") (typed "1.5e3" (xsd "double")),
      tr s (ex "date") (typed "2026-10-15" (xsd "date")),
      tr s (ex "custom") (typed "v" (ex "datatype"))],
    named := [
      { name := sIri (ex "g"), graph := [tr s (ex "ing") (typed "9" (xsd "integer"))] }] }

/-- RDF 1.2: a directional language-tagged literal and triple terms, one nested in
    another, in the default graph and in a named graph. -/
def caseTerms12 : Dataset :=
  let s := sIri (ex "terms12")
  { default := [
      tr s (ex "dir") (.literal (Literal.dirLangString "salam" "ar" .rtl)),
      tr s (ex "tt") (.tripleTerm (sIri (ex "x")) (iriOf (ex "y")) (tIri (ex "z"))),
      tr s (ex "nested")
        (.tripleTerm (sIri (ex "x")) (iriOf (ex "y"))
          (.tripleTerm (.bnode "n") (iriOf (ex "y2")) (lang "deep" "FR")))],
    named := [
      { name := sIri (ex "g12"), graph := [
          tr s (ex "tt") (.tripleTerm (.bnode "m") (iriOf (ex "y")) (typed "5" (xsd "integer")))] }] }

/-- A generated dataset: `n` subjects with eight triples each, four named graphs
    that hold every fifth subject. Deterministic. -/
def caseBig (n : Nat) : Dataset :=
  let sub (i : Nat) : Subject := sIri (ex s!"s/{i}")
  let triples (i : Nat) : List Triple := [
      tr (sub i) (ex "name") (plain s!"Name {i} café"),
      tr (sub i) (ex "age") (typed (toString (18 + i % 60)) (xsd "integer")),
      tr (sub i) (ex "knows") (.iri (iriOf (ex s!"s/{(i * 7 + 3) % n}"))),
      tr (sub i) (ex "score") (typed s!"{i}.{i % 100}" (xsd "decimal")),
      tr (sub i) (ex "label") (lang s!"hello {i}" "en"),
      tr (sub i) (ex "label") (lang s!"bonjour {i}" "fr"),
      tr (sub i) (ex "blank") (.bnode s!"b{i % 500}"),
      tr (.bnode s!"b{i % 500}") (ex "of") (.iri (iriOf (ex s!"s/{i}")))]
  let ids := List.range n
  { default := ids.flatMap triples,
    named := (List.range 4).map fun g =>
      { name := sIri (ex s!"graph/{g}"),
        graph := (ids.filter (· % 5 == g)).flatMap fun i => [tr (sub i) (ex "in") (plain s!"graph {g}")] } }

def cases : List (String × Dataset) :=
  [("empty", Dataset.empty), ("default", caseDefault), ("named", caseNamed), ("mixed", caseMixed),
   ("terms", caseTerms), ("terms12", caseTerms12),
   -- 6,000 subjects: 52,800 quads that share 500 blank nodes. It was 1,000 (8,800 quads)
   -- while the isomorphism test took time in n² (https://github.com/danbri/factoidal/issues/868).
   ("big", caseBig 6000)]

/-- Whether a term is RDF 1.2 only: a triple term or a directional literal. -/
def termIsRdf12 : Term → Bool
  | .tripleTerm .. => true
  | .literal l => l.val.direction.isSome
  | _ => false

/-- Whether a dataset needs RDF 1.2 (RDFC-1.0 is defined on RDF 1.1 datasets). -/
def datasetIsRdf12 (d : Dataset) : Bool :=
  d.quadList.any fun (t, _) => termIsRdf12 t.o

/-! ## Reporting -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0

def record (t : IO.Ref Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    t.modify fun x => { x with pass := x.pass + 1 }
  else
    t.modify fun x => { x with fail := x.fail + 1 }
    IO.println s!"FAIL {name} {detail}"

/-! ## Producers -/

/-- The batches of a producer until its end. -/
def batchesOf (src : QuadSource) : IO (Array Batch) := do
  let mut out : Array Batch := #[]
  repeat
    match ← src.next with
    | none => break
    | some b => out := out.push b
  pure out

def flat (bs : Array Batch) : Array Quad := bs.foldl (fun acc b => acc ++ b.quads) #[]

/-- The graph names that the batches declare, in order. -/
def graphsOf (bs : Array Batch) : Array Subject := bs.foldl (fun acc b => acc ++ b.graphs) #[]

/-- The names of the named graphs of a dataset, one for each named graph, in order:
    what `ofDataset` declares (`QuadSourceTheorems.ofDataset_graphs`). -/
def namesOf (d : Dataset) : Array Subject := (d.named.map (·.name)).toArray

/-- A producer that declares graph names and gives no quad: one batch, or none
    when there is no name. The array producers have no named graph that has no
    triple; this producer gives them one. -/
def namesSource (names : Array Subject) : IO QuadSource :=
  QuadSource.ofPull (some names) fun s =>
    match s with
    | some ns => if ns.isEmpty then none else some ({ graphs := ns }, none)
    | none => none

/-- Whether a named graph of the dataset has no triple in any of its blocks: it is
    in no quad. -/
def hasEmptyGraph (d : Dataset) : Bool :=
  d.named.any fun ng => !(d.quadList.any fun (_, g) => g == some ng.name)

def batchSizes : List Nat := [0, 1, 2, 3, 7, 100, 4096, 1000000]

def checkProducers (t : IO.Ref Tally) : IO Unit := do
  for (name, d) in cases do
    let want := d.quadList.toArray
    for b in batchSizes do
      let label := s!"{name} batch={b}"
      -- a dataset
      let src ← QuadSource.ofDataset d b
      let bs ← batchesOf src
      record t s!"ofDataset {label} concatenation" (flat bs == want) s!"{(flat bs).size} quads, want {want.size}"
      record t s!"ofDataset {label} declared graph names" (graphsOf bs == namesOf d)
        s!"{(graphsOf bs).size} names, want {d.named.length}"
      record t s!"ofDataset {label} batch sizes" (bs.all fun x => 0 < x.size && x.size ≤ max 1 b)
      let model := ((datasetPull b).batches (want.size + d.named.length) (Cursor.start d)).toArray
      record t s!"ofDataset {label} equals the pure model" (bs == model)
      let again1 ← src.next
      let again2 ← src.next
      record t s!"ofDataset {label} stays ended" (again1.isNone && again2.isNone)
      -- an array
      let srcA ← QuadSource.ofArray want b
      let bsA ← batchesOf srcA
      record t s!"ofArray {label} concatenation" (flat bsA == want)
      record t s!"ofArray {label} declares no graph name" (graphsOf bsA).isEmpty
      record t s!"ofArray {label} batch sizes" (bsA.all fun x => 0 < x.size && x.size ≤ max 1 b)
      let endA ← srcA.next
      record t s!"ofArray {label} ended" endA.isNone
  -- the empty producer
  let e ← QuadSource.empty
  record t "empty producer" ((← e.next).isNone)
  -- a step that throws: the call throws, and so does every later call
  let one : Batch := { quads := #[(tr (sIri (ex "s")) (ex "p") (tIri (ex "o")), none)] }
  let bad ← QuadSource.ofStep (0 : Nat) fun n =>
    if n == 0 then pure (some (one, 1)) else throw (IO.userError "boom")
  let first ← bad.next
  record t "ofStep first call" (first == some one)
  let throws (src : QuadSource) : IO Bool := do
    try
      let _ ← src.next
      pure false
    catch _ => pure true
  record t "ofStep throwing call throws" (← throws bad)
  record t "ofStep call after a throw throws" (← throws bad)
  -- drain and foldBatches
  let srcD ← QuadSource.ofDataset caseMixed 2
  let all ← srcD.drain
  record t "drain" (all.quads == caseMixed.quadList.toArray && all.graphs == namesOf caseMixed)
  let srcF ← QuadSource.ofDataset caseMixed 2
  let count ← srcF.foldBatches 0 fun n b => pure (n + b.quads.size)
  record t "foldBatches" (count == caseMixed.quadList.length)
  -- the producer of declarations alone
  let ns ← batchesOf (← namesSource (namesOf caseMixed))
  record t "namesSource" (flat ns).isEmpty
  record t "namesSource declares the names" (graphsOf ns == namesOf caseMixed)
  let none0 ← (← namesSource #[]).next
  record t "namesSource of no name gives no batch" none0.isNone

/-! ## The packer entry -/

/-- The files of a directory, by name, with their bytes. -/
def readDir (dir : String) : IO (Array (String × ByteArray)) := do
  let entries ← System.FilePath.readDir (System.FilePath.mk dir)
  let names := L4Factoidal.Qlvr.mergeSortBy (entries.map (·.fileName)) fun a b => a < b || a == b
  let mut out := #[]
  for n in names do
    out := out.push (n, ← IO.FS.readBinFile (System.FilePath.mk dir / n))
  pure out

/-- `parts` slices of the array, as nearly equal as possible. -/
def slices (qs : Array Quad) (parts : Nat) : Array (Array Quad) :=
  (Array.range parts).map fun i => qs.extract (qs.size * i / parts) (qs.size * (i + 1) / parts)

def packFrom (sources : Array (IO QuadSource)) (dir : String) (runTerms : Nat) : IO Unit := do
  IO.FS.createDirAll dir
  let _ ← Sbm11Pack.packQuads sources dir runTerms 4096 524288 Sbm11Pack.SourceId.noDocument

def sameFiles (a b : Array (String × ByteArray)) : Bool :=
  a.size == b.size && (a.zip b).all fun ((n1, x), (n2, y)) => n1 == n2 && x == y

def checkPacks (t : IO.Ref Tally) (work : String) : IO Unit := do
  for (name, d) in cases do
    let qs := d.quadList.toArray
    let ref := s!"{work}/{name}-ref"
    packFrom #[QuadSource.ofDataset d 4096] ref 262144
    let refFiles ← readDir ref
    record t s!"pack {name} writes files" (refFiles.size > 0)
    -- the number of producers, the batch size and the term map size
    let mut n := 0
    let names := namesOf d
    for (parts, batch, runTerms) in [(1, 1, 262144), (1, 3, 262144), (2, 4096, 262144), (5, 3, 262144),
                                      (2, 1, 40), (5, 4096, 40), (1, 4096, 7)] do
      let dir := s!"{work}/{name}-p{n}"
      n := n + 1
      let sources := ((slices qs parts).map fun s => QuadSource.ofArray s batch).push (namesSource names)
      packFrom sources dir runTerms
      record t s!"pack {name} producers={parts} batch={batch} run-terms={runTerms} equals the first pack"
        (sameFiles refFiles (← readDir dir))
      IO.FS.removeDirAll (System.FilePath.mk dir)
    -- the order of the quads
    let rev := s!"{work}/{name}-rev"
    packFrom #[QuadSource.ofArray qs.reverse 5, namesSource names.reverse] rev 262144
    record t s!"pack {name} from the quads in reverse order equals the first pack" (sameFiles refFiles (← readDir rev))
    IO.FS.removeDirAll (System.FilePath.mk rev)
    -- without the declarations: a named graph with no triple is lost, and only then
    let bare := s!"{work}/{name}-bare"
    packFrom ((slices qs 2).map fun s => QuadSource.ofArray s 4096) bare 262144
    let same := sameFiles refFiles (← readDir bare)
    record t s!"pack {name} without the declared names {if hasEmptyGraph d then "differs from" else "equals"} the first pack"
      (same == !hasEmptyGraph d)
    IO.FS.removeDirAll (System.FilePath.mk bare)
    -- datasets as producers: the default graph and each named graph cut among producers
    let part := s!"{work}/{name}-ds"
    let halves : Array Dataset := #[{ d with named := [] }, { default := [], named := d.named }]
    packFrom (halves.map fun h => QuadSource.ofDataset h 11) part 262144
    record t s!"pack {name} from two datasets (default graph, named graphs) equals the first pack" (sameFiles refFiles (← readDir part))
    IO.FS.removeDirAll (System.FilePath.mk part)
    IO.FS.removeDirAll (System.FilePath.mk ref)

/-! ## Commands -/

def selftest (work : String) : IO UInt32 := do
  IO.FS.createDirAll work
  let t ← IO.mkRef ({} : Tally)
  checkProducers t
  checkPacks t work
  let r ← t.get
  IO.println s!"quad source selftest: {r.pass} pass, {r.fail} fail (out of {r.pass + r.fail})"
  pure (if r.fail == 0 then 0 else 1)

def findCase (name : String) : Option Dataset := (cases.find? (·.1 == name)).map (·.2)

structure PackOpts where
  batch : Nat := 4096
  producers : Nat := 1
  runTerms : Nat := 262144
  expected : Option String := none

def parsePackOpts : List String → PackOpts → Option PackOpts
  | [], o => some o
  | "--batch" :: v :: rest, o => v.toNat?.bind fun n => parsePackOpts rest { o with batch := n }
  | "--producers" :: v :: rest, o => v.toNat?.bind fun n => parsePackOpts rest { o with producers := max 1 n }
  | "--run-terms" :: v :: rest, o => v.toNat?.bind fun n => parsePackOpts rest { o with runTerms := max 1 n }
  | "--expected" :: v :: rest, o => parsePackOpts rest { o with expected := some v }
  | _, _ => none

def packDataset (name dir : String) (o : PackOpts) : IO UInt32 := do
  let some d := findCase name
    | IO.eprintln s!"l4sbm11-quad-source: no test dataset '{name}' (cases: {", ".intercalate (cases.map (·.1))})"; return 2
  if let some f := o.expected then
    match Sink.serializeDataset {} .nquads .rdf12 d with
    | .error e => throw (IO.userError s!"the expected N-Quads: {e}")
    | .ok text => IO.FS.writeFile f text
  let qs := d.quadList.toArray
  let sources : Array (IO QuadSource) :=
    if o.producers == 1 then #[QuadSource.ofDataset d o.batch]
    else ((slices qs o.producers).map fun s => QuadSource.ofArray s o.batch).push (namesSource (namesOf d))
  IO.FS.createDirAll dir
  let r ← Sbm11Pack.packQuads sources dir o.runTerms 4096 524288 Sbm11Pack.SourceId.noDocument
  IO.println s!"quad-source: pack-dataset case={name} producers={r.workers} batch={o.batch} quads-read={r.phase1.quads} quads={r.report.outs[0]!.rows} terms={r.report.terms} batches={r.phase1.batches.size}"
  pure 0

def hdtDump (file : String) : IO UInt32 := do
  let some gs ← L4Factoidal.HDT.openGraphStore none (System.FilePath.mk file) none
    | IO.eprintln s!"l4sbm11-quad-source: {file} is not a readable HDT file"; return 1
  let out ← IO.getStdout
  for t in L4Factoidal.HDT.searchTriples gs none none none do
    match Sink.nquadsLineOfTerms .rdf12 t.s.toTerm (.iri t.p) t.o none with
    | .ok line => out.putStrLn line
    | .error e => throw (IO.userError s!"the HDT triple has no N-Quads form: {e}")
  out.flush
  pure 0

/-- Whether an `Except` holds an error. -/
def isError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def hdtErrors (file : String) : IO UInt32 := do
  let some gs ← L4Factoidal.HDT.openGraphStore none (System.FilePath.mk file) none
    | IO.eprintln s!"l4sbm11-quad-source: {file} is not a readable HDT file"; return 1
  let t ← IO.mkRef ({} : Tally)
  let subjects := (L4Factoidal.HDT.numSubjects gs.bytes gs.triples).getD 0
  let beyond := 1000000000
  record t "the store has subjects" (0 < subjects) s!"{subjects} subjects"
  record t "subject id 0 is an error" (isError (gs.subjectOf 0))
  record t "subject id outside the dictionary is an error" (isError (gs.subjectOf beyond))
  record t "predicate id 0 is an error" (isError (gs.predicateOf 0))
  record t "predicate id outside the dictionary is an error" (isError (gs.predicateOf beyond))
  record t "object id 0 is an error" (isError (gs.objectOf 0))
  record t "object id outside the dictionary is an error" (isError (gs.objectOf beyond))
  record t "a subject after the last subject is an error" (isError (gs.subjectBatch (subjects + 5) 10 (subjects + 1)))
  record t "the subjects that the store has are not an error" (!isError (gs.subjectBatch subjects 1000000 1))
  let r ← t.get
  IO.println s!"hdt errors: {r.pass} pass, {r.fail} fail (out of {r.pass + r.fail})"
  pure (if r.fail == 0 then 0 else 1)

/-- The distinct graph names of the test dataset, in the order of their first named
    graph, one term on each line. -/
def printNames (name : String) : IO UInt32 := do
  let some d := findCase name
    | IO.eprintln s!"l4sbm11-quad-source: no test dataset '{name}'"; return 2
  let mut seen : Array Subject := #[]
  for g in namesOf d do
    if !seen.contains g then
      seen := seen.push g
      match g with
      | .iri i => IO.println s!"<{i.val}>"
      | .bnode b => IO.println s!"_:{b}"
  pure 0

def usage : String :=
  "usage: l4sbm11-quad-source selftest WORKDIR | cases | names CASE | pack-dataset CASE OUTDIR [--batch B] [--producers K] [--run-terms N] [--expected FILE] | hdt-dump FILE.hdt | hdt-errors FILE.hdt"

end Sbm11QuadSource

open Sbm11QuadSource in
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["selftest", work] => selftest work
    | ["cases"] => do
        for (n, d) in cases do IO.println s!"{n}\t{d.quadList.length}\t{if datasetIsRdf12 d then "rdf12" else "rdf11"}"
        pure 0
    | ["names", name] => printNames name
    | "pack-dataset" :: name :: dir :: rest =>
        match parsePackOpts rest {} with
        | some o => packDataset name dir o
        | none => IO.eprintln usage; pure 2
    | ["hdt-dump", file] => hdtDump file
    | ["hdt-errors", file] => hdtErrors file
    | _ => IO.eprintln usage; pure 2
  catch e =>
    IO.eprintln s!"l4sbm11-quad-source: {e}"
    pure 1
