/-
L4Factoidal.Syntax.RdfXmlChunkFold — RDF/XML read in chunks: each child of
`rdf:RDF` is read and walked when its end is in hand.

Tracking: https://github.com/danbri/factoidal/issues/838.

`RdfXml.parseRdfXml` reads the whole document into one character array (8
bytes for each character) before it walks the children of `rdf:RDF`
(`parseRdfXml_eq_stream`, design record section 3c.3). The source layer
(`RDF/Source.lean`) kept every chunk until the end of the document and then
gave the joined text to that parser, so `l4sbm11-pack SOURCE.rdf` held 11 to
14.5 bytes of peak memory for each source byte.

## What this module does

The text arrives in chunks. The fold has three phases.

1. **Prologue.** The characters are kept until the start tag of the document
   element is complete (`scanProlog`: the XML declaration, comments,
   processing instructions, the `[28] doctypedecl` with its internal subset).
   The prologue and that start tag are read with the XML parser's own
   functions (`XML.documentPrologue`, then the start-tag productions in the
   order `XML.parseElement` calls them) and `RdfXml.rdfStart`: this gives the
   entity table, the attribute-list declarations, and the parser state after
   the attributes of `rdf:RDF` (namespace scope, `xml:base`, `xml:lang`,
   `its:dir`, `rdf:version`).
2. **Children.** A scanner (`Scan`, one state for each kind of markup)
   finds the end of each top-level item of the content of `rdf:RDF`: an
   element (with its depth of nesting), a comment, a processing instruction,
   a CDATA section, or a run of text. The characters of one item are given to
   `XML.parseChildren` with the entity table and the attribute declarations
   of the document, and each element it gives to `RdfXml.nodeElement` with the
   state the previous child left. The triples go to the consumer at once, in
   the order of the document; the item is then dropped.
3. **End.** The end tag of `rdf:RDF` and the `Misc*` after it are kept and
   checked at the end of the text (`XML.documentEpilog`).

## When the whole document is read instead (the fall-back rule)

The fold gives the document to the whole-document reader
(`RdfXml.parseRdfXml` of the joined text, the reader the source layer used
before) when one of these holds at the end of the prologue:

* the prologue, or the start tag of the document element, does not parse by
  the functions above, or the text ends before the start tag is complete;
* the document element is not `rdf:RDF` ([7.2.2] doc: one node element), or
  it is an empty-element tag;
* the document declares XML 1.1 (its line-end and restricted-character rules
  are checked over the whole text);
* the document type declaration declares a general entity that is external,
  or whose replacement text holds `<` or `&` (a markup entity at the top
  level of `rdf:RDF` expands into children, and a chain of references can
  expand beyond the fuel of one item);
* the prologue holds more than `prologLimit` characters.

From then on the fold keeps the chunks and parses their join at the end:
the quads and the error are those of the whole-document reader
(`finish_whole`, `fold_whole_join` in this file).

## What is proved and what is measured

Proved here: in the prologue and fall-back phases the fold keeps exactly the
text it was given and no quad has been given to the consumer
(`foldlM_inv`); so when the fold ends in either phase it gives the
whole-document reader's result for the joined chunks
(`readAll_eq_whole_of_notStreamed`).

Not proved: in the children phase, the quads equal those of the
whole-document reader. Each item is parsed from its own character array,
where the whole-document reader parses it at its position in the array of
the whole text; the equality needs a locality theorem for the XML parser
(an item's parse reads only the item's characters). The equality is
measured: `l4rdfxml-chunk-diff` (`Harness/RdfXmlChunkDiff.lean`) compares the
two readers over every RDF/XML file of the W3C suites and the vendored
ontologies, with chunks of 1, 7, 64 and 65,536 characters; the `#guard`s
below cut documents at every position. Open issue:
https://github.com/danbri/factoidal/issues/936; expected failure: row RX-1
of `tests/known-defects/run.sh` (XFAIL while no theorem named
`rdfxml_chunk_readAll_eq_whole` exists).

Error messages and positions may differ from the whole-document reader's:
a document refused by one reader is refused by the other, but the first
error found can be another one (an RDF/XML error in an early child before an
XML error in a later child), and a position counts the characters before
the item that failed.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.RdfXml

namespace L4Factoidal.Syntax.RdfXmlChunkFold

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Syntax.RdfXml

/-! ## The prologue -/

/-- The most characters kept before the start tag of the document element
is complete. A longer prologue is read whole. -/
def prologLimit : Nat := 8 * 1024 * 1024

/-- What the scan of the prologue found. -/
inductive PrologScan where
  /-- The text so far ends inside the prologue; the scan can start again at
  `resume`, the start of the first item it did not finish. -/
  | more (resume : Nat)
  /-- The start tag of the document element ends just before `endPos`. -/
  | root (endPos : Nat)
  /-- Read the document whole. -/
  | fallback
  deriving Repr, DecidableEq

/-- The characters `p` are at `i` in `a`. -/
def litAt (a : Array Char) : List Char → Nat → Bool
  | [], _ => true
  | c :: cs, i => a.getD i (Char.ofNat 0) == c && litAt a cs (i + 1)

/-- The position after the first `p` at or after `j`. -/
def findLit (a : Array Char) (p : List Char) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, j =>
    if j + p.length > a.size then none
    else if litAt a p j then some (j + p.length)
    else findLit a p fuel (j + 1)

/-- The position of the `>` that ends a start tag whose name starts at `j`:
the first `>` outside a quoted attribute value. -/
def stagEnd (a : Array Char) : Nat → Option Char → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, q, j =>
    if j ≥ a.size then none
    else
      let c := a.getD j ' '
      match q with
      | some qc => stagEnd a fuel (if c == qc then none else some qc) j.succ
      | none =>
        if c == '>' then some j
        else if c == '"' || c == '\'' then stagEnd a fuel (some c) j.succ
        else stagEnd a fuel none j.succ

/-- The position after the `>` that ends a `[28] doctypedecl`: brackets of
the internal subset counted outside literals, comments and processing
instructions. -/
def doctypeEnd (a : Array Char) : Nat → Option Char → Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, q, depth, j =>
    if j ≥ a.size then none
    else
      let c := a.getD j ' '
      match q with
      | some qc => doctypeEnd a fuel (if c == qc then none else some qc) depth j.succ
      | none =>
        if c == '"' || c == '\'' then doctypeEnd a fuel (some c) depth j.succ
        else if c == '<' && litAt a ['<', '!', '-', '-'] j then
          match findLit a ['-', '-', '>'] (a.size + 1) (j + 4) with
          | some k => doctypeEnd a fuel none depth k
          | none => none
        else if c == '<' && litAt a ['<', '?'] j then
          match findLit a ['?', '>'] (a.size + 1) (j + 2) with
          | some k => doctypeEnd a fuel none depth k
          | none => none
        else if c == '[' then doctypeEnd a fuel none (depth + 1) j.succ
        else if c == ']' then doctypeEnd a fuel none (depth - 1) j.succ
        else if c == '>' && depth == 0 then some j.succ
        else doctypeEnd a fuel none depth j.succ

/-- Scan the prologue from `i`, an item boundary. -/
def scanProlog (a : Array Char) : Nat → Nat → PrologScan
  | 0, i => .more i
  | fuel + 1, i =>
    if i ≥ a.size then .more i
    else
      let c := a.getD i ' '
      if XML.isXmlSpace c || (i == 0 && c.toNat == 0xFEFF) then scanProlog a fuel i.succ
      else if c != '<' then .fallback
      else if i + 1 ≥ a.size then .more i
      else
        let c2 := a.getD (i + 1) ' '
        if c2 == '?' then
          match findLit a ['?', '>'] (a.size + 1) (i + 2) with
          | some k => scanProlog a fuel k
          | none => .more i
        else if c2 == '!' then
          if i + 9 > a.size then .more i
          else if litAt a ['<', '!', '-', '-'] i then
            match findLit a ['-', '-', '>'] (a.size + 1) (i + 4) with
            | some k => scanProlog a fuel k
            | none => .more i
          else if litAt a "<!DOCTYPE".toList i then
            match doctypeEnd a (a.size + 1) none 0 (i + 2) with
            | some k => scanProlog a fuel k
            | none => .more i
          else .fallback
        else if c2 == '/' then .fallback
        else
          match stagEnd a (a.size + 1) none (i + 1) with
          | some k => if a.getD (k - 1) ' ' == '/' then .fallback else .root k.succ
          | none => .more i

/-- What the children of `rdf:RDF` are read with. -/
structure Ctx where
  ents : XML.EntityTable
  atts : List XML.AttDecl
  rootTag : String

/-- A general entity this fold does not read item by item. -/
def unsafeEntity (d : XML.EntityDef) : Bool :=
  d.external || d.value.any (· == '<') || d.value.any (· == '&')

/-- The prologue and the start tag of the document element, `pre`, read
with the XML parser's functions: the context of the children and the
parser state after the attributes of `rdf:RDF`. `none` when the fall-back
rule applies. -/
def startBody (base : Option String) (pre : String) : Option (Ctx × St) :=
  match XML.documentPrologue (fun _ => none) false pre with
  | .error _ => none
  | .ok pr =>
    if pr.ver != .v10 then none
    else if pr.ents.defs.any (fun (_, d) => unsafeEntity d) then none
    else
      let s := pr.s
      match XML.pchar '<' s pr.pos with
      | .err _ _ => none
      | .ok _ p1 =>
        match XML.parseName s p1 with
        | .err _ _ => none
        | .ok tag p2 =>
          match XML.parseAttributes pr.ents s p2 (s.size + 1) with
          | .err _ _ => none
          | .ok attrs0 p3 =>
            let attrs1 := XML.normalizeAttrsByType pr.usable tag attrs0
            match XML.defaultedAttrs pr.ents pr.usable tag attrs1 with
            | .error _ => none
            | .ok defaulted =>
              match rdfStart 0 (St.init (base.getD "")) tag (attrs1 ++ defaulted) with
              | none => none
              | some w =>
                let p4 := XML.skipSpace s p3
                if XML.peekLit "/>" s p4 then none
                else
                  match XML.pchar '>' s p4 with
                  | .err _ _ => none
                  | .ok _ p5 =>
                    if p5 == s.size then some (⟨pr.ents, pr.usable, tag⟩, w.st) else none

/-! ## The children of `rdf:RDF` -/

/-- Where the scanner is inside the markup of one item. -/
inductive Scan where
  /-- Character data. -/
  | text
  /-- After `<`. -/
  | lt
  /-- After `<!`. -/
  | bang
  /-- After `<!-`. -/
  | bangDash
  /-- Inside a comment; `dashes` is the number of `-` just read (at most 2). -/
  | comment (dashes : Nat)
  /-- Inside a CDATA section; `brackets` is the number of `]` just read
  (at most 2). -/
  | cdata (brackets : Nat)
  /-- Inside a processing instruction; `q`: the last character was `?`. -/
  | pi (q : Bool)
  /-- Inside a start tag; `quote`: inside an attribute value; `slash`: the
  last character was `/`. -/
  | stag (quote : Option Char) (slash : Bool)
  /-- Inside an end tag. -/
  | etag
  deriving Repr, DecidableEq, Inhabited

/-- The state of the children phase. -/
structure Body (α : Type) where
  ctx : Ctx
  /-- The parser state the next child starts from. -/
  st : St
  acc : α
  scan : Scan
  /-- Elements open inside the current item. -/
  depth : Nat
  /-- The characters of the current item. -/
  seg : String
  /-- The number of characters before `seg`. -/
  segAt : Nat
  /-- The number of characters read. -/
  pos : Nat
  /-- After the `</` of the end tag of `rdf:RDF`: the text from there. -/
  tail : Option String
  err : Option ParseError

/-- Give the elements of one item to `nodeElement`, in order, and their
triples to the consumer. -/
def walkNodes {α : Type} (emit : α → Triple → α) (fuel : Nat) :
    St → α → List XML.Node → Except ParseError (St × α)
  | st, acc, [] => .ok (st, acc)
  | st, acc, n :: rest =>
    match n with
    | .element _ _ _ =>
      let r := nodeElement fuel st n
      match r.st.err with
      | some e => .error e
      | none => walkNodes emit fuel r.st (r.triples.foldl emit acc) rest
    | _ => walkNodes emit fuel st acc rest

/-- The characters of an item, with the line ends of XML 1.0 section 2.11. -/
def itemChars (seg : String) : XML.Chars :=
  if seg.any (· == '\r') then (XML.normalizeLineEndingsFor .v10 seg.toList).toArray
  else XML.stringChars seg

/-- The current item is complete: parse it and walk its elements. -/
def Body.flush {α : Type} (emit : α → Triple → α) (b : Body α) : Body α :=
  if b.seg.all XML.isXmlSpace then { b with seg := "" }
  else
    let arr := itemChars b.seg
    let b := { b with seg := "" }
    match XML.parseChildren b.ctx.ents b.ctx.atts arr 0 [] {} {} (arr.size + 1) with
    | .err m p => { b with err := some { msg := s!"XML: {m}", pos := b.segAt + p } }
    | .ok (nodes, _, _) p =>
      if p < arr.size then
        { b with err := some { msg := "XML: markup in the content of rdf:RDF does not parse as [43] content", pos := b.segAt + p } }
      else
        match walkNodes emit (arr.size + 2) b.st b.acc nodes with
        | .error e => { b with err := some e }
        | .ok (st, acc) => { b with st := st, acc := acc }

/-- An item closes: when it is at the top level of `rdf:RDF`, read it. -/
def Body.close {α : Type} (emit : α → Triple → α) (b : Body α) : Body α :=
  let b := { b with scan := .text }
  if b.depth == 0 then b.flush emit else b

/-- One character. -/
def Body.step {α : Type} (emit : α → Triple → α) (b : Body α) (c : Char) : Body α :=
  match b.tail with
  | some t => { b with tail := some (t.push c), pos := b.pos + 1 }
  | none =>
  let b1 := { b with pos := b.pos + 1 }
  let push (x : Body α) : Body α := { x with seg := x.seg.push c }
  match b.scan with
  | .text =>
    if c == '<' then
      if b.depth == 0 then
        let b2 := if b1.seg.isEmpty then b1 else b1.flush emit
        { b2 with seg := "<", segAt := b.pos, scan := .lt }
      else { push b1 with scan := .lt }
    else if b.seg.isEmpty then { push b1 with segAt := b.pos }
    else push b1
  | .lt =>
    if c == '/' then
      if b.depth == 0 then { b1 with seg := "", tail := some "</", scan := .text }
      else { push b1 with scan := .etag }
    else if c == '!' then { push b1 with scan := .bang }
    else if c == '?' then { push b1 with scan := .pi false }
    else { push b1 with scan := .stag none false }
  | .bang =>
    if c == '-' then { push b1 with scan := .bangDash }
    else if c == '[' then { push b1 with scan := .cdata 0 }
    else { b1 with err := some { msg := "XML: a markup declaration may not appear in content ([43] content)", pos := b.pos } }
  | .bangDash =>
    if c == '-' then { push b1 with scan := .comment 0 }
    else { b1 with err := some { msg := "XML: expected '<!--'", pos := b.pos } }
  | .comment d =>
    if c == '>' && d ≥ 2 then (push b1).close emit
    else { push b1 with scan := .comment (if c == '-' then min (d + 1) 2 else 0) }
  | .cdata r =>
    if c == '>' && r ≥ 2 then (push b1).close emit
    else { push b1 with scan := .cdata (if c == ']' then min (r + 1) 2 else 0) }
  | .pi q =>
    if c == '>' && q then (push b1).close emit
    else { push b1 with scan := .pi (c == '?') }
  | .stag q sl =>
    match q with
    | some qc => { push b1 with scan := .stag (if c == qc then none else some qc) false }
    | none =>
      if c == '>' then
        if sl then (push b1).close emit
        else { push b1 with depth := b.depth + 1, scan := .text }
      else if c == '"' || c == '\'' then { push b1 with scan := .stag (some c) false }
      else { push b1 with scan := .stag none (c == '/') }
  | .etag =>
    if c == '>' then (push { b1 with depth := b.depth - 1 }).close emit
    else push b1

/-- The characters of one chunk; stops at the first error. -/
def Body.feedChars {α : Type} (emit : α → Triple → α) (b : Body α) : List Char → Body α
  | [] => b
  | c :: cs =>
    match b.err with
    | some _ => b
    | none => Body.feedChars emit (b.step emit c) cs

/-- The end of the text: the end tag of `rdf:RDF`, then `Misc*`. -/
def Body.finish {α : Type} (b : Body α) : Except ParseError α :=
  match b.err with
  | some e => .error e
  | none =>
  match b.tail with
  | none => .error { msg := "XML: the text ends inside rdf:RDF", pos := b.pos }
  | some t =>
    let at0 := b.segAt
    let cs := itemChars t
    match XML.pstring "</" cs 0 with
    | .err m p => .error { msg := s!"XML: {m}", pos := at0 + p }
    | .ok _ p1 =>
      match XML.parseName cs p1 with
      | .err m p => .error { msg := s!"XML: {m}", pos := at0 + p }
      | .ok closeTag p2 =>
        if closeTag != b.ctx.rootTag then
          .error { msg := s!"XML: closing tag '</{closeTag}>' does not match opening '<{b.ctx.rootTag}>' (WFC: Element Type Match)", pos := at0 + p1 }
        else
          match XML.pchar '>' cs (XML.skipSpace cs p2) with
          | .err m p => .error { msg := s!"XML: {m}", pos := at0 + p }
          | .ok _ p3 =>
            match XML.documentEpilog .v10 cs p3 with
            | .error e => .error { msg := s!"XML: {e.message}", pos := at0 + e.position }
            | .ok _ => .ok b.acc

/-! ## The fold -/

/-- The state of the fold. -/
inductive State (α : Type) where
  /-- The characters so far, all in the prologue; `resume` is where the next
  scan starts. -/
  | prolog (base : Option String) (acc : α) (chars : Array Char) (resume : Nat)
  /-- The fall-back: the chunks, newest first. -/
  | whole (base : Option String) (acc : α) (bufRev : List String)
  /-- The children phase. -/
  | body (b : Body α)

def State.init {α : Type} (base : Option String) (acc : α) : State α :=
  .prolog base acc #[] 0

/-- The whole-document reader. -/
def readWhole {α : Type} (emit : α → Triple → α) (base : Option String) (acc : α)
    (text : String) : Except ParseError α :=
  (parseRdfXml text base).map (fun g => g.foldl emit acc)

/-- The prologue phase with the characters `a`. -/
def afterProlog {α : Type} (emit : α → Triple → α) (base : Option String) (acc : α)
    (a : Array Char) (resume : Nat) : State α :=
  match scanProlog a (a.size + 1) resume with
  | .more r =>
    if a.size > prologLimit then .whole base acc [String.ofList a.toList]
    else .prolog base acc a r
  | .fallback => .whole base acc [String.ofList a.toList]
  | .root k =>
    match startBody base (String.ofList (a.extract 0 k).toList) with
    | none => .whole base acc [String.ofList a.toList]
    | some (ctx, st) =>
      let b : Body α := { ctx := ctx, st := st, acc := acc, scan := .text, depth := 0,
                          seg := "", segAt := k, pos := k, tail := none, err := none }
      .body (b.feedChars emit (a.extract k a.size).toList)

/-- Feed one chunk. -/
def State.feed {α : Type} (emit : α → Triple → α) : State α → String → Except ParseError (State α)
  | .prolog base acc a resume, text => .ok (afterProlog emit base acc (text.foldl Array.push a) resume)
  | .whole base acc bufRev, text => .ok (.whole base acc (text :: bufRev))
  | .body b, text =>
    let b := b.feedChars emit text.toList
    match b.err with
    | some e => .error e
    | none => .ok (.body b)

/-- The end of the text. -/
def State.finish {α : Type} (emit : α → Triple → α) : State α → Except ParseError α
  | .prolog base acc a _ => readWhole emit base acc (String.ofList a.toList)
  | .whole base acc bufRev => readWhole emit base acc (String.join bufRev.reverse)
  | .body b => b.finish

def State.acc {α : Type} : State α → α
  | .prolog _ acc _ _ => acc
  | .whole _ acc _ => acc
  | .body b => b.acc

/-- Take the accumulator out, give it to `f`, put the first result back. -/
def State.withAcc {α β : Type} (f : α → α × β) : State α → State α × β
  | .prolog base acc a r =>
    let (acc, x) := f acc
    (.prolog base acc a r, x)
  | .whole base acc bufRev =>
    let (acc, x) := f acc
    (.whole base acc bufRev, x)
  | .body ⟨ctx, st, acc, scan, depth, seg, segAt, pos, tail, err⟩ =>
    let (acc, x) := f acc
    (.body ⟨ctx, st, acc, scan, depth, seg, segAt, pos, tail, err⟩, x)

/-- Feed a list of chunks and finish. -/
def readAll {α : Type} (emit : α → Triple → α) (base : Option String) (acc : α)
    (chunks : List String) : Except ParseError α :=
  match chunks.foldlM (fun s c => s.feed emit c) (State.init base acc) with
  | .error e => .error e
  | .ok s => s.finish emit

/-! ## The prologue and fall-back phases keep the text -/

/-- Not in the children phase. -/
def State.notStreamed {α : Type} : State α → Bool
  | .body _ => false
  | _ => true

/-- In the prologue and fall-back phases the fold holds the text it was
given (`text`) and the accumulator it started with. -/
def State.Holds {α : Type} (base : Option String) (acc0 : α) (text : String) : State α → Prop
  | .prolog b acc a _ => b = base ∧ acc = acc0 ∧ a.toList = text.toList
  | .whole b acc bufRev => b = base ∧ acc = acc0 ∧ String.join bufRev.reverse = text
  | .body _ => True

theorem foldl_push_toList (text : String) (a : Array Char) :
    (text.foldl Array.push a).toList = a.toList ++ text.toList := by
  rw [String.foldl_eq_foldl_toList]
  generalize text.toList = l
  induction l generalizing a with
  | nil => simp
  | cons c cs ih => simp [List.foldl_cons]

theorem ofList_toList_eq (a : Array Char) (text : String) (h : a.toList = text.toList) :
    String.ofList a.toList = text := by
  rw [h]; simp

theorem afterProlog_holds {α : Type} (emit : α → Triple → α) (base : Option String) (acc : α)
    (a : Array Char) (resume : Nat) (text : String) (h : a.toList = text.toList) :
    (afterProlog emit base acc a resume).Holds base acc text := by
  unfold afterProlog
  cases scanProlog a (a.size + 1) resume with
  | more r =>
    dsimp only
    split
    · exact ⟨rfl, rfl, by simp [ofList_toList_eq a text h]⟩
    · exact ⟨rfl, rfl, h⟩
  | fallback => exact ⟨rfl, rfl, by simp [ofList_toList_eq a text h]⟩
  | root k =>
    dsimp only
    split
    · exact ⟨rfl, rfl, by simp [ofList_toList_eq a text h]⟩
    · trivial

/-- A feed keeps `Holds`, with the chunk added to the text. -/
theorem feed_holds {α : Type} (emit : α → Triple → α) (base : Option String) (acc0 : α)
    (text : String) (s : State α) (c : String) (s' : State α)
    (hs : s.Holds base acc0 text) (hf : s.feed emit c = .ok s') :
    s'.Holds base acc0 (text ++ c) := by
  cases s with
  | prolog b acc a resume =>
    obtain ⟨hb, ha, ht⟩ := hs
    subst hb; subst ha
    simp only [State.feed, Except.ok.injEq] at hf
    subst hf
    apply afterProlog_holds
    rw [foldl_push_toList, ht, String.toList_append]
  | whole b acc bufRev =>
    obtain ⟨hb, ha, ht⟩ := hs
    subst hb; subst ha
    simp only [State.feed, Except.ok.injEq] at hf
    subst hf
    refine ⟨rfl, rfl, ?_⟩
    simp [String.join, List.reverse_cons, List.foldl_append] at ht ⊢
    rw [← ht]
  | body b =>
    simp only [State.feed] at hf
    split at hf
    · cases hf
    · cases hf; trivial

/-- The children phase never goes back to the prologue or the fall-back. -/
theorem feed_body_streamed {α : Type} (emit : α → Triple → α) (b : Body α) (c : String)
    (s' : State α) (hf : (State.body b).feed emit c = .ok s') : s'.notStreamed = false := by
  simp only [State.feed] at hf
  split at hf
  · cases hf
  · cases hf; rfl

/-- **The fold keeps the text.** After any list of chunks that the fold
accepts, a state in the prologue or fall-back phase holds the joined chunks
and the accumulator it started with. -/
theorem foldlM_inv {α : Type} (emit : α → Triple → α) (base : Option String) (acc0 : α) :
    ∀ (chunks : List String) (text : String) (s s' : State α), s.Holds base acc0 text →
      chunks.foldlM (fun s c => s.feed emit c) s = .ok s' →
      s'.Holds base acc0 (text ++ String.join chunks)
  | [], text, s, s', hs, hf => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
    subst hf; simpa using hs
  | c :: rest, text, s, s', hs, hf => by
    rw [List.foldlM_cons] at hf
    cases h1 : s.feed emit c with
    | error e => rw [h1] at hf; cases hf
    | ok s1 =>
      rw [h1] at hf
      have := foldlM_inv emit base acc0 rest (text ++ c) s1 s' (feed_holds emit base acc0 text s c s1 hs h1) hf
      simpa [String.join_cons, String.append_assoc] using this

/-- **The fall-back gives the whole-document reader.** When the fold of the
chunks ends in the prologue or the fall-back phase, the result is the
whole-document reader's on the joined chunks: the same quads, in the same
order, and the same error. -/
theorem readAll_eq_whole_of_notStreamed {α : Type} (emit : α → Triple → α)
    (base : Option String) (acc0 : α) (chunks : List String) (s : State α)
    (hf : chunks.foldlM (fun s c => s.feed emit c) (State.init base acc0) = .ok s)
    (hn : s.notStreamed = true) :
    readAll emit base acc0 chunks = readWhole emit base acc0 (String.join chunks) := by
  have hinv := foldlM_inv emit base acc0 chunks "" (State.init base acc0) s
    ⟨rfl, rfl, by simp⟩ hf
  simp only [String.empty_append] at hinv
  simp only [readAll, hf]
  cases s with
  | prolog b acc a r =>
    obtain ⟨hb, ha, ht⟩ := hinv
    subst hb; subst ha
    simp only [State.finish, ofList_toList_eq a _ ht]
  | whole b acc bufRev =>
    obtain ⟨hb, ha, ht⟩ := hinv
    subst hb; subst ha
    simp only [State.finish, ht]
  | body b => cases hn

#print axioms foldl_push_toList
#print axioms afterProlog_holds
#print axioms feed_holds
#print axioms feed_body_streamed
#print axioms foldlM_inv
#print axioms readAll_eq_whole_of_notStreamed

/-! ## Build-time checks -/

private def collectT : List Triple → Triple → List Triple := fun acc t => t :: acc

/-- The fold over the document cut at `cut`, and the whole-document reader,
give the same triples in the same order, or both refuse. -/
private def cutAgrees (doc : String) (cut : Nat) : Bool :=
  let cs := doc.toList
  let chunks := [String.ofList (cs.take cut), String.ofList (cs.drop cut)]
  let want := (parseRdfXml doc none).toOption
  let got := (readAll collectT none [] chunks).toOption.map List.reverse
  got == want

private def allCutsAgree (doc : String) : Bool :=
  (List.range (doc.length + 1)).all (cutAgrees doc)

/-- The fold over chunks of `n` characters. -/
private def chunked (doc : String) (n : Nat) : List String :=
  let rec go (fuel : Nat) (cs : List Char) (acc : List String) : List String :=
    match fuel, cs with
    | 0, _ => acc.reverse
    | _, [] => acc.reverse
    | f + 1, cs => go f (cs.drop n) (String.ofList (cs.take n) :: acc)
  go (doc.length + 1) doc.toList []

private def notStreamedAt (doc : String) : Bool :=
  match (chunked doc 1).foldlM (fun s c => s.feed collectT c) (State.init none ([] : List Triple)) with
  | .ok s => s.notStreamed
  | .error _ => false

private def rdfHead : String :=
  "<?xml version=\"1.0\"?>\n<!-- a comment > with a bracket -->\n<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"http://e/\" xml:base=\"http://e/base/\" xml:lang=\"en\">"

private def docA : String :=
  rdfHead ++ "\n  <rdf:Description rdf:about=\"a\"><e:p rdf:resource=\"b\"/><e:q>x</e:q></rdf:Description>\n" ++
  "<!-- between > children --><?pi x?>\n  <e:T rdf:about=\"t\" e:attr=\"v>w\"><e:r><rdf:Description><e:s>y</e:s></rdf:Description></e:r></e:T>\n" ++
  "  <rdf:Description><e:l rdf:parseType=\"Literal\"><b>z<![CDATA[ ]] > ]]></b></e:l><e:li xml:lang=\"de\">w</e:li></rdf:Description>\n" ++
  "  <rdf:Description rdf:nodeID=\"k\"><e:c rdf:parseType=\"Collection\"><rdf:Description rdf:about=\"c1\"/></e:c></rdf:Description>\r\n" ++
  "</rdf:RDF>\n<!-- after -->\n"

-- A DOCTYPE with namespace entities, used in attribute values of the children.
private def docEnt : String :=
  "<?xml version=\"1.0\"?>\n<!DOCTYPE rdf:RDF [\n  <!ENTITY e \"http://e/\">\n  <!-- don't [ -->\n  <!ENTITY rdf 'http://www.w3.org/1999/02/22-rdf-syntax-ns#'>\n]>\n" ++
  "<rdf:RDF xmlns:rdf=\"&rdf;\" xmlns:e=\"&e;\"><rdf:Description rdf:about=\"&e;a\"><e:p>&e; &amp; &#65;</e:p></rdf:Description></rdf:RDF>"

-- A markup entity: read whole.
private def docMarkupEnt : String :=
  "<!DOCTYPE rdf:RDF [<!ENTITY d '<rdf:Description rdf:about=\"http://e/m\"><e:p>m</e:p></rdf:Description>'>]>" ++
  "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"http://e/\">&d;<rdf:Description rdf:about=\"http://e/n\"/></rdf:RDF>"

-- The document element is a node element: read whole.
private def docNode : String :=
  "<e:T xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"http://e/\" rdf:about=\"http://e/x\"><e:p>v</e:p></e:T>"

#guard (parseRdfXml docA none).toOption.map List.length == some 11
#guard allCutsAgree docA
#guard (parseRdfXml docEnt none).toOption.map List.length == some 1
#guard allCutsAgree docEnt
#guard allCutsAgree docMarkupEnt
#guard allCutsAgree docNode
#guard notStreamedAt docMarkupEnt && notStreamedAt docNode
#guard !notStreamedAt docA && !notStreamedAt docEnt

-- Refused by both, at every cut: an end tag that does not match, a missing end
-- tag, content after the document element, an RDF/XML rule (a property
-- element name with no namespace), an undeclared entity, a markup declaration
-- in content.
#guard allCutsAgree (rdfHead ++ "<rdf:Description></rdf:Descriptio></rdf:RDF>")
#guard allCutsAgree (rdfHead ++ "<rdf:Description/>")
#guard allCutsAgree (rdfHead ++ "<rdf:Description/></rdf:RDF><x/>")
#guard allCutsAgree (rdfHead ++ "<rdf:Description><p>1</p></rdf:Description></rdf:RDF>")
#guard allCutsAgree (rdfHead ++ "<rdf:Description><e:p>&u;</e:p></rdf:Description></rdf:RDF>")
#guard allCutsAgree (rdfHead ++ "<!ELEMENT x ANY></rdf:RDF>")
#guard allCutsAgree (rdfHead ++ "text &amp; more<rdf:Description/></rdf:RDF  >")
#guard allCutsAgree (rdfHead ++ "</rdf:RDF>")
#guard allCutsAgree ("<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"/>")
#guard allCutsAgree "<rdf:RDF"
#guard allCutsAgree ""

end L4Factoidal.Syntax.RdfXmlChunkFold
