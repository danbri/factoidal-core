/-
L4Factoidal.Syntax.JsonLdChunkFold — JSON-LD read in chunks: one top-level node
object at a time.

Tracking: https://github.com/danbri/factoidal/issues/839.

The source layer used to keep every chunk of a JSON-LD document and give the
joined text to `JSONLD.parseJsonLd`: the text, the JSON tree, the expanded tree
and the dataset were all live together, 11.3 to 13.5 bytes of peak resident
memory for each source byte.

## The document forms that are read item by item

The streaming document form of "Streaming JSON-LD" (W3C Working Group Note,
7 May 2020, https://www.w3.org/TR/json-ld11-streaming/) puts `@context` first
in a node object. This module reads two shapes, one top-level node object at a
time:

* A: the top-level value is an array: `[ node, node, ... ]`.
* B: the top-level value is an object with exactly two members, in this order:
  `{ "@context": C, "@graph": [ node, node, ... ] }`, and nothing follows the
  closing brace but white space.

For each node object the consumer calls the item function that `Ops.begin`
made for the document (it holds the processing of the shared context `C`), and
the quads go to the consumer at once; the node object's text is then dropped.
The generated blank-node counter passes from one node object to the next, so
the labels are those of the whole-document reader (`JSONLD.ToRdf.expandTops`
threads one counter through the top-level objects in the same order).

## The fall-back rule

A document is read item by item only when its `Probe` (one read of the bytes
before the first chunk, like the pre-pass of Turtle) finds both:

1. the document has shape A or shape B above (`Scan` ends in an accepting
   state), and
2. no JSON string of the document (a key or a value, after the unescaping of
   `\u` and the other escapes) contains the nine characters `_jld_anon`, the
   base of the generated blank-node labels (`JSONLD.ToRdf.anonBase`). Then the
   generated prefix of the whole-document reader is `_jld_anon` itself
   (`JSONLD.ToRdf.generatedPrefix`: no label of the document begins with it),
   and the streaming reader uses that prefix without having seen the end of the
   document. The test is stronger than the one `generatedPrefix` makes, so a
   document that mentions `_jld_anon` in a context definition or in a name that
   the expansion drops is read whole although the labels would not differ.

Otherwise the source layer builds the whole-document reader, as before
(`Source.Reader.init`: the generated-prefix argument is not `streamPrefix`).

## What is proved and what is measured

Proved (`RDF/SourceTheorems.lean`): when the reader is the whole-document
reader it gives `parseDocument` of the joined chunks for every list of chunks
(`jsonld_readAll_of_notStreamed`).

Not proved: when the reader reads item by item, the quads equal those of the
whole-document reader. The proof needs (1) the expansion of an array or of an
`@graph` array to be the concatenation of the expansions of its items, with
each item's fuel sufficient, and (2) `expandTops` to be a fold over its items
with the counter passed on. The equality is measured:
`Harness/JsonLdChunkDiff.lean` (`tools/jsonld-chunk-differential.sh`). The
quads of a document with named graphs agree as a multiset but not in order:
the whole-document reader gives the default graph first, then the named
graphs; the item reader gives each item's default graph and named graphs in
turn. Open issue: https://github.com/danbri/factoidal/issues/946; expected
failure: row JS-1 of `tests/known-defects/run.sh`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Parser
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.Syntax.JsonLdChunkFold

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The generated-prefix argument that asks for the item reader. It is the base
of the generated labels: `JSONLD.ToRdf.anonBase`. -/
def streamPrefix : String := "_jld_anon"

/-! ## The scan of the document structure -/

/-- Where the scan is in the document. -/
inductive Phase where
  /-- before the top-level value -/
  | start
  /-- matching `"@context"`, `i` characters matched -/
  | ctxKey (i : Nat)
  | ctxColon
  | ctxValue
  /-- after the context value and its comma -/
  | afterCtx
  /-- matching `"@graph"`, `i` characters matched -/
  | graphKey (i : Nat)
  | graphColon
  | graphOpen
  /-- after `[`, before the first item or `]` -/
  | elemFirst
  /-- after `,`, before an item -/
  | elemNext
  /-- inside an item; `true` for the context value -/
  | inItem (isCtx : Bool)
  /-- after the `]` that ends the items -/
  | afterElems
  /-- after the `}` that ends the object; also after the `]` of shape A -/
  | done
  | bad
  deriving DecidableEq

/-- What a character was. -/
inductive Act where
  /-- structure or white space -/
  | skip
  /-- a character of an item -/
  | item
  /-- the character ends an item (the character is not part of it); `true` for
  the context value -/
  | endItem (isCtx : Bool)
  deriving DecidableEq

structure Scan where
  phase : Phase := .start
  depth : Nat := 0
  inStr : Bool := false
  esc : Bool := false
  /-- shape B -/
  viaGraph : Bool := false

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def ctxLit : Array Char := "\"@context\"".toList.toArray
def graphLit : Array Char := "\"@graph\"".toList.toArray

/-- One character inside an item. A `,` or the closing bracket of the enclosing
array at depth 0, outside a string, ends the item. -/
def Scan.itemChar (s : Scan) (isCtx : Bool) (c : Char) : Scan × Act :=
  if s.inStr then
    if s.esc then ({ s with esc := false }, .item)
    else if c == '\\' then ({ s with esc := true }, .item)
    else if c == '"' then ({ s with inStr := false }, .item)
    else (s, .item)
  else if c == '"' then ({ s with inStr := true }, .item)
  else if c == '{' || c == '[' then ({ s with depth := s.depth + 1 }, .item)
  else if c == '}' || c == ']' then
    if s.depth > 0 then ({ s with depth := s.depth - 1 }, .item)
    else if c == ']' && !isCtx then ({ s with phase := .afterElems }, .endItem false)
    else ({ s with phase := .bad }, .skip)
  else if c == ',' && s.depth == 0 then
    if isCtx then ({ s with phase := .afterCtx }, .endItem true)
    else ({ s with phase := .elemNext }, .endItem false)
  else (s, .item)

/-- The start of an item (`c` is not white space): the item's first character. -/
def Scan.startItem (s : Scan) (isCtx : Bool) (c : Char) : Scan × Act :=
  let (s', a) := s.itemChar isCtx c
  if s'.phase == .bad || a != .item then (s', a) else ({ s' with phase := .inItem isCtx }, a)

/-- One character of the document. -/
def Scan.step (s : Scan) (c : Char) : Scan × Act :=
  let bad : Scan × Act := ({ s with phase := .bad }, .skip)
  match s.phase with
  | .start =>
    if isWs c then (s, .skip)
    else if c == '[' then ({ s with phase := .elemFirst }, .skip)
    else if c == '{' then ({ s with phase := .ctxKey 0, viaGraph := true }, .skip)
    else bad
  | .ctxKey i =>
    if i == 0 && isWs c then (s, .skip)
    else if ctxLit.getD i ' ' == c then
      (if i + 1 == ctxLit.size then ({ s with phase := .ctxColon }, .skip)
       else ({ s with phase := .ctxKey (i + 1) }, .skip))
    else bad
  | .ctxColon =>
    if isWs c then (s, .skip)
    else if c == ':' then ({ s with phase := .ctxValue }, .skip)
    else bad
  | .ctxValue =>
    if isWs c then (s, .skip)
    else if c == ',' || c == ']' || c == '}' then bad
    else s.startItem true c
  | .afterCtx =>
    if isWs c then (s, .skip)
    else if c == '"' then ({ s with phase := .graphKey 1 }, .skip)
    else bad
  | .graphKey i =>
    if graphLit.getD i ' ' == c then
      (if i + 1 == graphLit.size then ({ s with phase := .graphColon }, .skip)
       else ({ s with phase := .graphKey (i + 1) }, .skip))
    else bad
  | .graphColon =>
    if isWs c then (s, .skip)
    else if c == ':' then ({ s with phase := .graphOpen }, .skip)
    else bad
  | .graphOpen =>
    if isWs c then (s, .skip)
    else if c == '[' then ({ s with phase := .elemFirst }, .skip)
    else bad
  | .elemFirst =>
    if isWs c then (s, .skip)
    else if c == ']' then ({ s with phase := .afterElems }, .skip)
    else if c == ',' || c == '}' then bad
    else s.startItem false c
  | .elemNext =>
    if isWs c then (s, .skip)
    else if c == ',' || c == ']' || c == '}' then bad
    else s.startItem false c
  | .inItem isCtx => s.itemChar isCtx c
  | .afterElems =>
    if isWs c then (s, .skip)
    else if s.viaGraph && c == '}' then ({ s with phase := .done }, .skip)
    else if s.viaGraph then bad
    else bad
  | .done => if isWs c then (s, .skip) else bad
  | .bad => (s, .skip)

/-- The document ended in an accepting state: shape A after its `]`, shape B
after its `}`. -/
def Scan.accepted (s : Scan) : Bool :=
  match s.phase with
  | .done => true
  | .afterElems => !s.viaGraph
  | _ => false

/-! ## Whether a string of the document mentions the generated-label base -/

/-- The characters of the strings of a JSON text, unescaped, matched against
`_jld_anon`. -/
structure Mention where
  /-- 0 outside a string, 1 inside, 2 after a backslash, 3 in the four hex digits
  of a `\u` escape -/
  mode : Nat := 0
  hexLeft : Nat := 0
  hexAcc : Nat := 0
  /-- characters of the pattern matched in the current string -/
  k : Nat := 0
  found : Bool := false

def anonPattern : Array Char := "_jld_anon".toList.toArray

def Mention.char (m : Mention) (c : Char) : Mention :=
  if anonPattern.getD m.k ' ' == c then
    if m.k + 1 == anonPattern.size then { m with found := true } else { m with k := m.k + 1 }
  else { m with k := if c == '_' then 1 else 0 }

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def Mention.feed (m : Mention) (c : Char) : Mention :=
  if m.found then m else
  match m.mode with
  | 0 => if c == '"' then { m with mode := 1, k := 0 } else m
  | 1 =>
    if c == '"' then { m with mode := 0 }
    else if c == '\\' then { m with mode := 2 }
    else m.char c
  | 2 =>
    if c == 'u' then { m with mode := 3, hexLeft := 4, hexAcc := 0 }
    else
      let c' := if c == 'b' || c == 'f' || c == 'n' || c == 'r' || c == 't' then ' ' else c
      { m with mode := 1 }.char c'
  | _ =>
    let acc := m.hexAcc * 16 + hexVal c
    if m.hexLeft ≤ 1 then
      { m with mode := 1, hexLeft := 0, hexAcc := 0 }.char (if acc < 128 then Char.ofNat acc else ' ')
    else { m with hexLeft := m.hexLeft - 1, hexAcc := acc }

/-! ## The probe -/

/-- One read of the document before the first chunk: its shape, and whether a
string mentions `_jld_anon`. -/
structure Probe where
  scan : Scan := {}
  mention : Mention := {}

def Probe.feed (p : Probe) (c : Char) : Probe :=
  { scan := (p.scan.step c).1, mention := p.mention.feed c }

def Probe.feedString (p : Probe) (text : String) : Probe :=
  text.foldl Probe.feed p

/-- The document can be read item by item (the fall-back rule). -/
def Probe.eligible (p : Probe) : Bool := p.scan.accepted && !p.mention.found

/-- The generated-prefix argument for `Source.Reader.init`: `streamPrefix` when
the document is read item by item, `""` otherwise. -/
def Probe.prefixArg (p : Probe) : String := if p.eligible then streamPrefix else ""

/-! ## The consumer of items -/

/-- Converts one top-level node object (any JSON value, as the document wrote
it) given the generated blank-node counter, and gives the dataset of that object
and the counter after it. -/
abbrev ItemFn := Nat → Json → Except ParseError (Dataset × Nat)

/-- What the JSON-LD library supplies. -/
structure Ops where
  /-- `begin mode base context`: the item function of a document whose shared
  context is `context` (`none` for shape A). The only failure is a context that
  does not process. -/
  begin : Mode → Option String → Option Json → Except ParseError ItemFn
  /-- the error of an item or a context that is not JSON -/
  notJson : ParseError

/-! ## The fold -/

structure State (α : Type) where
  ops : Ops
  mode : Mode
  base : Option String
  scan : Scan
  acc : α
  /-- the characters of the item being read -/
  text : String
  fn : Option ItemFn
  ctr : Nat
  err : Option ParseError

def State.init {α : Type} (ops : Ops) (mode : Mode) (base : Option String) (acc : α) : State α :=
  { ops, mode, base, scan := {}, acc, text := "", fn := none, ctr := 0, err := none }

/-- The quads of a dataset to the consumer, the declaration of each named graph
before its triples: `Source.foldDatasetD`. -/
def emit {α : Type} (step : α → Triple → Option Subject → α) (decl : α → Subject → α)
    (acc : α) (ds : Dataset) : α :=
  ds.named.foldl (fun a ng => ng.graph.foldl (fun a t => step a t (some ng.name)) (decl a ng.name))
    (ds.default.foldl (fun a t => step a t none) acc)

def streamError : ParseError :=
  { msg := "invalid or unsupported JSON-LD (the document is not in streaming form)", pos := 0 }

/-- An item or the context is complete. The accumulator is taken out of the state
by a match, so `emit` holds the only reference and updates it in place. -/
def State.endItem {α : Type} (step : α → Triple → Option Subject → α) (decl : α → Subject → α)
    (isCtx : Bool) : State α → State α
  | { ops, mode, base, scan, acc, text, fn, ctr, err } =>
    match parseJson text with
    | .error _ => { ops, mode, base, scan, acc, text := "", fn, ctr, err := some ops.notJson }
    | .ok j =>
      if isCtx then
        match ops.begin mode base (some j) with
        | .error e => { ops, mode, base, scan, acc, text := "", fn, ctr, err := some e }
        | .ok f => { ops, mode, base, scan, acc, text := "", fn := some f, ctr, err }
      else
        let fnE : Except ParseError ItemFn :=
          match fn with
          | some f => .ok f
          | none => ops.begin mode base none
        match fnE with
        | .error e => { ops, mode, base, scan, acc, text := "", fn, ctr, err := some e }
        | .ok f =>
          match f ctr j with
          | .error e => { ops, mode, base, scan, acc, text := "", fn := some f, ctr, err := some e }
          | .ok (ds, ctr') =>
            { ops, mode, base, scan, acc := emit step decl acc ds, text := "", fn := some f,
              ctr := ctr', err }

def State.stepChar {α : Type} (step : α → Triple → Option Subject → α) (decl : α → Subject → α)
    (s : State α) (c : Char) : State α :=
  match s.err with
  | some _ => s
  | none =>
    let (sc, act) := s.scan.step c
    let s := { s with scan := sc }
    if sc.phase == .bad then { s with err := some streamError }
    else
      match act with
      | .skip => s
      | .item => { s with text := s.text.push c }
      | .endItem isCtx => State.endItem step decl isCtx s

/-- Feed one chunk. -/
def State.feed {α : Type} (step : α → Triple → Option Subject → α) (decl : α → Subject → α)
    (s : State α) (text : String) : Except ParseError (State α) :=
  let s := text.foldl (State.stepChar step decl) s
  match s.err with
  | some e => .error e
  | none => .ok s

/-- The end of the text. -/
def State.finish {α : Type} (s : State α) : Except ParseError α :=
  match s.err with
  | some e => .error e
  | none => if s.scan.accepted then .ok s.acc else .error streamError

def State.acc' {α : Type} (s : State α) : α := s.acc

/-- Take the accumulator out, give it to `f`, put the first result back. -/
def State.withAcc {α β : Type} (f : α → α × β) (s : State α) : State α × β :=
  match s with
  | { ops, mode, base, scan, acc, text, fn, ctr, err } =>
    let (acc, b) := f acc
    ({ ops, mode, base, scan, acc, text, fn, ctr, err }, b)

/-! ## Build-time checks -/

private def probeOf (doc : String) : Probe := doc.foldl Probe.feed {}

private def shapeA : String := "[{\"@id\":\"http://e/a\"},{\"@id\":\"http://e/b\"}]"
private def shapeB : String := " {\"@context\" : {\"e\":\"http://e/\"} , \"@graph\":[ {\"@id\":\"e:a\"} , {\"@id\":\"e:b\"} ] } "

#guard (probeOf shapeA).eligible
#guard (probeOf shapeB).eligible
#guard (probeOf "[]").eligible
#guard (probeOf "{\"@context\":{},\"@graph\":[]}").eligible
-- other shapes are read whole
#guard !(probeOf "{\"@id\":\"http://e/a\"}").eligible
#guard !(probeOf "{\"@graph\":[]}").eligible
#guard !(probeOf "{\"@graph\":[],\"@context\":{}}").eligible
#guard !(probeOf "{\"@context\":{},\"@graph\":[],\"x\":1}").eligible
#guard !(probeOf "{\"@context\":{},\"@graph\":{}}").eligible
#guard !(probeOf "[{\"@id\":\"http://e/a\"}] x").eligible
#guard !(probeOf "[1,]").eligible
#guard !(probeOf "[,1]").eligible
#guard !(probeOf "[{\"a\":[1,2}]").eligible
#guard !(probeOf "[").eligible
#guard !(probeOf "").eligible
-- a comma, a bracket and a quote inside a string do not end an item
#guard (probeOf "[{\"@id\":\"a,]\\\"}\"},1,\"x\"]").eligible
-- the base of the generated labels in a string, plain or escaped, in a key or a value
#guard !(probeOf "[{\"@id\":\"_:_jld_anon0\"}]").eligible
#guard !(probeOf "[{\"_jld_anon\":1}]").eligible
#guard !(probeOf "[{\"@id\":\"\\u005fjld_anon\"}]").eligible
#guard !(probeOf "[{\"@id\":\"a_jld_\\u0061non\"}]").eligible
#guard !(probeOf "[{\"@id\":\"_jld_ano\"},\"x_jld_anonx\"]").eligible
#guard (probeOf "[{\"@id\":\"_jld_ano\"},\"_jl d_anon\"]").eligible
-- outside a string it is not a mention
#guard (probeOf "[1, 2]").mention.found == false

end L4Factoidal.Syntax.JsonLdChunkFold
