/-
L4Factoidal.JSONLD.Flatten — JSON-LD 1.1 Flattening.

Port of `formal/fstar/JSONLD.Flatten.fst`.

Specifications implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §7.1 Node Map Generation — `nmg`: walk the EXPANDED document,
    collecting every node's properties into a per-graph node map keyed
    by node identifier, relabelling every blank node identifier through
    the §7.2 issuer (`_:b0`, `_:b1`, … in first-issue order — the
    fixtures pin the exact labels, so issue order follows the spec's
    step order: `@type` items first, then `@id`, then `@reverse` /
    `@graph` / `@included` / the remaining properties in code-point key
    order);
  * §7.2 Generate Blank Node Identifier — `issueKeyed` / `issueFresh`;
  * §6.1's flattening fold (`flattenExpanded`): fold each named graph's
    nodes (ordered by id) under a `@graph` entry of that graph's
    name-node in the default graph (graph names ordered
    lexicographically), then emit the default graph's nodes ordered by
    id, dropping nodes that consist ONLY of an `@id`;
  * the `JsonLdProcessor.flatten()` entry point (`flattenDocument`):
    expand, flatten, and — when the caller supplies a context — compact
    the flattened array with `JSONLD.Compact`, keeping a top-level
    `@graph` (or its alias) and re-attaching the original context.

All map lookups here are on EXPANDED-form JSON (literal `@id` / `@value`
keys — expansion has already resolved aliases); aliases matter only for
the OUTPUT `@graph` key of the compaction step.

## Error model

`Res` (`Except JsonLdError`). The flatten manifest's single negative
test expects `conflicting indexes`, raised at Node Map Generation step
6.8 when two different `@index` values reach one node id; this port
produces exactly that code. Fuel exhaustion is `contextOverflow` — an
honest failure, never a wrong answer.

## Termination

Node Map Generation recurses over the document tree through a mutual
group; every function in it carries an explicit fuel `Nat` derived from
`Json.size`, exactly as the F* source does.
-/
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSONLD.OrderedMap

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Node-map representation

The node map is a tree of persistent maps (see `OrderedMap.lean` for why
persistent): the state maps a graph name to a graph, a graph maps a node
identifier to a node, and a node maps a property to its value. Lookup and
update cost a logarithmic number of string comparisons, so node map
generation is `O(n log n)` in the number of nodes. The earlier port kept
all four levels as association lists, which made every lookup a scan and
node map generation quadratic
(`docs/designissues/2026-10-10-jsonld-node-map-scaling.md`).

Orders the spec and the fixtures observe:

  * a node's entries come out in first-creation order (`@id` first, then
    `@type` / `@index` / properties as they were first touched) — an
    `OMap`;
  * a graph's nodes and the graph names come out "ordered by id" /
    "lexicographically" — the traversal order of a `Std.TreeMap` keyed by
    `String`, which is code-point order (`strLt_iff_compare_lt` in
    `NodeMapTheorems.lean` ties it to the `strLt` the earlier port sorted
    with). -/

/-- The values collected under one property of a node, in append order.
`rev` is the list newest-first (appending is a `cons`); `seen` holds the
RFC 8785 canonical form (`jcsDocument`) of every item in `rev`, so the
spec's "the value is not already in the array" check
(`expandedEqual`, which compares canonical forms) is one set lookup
instead of a scan that serialises every item already present. -/
structure DedupArr where
  rev  : List Json
  seen : Std.TreeSet String

namespace DedupArr

def empty : DedupArr := { rev := [], seen := Std.TreeSet.empty }

/-- Append `v`, whose canonical form is `key`. -/
def pushKeyed (a : DedupArr) (key : String) (v : Json) : DedupArr :=
  { rev := v :: a.rev, seen := a.seen.insert key }

def push (a : DedupArr) (v : Json) : DedupArr := a.pushKeyed (jcsDocument v) v

/-- The spec's "already in the array" test. -/
def has (a : DedupArr) (v : Json) : Bool := a.seen.contains (jcsDocument v)

/-- The items, in append order. -/
def toList (a : DedupArr) : List Json := a.rev.reverse

/-- Append `v` unless `dedup` is set and an equal value is already
present. -/
def pushDedup (a : DedupArr) (v : Json) (dedup : Bool) : DedupArr :=
  let key := jcsDocument v
  if dedup && a.seen.contains key then a else a.pushKeyed key v

def ofList (xs : List Json) : DedupArr := xs.foldl push empty

end DedupArr

/-- One entry of a node. `one` is a scalar entry (`@id`, `@index`);
`many` is an array entry (`@type` and every property). -/
inductive NmVal where
  | one  : Json → NmVal
  | many : DedupArr → NmVal

/-- The JSON value an entry stands for. -/
def NmVal.toJson : NmVal → Json
  | .one j  => j
  | .many a => .array a.toList

/-- The entry read as a list of values (`asArray` of its JSON value). -/
def NmVal.items : NmVal → List Json
  | .one j  => asArray j
  | .many a => a.toList

/-- A node's collected entries: `@id` first (always present), then `@type`
/ `@index` / properties in first-seen order. Emitted verbatim as an
object — member order is insignificant under the suite's JCS-canonical
comparison, but ARRAY order inside each property's value IS significant
and follows the spec's append order. -/
abbrev NmNode := OMap NmVal

/-- One graph's node map: node id → node. Its traversal order is the
spec's "ordered by id". -/
abbrev NmGraph := Std.TreeMap String NmNode

/-- Whole-algorithm state: graph name → graph (`"@default"` plus named
graphs), the blank-node relabelling map (old label → issued label), and
the issuer counter. -/
structure NmState where
  graphs : Std.TreeMap String NmGraph
  idmap  : Std.TreeMap String String
  ctr    : Nat

/-! ## Association-list helpers

These stay for the places that hold SMALL association lists: the members
of one input JSON object or frame object. `NodeMapTheorems.lean` proves the
node-map operations against them. -/

def flLookup {α : Type} (xs : List (String × α)) (k : String) : Option α :=
  (xs.find? (fun kv => kv.1 == k)).map Prod.snd

/-- Replace `k`'s value in place (preserving position) or append at the
end. -/
def flUpd {α : Type} : List (String × α) → String → α → List (String × α)
  | [],               k, v => [(k, v)]
  | (k2, v2) :: rest, k, v => if k2 == k then (k2, v) :: rest else (k2, v2) :: flUpd rest k v

def flRemove {α : Type} : List (String × α) → String → List (String × α)
  | [],               _ => []
  | (k2, v2) :: rest, k => if k2 == k then rest else (k2, v2) :: flRemove rest k

/-- Insertion sort by key, code-point order — the spec's "ordered
lexicographically". Equal keys come out in REVERSE of their input order
(a later equal key is inserted after the earlier ones already placed
ahead of it). -/
def flInsertByKey {α : Type} (kv : String × α) : List (String × α) → List (String × α)
  | []      => [kv]
  | y :: rest => if strLt kv.1 y.1 then kv :: y :: rest else y :: flInsertByKey kv rest

def flSortByKey {α : Type} : List (String × α) → List (String × α)
  | []        => []
  | kv :: rest => flInsertByKey kv (flSortByKey rest)

/-- "the value is already in the array" — the spec's duplicate check
compares maps structurally; `expandedEqual` (JCS canonical form) is that
comparison: member order insignificant, array order significant, numbers
by canonical value. -/
def flArrContains (items : List Json) (v : Json) : Bool :=
  items.any (fun it => expandedEqual it v)

/-! ## Node-level operations -/

/-- The node's entry under `k`, as a JSON value. -/
def NmNode.getJson (n : NmNode) (k : String) : Option Json := (n.find? k).map NmVal.toJson

/-- The node's entries as JSON members, in first-creation order. -/
def NmNode.toFields (n : NmNode) : List (String × Json) :=
  n.toList.map (fun kv => (kv.1, kv.2.toJson))

/-- The node's entries as JSON members, in code-point order of the key. -/
def NmNode.toSortedFields (n : NmNode) : List (String × Json) :=
  n.toSortedList.map (fun kv => (kv.1, kv.2.toJson))

/-- The node `{"@id": id}` a node map creates on first sight of `id`. -/
def NmNode.fresh (id : String) : NmNode := OMap.upsert OMap.empty "@id" (.one (.string id))

/-- Append `v` to the node's property array (creating the entry),
skipping the append when `dedup` is set and an equal value is already
present. -/
def nodeAppendProp (n : NmNode) (prop : String) (v : Json) (dedup : Bool) : NmNode :=
  match n.find? prop with
  | some (.many a) =>
    let key := jcsDocument v
    if dedup && a.seen.contains key then n else n.upsert prop (.many (a.pushKeyed key v))
  | some (.one o) =>  -- non-array: defensive, never built here
    n.upsert prop (.many ((DedupArr.empty.push o).push v))
  | none => n.upsert prop (.many (DedupArr.empty.push v))

/-- §7.1 step 6.12.2: the property entry exists even if no value
survives recursion. -/
def nodeEnsureProp (n : NmNode) (prop : String) : NmNode :=
  if n.contains prop then n else n.upsert prop (.many DedupArr.empty)

/-- Merge `@type` items into the node's `@type` array, skipping
duplicates (step 6.7's "unless it already exists"). -/
def nodeMergeTypes (n : NmNode) (items : List Json) : NmNode :=
  let start : DedupArr :=
    match n.find? "@type" with
    | some (.many a) => a
    | some (.one o)  => DedupArr.empty.push o  -- non-array: defensive, never built here
    | none           => DedupArr.empty
  n.upsert "@type" (.many (items.foldl (fun a hd => a.pushDedup hd true) start))

/-- Step 6.8: a second, DIFFERENT `@index` for the same node id is the
spec's "conflicting indexes" error (fixture e001). -/
def nodeSetIndex (n : NmNode) (idx : Json) : Option NmNode :=
  match n.find? "@index" with
  | some old => if expandedEqual old.toJson idx then some n else none
  | none     => some (n.upsert "@index" (.one idx))

/-- A node that consists only of an `@id` entry. -/
def nodeHasOnlyId (n : NmNode) : Bool :=
  match n.rev with
  | [k] => k == "@id"
  | _   => false

/-! ## State-level operations -/

/-- The state before any node is seen: only the `"@default"` graph exists. -/
def NmState.initial : NmState :=
  { graphs := (Std.TreeMap.empty : Std.TreeMap String NmGraph).insert "@default" Std.TreeMap.empty,
    idmap := Std.TreeMap.empty, ctr := 0 }

/-- How many nodes the state holds, summed over every graph. -/
def NmState.nodeCount (st : NmState) : Nat :=
  st.graphs.foldl (fun a _ g => a + g.size) 0

def stGraph (st : NmState) (g : String) : NmGraph :=
  (st.graphs.get? g).getD Std.TreeMap.empty

def stPutGraph (st : NmState) (g : String) (gr : NmGraph) : NmState :=
  { st with graphs := st.graphs.insert g gr }

/-- Step 6.3: create `graph[id] = { "@id": id }` when absent (also
registers the graph itself on first touch). -/
def stEnsureNode (st : NmState) (g id : String) : NmState :=
  let gr := stGraph st g
  if gr.contains id then st
  else stPutGraph st g (gr.insert id (NmNode.fresh id))

/-- Apply `f` to `graph[id]`, creating the node first if needed. -/
def stNodeUpdate (st : NmState) (g id : String) (f : NmNode → NmNode) : NmState :=
  let gr := stGraph st g
  match gr.get? id with
  | some n => stPutGraph st g (gr.insert id (f n))
  | none   => stPutGraph st g (gr.insert id (f (NmNode.fresh id)))

/-- Add `v` to `subject-node[aprop]` when both an active subject (an
IRI/bnode string) and an active property are in scope. A free-floating
value with no subject is silently dropped — expansion has already
removed the ones the spec drops, so this is pure defence. -/
def stAddValue (st : NmState) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (v : Json) (dedup : Bool) : NmState :=
  match asubj, aprop with
  | some (.string sid), some p =>
    stNodeUpdate st agraph sid (fun n => nodeAppendProp n p v dedup)
  | _, _ => st

/-! ## Generate Blank Node Identifier — API §7.2 -/

/-- Relabel a specific existing blank node identifier: return its issued
label if seen before, else issue `_:b<counter>` and record the
mapping. -/
def issueKeyed (st : NmState) (old : String) : String × NmState :=
  match st.idmap.get? old with
  | some nid => (nid, st)
  | none =>
    let nid := "_:b" ++ toString st.ctr
    (nid, { st with idmap := st.idmap.insert old nid, ctr := st.ctr + 1 })

/-- Issue a fresh label — the spec's issuer called with a null
identifier (an anonymous node object with no `@id`). -/
def issueFresh (st : NmState) : String × NmState :=
  ("_:b" ++ toString st.ctr, { st with ctr := st.ctr + 1 })

/-- §7.1 step 3: relabel blank node identifiers among the element's
`@type` items. This runs BEFORE `@id` issuance — the fixtures pin the
resulting label order. -/
def flRelabelTypeItems (st : NmState) : List Json → NmState × List Json
  | []               => (st, [])
  | .string s :: tl  =>
    if isBnodeId s then
      let (nid, st1) := issueKeyed st s
      let (st2, tl') := flRelabelTypeItems st1 tl
      (st2, .string nid :: tl')
    else
      let (st1, tl') := flRelabelTypeItems st tl
      (st1, .string s :: tl')
  | hd :: tl =>
    let (st1, tl') := flRelabelTypeItems st tl
    (st1, hd :: tl')

/-- Shape-preserving: a node object's `@type` is an array in expanded
form, but a VALUE object's `@type` is a bare string — step 3 only
substitutes blank node identifiers, it never re-shapes (flatten/0002
pins the value-object scalar staying scalar). -/
def flRelabelTypes (st : NmState) (fields : List (String × Json))
    : NmState × List (String × Json) :=
  match flLookup fields "@type" with
  | some (.array items) =>
    let (st1, items') := flRelabelTypeItems st items
    (st1, flUpd fields "@type" (.array items'))
  | some (.string s) =>
    if isBnodeId s then
      let (nid, st1) := issueKeyed st s
      (st1, flUpd fields "@type" (.string nid))
    else (st, fields)
  | _ => (st, fields)

/-- JSON-LD-star: the reified triple of a value (a value object or a
triple term) of the active subject's active property, as a node object:
`{"@id": subject, property: [value]}`. -/
def flReification (asubj : Option Json) (aprop : Option String) (value : Json) : Option Json :=
  match asubj, aprop with
  | some (.string sid), some p => some (.object [("@id", .string sid), (p, .array [value])])
  | _, _ => none

/-! ## Node Map Generation — API §7.1

`nmg`'s parameters mirror the spec's: the node map (inside `NmState`),
the active graph (a graph name), the active subject (`none`, a
`.string id`, or — for the `@reverse` case — an object node reference),
the active property, and `acc`, the in-progress `@list` array (`none` is
the spec's "list is null"). `acc` holds the items NEWEST FIRST, so adding
an item is a `cons`; the list branch reverses it once when the list is
complete. -/

mutual

def nmg (st : NmState) (element : Json) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (acc : Option (List Json)) (fuel : Nat)
    : Res (NmState × Option (List Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match element with
    -- Step 1: arrays — process each item in order.
    | .array items => nmgItems st items agraph asubj aprop acc fuel
    | .object fields0 =>
      -- Step 3: relabel blank node identifiers among @type items.
      let (st, fields) := flRelabelTypes st fields0
      if hasField "@value" fields then
        -- Step 4: value object. JSON-LD-star: an `@annotation` entry is
        -- removed and each annotation becomes a reifier node of the
        -- triple (active subject, active property, value).
        let value := Json.object (flRemove fields "@annotation")
        match nmgAnnotated st fields agraph (flReification asubj aprop value) fuel with
        | .error e => .error e
        | .ok st =>
          match acc with
          | none    => .ok (stAddValue st agraph asubj aprop value true, none)
          | some xs => .ok (st, some (value :: xs))
      else if hasField "@triple" fields then
        -- JSON-LD-star triple term: it stays embedded (its blank node
        -- identifiers are the renamed ones of `flRenameBnodeIds`); only
        -- its annotations go to the node map, as for a value object.
        let value := Json.object (fields.filter (fun kv => kv.1 == "@triple"))
        match nmgAnnotated st fields agraph (flReification asubj aprop value) fuel with
        | .error e => .error e
        | .ok st =>
          match acc with
          | none    => .ok (stAddValue st agraph asubj aprop value true, none)
          | some xs => .ok (st, some (value :: xs))
      else if hasField "@list" fields then
        -- Step 5: list object — collect the nested items into a fresh
        -- accumulator, then attach {"@list": [...]} where the spec says.
        match flLookup fields "@list" with
        | none      => .error .notJsonLd  -- unreachable: hasField just held
        | some lval =>
          match nmg st lval agraph asubj aprop (some []) fuel with
          | .ok (st1, some litemsRev) =>
            let result := Json.object [("@list", .array litemsRev.reverse)]
            (match acc with
             | none    => .ok (stAddValue st1 agraph asubj aprop result false, none)
             | some xs => .ok (st1, some (result :: xs)))
          | .ok (_, none) => .error .notJsonLd
          | .error e      => .error e
      else
        -- Step 6: node object.
        nmgNode st fields agraph asubj aprop acc fuel
    -- Scalars never appear in expanded form (expansion wraps every value
    -- in a value object); drop defensively rather than error.
    | _ => .ok (st, acc)
termination_by fuel

def nmgItems (st : NmState) (items : List Json) (agraph : String) (asubj : Option Json)
    (aprop : Option String) (acc : Option (List Json)) (fuel : Nat)
    : Res (NmState × Option (List Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | []       => .ok (st, acc)
    | hd :: tl =>
      match nmg st hd agraph asubj aprop acc fuel with
      | .error e         => .error e
      | .ok (st1, acc1)  => nmgItems st1 tl agraph asubj aprop acc1 fuel
termination_by fuel

/-- Step 6's body. `fields` arrives with `@type` already relabelled. -/
def nmgNode (st : NmState) (fields : List (String × Json)) (agraph : String)
    (asubj : Option Json) (aprop : Option String) (acc : Option (List Json)) (fuel : Nat)
    : Res (NmState × Option (List Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    -- Steps 6.1-6.2: determine the id (relabelling blank node
    -- identifiers), removing @id from the element.
    let idRes : Option (NmState × String × List (String × Json)) :=
      match flLookup fields "@id" with
      | some (.string s) =>
        if isBnodeId s then
          let (nid, st1) := issueKeyed st s
          some (st1, nid, flRemove fields "@id")
        else some (st, s, flRemove fields "@id")
      | some _ => none  -- a non-string @id cannot survive expansion
      | none =>
        let (nid, st1) := issueFresh st
        some (st1, nid, fields)
    match idRes with
    | none => .error .invalidIdValue
    | some (st, id, fields) =>
      -- Steps 6.3-6.4: ensure graph[id] exists.
      let st := stEnsureNode st agraph id
      -- Steps 6.5-6.6: link this node from where we came from.
      let (st, acc) :=
        match asubj with
        | some (.object reffields) =>
          -- 6.5: reverse relationship — append the REFERENCING node's
          -- reference to THIS node's active-property array (dedup).
          (match aprop with
           | some p =>
             (stNodeUpdate st agraph id
                (fun n => nodeAppendProp n p (.object reffields) true), acc)
           | none => (st, acc))
        | _ =>
          match aprop with
          | none => (st, acc)
          | some p =>
            let reference := Json.object [("@id", .string id)]
            match acc with
            | some xs => (st, some (reference :: xs))
            | none    => (stAddValue st agraph asubj (some p) reference true, none)
      -- JSON-LD-star: the node's annotations reify the triple that links
      -- it to the active subject (for a reverse property, the triple from
      -- this node to the referencing node).
      let reification : Option Json :=
        match asubj, aprop with
        | some (.object reffields), some p =>
          some (.object [("@id", .string id), (p, .array [.object reffields])])
        | some (.string sid), some p =>
          some (.object [("@id", .string sid), (p, .array [.object [("@id", .string id)]])])
        | _, _ => none
      match nmgAnnotated st fields agraph reification fuel with
      | .error e => .error e
      | .ok st =>
      let fields := flRemove fields "@annotation"
      -- JSON-LD-star: the reified triples of a reifier stay embedded under
      -- `@reifies` (duplicates skipped).
      let st :=
        match flLookup fields "@reifies" with
        | some rv => stNodeUpdate st agraph id (fun n =>
            (asArray rv).foldl (fun n r => nodeAppendProp n "@reifies" r true) n)
        | none => st
      let fields := flRemove fields "@reifies"
      -- Step 6.7: merge @type into the node.
      let st :=
        match flLookup fields "@type" with
        | some (.array items) => stNodeUpdate st agraph id (fun n => nodeMergeTypes n items)
        | some (.string s)    => stNodeUpdate st agraph id (fun n => nodeMergeTypes n [.string s])
        | _                   => st
      let fields := flRemove fields "@type"
      -- Step 6.8: @index (the conflicting-indexes error surfaces here).
      let idxRes : Option (NmState × List (String × Json)) :=
        match flLookup fields "@index" with
        | some idx =>
          let gr := stGraph st agraph
          (match gr.get? id with
           | some n =>
             (match nodeSetIndex n idx with
              | none    => none
              | some n1 => some (stPutGraph st agraph (gr.insert id n1), flRemove fields "@index"))
           | none => some (st, flRemove fields "@index"))
        | none => some (st, fields)
      match idxRes with
      | none => .error .conflictingIndexes
      | some (st, fields) =>
        -- Step 6.9: @reverse — recurse into each reverse value with THIS
        -- node's reference as the active subject (map form triggers 6.5).
        let revRes : Res NmState :=
          match flLookup fields "@reverse" with
          | some (.object rentries) =>
            nmgReverseEntries st (sortMapEntries rentries) agraph id fuel
          | some _ => .error .invalidReversePropertyMap
          | none   => .ok st
        match revRes with
        | .error e => .error e
        | .ok st =>
          let fields := flRemove fields "@reverse"
          -- Step 6.10: @graph — recurse with id as the active graph.
          let graphRes : Res NmState :=
            match flLookup fields "@graph" with
            | some gval =>
              (match nmg st gval id none none none fuel with
               | .ok (st1, _) => .ok st1
               | .error e     => .error e)
            | none => .ok st
          match graphRes with
          | .error e => .error e
          | .ok st =>
            let fields := flRemove fields "@graph"
            -- Step 6.11: @included — recurse in the SAME active graph,
            -- with no active subject or property.
            let inclRes : Res NmState :=
              match flLookup fields "@included" with
              | some ival =>
                (match nmg st ival agraph none none none fuel with
                 | .ok (st1, _) => .ok st1
                 | .error e     => .error e)
              | none => .ok st
            match inclRes with
            | .error e => .error e
            | .ok st =>
              let fields := flRemove fields "@included"
              -- Step 6.12: the remaining properties, in code-point key order.
              match nmgProps st (sortMapEntries fields) agraph id fuel with
              | .error e => .error e
              | .ok st   => .ok (st, acc)
termination_by fuel

def nmgProps (st : NmState) (props : List (String × Json)) (agraph id : String) (fuel : Nat)
    : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match props with
    | []            => .ok st
    | (p, v) :: tl =>
      -- 6.12.1: a property that is itself a blank node identifier gets
      -- relabelled through the same issuer (generalized RDF).
      let (p', st) := if isBnodeId p then issueKeyed st p else (p, st)
      -- 6.12.2: the property entry exists even if no value survives.
      let st := stNodeUpdate st agraph id (fun n => nodeEnsureProp n p')
      -- 6.12.3: recurse with id as the active subject.
      match nmg st v agraph (some (.string id)) (some p') none fuel with
      | .error e     => .error e
      | .ok (st1, _) => nmgProps st1 tl agraph id fuel
termination_by fuel

def nmgReverseEntries (st : NmState) (entries : List (String × Json)) (agraph id : String)
    (fuel : Nat) : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | []              => .ok st
    | (p, vals) :: tl =>
      match nmgReverseValues st (asArray vals) p agraph id fuel with
      | .error e => .error e
      | .ok st1  => nmgReverseEntries st1 tl agraph id fuel
termination_by fuel

/-- JSON-LD-star: the annotations of an element (its `@annotation`
entry, if any). Each annotation is a node object that becomes the
reifier of `reification`: its `@id`, else a new blank node, with
`@reifies` set to `[reification]`; it then goes through node map
generation like any node object, in the same graph, with no active
subject. Two details follow the reference implementation (Ruby json-ld,
which produced the fixtures, `create_node_map`): a new identifier is
issued for EVERY annotation, also one with an `@id`
(`a.fetch('@id', namer.get_name)` evaluates its default), and that new
identifier is then relabelled like any blank node identifier of the
input, so an annotation takes two labels (fixtures st18 `_:b1`, st20
`_:b1` and `_:b3`). No reification (no active subject or property, which
expansion does not allow) means no reifier. -/
def nmgAnnotated (st : NmState) (fields : List (String × Json)) (agraph : String)
    (reification : Option Json) (fuel : Nat) : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match flLookup fields "@annotation", reification with
    | some anns, some r => nmgAnnotations st (asArray anns) agraph r fuel
    | _, _ => .ok st
termination_by fuel

def nmgAnnotations (st : NmState) (anns : List Json) (agraph : String) (reification : Json)
    (fuel : Nat) : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match anns with
    | [] => .ok st
    | .object afs :: tl =>
      let (fresh, st) := issueFresh st
      let reifier := match flLookup afs "@id" with
                     | some (.string s) => s
                     | _ => fresh
      let ann := Json.object (flUpd (flUpd afs "@id" (.string reifier)) "@reifies"
                                (.array [reification]))
      match nmg st ann agraph none none none fuel with
      | .error e     => .error e
      | .ok (st1, _) => nmgAnnotations st1 tl agraph reification fuel
    | _ :: tl => nmgAnnotations st tl agraph reification fuel
termination_by fuel

def nmgReverseValues (st : NmState) (vals : List Json) (p agraph id : String) (fuel : Nat)
    : Res NmState :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match vals with
    | []      => .ok st
    | v :: tl =>
      match nmg st v agraph (some (.object [("@id", .string id)])) (some p) none fuel with
      | .error e     => .error e
      | .ok (st1, _) => nmgReverseValues st1 tl p agraph id fuel
termination_by fuel

end

/-! ## JSON-LD-star: blank node identifiers of embedded triples

Node map generation does not walk into a triple term (`@triple`) or a
reified triple (`@reifies`): they stay embedded. Their blank node
identifiers must still name the same blank nodes as the rest of the
output. The reference implementation (Ruby json-ld, which produced the
fixtures) does this with a pass before node map generation: it renames
every `@id` blank node identifier of the expanded document, in document
order, through the same issuer (`rename_bnodes`), and node map
generation then relabels the identifiers it meets AGAIN. The fixtures pin
the resulting labels (st28: `_:rei` becomes `_:b0`, then `_:b2`; `_:value`
in `@reifies` keeps `_:b1`). `flRenameBnodeIds` is that first pass;
`flRelabelEmbedded` then maps each embedded identifier that node map
generation relabelled to its final label, so a blank node that occurs
both in an embedded triple and as a node keeps one identifier (the
reference implementation leaves the two apart; no fixture has the
case). Both passes run only when `rdfstar` is set. -/

mutual

/-- Rewrite each blank node `@id` string in `j` through `step`, threading
the state `s`. `inside` is false outside embedded triples: then only the
contents of `@triple` and `@reifies` entries are rewritten. The contents
of `@value` (a JSON literal) are never rewritten. -/
def flRwJson {σ : Type} (step : σ → String → String × σ) (inside : Bool) (s : σ)
    (j : Json) (fuel : Nat) : Res (Json × σ) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match j with
    | .array items =>
      match flRwItems step inside s items [] fuel with
      | .error e      => .error e
      | .ok (xs, s1)  => .ok (.array xs, s1)
    | .object fs =>
      match flRwMembers step inside s fs [] fuel with
      | .error e      => .error e
      | .ok (ms, s1)  => .ok (.object ms, s1)
    | _ => .ok (j, s)
termination_by fuel

def flRwItems {σ : Type} (step : σ → String → String × σ) (inside : Bool) (s : σ)
    (items acc : List Json) (fuel : Nat) : Res (List Json × σ) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok (acc.reverse, s)
    | hd :: tl =>
      match flRwJson step inside s hd fuel with
      | .error e      => .error e
      | .ok (hd', s1) => flRwItems step inside s1 tl (hd' :: acc) fuel
termination_by fuel

def flRwMembers {σ : Type} (step : σ → String → String × σ) (inside : Bool) (s : σ)
    (ms acc : List (String × Json)) (fuel : Nat) : Res (List (String × Json) × σ) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match ms with
    | [] => .ok (acc.reverse, s)
    | (k, v) :: tl =>
      if k == "@value" then flRwMembers step inside s tl ((k, v) :: acc) fuel
      else
        match k, v with
        | "@id", .string x =>
          if inside && isBnodeId x then
            let (x', s1) := step s x
            flRwMembers step inside s1 tl ((k, .string x') :: acc) fuel
          else flRwMembers step inside s tl ((k, v) :: acc) fuel
        | _, _ =>
          let inside' := inside || k == "@triple" || k == "@reifies"
          match flRwJson step inside' s v fuel with
          | .error e     => .error e
          | .ok (v', s1) => flRwMembers step inside s1 tl ((k, v') :: acc) fuel
termination_by fuel

end

/-- The fuel of a rewrite of `j`: each item and member costs one step of
the list loop and one of the value. -/
def flRwFuel (j : Json) : Nat := 2 * Json.size j + 8

/-- The first pass: rename every blank node `@id` of the expanded document
through the issuer, in document order. -/
def flRenameBnodeIds (st : NmState) (expanded : Json) : Res (Json × NmState) :=
  flRwJson (fun st x => issueKeyed st x) true st expanded (flRwFuel expanded)

/-- Map the blank node identifiers inside the embedded triples of every node
(the contents of `@reifies` and `@triple` entries) through the labels that
node map generation issued (`idmap`); an identifier node map generation did
not meet stays as it is. -/
def flRelabelEmbedded (st : NmState) : Res NmState :=
  if st.idmap.isEmpty then .ok st else
  let step : Unit → String → String × Unit := fun _ x => ((st.idmap.get? x).getD x, ())
  let relabelVal : String → NmVal → Res NmVal := fun k v => match v with
    | .one j  => .ok (.one j)
    | .many a =>
      let arr := Json.array a.toList
      match flRwJson step (k == "@reifies") () arr (flRwFuel arr) with
      | .ok (.array xs, _) => .ok (.many (DedupArr.ofList xs))
      | .ok _              => .ok (.many a)
      | .error e           => .error e
  let relabelNode : NmNode → Res NmNode := fun n => n.toList.foldlM (init := n)
    (fun m kv => match relabelVal kv.1 kv.2 with
      | .ok v    => .ok (m.upsert kv.1 v)
      | .error e => .error e)
  let relabelGraph : NmGraph → Res NmGraph := fun gr => gr.foldlM (init := gr)
    (fun g id n => match relabelNode n with
      | .ok n'   => .ok (g.insert id n')
      | .error e => .error e)
  let gsRes : Res (Std.TreeMap String NmGraph) := st.graphs.foldlM (init := st.graphs)
    (fun gs name gr => match relabelGraph gr with
      | .ok gr'  => .ok (gs.insert name gr')
      | .error e => .error e)
  match gsRes with
  | .ok gs    => .ok { st with graphs := gs }
  | .error e  => .error e

/-- API §7.1 Node Map Generation for a whole EXPANDED document: the
entry point the flattening and framing algorithms share. The fuel is
derived from the document size, as in `flattenExpanded`. With `rdfstar`
the blank node identifiers of embedded triples are renamed first and
relabelled after (see above). -/
def generateNodeMap (expanded : Json) (rdfstar : Bool := false) : Res NmState :=
  let fuel := 16 * Json.size expanded + 128
  if rdfstar then
    match flRenameBnodeIds NmState.initial expanded with
    | .error e => .error e
    | .ok (renamed, st0) =>
      -- node map generation keeps the issuer's counter but starts a new
      -- relabelling map: it relabels the renamed identifiers
      match nmg { st0 with idmap := Std.TreeMap.empty } renamed "@default" none none none fuel with
      | .error e => .error e
      | .ok (st, _) => flRelabelEmbedded st
  else
    match nmg NmState.initial expanded "@default" none none none fuel with
    | .error e => .error e
    | .ok (st, _) => .ok st

/-! ## JSON-LD-star: Create Annotations

The design record's "Create Annotations" outline (Gregg Kellogg), as the
reference implementation runs it (`create_annotations`): for each node
with `@reifies` (in id order), and each reified triple
`{"@id": s, p: [v]}` of it whose subject node `s` is in the same graph
and has a value equal to `v` (ignoring `@annotation`) under `p`, add the
node (its `@id` and every entry but `@reifies`) to that value's
`@annotation` and drop the triple from `@reifies`; a node whose
`@reifies` becomes empty is removed. Unlike the fold of `FromRdf`
(`foldAllAnnotations`), this one does not require the reifier to be a
blank node or unreferenced: fixture st35n folds `_:b1`, which `ex:sue`
references. -/

/-- The subject, property and single value of a reified triple. -/
def flReifiedTriple : Json → Option (String × String × Json)
  | .object fs =>
    match flLookup fs "@id", fs.filter (fun kv => kv.1 != "@id") with
    | some (.string s), [(p, .array [v])] => if p.startsWith "@" then none else some (s, p, v)
    | _, _ => none
  | _ => none

/-- Add `ann` to every value of the reified triple `reif` in `gr`; `none`
when there is no such value. -/
def flAnnotateTriple (gr : NmGraph) (ann reif : Json) : Option NmGraph :=
  match flReifiedTriple reif with
  | none => none
  | some (s, p, v) =>
    match gr.get? s with
    | none => none
    | some target =>
      match target.find? p with
      | some (.many a) =>
        let items := a.toList
        if items.any (fun t => expandedEqual (FromRdf.stripAnnotation t) v) then
          let items' := items.map (fun t =>
            if expandedEqual (FromRdf.stripAnnotation t) v then FromRdf.addAnnotation ann t else t)
          some (gr.insert s (target.upsert p (.many (DedupArr.ofList items'))))
        else none
      | _ => none

/-- Fold the reifier node `rid` into annotations where its triples are
found. -/
def flFoldReifier (gr : NmGraph) (rid : String) : NmGraph :=
  match gr.get? rid with
  | none => gr
  | some node =>
    let reifs := ((node.find? "@reifies").map NmVal.items).getD []
    let ann := Json.object (("@id", .string rid) ::
      node.toFields.filter (fun kv => kv.1 != "@id" && kv.1 != "@reifies"))
    let (gr, kept) := reifs.foldl (fun (acc : NmGraph × List Json) reif =>
      match flAnnotateTriple acc.1 ann reif with
      | some g => (g, acc.2)
      | none   => (acc.1, reif :: acc.2)) (gr, [])
    if kept.isEmpty then gr.erase rid
    else if kept.length == reifs.length then gr
    else
      match gr.get? rid with
      | some n => gr.insert rid (n.upsert "@reifies" (.many (DedupArr.ofList kept.reverse)))
      | none   => gr

/-- Create Annotations over one graph of the node map. -/
def flCreateAnnotations (gr : NmGraph) : NmGraph :=
  let rids := gr.foldr (fun id n acc => if n.contains "@reifies" then id :: acc else acc) []
  rids.foldl flFoldReifier gr

/-! ## The Flattening Algorithm — API §6.1 -/

/-- Emit a graph's nodes in id order, dropping any that consist only of
`@id` (the spec's "unless node consists only of `@id`"). -/
def flEmitNodes (gr : NmGraph) : List Json :=
  gr.foldr (fun _ n acc => if nodeHasOnlyId n then acc else .object n.toFields :: acc) []

/-- Step 3: fold each named graph (ordered by name) under a `@graph`
entry of its name-node in the default graph. -/
def flFoldNamed : NmGraph → List (String × NmGraph) → NmGraph
  | dflt, []                => dflt
  | dflt, (gname, gr) :: tl =>
    let gnodes := flEmitNodes gr
    let dflt1 := match dflt.get? gname with
                 | some n => dflt.insert gname (n.upsert "@graph" (.one (.array gnodes)))
                 | none   => dflt.insert gname
                               ((NmNode.fresh gname).upsert "@graph" (.one (.array gnodes)))
    flFoldNamed dflt1 tl

/-- Flatten an EXPANDED document (normally an array of node objects) to
the ordered node array the flatten suite's context-free fixtures
expect. -/
def flattenExpanded (expanded : Json) (rdfstar createAnnotations : Bool := false) :
    Res (List Json) :=
  match generateNodeMap expanded rdfstar with
  | .error e => .error e
  | .ok st =>
    let st := if createAnnotations then
                { st with graphs := st.graphs.map (fun _ gr => flCreateAnnotations gr) }
              else st
    let dflt := stGraph st "@default"
    let named := (st.graphs.erase "@default").toList
    let dflt1 := flFoldNamed dflt named
    .ok (flEmitNodes dflt1)

/-! ## `JsonLdProcessor.flatten()` -/

/-- Flatten a JSON-LD document.

  * `input`         — the document text (expanded by §5.1 first);
  * `ctxDoc`        — the OPTIONAL compaction context DOCUMENT text (the
    manifest's `context` file; most flatten tests have none and expect
    the bare flattened array);
  * `base`          — the input document's base IRI;
  * `ctxUrl`        — the context document's own URL;
  * `compactArrays` — the API option, consulted only when `ctxDoc` is
    supplied;
  * `processingMode` — `"json-ld-1.0"` selects 1.0 mode. -/
def flattenDocument (loader : Loader) (input : String) (ctxDoc : Option String)
    (base ctxUrl : Option String) (compactArrays : Bool) (processingMode : Option String)
    (rdfstar : Bool := false) (createAnnotations : Bool := false) : Res Json :=
  match expandDocument loader input base none processingMode (rdfstar := rdfstar) with
  | .error e => .error e
  | .ok expanded =>
    match flattenExpanded expanded rdfstar (rdfstar && createAnnotations) with
    | .error e => .error e
    | .ok flattened =>
      match ctxDoc with
      | none => .ok (.array flattened)
      | some ctxText =>
        -- §6.1 step 6: compact the flattened array, ENSURING the result
        -- keeps @graph (or its alias) at the top level, then re-attach
        -- the original context — the same tail as `compactDocument`,
        -- minus its singleton unwrapping (flatten's output shape is
        -- pinned to @graph).
        match parseJson ctxText with
        | .error _ => .error .invalidLocalContext
        | .ok ctxRoot =>
          let ctxVal := match ctxRoot with
                        | .object cf => (match cmpField cf "@context" with
                                         | some c => c | none => ctxRoot)
                        | _ => ctxRoot
          let mode10 := processingMode == some "json-ld-1.0"
          let acSeed : ActiveContext :=
            { cur := { emptyContextCore with
                       base := base, mode10 := mode10,
                       docUrl := (match ctxUrl with | some u => some u | none => base),
                       originalBase := base },
              prev := [] }
          match contextProcess loader acSeed ctxVal false contextFuel remoteContextFuel [] with
          | .error e => .error e
          | .ok ac =>
            let co : CmpOpts := { arrays := compactArrays, rel := true }
            let farr := Json.array flattened
            let fuel := 16 * Json.size farr + 128
            match compactElem loader ac none farr co fuel with
            | .error e => .error e
            | .ok compacted0 =>
              let garr := match compacted0 with
                          | .array xs => Json.array xs
                          | other     => Json.array [other]
              let gkey := aliasKw ac co "@graph"
              if cmpCtxIsEmpty ctxVal then .ok (.object [(gkey, garr)])
              else .ok (.object [("@context", ctxVal), (gkey, garr)])

end L4Factoidal.JSONLD
