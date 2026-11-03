/-
L4Factoidal.XPath4.SchemaType — `fn:schema-type`, `fn:atomic-type-annotation`
and `fn:node-type-annotation` (F&O 4.0 §20.1) for the types that every
processor has: the built-in types of XSD 1.1 Part 2 (their hierarchy is
`XSD.Builtin.base?`), `xs:untypedAtomic`, `xs:anyType`, `xs:untyped`,
`xs:anySimpleType`, and the union types `xs:numeric` and `xs:error`.

The result is an `fn:schema-type-record`. Its `base-type`,
`primitive-type` and `members` fields are functions that call
`fn:schema-type` again, so the records are built only on demand.

Hook for schema-aware processing (`L4Factoidal/XSD11/`): a type name
that is not a built-in type gives `none` from `builtinSchemaType?`; a
schema-aware host replaces `schemaTypeFn` with one that also looks up the
in-scope schema types. `fn:node-type-annotation` gives the record of a
node's type annotation (`NRec.tann`, set by schema validation): a built-in
type, or a type of the in-scope schema (`SchemaHook.typeInfo`); else
`xs:untyped` for elements and documents and `xs:untypedAtomic` for
attributes. Atomic values carry built-in types only, so
`fn:atomic-type-annotation` never names a user-defined type:
https://github.com/danbri/factoidal/issues/1101.
-/
import L4Factoidal.XPath4.Lib

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

def xsQ (l : String) : QN := { uri := nsXS, loc := l, pfx := "xs" }

/-- `fn:schema-type#1` with the argument fixed: a function of arity 0
    that gives the record of the named type. -/
def schemaTypeThunkQ (q : QN) : Item :=
  .fn (.papp (.fn (.builtin { uri := nsFN, loc := "schema-type" } 1)) [some [.atom (Atomic.ofQN q)]])

def schemaTypeThunk (l : String) : Item := schemaTypeThunkQ (xsQ l)

/-- A function of arity 0 that gives the empty sequence. -/
def emptyThunk : Item := .fn (.inline [] (.seq .item .star) (.seq []) false [])

/-- A function of arity 0 that gives the records of the named types. -/
def membersThunk (ls : List String) : Item :=
  .fn (.inline [] (.seq .item .star)
    (.seq (ls.map (fun l => .call { uri := nsFN, loc := "schema-type" } [some (.lit (Atomic.ofQN (xsQ l)))] [])))
    false [])

/-- `fn($v as xs:anyAtomicType) as xs:boolean { $v instance of T }`. -/
def matchesFn (t : IType) : Item :=
  let v : QN := { uri := "#schema-type", loc := "v" }
  .fn (.inline [(v, .atomic (.b .anyAtomicType))] (.atomic (.b .boolean)) (.instOf (.var v) t) false [])

def str (s : String) : Seq := [.atom (Atomic.ofStr s)]

def docOrElem : IType := .choice [.doc none, .elem none]

/-- `valid`: whether the string value of the node is castable to the
    atomic type (for a type without an atomic form: false). -/
def validFn (t : Option IType) : Item :=
  let n : QN := { uri := "#schema-type", loc := "n" }
  let body : Expr := match t with
    | some ty@(.atomic _) => .castable (.call { uri := nsFN, loc := "string" } [some (.var n)] []) ty false
    | _ => .lit (Atomic.ofBool false)
  .fn (.inline [(n, docOrElem)] (.atomic (.b .boolean)) body false [])

/-- `validate`: making typed nodes needs schema-aware processing, which
    this tree does not have (FOER0000 with the reason). -/
def validateFn : Item :=
  let n : QN := { uri := "#schema-type", loc := "n" }
  .fn (.inline [(n, docOrElem)] docOrElem
    (.call { uri := nsFN, loc := "error" } [some (.lit (Atomic.ofQN { uri := nsERR, loc := "FOER0000", pfx := "err" })),
      some (.lit (Atomic.ofStr "validation to typed nodes needs schema-aware processing"))] []) false [])

/-- The record of a type: the fields of `fn:schema-type-record` that the
    type has. -/
def typeRecord (name : String) (simple : Bool) (base : Option String) (prim : Option String)
    (variety : Option String) (members : Option (List String)) (t : Option IType) (ctor : Bool) : Seq :=
  let kv (k : String) (v : Seq) : Atomic × Seq := (Atomic.ofStr k, v)
  [.map ([kv "name" [.atom (Atomic.ofQN (xsQ name))], kv "is-simple" [.atom (Atomic.ofBool simple)],
          kv "base-type" [match base with | some b => schemaTypeThunk b | none => emptyThunk]] ++
         (match prim with | some p => [kv "primitive-type" [schemaTypeThunk p]] | none => []) ++
         (match variety with | some v => [kv "variety" (str v)] | none => []) ++
         (match members with | some ms => [kv "members" [membersThunk ms]] | none => []) ++
         (match t with | some ty => [kv "matches" [matchesFn ty]] | none => []) ++
         (if ctor then [kv "constructor" [.fn (.builtin (xsQ name) 1)]] else []) ++
         [kv "validate" [validateFn], kv "valid" [validFn t]])]

/-- The record of a built-in type, by local name in the XSD namespace;
    `none` when there is no such built-in type. -/
def builtinSchemaType? (l : String) : Option Seq :=
  match l with
  | "anyType" => some (typeRecord "anyType" false none none (some "mixed") none none false)
  | "untyped" => some (typeRecord "untyped" false (some "anyType") none (some "mixed") none none false)
  | "anySimpleType" => some (typeRecord "anySimpleType" true (some "anyType") none none none none false)
  | "anyAtomicType" => some (typeRecord "anyAtomicType" true (some "anySimpleType") none (some "atomic") none
      (some (.atomic (.b .anyAtomicType))) false)
  | "untypedAtomic" => some (typeRecord "untypedAtomic" true (some "anyAtomicType") (some "untypedAtomic")
      (some "atomic") none (some (.atomic .untyped)) true)
  | "numeric" => some (typeRecord "numeric" true (some "anySimpleType") none (some "union")
      (some ["double", "float", "decimal"])
      (some (.choice [.atomic (.b .double), .atomic (.b .float), .atomic (.b .decimal)])) true)
  | "error" => some (typeRecord "error" true (some "anySimpleType") none (some "union") (some [])
      (some (.choice [])) true)
  | _ =>
    match builtinOfName? l with
    | some b =>
      let base := (b.base?.map Builtin.localName).getD "anySimpleType"
      match builtinListItem? b with
      | some item =>
        some (typeRecord l true (some base) none (some "list") none none true |>.map (fun i => match i with
          | .map kvs => .map (kvs ++ [(Atomic.ofStr "members", [membersThunk [item.localName]])])
          | other => other))
      | none =>
        some (typeRecord l true (some base) (b.primitive.map Builtin.localName) (some "atomic") none
          (some (.atomic (.b b))) (b != .notation && b != .qname))
    | none => none

/-- The record of a type of the in-scope schema (`SchemaHook.typeInfo`).
No atomic value of this tree carries a user-defined type, so `matches`
gives false; `constructor` validates the lexical form against the type
(`fn:schema-type-cast#`). -/
def userTypeRecord (q : QN) (i : SchemaTypeInfo) : Seq :=
  let kv (k : String) (v : Seq) : Atomic × Seq := (Atomic.ofStr k, v)
  [.map ((match i.name with | some n => [kv "name" [.atom (Atomic.ofQN n)]] | none => []) ++
         [kv "is-simple" [.atom (Atomic.ofBool i.simple)], kv "base-type" [schemaTypeThunkQ i.base]] ++
         (match i.primitive with | some p => [kv "primitive-type" [schemaTypeThunkQ p]] | none => []) ++
         [kv "variety" (str i.variety)] ++
         (if i.simple then [kv "matches" [matchesFn (.choice [])]] else []) ++
         (if i.cast.isSome && i.variety == "atomic" then
            [kv "constructor" [.fn (.papp (.fn (.builtin { uri := nsFN, loc := "schema-type-cast#" } 2))
              [some [.atom (Atomic.ofQN q)], none])]]
          else []) ++
         [kv "validate" [validateFn], kv "valid" [validFn none]])]

/-- The record of a type name: a built-in type, or a type of the in-scope
schema. -/
def typeRecordOf (e : Env) (q : QN) : Seq :=
  if q.uri == nsXS then (builtinSchemaType? q.loc).getD []
  else match e.schema.typeInfo q with
    | some i => userTypeRecord q i
    | none => []

/-- `fn:schema-type($name as xs:QName) as schema-type-record?`. -/
def schemaTypeFn : LibFn := fun _ e a =>
  match optAtom (argN a 0) with
  | some ⟨_, .qn q⟩ => pure (typeRecordOf e q)
  | _ => pure []

/-- The `constructor` of a type of the in-scope schema: the typed value of
the string value, validated against the type (FORG0001 when not valid). -/
def schemaTypeCastFn : LibFn := fun _ e a => do
  match optAtom (argN a 0), optAtom (argN a 1) with
  | some ⟨_, .qn q⟩, some v =>
    match (e.schema.typeInfo q).bind (·.cast) with
    | some f => match f v.str with
      | some vs => pure (vs.map Item.atom)
      | none => err "FORG0001" ("the value " ++ v.str ++ " is not valid for the type " ++ q.eqn)
    | none => err "XPST0051" ("no such type " ++ q.eqn)
  | _, none => pure []
  | _, _ => err "XPTY0004" "schema-type-cast# expects a type name"

def schemaTypeTable : List (String × LibFn) := [
  ("schema-type", schemaTypeFn), ("schema-type-cast#", schemaTypeCastFn),
  ("atomic-type-annotation", fun _ _ a =>
    match optAtom (argN a 0) with
    | some x => pure ((builtinSchemaType? x.ty.name).getD [])
    | none => err "XPTY0004" "fn:atomic-type-annotation expects one atomic item"),
  ("node-type-annotation", fun _ e a =>
    match argN a 0 with
    | [.node n] =>
      let k := (e.nrec n).kind
      -- the type annotation of a validated node (`NRec.tann`, from the
      -- schema hook) when it names a built-in type
      let ann := match (e.nrec n).tann with
        | some q => match typeRecordOf e q with
          | [] => none
          | r => some r
        | none => none
      if let some r := ann then
        if k == .attribute || k == .element then pure r
        else err "XPTY0004" "fn:node-type-annotation expects an element, attribute or document node"
      else if k == .attribute then pure ((builtinSchemaType? "untypedAtomic").getD [])
      else if k == .element || k == .document then pure ((builtinSchemaType? "untyped").getD [])
      else err "XPTY0004" "fn:node-type-annotation expects an element, attribute or document node"
    | _ => err "XPTY0004" "fn:node-type-annotation expects a node")
]

#guard (builtinSchemaType? "boolean").isSome
#guard (builtinSchemaType? "nonsense").isNone

end L4Factoidal.XPath4
