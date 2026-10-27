/-
L4Factoidal.WebDAV.If — the `If` header field (RFC 4918 §10.4).
https://github.com/danbri/factoidal/issues/1066

    If = ( 1*No-tag-list | 1*Tagged-list )
    No-tag-list = List
    Tagged-list = Resource-Tag 1*List
    List = "(" 1*Condition ")"
    Condition = ["Not"] (State-token | "[" entity-tag "]")
    State-token = Coded-URL
    Resource-Tag = "<" Simple-ref ">"

§10.4.2: "the If header is evaluated as true if any of its lists evaluates
true; a list is true when all of its conditions are" (paraphrased; the
evaluation is `Server.ifHolds`). This module reads the field; it is one
loop over the characters (`tokens`, then `lists`, both tail calls), so a
field of any length is read in fixed stack.
-/
import L4Factoidal.WebDAV.Config

namespace L4Factoidal.WebDAV

/-- One condition: a state token (`<urn:...>`) or an entity tag
(`["..."]`), maybe negated. -/
structure Cond where
  negated : Bool := false
  token : Option String := none
  etag : Option String := none
deriving DecidableEq, Repr, Inhabited

/-- One list, with the resource tag it applies to (`none`: the request
target). -/
structure IfList where
  tag : Option String := none
  conds : List Cond
deriving DecidableEq, Repr, Inhabited

/-- The lexical pieces of the field. -/
inductive Tok where
  | angle (s : String)
  | square (s : String)
  | lparen
  | rparen
  | notKw
deriving DecidableEq, Repr

/-- Read up to (not including) `close`, then continue after it. -/
def readUntil (close : Char) : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | c :: rest, acc => if c == close then some (String.ofList acc.reverse, rest) else readUntil close rest (c :: acc)

/-- The lexical pieces, in one loop. `none`: not a field of this grammar. -/
def tokens (fuel : Nat) : List Char → List Tok → Option (List Tok)
  | [], acc => some acc.reverse
  | c :: rest, acc =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if c == ' ' || c == '\t' then tokens fuel rest acc
      else if c == '(' then tokens fuel rest (.lparen :: acc)
      else if c == ')' then tokens fuel rest (.rparen :: acc)
      else if c == '<' then
        match readUntil '>' rest [] with
        | some (s, rest') => tokens fuel rest' (.angle s :: acc)
        | none => none
      else if c == '[' then
        match readUntil ']' rest [] with
        | some (s, rest') => tokens fuel rest' (.square s :: acc)
        | none => none
      else if (c == 'N' || c == 'n') then
        match rest with
        | o :: t :: rest' =>
          if (o == 'o' || o == 'O') && (t == 't' || t == 'T') then tokens fuel rest' (.notKw :: acc)
          else none
        | _ => none
      else none

/-- The reader's state: the resource tag in force, the list being read, the
lists read. -/
structure LState where
  tag : Option String := none
  open_ : Option (List Cond) := none
  neg : Bool := false
  done : List IfList := []

/-- The lists, in one loop over the pieces. -/
def lists : List Tok → LState → Option (List IfList)
  | [], st => if st.open_.isSome || st.neg then none else some st.done.reverse
  | t :: rest, st =>
    match st.open_, t with
    | none, .angle s => lists rest { st with tag := some s }
    | none, .lparen => lists rest { st with open_ := some [] }
    | some cs, .notKw => if st.neg then none else lists rest { st with open_ := some cs, neg := true }
    | some cs, .angle s => lists rest { st with open_ := some (cs ++ [{ negated := st.neg, token := some s }]), neg := false }
    | some cs, .square s => lists rest { st with open_ := some (cs ++ [{ negated := st.neg, etag := some s }]), neg := false }
    | some cs, .rparen =>
      if cs.isEmpty || st.neg then none
      else lists rest { st with open_ := none, done := { tag := st.tag, conds := cs } :: st.done }
    | _, _ => none

/-- Read an `If` field. `none`: malformed (400). -/
def parseIf (v : String) : Option (List IfList) := do
  let cs := v.toList
  let ts ← tokens cs.length cs []
  let ls ← lists ts {}
  if ls.isEmpty then none else
  -- No-tag-lists and tagged lists do not mix (the grammar's alternation).
  if ls.any (·.tag.isSome) && ls.any (·.tag.isNone) then none else some ls

/-- The state tokens the field names outside a `Not`: the lock tokens the
request SUBMITS (RFC 4918 §10.4.1). -/
def submittedTokens (ls : List IfList) : List String :=
  ls.foldl (fun acc l => acc ++ l.conds.filterMap (fun c => if c.negated then none else c.token)) []

#guard parseIf "(<urn:uuid:a>)" == some [{ conds := [{ token := some "urn:uuid:a" }] }]
#guard parseIf "(<urn:uuid:a> [\"e1\"]) (Not <DAV:no-lock> [\"e1\"])" ==
  some [ { conds := [{ token := some "urn:uuid:a" }, { etag := some "\"e1\"" }] }
       , { conds := [{ negated := true, token := some "DAV:no-lock" }, { etag := some "\"e1\"" }] } ]
#guard parseIf "<http://h/m/a> (<urn:x>)" == some [{ tag := some "http://h/m/a", conds := [{ token := some "urn:x" }] }]
#guard parseIf "(<urn:x>" == none
#guard parseIf "()" == none
#guard parseIf "(Not)" == none
#guard parseIf "<http://h/a> (<x>) (<y>)" ==
  some [{ tag := some "http://h/a", conds := [{ token := some "x" }] },
        { tag := some "http://h/a", conds := [{ token := some "y" }] }]
#guard parseIf "(<a>) <http://h/b> (<c>)" == none
#guard submittedTokens ((parseIf "(<a>) (Not <b>)").getD []) == ["a"]

end L4Factoidal.WebDAV
