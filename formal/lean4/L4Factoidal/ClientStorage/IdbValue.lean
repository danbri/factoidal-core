/-
L4Factoidal.ClientStorage.IdbValue — a stored value and the key paths over it (Indexed
Database API 3.0 §2.3 "Values", §2.8 "Key path", §7.1 "evaluate a key path on a value",
§7.3 "inject a key into a value using a key path").

A value is stored as the record of its structured serialisation: tokens in pre-order, one
byte string each (`Val`). The page side writes them when it serialises a JavaScript value
(HTML StructuredSerializeForStorage) and reads them back into a new object; what the
tokens mean to JavaScript is that side's. This module reads only what a key path needs:

  `u` undefined, `z` null, `t` `f` booleans, `n`/`d` + 16 hex digits (number, date),
  `i` BigInt, `s` string, `r` RegExp, `b` + bytes (ArrayBuffer), `@` + index (a reference
  to an object written earlier), `k` + name (a property key);
  with children: `A` + n (dense array: n values), `a` + len,n (array: n key and value
  pairs), `o` + n (object: n pairs), `M` + n (Map: n pairs of values), `S` + n (Set),
  `V` + kind,offset,length (view: its buffer), `B` + type (boxed primitive: the primitive),
  `E` + name (Error: message, stack, cause), `X` (DOMException: message, name),
  `L` + type (Blob: its bytes), `F` + type (File: name, lastModified, bytes).

Because key paths are evaluated on the stored record, they are evaluated on the clone, as
§7.1 requires, and no getter of the page's object runs.

Every loop is bounded by the token count.
-/
import L4Factoidal.ClientStorage.IdbKey

namespace L4Factoidal.ClientStorage.Idb

/-- A stored value: the tokens of its serialisation. -/
abbrev Val := Array Tok

/-- The bytes a value holds (the sum of its tokens). -/
def Val.size (v : Val) : Nat := v.foldl (fun n t => n + t.size) 0

/-- The first number of a token's body (`A3`, `o2`, `M4`). -/
def countOf (t : Tok) : Nat := (((bodyStr t).splitOn ",").headD "").toNat?.getD 0
/-- The second number of a token's body (`a10,3`). -/
def count2Of (t : Tok) : Nat := ((((bodyStr t).splitOn ",").drop 1).headD "").toNat?.getD 0

/-- The subtrees (values and property keys) that follow a token as its children. -/
def kids (t : Tok) : Nat :=
  match tagOf t with
  | 'A' | 'S' => countOf t
  | 'o' | 'M' => 2 * countOf t
  | 'a' => 2 * count2Of t
  | 'V' | 'B' | 'L' => 1
  | 'X' => 2
  | 'E' | 'F' => 3
  | _ => 0

/-- The index after the subtree that starts at `i`. -/
def skip (ts : Val) (i : Nat) : Nat :=
  ((List.range ts.size).foldl (fun (st : Nat × Nat) _ =>
    if st.1 == 0 then st else
    match ts[st.2]? with
    | some t => (st.1 - 1 + kids t, st.2 + 1)
    | none => (0, st.2)) (1, i)).2

/-- The subtree at `i` as a value of its own. -/
def subtree (ts : Val) (i : Nat) : Val := ts.extract i (skip ts i)

/-- The index of the `n`th child subtree of the token at `i`. -/
def childAt (ts : Val) (i n : Nat) : Nat := (List.range n).foldl (fun j _ => skip ts j) (i + 1)

/-- The bits of the double that is the natural number `n` (exact below 2^53). For a
positive double the bits are also its order image (`numImage`). -/
def natBits (n : Nat) : Nat :=
  if n == 0 then 0 else
  let e := Nat.log2 n
  let mant := if e ≤ 52 then (n - 2 ^ e) <<< (52 - e) else (n - 2 ^ e) >>> (e - 52)
  ((1023 + e) <<< 52) + mant

/-- The token of the number `n`. -/
def numTok (tag : Char) (n : Nat) : Tok :=
  let bits := natBits n
  (String.singleton tag).toUTF8 ++ hex8 (bits >>> 32) ++ hex8 (bits % 4294967296)

/-- The integer part of the positive double whose order image is `v` (0 for a negative
one), at most 2^53: what a key generator reads from an explicit key (§2.11). -/
def floorOfImage (v : Int) : Nat :=
  if v ≤ 0 then 0 else
  let bits := v.toNat
  let e := bits >>> 52
  let mant := bits % (1 <<< 52) + (1 <<< 52)
  if e < 1023 then 0
  else if e ≥ 1023 + 53 then 1 <<< 53
  else if e ≥ 1023 + 52 then mant <<< (e - 1023 - 52) else mant >>> (1023 + 52 - e)

/-- The value of the own property `id` of the object or array at `i` (pairs of a `k` token
and a value), among `n` pairs from `j`. -/
def propAt (ts : Val) (j n : Nat) (id : String) : Option Nat :=
  ((List.range n).foldl (fun (st : Option Nat × Nat) _ =>
    match st.1 with
    | some _ => st
    | none =>
      match ts[st.2]? with
      | some k => if bodyStr k == id then (some (st.2 + 1), st.2) else (none, skip ts (st.2 + 1))
      | none => st) (none, j)).1

/-- One identifier of a key path on the value `ts` (§7.1 step 4): the value it names. -/
def evalIdent (ts : Val) (id : String) : Option Val :=
  match ts[0]? with
  | none => none
  | some t =>
    match tagOf t with
    | 's' => if id == "length" then some #[numTok 'n' (unitsOf (bodyStr t)).length] else none
    | 'A' =>
      if id == "length" then some #[numTok 'n' (countOf t)] else
      match id.toNat? with
      | some n => if n < countOf t && toString n == id then some (subtree ts (childAt ts 0 n)) else none
      | none => none
    | 'a' =>
      if id == "length" then some #[numTok 'n' (countOf t)] else
      (propAt ts 1 (count2Of t) id).map (subtree ts)
    | 'o' => (propAt ts 1 (countOf t) id).map (subtree ts)
    | 'L' =>
      if id == "size" then some #[numTok 'n' ((ts[1]?.map (·.size - 1)).getD 0)]
      else if id == "type" then some #[tok 's' (bodyStr t)] else none
    | 'F' =>
      if id == "name" then some (subtree ts 1)
      else if id == "lastModified" then some (subtree ts 2)
      else if id == "lastModifiedDate" then (ts[2]?).map fun m => #["d".toUTF8 ++ bodyOf m]
      else if id == "size" then some #[numTok 'n' ((ts[3]?.map (·.size - 1)).getD 0)]
      else if id == "type" then some #[tok 's' (bodyStr t)] else none
    | _ => none

/-- The identifiers of a key path string (`""` names the value itself). -/
def identsOf (path : String) : List String := if path == "" then [] else path.splitOn "."

/-- "Evaluate a key path on a value" (§7.1) for one key path string. -/
def evalPath (ts : Val) (path : String) : Option Val :=
  (identsOf path).foldl (fun acc id => acc.bind fun v => evalIdent v id) (some ts)

/-- A key path: none (out-of-line keys), one string, or a sequence of strings. -/
inductive KeyPath where
  | none
  | one (path : String)
  | many (paths : List String)
  deriving DecidableEq, Repr, Inhabited

/-- "Extract a key from a value using a key path" (§7.2): `none` when a path does not
resolve (failure), `some none` when it resolves to something that is not a key (invalid). -/
def extractKey (ts : Val) : KeyPath → Option (Option Key)
  | .none => none
  | .one p => (evalPath ts p).map Key.ofToks
  | .many ps =>
    ps.foldr (fun p acc =>
      match acc, evalPath ts p with
      | some (some items), some v => some ((Key.ofToks v).map fun k => Key.cons k items)
      | some none, some _ => some none
      | _, _ => none) (some (some Key.nil))

def identStart (c : Char) : Bool := c.isAlpha || c == '$' || c == '_' || c.toNat > 127
def identPart (c : Char) : Bool := identStart c || c.isDigit

/-- A valid key path string (§2.8): empty, or identifiers joined by dots. The identifier
test is ASCII-exact; any character above U+007F is taken as an identifier character
(wider than ECMAScript's IdentifierName). -/
def validPath (p : String) : Bool :=
  p == "" || (p.splitOn ".").all fun id =>
    match id.toList with
    | [] => false
    | c :: cs => identStart c && cs.all identPart

/-- A valid key path (§2.8): a valid string, or a non-empty sequence of valid strings. -/
def KeyPath.valid : KeyPath → Bool
  | .none => true
  | .one p => validPath p
  | .many ps => !ps.isEmpty && ps.all validPath

/-- The token at `i` with its count raised by one (`o2` to `o3`). -/
def bump (ts : Val) (i : Nat) : Val :=
  match ts[i]? with
  | some t => ts.set! i (tok (tagOf t) (toString (countOf t + 1)))
  | none => ts

def insertAt (ts : Val) (p : Nat) (ins : Val) : Val := ts.extract 0 p ++ ins ++ ts.extract p ts.size

/-- "Inject a key into a value using a key path" (§7.3), with "check that a key could be
injected" (its failure is `none`): walk the identifiers from the object at `i`; an
identifier that is absent is made (a new object for each but the last, the key for the
last); one that is present and not an object is a failure. -/
def inject (ts : Val) (key : Val) : Nat → List String → Option Val
  | _, [] => none
  | i, id :: rest =>
    match ts[i]? with
    | none => none
    | some t =>
      if tagOf t != 'o' then none else
      match propAt ts (i + 1) (countOf t) id, rest with
      | some j, _ :: _ => inject ts key j rest
      | some _, [] => none
      | none, _ =>
        -- absent: the new property and, for the identifiers that remain, nested new objects
        let chain := rest.foldl (fun acc id' => acc ++ #[tok 'o' "1", tok 'k' id']) #[tok 'k' id]
        some (bump (insertAt ts (skip ts i) (chain ++ key)) i)

/-! ## Checks (WPT IndexedDB/keypath.any.js, keypath-special-identifiers.any.js, keygenerator-inject.any.js) -/

private def T (xs : List String) : Val := (xs.map String.toUTF8).toArray
private def one : String := "n3ff0000000000000"
private def two : String := "n4000000000000000"
-- { a: 1, b: { c: "x", d: [1, 2] } }
private def v1 : Val := T ["o2", "ka", one, "kb", "o2", "kc", "sx", "kd", "A2", one, two]
#guard skip v1 0 == 11 && skip v1 4 == 11 && skip v1 8 == 11 && skip v1 2 == 3
#guard evalPath v1 "a" == some (T [one])
#guard evalPath v1 "b.c" == some (T ["sx"])
#guard evalPath v1 "b.d" == some (T ["A2", one, two])
#guard evalPath v1 "b.d.length" == some (T [two])
#guard evalPath v1 "b.c.length" == some (T [one])
#guard evalPath v1 "" == some v1
#guard evalPath v1 "x" == none && evalPath v1 "a.b" == none
#guard extractKey v1 (.one "b.d") == some (some (Key.ofList [.number 4607182418800017408, .number 4611686018427387904]))
#guard extractKey v1 (.one "b") == some none
#guard extractKey v1 (.one "q") == none
#guard extractKey v1 (.many ["a", "b.c"]) == some (some (Key.ofList [.number 4607182418800017408, .string [120]]))
#guard extractKey v1 (.many ["a", "b"]) == some none
#guard extractKey v1 (.many ["a", "zz"]) == none
#guard numTok 'n' 1 == one.toUTF8 && numTok 'n' 2 == two.toUTF8 && numTok 'n' 3 == "n4008000000000000".toUTF8
#guard numTok 'n' 1000 == "n408f400000000000".toUTF8
#guard floorOfImage (Int.ofNat (natBits 1000)) == 1000 && floorOfImage (Int.ofNat (natBits 1)) == 1
#guard floorOfImage 0x4008cccccccccccd == 3 && floorOfImage 0x3fe0000000000000 == 0 && floorOfImage (-5) == 0
-- a Blob's size and type, a File's name
#guard evalPath (T ["Ltext/plain", "bhello"]) "size" == some #[numTok 'n' 5]
#guard evalPath (T ["Ltext/plain", "bhello"]) "type" == some (T ["stext/plain"])
#guard evalPath (T ["F", "sa.txt", one, "b"]) "name" == some (T ["sa.txt"])
#guard validPath "" && validPath "a.b_c.$d" && !validPath "a..b" && !validPath "1a" && !validPath "a b" && !validPath "." && !validPath "a,b"
#guard (KeyPath.many []).valid == false && (KeyPath.many ["a", ""]).valid
-- inject
#guard inject (T ["o1", "kx", one]) (T [two]) 0 ["id"] == some (T ["o2", "kx", one, "kid", two])
#guard inject (T ["o1", "kx", "o0"]) (T [two]) 0 ["x", "id"] == some (T ["o1", "kx", "o1", "kid", two])
#guard inject (T ["o0"]) (T [two]) 0 ["a", "b", "c"] == some (T ["o1", "ka", "o1", "kb", "o1", "kc", two])
#guard inject (T ["o1", "kx", one]) (T [two]) 0 ["x", "id"] == none
#guard inject (T ["sx"]) (T [two]) 0 ["id"] == none
#guard evalPath ((inject (T ["o1", "kx", "o0"]) (T [two]) 0 ["x", "id"]).getD #[]) "x.id" == some (T [two])

end L4Factoidal.ClientStorage.Idb
