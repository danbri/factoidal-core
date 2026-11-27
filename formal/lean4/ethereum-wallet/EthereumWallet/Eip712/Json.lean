import EthereumWallet.Abi.Hash

/-!
# A bounded JSON reader for typed data

Typed data arrives from web pages, so the reader has fixed limits and a named
refusal at each:

* input over `maxJsonBytes` bytes: `jsonTooLong`, before any scan;
* nesting over `maxJsonDepth`: `jsonTooDeep`;
* an object with more than `maxMembers` members: `tooManyMembers`;
* a repeated key in one object: `duplicateKey` (readers disagree on which
  value wins, so a page could show one and have another signed).

It does not use `Lean.Data.Json`, so executables that link it need no part of
the Lean frontend. Numbers are kept as their source text; only whole numbers
are accepted later. The reader's functions recurse only on nesting; the
loops over elements, members and string characters are tail calls.
-/

namespace EthereumWallet.Eip712

open EthereumWallet.Abi

inductive Json where
  | null
  | bool (b : Bool)
  | num (raw : List Char)
  | str (s : String)
  | arr (items : List Json)
  | obj (members : List (String × Json))

instance : Inhabited Json := ⟨.null⟩

def maxJsonBytes : Nat := 1048576
def maxJsonDepth : Nat := 64
def maxMembers : Nat := 256

inductive Err712 where
  | jsonTooLong
  | jsonTooDeep
  | jsonSyntax
  | duplicateKey
  | tooManyMembers
  /-- The document is not shaped as typed data (`types`, `primaryType`, `domain`, `message`). -/
  | badShape
  /-- A type name that is neither elementary nor declared, or a bad declaration. -/
  | badType (name : String)
  /-- Too many declared types or fields. -/
  | tooManyTypes
  /-- A value that does not fit its declared type. -/
  | badValue (field : String)
  | missingField (field : String)
  /-- A member of the data that no declared field covers. -/
  | extraField
  /-- Data nested beyond `maxDataDepth`. -/
  | dataTooDeep
  deriving Repr, DecidableEq, Inhabited

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\r' || c == '\t'

def skipWs (cs : List Char) : List Char := cs.dropWhile isWs

def hex4 (a b c d : Char) : Option Nat :=
  match hexVal a, hexVal b, hexVal c, hexVal d with
  | some w, some x, some y, some z => some (((w * 16 + x) * 16 + y) * 16 + z)
  | _, _, _, _ => none

/-- The body of a string, after the opening quote. -/
def parseStr : Nat → List Char → List Char → Except Err712 (String × List Char)
  | 0, _, _ => .error .jsonSyntax
  | fuel + 1, cs, acc =>
    match cs with
    | [] => .error .jsonSyntax
    | '"' :: rest => .ok (String.ofList acc.reverse, rest)
    | '\\' :: rest =>
      match rest with
      | '"' :: r => parseStr fuel r ('"' :: acc)
      | '\\' :: r => parseStr fuel r ('\\' :: acc)
      | '/' :: r => parseStr fuel r ('/' :: acc)
      | 'b' :: r => parseStr fuel r (Char.ofNat 8 :: acc)
      | 'f' :: r => parseStr fuel r (Char.ofNat 12 :: acc)
      | 'n' :: r => parseStr fuel r ('\n' :: acc)
      | 'r' :: r => parseStr fuel r ('\r' :: acc)
      | 't' :: r => parseStr fuel r ('\t' :: acc)
      | 'u' :: a :: b :: c :: d :: r =>
        match hex4 a b c d with
        | none => .error .jsonSyntax
        | some u =>
          if 0xD800 ≤ u ∧ u ≤ 0xDBFF then
            match r with
            | '\\' :: 'u' :: a2 :: b2 :: c2 :: d2 :: r2 =>
              match hex4 a2 b2 c2 d2 with
              | some lo =>
                if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
                  parseStr fuel r2
                    (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (lo - 0xDC00)) :: acc)
                else .error .jsonSyntax
              | none => .error .jsonSyntax
            | _ => .error .jsonSyntax
          else if 0xDC00 ≤ u ∧ u ≤ 0xDFFF then .error .jsonSyntax
          else parseStr fuel r (Char.ofNat u :: acc)
      | _ => .error .jsonSyntax
    | c :: rest => if c.toNat < 0x20 then .error .jsonSyntax else parseStr fuel rest (c :: acc)

/-- A number token, kept as text. The whole-number part follows the JSON grammar; a fraction
    or exponent is carried along and refused where a whole number is needed. -/
def parseNum (cs : List Char) : Except Err712 (List Char × List Char) :=
  let neg : List Char × List Char :=
    match cs with
    | '-' :: r => (['-'], r)
    | _ => ([], cs)
  let sp := neg.2.span Char.isDigit
  if sp.1.isEmpty then .error .jsonSyntax
  else if sp.1.length > 1 && sp.1.head? == some '0' then .error .jsonSyntax
  else
    let tl := sp.2.span fun c => c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-'
    .ok (neg.1 ++ sp.1 ++ tl.1, tl.2)

mutual
def parseValue : Nat → Nat → List Char → Except Err712 (Json × List Char)
  | 0, _, _ => .error .jsonSyntax
  | fuel + 1, depth, cs =>
    match skipWs cs with
    | 'n' :: 'u' :: 'l' :: 'l' :: r => .ok (.null, r)
    | 't' :: 'r' :: 'u' :: 'e' :: r => .ok (.bool true, r)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => .ok (.bool false, r)
    | '"' :: r =>
      match parseStr (fuel + 1) r [] with
      | .error e => .error e
      | .ok p => .ok (.str p.1, p.2)
    | '[' :: r =>
      if depth ≥ maxJsonDepth then .error .jsonTooDeep
      else
        match skipWs r with
        | ']' :: r' => .ok (.arr [], r')
        | r' =>
          match parseElems fuel (depth + 1) r' [] with
          | .error e => .error e
          | .ok p => .ok (.arr p.1, p.2)
    | '{' :: r =>
      if depth ≥ maxJsonDepth then .error .jsonTooDeep
      else
        match skipWs r with
        | '}' :: r' => .ok (.obj [], r')
        | r' =>
          match parseMembers fuel (depth + 1) r' [] 0 with
          | .error e => .error e
          | .ok p => .ok (.obj p.1, p.2)
    | cs' =>
      match parseNum cs' with
      | .error e => .error e
      | .ok p => .ok (.num p.1, p.2)
def parseElems : Nat → Nat → List Char → List Json → Except Err712 (List Json × List Char)
  | 0, _, _, _ => .error .jsonSyntax
  | fuel + 1, depth, cs, acc =>
    match parseValue fuel depth cs with
    | .error e => .error e
    | .ok p =>
      match skipWs p.2 with
      | ',' :: r => parseElems fuel depth r (p.1 :: acc)
      | ']' :: r => .ok ((p.1 :: acc).reverse, r)
      | _ => .error .jsonSyntax
def parseMembers : Nat → Nat → List Char → List (String × Json) → Nat →
    Except Err712 (List (String × Json) × List Char)
  | 0, _, _, _, _ => .error .jsonSyntax
  | fuel + 1, depth, cs, acc, count =>
    if count ≥ maxMembers then .error .tooManyMembers
    else
      match skipWs cs with
      | '"' :: r =>
        match parseStr (fuel + 1) r [] with
        | .error e => .error e
        | .ok k =>
          if acc.any (fun m => m.1 == k.1) then .error .duplicateKey
          else
            match skipWs k.2 with
            | ':' :: r2 =>
              match parseValue fuel depth r2 with
              | .error e => .error e
              | .ok p =>
                match skipWs p.2 with
                | ',' :: r3 => parseMembers fuel depth r3 ((k.1, p.1) :: acc) (count + 1)
                | '}' :: r3 => .ok (((k.1, p.1) :: acc).reverse, r3)
                | _ => .error .jsonSyntax
            | _ => .error .jsonSyntax
      | _ => .error .jsonSyntax
end

/-- Read one JSON document. -/
def parseJson (s : String) : Except Err712 Json :=
  if s.utf8ByteSize > maxJsonBytes then .error .jsonTooLong
  else
    let cs := s.toList
    match parseValue (2 * cs.length + 2) 0 cs with
    | .error e => .error e
    | .ok p => if (skipWs p.2).isEmpty then .ok p.1 else .error .jsonSyntax

/-- Kind: refusal at the bound. Says: a document over `maxJsonBytes` bytes is refused before
    it is scanned.
    Does not say: anything about smaller documents. -/
theorem parseJson_too_long (s : String) (h : maxJsonBytes < s.utf8ByteSize) :
    parseJson s = .error .jsonTooLong := by
  simp [parseJson, h]

/-- Kind: refusal at the bound. Says: an array opened at the depth limit is refused.
    Does not say: that every accepted document is within the limit (tested, not proved). -/
theorem parseValue_array_too_deep (fuel depth : Nat) (cs r : List Char)
    (h : skipWs cs = '[' :: r) (hd : maxJsonDepth ≤ depth) :
    parseValue (fuel + 1) depth cs = .error .jsonTooDeep := by
  simp [parseValue, h, hd]

/-- Kind: refusal at the bound. Says: an object opened at the depth limit is refused.
    Does not say: that every accepted document is within the limit (tested, not proved). -/
theorem parseValue_object_too_deep (fuel depth : Nat) (cs r : List Char)
    (h : skipWs cs = '{' :: r) (hd : maxJsonDepth ≤ depth) :
    parseValue (fuel + 1) depth cs = .error .jsonTooDeep := by
  simp [parseValue, h, hd]

def Json.get? (j : Json) (key : String) : Option Json :=
  match j with
  | .obj members => members.lookup key
  | _ => none

end EthereumWallet.Eip712
