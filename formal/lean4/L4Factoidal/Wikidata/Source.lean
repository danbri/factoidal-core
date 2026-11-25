import L4Factoidal.Wikidata.Parser
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/PreParseTokens.java
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/WdqsPrefixes.java


/-! Source ranges for the pre-parse rules, using Factoidal's SPARQL lexer.
Upstream counterpart:
-/
namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL L4Factoidal.Syntax

structure LocatedToken where
  token : Token
  start : Nat
  stop : Nat

private def scan (allowPercent : Bool) : Nat → Nat → List Char → List LocatedToken → List LocatedToken
  | 0, _, _, acc => acc.reverse
  | fuel + 1, offset, chars, acc =>
    let (token, start, stop, rest) := nextToken false offset chars
    if token != .eof then scan allowPercent fuel stop rest (⟨token, start, stop⟩ :: acc)
    else if allowPercent && start < stop && chars[start - offset]? == some '%' then
      let (name, stop, tail) := scanWhile (fun c => c.isAlphanum || c == '_') stop rest []
      scan allowPercent fuel stop tail (⟨.invalid ("%" ++ String.ofList name), start, stop⟩ :: acc)
    else acc.reverse

def sourceTokens (text : String) (allowPercent := false) : List LocatedToken :=
  scan allowPercent (text.length + 1) 0 text.toList []

def sourceState (tokens : List LocatedToken) (defaults := defaultPrefixes) :
    Except L4Factoidal.Syntax.ParseError (PState × TStream) :=
  pPrologue (tokens.length + 1) { prefixes := defaults }
    (tokens.map fun t => ⟨t.token, t.start⟩)

def tokenIri (state : PState) : Token → Option String
  | .iri iri => some (resolveAgainst? state.base iri)
  | .pname name => (resolvePnameIri state name).map (·.val)
  | _ => none

structure Edit where
  start : Nat
  stop : Nat
  replacement : String

private def splice (offset : Nat) (rest : List Char) (edits : List Edit) : List String :=
  go offset rest edits []
where
  go (offset : Nat) (rest : List Char) (edits : List Edit) (acc : List String) :
      List String :=
    match edits with
    | [] => (String.ofList rest :: acc).reverse
    | edit :: edits =>
      let unchanged := String.ofList (rest.take (edit.start - offset))
      go edit.stop (rest.drop (edit.stop - offset)) edits (edit.replacement :: unchanged :: acc)

private noncomputable def spliceSpec (offset : Nat) (rest : List Char) : List Edit → List String
  | [] => [String.ofList rest]
  | edit :: edits =>
    String.ofList (rest.take (edit.start - offset)) :: edit.replacement ::
      spliceSpec edit.stop (rest.drop (edit.stop - offset)) edits

private theorem splice_go_eq (offset : Nat) (rest : List Char) (edits : List Edit)
    (acc : List String) :
    splice.go offset rest edits acc = acc.reverse ++ spliceSpec offset rest edits := by
  induction edits generalizing offset rest acc with
  | nil => simp [splice.go, spliceSpec]
  | cons edit edits ih => simp [splice.go, spliceSpec, ih, List.append_assoc]

private theorem splice_eq (offset : Nat) (rest : List Char) (edits : List Edit) :
    splice offset rest edits = spliceSpec offset rest edits := by
  simp [splice, splice_go_eq]

/-- The rule planners supply disjoint ranges in source order. -/
def applyEdits (text : String) (edits : List Edit) : String :=
  String.join (splice 0 text.toList edits)

@[simp] theorem applyEdits_empty (text : String) : applyEdits text [] = text := by
  simp [applyEdits, splice, splice.go]

/-- Materialise referenced WDQS defaults while honouring user declarations.
-/
def standalone (text : String) : String :=
  let tokens := sourceTokens text
  match sourceState tokens [] with
  | .error _ => text
  | .ok (authored, body) =>
    let used := body.filterMap fun t => match t.tok with
      | .pname name => some (splitPname name).1
      | _ => none
    let needed := defaultPrefixes.filter fun (name, _) =>
      used.contains name && (lookupPrefix name authored.prefixes).isNone
    String.join (needed.map fun (name, iri) => s!"PREFIX {name}: <{iri}>\n") ++ text

end L4Factoidal.Wikidata
