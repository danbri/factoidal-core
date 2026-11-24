import L4Factoidal.SPARQL.Tokenizer

namespace L4Factoidal.SPARQL

/-- A source comment, including its `#`, with half-open offsets measured
in Unicode code points in the original query string. -/
structure SourceComment where
  text : String
  start : Nat
  stop : Nat

private def commentsInGap : Nat → Nat → List Char → List SourceComment → List SourceComment
  | 0, _, _, found | _, _, [], found => found
  | fuel + 1, offset, '#' :: rest, found =>
    let line := rest.takeWhile (· != '\n')
    let content := if line.getLast? == some '\r' then line.dropLast else line
    let stop := offset + 1 + content.length
    let comment := ⟨String.ofList ('#' :: content), offset, stop⟩
    commentsInGap fuel (offset + 1 + line.length) (rest.drop line.length) (comment :: found)
  | fuel + 1, offset, _ :: rest, found => commentsInGap fuel (offset + 1) rest found

private def collectComments (v12 : Bool) : Nat → Nat → List Char → List SourceComment →
    List SourceComment
  | 0, _, _, found | _, _, [], found => found.reverse
  | fuel + 1, offset, chars, found =>
    let (_, start, stop, rest) := nextToken v12 offset chars
    let gap := start - offset
    let found := commentsInGap gap offset (chars.take gap) found
    if stop ≤ offset then found.reverse else collectComments v12 fuel stop rest found

/-- Recover the trivia skipped by the standard lexer. A `#` inside an IRI,
string literal or escaped prefixed name is part of its token. -/
def sourceComments (text : String) (v12 : Bool := false) : List SourceComment :=
  if text.contains '#' then collectComments v12 (text.length + 1) 0 text.toList [] else []

#guard (sourceComments "ASK { BIND(\"🗺#string\" AS ?label) } # note\r\n# again").map
  (fun comment => (comment.text, comment.start, comment.stop)) ==
    [("# note", 35, 41), ("# again", 43, 50)]

end L4Factoidal.SPARQL
