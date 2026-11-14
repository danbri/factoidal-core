/-
L4Factoidal.MathML.Intent — the grammar of the MathML 4 `intent` attribute.

Specification: MathML 4.0, W3C Working Draft 2026-11-12
(https://www.w3.org/TR/2026/WD-mathml4-20261112/), section 5.1 "The Grammar for intent":

    intent             := self-property-list | expression
    self-property-list := property+ S
    expression         := S ( term property* ) S
    term               := concept-or-literal | number | reference | application
    concept-or-literal := NCName
    number             := '-'? \d+ ( '.' \d+ )?
    reference          := '$' NCName
    application        := expression '(' arguments? S ')'
    arguments          := expression ( ',' expression )*
    property           := S ':' NCName
    S                  := [ \t\n\r]*

`application` is left-recursive, so the reader takes a first term (a name, a number or a reference)
and then repeats: properties, then an argument list if a `(` follows. The recursion is on a fuel
taken from the length of the input; an input that would need more is refused.

This module is a reader and a writer with tests. Nothing emits `intent` yet, so theorem 5 of
`docs/designissues/2026-10-28-mathml-finish.md` is not stated here.
-/
import L4Factoidal.XML.Wellformedness

namespace L4Factoidal.MathML

open L4Factoidal.XML

/-- An intent expression. `props e ps` is a term with one or more properties. -/
inductive Intent where
  | concept (name : String)
  | number (lex : String)
  | ref (name : String)
  | app (head : Intent) (args : List Intent)
  | props (e : Intent) (ps : List String)
deriving Repr, Inhabited

/-- The value of an `intent` attribute. -/
inductive IntentValue where
  | selfProps (ps : List String)
  | expr (e : Intent)
deriving Repr, Inhabited

/-- A literal is a name starting with `_` (section 5.1). -/
def Intent.isLiteral : Intent → Bool
  | .concept name => name.startsWith "_"
  | _             => false

/-- `S := [ \t\n\r]*`. -/
def intentSkipS : List Char → List Char
  | c :: cs => if c == ' ' || c == '\t' || c == '\n' || c == '\r' then intentSkipS cs else c :: cs
  | []      => []

/-- An `NCName` at the front of the input, and the rest. -/
def intentNCName : List Char → Option (String × List Char)
  | c :: rest =>
      if isNCNameStartChar c then
        some (String.ofList (c :: rest.takeWhile isNCNameChar), rest.dropWhile isNCNameChar)
      else none
  | [] => none

/-- `number := '-'? \d+ ( '.' \d+ )?` at the front of the input, and the rest. -/
def intentNumber (cs : List Char) : Option (String × List Char) :=
  let (sign, r) : List Char × List Char := match cs with
    | '-' :: r => (['-'], r)
    | _        => ([], cs)
  let ds := r.takeWhile Char.isDigit
  let r1 := r.dropWhile Char.isDigit
  if ds.isEmpty then none
  else match r1 with
    | '.' :: r2 =>
        let fs := r2.takeWhile Char.isDigit
        if fs.isEmpty then some (String.ofList (sign ++ ds), r1)
        else some (String.ofList (sign ++ ds ++ '.' :: fs), r2.dropWhile Char.isDigit)
    | _ => some (String.ofList (sign ++ ds), r1)

/-- `property*`: each is `S ':' NCName`. White space is consumed only in front of a property. -/
def intentProps : Nat → List String → List Char → List String × List Char
  | 0, acc, cs => (acc.reverse, cs)
  | fuel + 1, acc, cs =>
      match intentSkipS cs with
      | ':' :: r =>
          match intentNCName r with
          | some (name, r') => intentProps fuel (name :: acc) r'
          | none            => (acc.reverse, cs)
      | _ => (acc.reverse, cs)

/-- The first term of an expression: a reference, a number or a name. -/
def intentFirst : List Char → Option (Intent × List Char)
  | '$' :: r => (intentNCName r).map (fun (name, r') => (Intent.ref name, r'))
  | c :: r   =>
      if c == '-' || c.isDigit then (intentNumber (c :: r)).map (fun (lex, r') => (Intent.number lex, r'))
      else (intentNCName (c :: r)).map (fun (name, r') => (Intent.concept name, r'))
  | [] => none

mutual
/-- `expression`, with its leading and trailing `S`. -/
def intentExpr : Nat → List Char → Option (Intent × List Char)
  | 0, _ => none
  | fuel + 1, cs =>
      match intentFirst (intentSkipS cs) with
      | some (t, r) => intentPostfix fuel t r
      | none        => none
/-- After a term: its properties, then either an argument list (the whole is a term again) or the
    end of the expression. -/
def intentPostfix : Nat → Intent → List Char → Option (Intent × List Char)
  | 0, _, _ => none
  | fuel + 1, t, cs =>
      match intentProps (cs.length + 1) [] cs with
      | (ps, r) =>
          let t' := if ps.isEmpty then t else Intent.props t ps
          match intentSkipS r with
          | '(' :: r1 =>
              match intentSkipS r1 with
              | ')' :: r2 => intentPostfix fuel (.app t' []) r2
              | _ =>
                  match intentArgs fuel r1 [] with
                  | some (args, r2) => intentPostfix fuel (.app t' args) r2
                  | none            => none
          | r' => some (t', r')
/-- `arguments S ')'`: expressions separated by `,`, up to the closing bracket. -/
def intentArgs : Nat → List Char → List Intent → Option (List Intent × List Char)
  | 0, _, _ => none
  | fuel + 1, cs, acc =>
      match intentExpr fuel cs with
      | some (e, ',' :: r) => intentArgs fuel r (e :: acc)
      | some (e, ')' :: r) => some ((e :: acc).reverse, r)
      | _                  => none
end

/-- Read the value of an `intent` attribute (section 5.1). `none` when it does not match the
    grammar. -/
def parseIntent (s : String) : Option IntentValue :=
  let cs := s.toList
  match intentProps (cs.length + 1) [] cs with
  | (ps, r) =>
      if !ps.isEmpty && (intentSkipS r).isEmpty then some (.selfProps ps)
      else match intentExpr (4 * cs.length + 8) cs with
        | some (e, []) => some (.expr e)
        | _            => none

mutual
/-- Write an expression with no white space. -/
def intentStr : Intent → String
  | .concept name => name
  | .number lex   => lex
  | .ref name     => "$" ++ name
  | .app h args   => intentStrArgs args true (intentStr h ++ "(") ++ ")"
  | .props e ps   => ps.foldl (fun acc p => acc ++ ":" ++ p) (intentStr e)
/-- The arguments, appended to `acc` with commas between (a loop over the list). -/
def intentStrArgs : List Intent → Bool → String → String
  | [], _, acc          => acc
  | a :: as, first, acc => intentStrArgs as false (acc ++ (if first then "" else ",") ++ intentStr a)
end

def IntentValue.str : IntentValue → String
  | .selfProps ps => ps.foldl (fun acc p => acc ++ ":" ++ p) ""
  | .expr e       => intentStr e

/-! ## Tests: the `intent` values of the MathML 4 examples (chapter 5) -/

/-- Reads, and writes back as `want` (the input without its optional white space). -/
private def reads (s want : String) : Bool :=
  match parseIntent s with
  | some v => v.str == want
  | none   => false

private def readsAs (s : String) (shape : Intent → Bool) : Bool :=
  match parseIntent s with
  | some (.expr e) => shape e
  | _              => false

#guard reads "power($base,$exp)" "power($base,$exp)"
#guard readsAs "power($base,$exp)" (fun e => match e with
  | .app (.concept "power") [.ref "base", .ref "exp"] => true
  | _ => false)
#guard reads "binomial-coefficent($power, $term)" "binomial-coefficent($power,$term)"
#guard reads "open-closed-interval($start,$end)" "open-closed-interval($start,$end)"
#guard reads "_($base,$script)" "_($base,$script)"
#guard reads "transpose" "transpose"
#guard reads "factorial:postfix" "factorial:postfix"
#guard readsAs "factorial:postfix" (fun e => match e with
  | .props (.concept "factorial") ["postfix"] => true
  | _ => false)
#guard reads "converse:postfix(L)" "converse:postfix(L)"
#guard reads "converse:postfix(L):infix(_x,_y)" "converse:postfix(L):infix(_x,_y)"
#guard readsAs "converse:postfix(L):infix(_x,_y)" (fun e => match e with
  | .app (.props (.app (.props (.concept "converse") ["postfix"]) [.concept "L"]) ["infix"])
      [.concept "_x", .concept "_y"] => true
  | _ => false)
#guard reads "factorial:postfix:function:prefix(_x)" "factorial:postfix:function:prefix(_x)"
#guard reads "highlighted-result(3)" "highlighted-result(3)"
#guard readsAs "highlighted-result(3)" (fun e => match e with
  | .app (.concept "highlighted-result") [.number "3"] => true
  | _ => false)
#guard reads "wibble(_x_squared,x_superscript_2,_x_squared)" "wibble(_x_squared,x_superscript_2,_x_squared)"
#guard reads "$op :postfix ($a)" "$op:postfix($a)"
#guard reads "$op:infix($x,$y)" "$op:infix($x,$y)"
#guard reads "$xf:prefix" "$xf:prefix"
#guard reads "$f:function($x)" "$f:function($x)"
#guard reads "_хикс" "_хикс"
#guard reads "_x-new" "_x-new"
#guard readsAs "_x-new" Intent.isLiteral
#guard !readsAs "transpose" Intent.isLiteral
-- A property list on its own (`self-property-list`).
#guard reads ":literal" ":literal"
#guard reads ":system-of-equations" ":system-of-equations"
#guard reads " :matrix :common " ":matrix:common"
#guard (match parseIntent ":literal" with
  | some (.selfProps ["literal"]) => true
  | _ => false)
-- Numbers, nesting, an empty argument list, white space.
#guard reads "f(-3.5, 2)" "f(-3.5,2)"
#guard reads " g ( ) " "g()"
#guard reads "f(g(h($x)))(1)" "f(g(h($x)))(1)"
-- Not in the grammar.
#guard (parseIntent "").isNone
#guard (parseIntent "f(").isNone
#guard (parseIntent "f(,)").isNone
#guard (parseIntent "f(x) y").isNone
#guard (parseIntent "3x").isNone
#guard (parseIntent "$").isNone
#guard (parseIntent "f: postfix").isNone
#guard (parseIntent "a:b:").isNone
#guard (parseIntent "1.").isNone

end L4Factoidal.MathML
