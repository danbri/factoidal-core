import L4Factoidal.DOM.Arena
import L4Factoidal.WHATWG.Encoding.Api

namespace L4Factoidal.HTML.DocumentEncoding
open L4Factoidal.WHATWG

/-- HTML §2.5 "algorithm for extracting a character encoding from a meta element": the
label after the first `charset`, ASCII case-insensitive, that an `=` follows. -/
def extractCharset (content : String) : Option String :=
  let cs := content.toList
  let ws := fun (c : Char) => c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '
  let lower := fun (c : Char) => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
  let rec go (fuel : Nat) (xs : List Char) : Option String :=
    match fuel, xs with
    | 0, _ | _, [] => none
    | fuel + 1, _ :: rest =>
      if (xs.take 7).map lower != "charset".toList then go fuel rest else
      let after := (xs.drop 7).dropWhile ws
      match after with
      | '=' :: more =>
        match more.dropWhile ws with
        | q :: tail =>
          if q == '"' || q == '\'' then
            if tail.contains q then some (String.ofList (tail.takeWhile (· != q))) else none
          else
            let v := (q :: tail).takeWhile (fun c => !ws c && c != ';')
            if v.isEmpty then none else some (String.ofList v)
        | [] => none
      | _ => go fuel (xs.drop 7)
  go (cs.length + 1) cs

/-- The encoding the first `meta` in `nodes` declares, as `documentEncoding` maps it. -/
def declared (d : L4Factoidal.DOM.Dom) (nodes : Array Nat) : Option Encoding.Encoding :=
  nodes.findSome? fun k =>
    if !L4Factoidal.DOM.Dom.isHtmlElement (d.get k) "meta" then none else
    let label := match d.getAttributeNS? k none "charset" with
      | some c => some c
      | none =>
        match d.getAttributeNS? k none "http-equiv", d.getAttributeNS? k none "content" with
        | some h, some c => if L4Factoidal.DOM.Dom.asciiLower h == "content-type" then extractCharset c else none
        | _, _ => none
    (label.bind Encoding.getEncoding).map fun e => match e with
      | .utf_16be | .utf_16le => .utf_8
      | .x_user_defined => .windows_1252
      | e => e

/-- Whether the page's text, comments and attribute values are all ASCII. -/
def pageAscii (d : L4Factoidal.DOM.Dom) (nodes : Array Nat) : Bool :=
  let ascii := fun (x : String) => x.toList.all (fun (c : Char) => c.toNat < 0x80)
  nodes.all fun (k : Nat) =>
    let n : L4Factoidal.DOM.Node := d.get k
    ascii n.data && n.attrs.all (fun (a : L4Factoidal.DOM.Attr) => ascii a.value)

/-- The encoding of a page from its tree: `declared` when the page is ASCII, else UTF-8.
The page's text is looked at only when a `meta` declares an encoding other than UTF-8
(the common `<meta charset=utf-8>`, and a page with no declaration, read no text). -/
def ofNodes (d : L4Factoidal.DOM.Dom) (nodes : Array Nat) : Encoding.Encoding :=
  match declared d nodes with
  | none | some .utf_8 => .utf_8
  | some e => if pageAscii d nodes then e else .utf_8

/-- The encoding a document declares in a `meta` element (HTML §13.2.3.2, the prescan's
rules on the parsed tree: the first `meta` whose `charset`, or whose `http-equiv`
content-type `content`, names an encoding; UTF-16 is UTF-8 and x-user-defined is
windows-1252).

The hosts give the engine the page as text: UTF-8 when the bytes are UTF-8, else
windows-1252 (`native_html_document.ts`), whatever a `meta` says. A declaration is the
document's encoding only when the page is ASCII (its text, comments and attribute values),
where every ASCII-compatible encoding reads the same characters; otherwise, and with no
declaration, the encoding is UTF-8. A byte-level decode of the page by its declaration
(HTML §13.2.3) is the hosts' to add. -/
def documentEncoding (d : L4Factoidal.DOM.Dom) : Encoding.Encoding :=
  ofNodes d (d.treeOrder 0 false)

/-- `documentEncoding` over the nodes below `parsed` only (those the parser made). -/
def parsedEncoding (d : L4Factoidal.DOM.Dom) (parsed : Option Nat) : Encoding.Encoding :=
  match parsed with
  | none => documentEncoding d
  | some n => ofNodes d ((d.treeOrder 0 false).filter (· < n))

/-- Kind: equivalence. Says: looking at the text only for a non-UTF-8 declaration gives
the same answer as the rule "UTF-8 unless the page is ASCII, then the declaration". Does
not say: that the hosts decode the bytes by it. -/
theorem ofNodes_eq (d : L4Factoidal.DOM.Dom) (nodes : Array Nat) :
    ofNodes d nodes = if pageAscii d nodes then (declared d nodes).getD .utf_8 else .utf_8 := by
  unfold ofNodes
  split <;> rename_i h <;> simp_all <;> split <;> simp_all

end L4Factoidal.HTML.DocumentEncoding
