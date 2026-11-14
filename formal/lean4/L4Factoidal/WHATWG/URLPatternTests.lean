/-
L4Factoidal.WHATWG.URLPatternTests — theorems and `#guard` tests of the URL Pattern Standard
in Lean (`WHATWG/URLPattern.lean`). The cases are web-platform-tests
`urlpattern/resources/urlpatterntestdata.json` (367 of its 369 entries pass through the page's
URLPattern class; the two that do not use the `v` flag's set operations, which `JS.Re` lacks).
-/
import L4Factoidal.WHATWG.URLPattern

namespace L4Factoidal.WHATWG.URLPattern

/-! ## Theorems -/

/-- Kind: totality. Says: the lenient tokenizer (the one the constructor string parser uses)
answers a token list for every input: a tokenizing error becomes an `invalidChar` token.
Does not say: what the tokens are. -/
theorem tokenizeGo_lenient (cs : Array Char) (fuel i : Nat) (acc : Array Tok) :
    (tokenizeGo cs false fuel i acc).isSome = true := by
  induction fuel generalizing i acc with
  | zero => simp [tokenizeGo]
  | succ n ih =>
    unfold tokenizeGo
    split
    · rfl
    · split
      · exact ih _ _
      · simp [ih]

/-- Kind: a refusal. Says: the constructor refuses a URLPatternInit together with a base URL
argument, whatever they hold (section 1.2, "create", step 4).
Does not say: anything about the message. -/
theorem create_init_with_base (i : Init) (b : String) (ic : Bool) :
    (create (.init i) (some b) ic).toOption = none := by
  simp [create, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- Kind: a refusal. Says: `test` and `exec` refuse a URLPatternInit together with a base URL
(section 1.2, "match", step 3.1): a TypeError, not a failed match. -/
theorem exec_init_with_base (p : Pattern) (i : Init) (b : String) :
    (exec p (.init i) (some b)).toOption = none := by
  simp [exec, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- Kind: an invariant of a match result. Says: a component's match gives one entry for each
of its group names, in order.
Does not say: which groups took part. -/
theorem Component.exec_size (c : Component) (s : String) (g : Array (String × Option String))
    (h : c.exec s = some g) : g.size = c.names.size := by
  unfold Component.exec at h
  dsimp only at h
  split at h
  · cases h
  · cases h; simp

/-! ## Tests (cases of `urlpatterntestdata.json`) -/

private def pat (i : Init) (base : Option String := none) (ic : Bool := false) : Option Pattern :=
  (create (.init i) base ic).toOption

private def strs (p : Pattern) : List String :=
  [p.protocol.pattern, p.username.pattern, p.password.pattern, p.hostname.pattern, p.port.pattern,
   p.pathname.pattern, p.search.pattern, p.hash.pattern]

/-- The groups of the pathname of a match, or `none`. -/
private def pathGroups (p : Option Pattern) (input : Input) (base : Option String := none) :
    Option (List (String × Option String)) :=
  match p with
  | none => none
  | some p => match exec p input base with
    | .ok (some r) => (r.components[5]?).map (·.2.toList)
    | _ => none

-- a fixed pathname; the other components are wildcards
#guard (pat { pathname := some "/foo/bar" }).map strs == some ["*", "*", "*", "*", "*", "/foo/bar", "*", "*"]
#guard pathGroups (pat { pathname := some "/foo/bar" }) (.init { pathname := some "/foo/bar" }) == some []
#guard pathGroups (pat { pathname := some "/foo/bar" }) (.init { pathname := some "/foo/ba" }) == none
-- a named group, a regexp group, a full wildcard, modifiers
#guard pathGroups (pat { pathname := some "/foo/:bar" }) (.init { pathname := some "/foo/baz" }) == some [("bar", some "baz")]
#guard pathGroups (pat { pathname := some "/foo/:bar" }) (.init { pathname := some "/foo/baz/x" }) == none
#guard pathGroups (pat { pathname := some "/foo/(\\d+)" }) (.init { pathname := some "/foo/123" }) == some [("0", some "123")]
#guard pathGroups (pat { pathname := some "/foo/*" }) (.init { pathname := some "/foo/a/b" }) == some [("0", some "a/b")]
#guard pathGroups (pat { pathname := some "/foo/:bar?" }) (.init { pathname := some "/foo" }) == some [("bar", none)]
#guard pathGroups (pat { pathname := some "/foo/:bar+" }) (.init { pathname := some "/foo/a/b" }) == some [("bar", some "a/b")]
#guard pathGroups (pat { pathname := some "/foo{/:bar}*" }) (.init { pathname := some "/foo" }) == some [("bar", none)]
-- the canonical pattern string: a segment wildcard regexp is written `*` or kept, names stay
#guard (pat { pathname := some "/foo/(.*)" }).map (·.pathname.pattern) == some "/foo/*"
#guard (pat { pathname := some "/foo/([^\\/]+?)" }).map (·.pathname.pattern) == some "/foo/([^\\/]+?)"
#guard (pat { pathname := some "/:foo(.*)" }).map (·.pathname.pattern) == some "/:foo(.*)"
#guard (pat { pathname := some "{/foo}?" }).map (·.pathname.pattern) == some "{/foo}?"
-- canonicalization: the hostname is lowered, a default port is dropped, a path is percent-encoded
#guard (pat { protocol := some "https", hostname := some "EXAMPLE.com", port := some "443" }).map
    (fun p => (p.hostname.pattern, p.port.pattern)) == some ("example.com", "")
#guard (pat { pathname := some "/café" }).map (·.pathname.pattern) == some "/caf%C3%A9"
#guard (pat { protocol := some "http", port := some "80 " }).map (·.port.pattern) == some "80"
-- a constructor string, with and without a base URL
#guard (create (.str "https://example.com:8080/foo?bar#baz") none false).toOption.map strs ==
  some ["https", "*", "*", "example.com", "8080", "/foo", "bar", "baz"]
#guard (create (.str "/foo?bar#baz") (some "https://example.com:8080") false).toOption.map strs ==
  some ["https", "*", "*", "example.com", "8080", "/foo", "bar", "baz"]
#guard (create (.str "/foo") none false).toOption.isNone
#guard (create (.str "data\\:foobar") none false).toOption.map strs ==
  some ["data", "*", "*", "", "", "foobar", "*", "*"]
-- errors: a name used twice, a group that does not close, an invalid protocol, a bad escape
#guard (pat { pathname := some "/:id/:id" }).isNone
#guard (pat { pathname := some "/foo/(bar" }).isNone
#guard (pat { protocol := some "(café)" }).isNone
#guard (pat { pathname := some "/(\\m)" }).isNone
-- names above ASCII: U+2118 is Other_ID_Start; an emoji is not a name
#guard (pat { pathname := some "/:℘" }).isSome
#guard (pat { pathname := some ":🚲".toList.asString }).isNone
-- a string input with a base URL; ignoreCase
#guard pathGroups (pat { pathname := some "/foo/:x", baseURL := some "https://example.com/" })
    (.str "../b/../foo/q") (some "https://example.com/a/") == some [("x", some "q")]
#guard pathGroups (pat { pathname := some "/FOO/:x" } none true) (.init { pathname := some "/foo/q" }) == some [("x", some "q")]
#guard pathGroups (pat { pathname := some "/FOO/:x" }) (.init { pathname := some "/foo/q" }) == none
-- the regular expression of a part list (section 2.1.3)
#guard (parsePattern "/a/:b{/c}?" pathnameOptions pure).toOption.map (fun ps => (regexOf ps pathnameOptions).1) ==
  some "^\\/a(?:\\/([^\\/]+?))(?:\\/c)?$"

end L4Factoidal.WHATWG.URLPattern
