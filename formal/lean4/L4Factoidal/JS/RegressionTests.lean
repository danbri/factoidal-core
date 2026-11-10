import L4Factoidal.JS.Tests

/-!
# Tests of repaired defects of the JavaScript engine

Each `#guard` runs a script and checks what it printed. The expected lines are what QuickJS-NG
0.18.0 and V8 (Node 22) both print for the same script. The defects were found on 2026-11-09 by
differential runs and by real-world code that did not load:
https://github.com/danbri/factoidal-core/issues/378 (BubblePopJS plan; its defect list) and
`docs/designissues/2026-11-09-foafnaut-perf-exploration.md`, section 6.4.
-/

namespace L4Factoidal.JS.Tests
open L4Factoidal.JS

/-! ## Division or regular expression

§12 of ECMA-262: the syntactic grammar chooses the reading of a `/` (the goal symbols
InputElementDiv and InputElementRegExp). The lexer makes a first choice from the tokens before
the `/` (`regexAllowed`); where the grammar decides otherwise, the parser asks for the other
reading (`P.relexAt`). Before the repair of 2026-11-10 the lexer's choice was final, a `/` after
every `)` and `}` was a division, and a `/` after every keyword and after `++` and `--` started a
regular expression: 19 of these 46 scripts gave a SyntaxError (for example
`if (s) /x/.test(s)`, `k++ / 2`, `o.default / 2` on a line with a second `/`). -/

-- A `/` after the `)` of an `if`, `while`, `for` or `with` header, after `else` and `do`, after a
-- `case` label and after the `}` of a block starts a regular expression literal.
#guard out "var s = 'x'; if (s) /x/.test(s); print(1)" == ["1"]
#guard out "var n = 0; for (var i = 0; i < 2; i++) /a/.test('a') ? n++ : 0; print(n)" == ["2"]
#guard out "if (1) {} /re/.test('re'); print(2)" == ["2"]
#guard out "function q() {} /stmt/.test('a'); print(3)" == ["3"]
#guard out "try { } finally { } /fin/.test('a'); print(4)" == ["4"]
#guard out "var w = [1, 2]; for (var e of w) /of/.test('o'); print(5)" == ["5"]
#guard out "var k = 0; while (k++ < 1) /w/.test('w'); print(k)" == ["2"]
#guard out "var y = 0; do y++; while (y < 3) /dw/.test('dw'); print(y)" == ["3"]
#guard out "var e2 = 0; if (e2) e2 = 1; else /else/.test('else') && (e2 = 2); print(e2)" == ["2"]
#guard out "var c2 = 1; switch (c2) { case 1: /case/.test('case') && print('c'); }" == ["c"]
#guard out "var g2 = 1; if (g2) { g2 = 2 } /blk/.test('blk') ? print('y') : print('n')" == ["y"]

-- A `/` after the `)` or `}` that ends an expression, and after a `]`, is a division.
#guard out "var a = (6) / 2 / 3; var o = {v: 8}.v / 4; print(a, o)" == ["1 2"]
#guard out "function f() { return 9 } print(f() / 3, [12][0] / 4)" == ["3 3"]
#guard out "var u = (function () { return 6 }) () / 3; print(u)" == ["2"]
#guard out "var v = [1, 2, 3].map(function (z) { return z * 2 }) [1] / 2; print(v)" == ["2"]
#guard out "var p2 = x => /arrow/.test(x); print(p2('arrow'), (() => { return 8 })() / 4)" == ["true 2"]
#guard out "var q2 = { m() { return 9 } }.m() / 3; print(q2)" == ["3"]
#guard out "var j2 = [4, 8]; var l2 = j2[1] / j2[0] / 2; print(l2)" == ["1"]
#guard out "print(((a, b) => { return a })(9, 1) / 3 / 3)" == ["1"]

-- A `/` after a postfix `++` or `--`, after a prefix one and its operand, and after a keyword
-- that is a property name, is a division.
#guard out "var b = {a: 1}; var c = b.a++ / 2; var d = /x/; print(c, String(d))" == ["0.5 /x/"]
#guard out "var k = 1; var w = k++ /2/1; print(w, k)" == ["0.5 2"]
#guard out "var m = 8; var r = m-- / 2 / 2; print(r)" == ["2"]
#guard out "var o = {typeof: 6, in: 8}; print(o.typeof / 2, o.in /2/ 1)" == ["3 4"]
#guard out "var x = 4, g = 2, i = 1; print(x /g/ i, x++ /g/ i)" == ["2 2"]
#guard out "var d = { default: 12, new: 30 }; var f = 3; print(d.default /f/ 2, d.new / f)" == ["2 10"]
#guard out "var S = { for: function (x) { return x } }; print(S.for(8) / 2 / 2)" == ["2"]
#guard out "var i2 = 2; print(++i2 / 3, typeof /pp/.source)" == ["1 string"]
#guard out "var o6 = { if: 3 }; print(o6.if /1/ 1, o6?.if / 3)" == ["3 1"]
#guard out "var m7 = 6; m7 /= 2; var n7 = m7 / 3 /1/ 1; print(m7, n7)" == ["3 1"]

-- The parser asks for a regular expression literal: after the `}` of a block that has a label,
-- and after a class declaration (the lexer takes these `}` as the end of an expression).
#guard out "var t = 0; label: { t = 1 } /lbl/.test('lbl') && t++; print(t)" == ["2"]
#guard out "class A { m() { return 1 } } /cls/.test('cls') && print('after class')" == ["after class"]

-- The parser asks for a division: after a function expression (the lexer takes its `}` as the
-- end of a block). The second script has the `/` in a block, and a regular expression literal
-- after that block: the brackets open at the `/` are kept (`openBefore`).
#guard out "print(isNaN(function () {} / 2), typeof (function () { return 4 } / 2))" == ["true number"]
#guard out "if (1) { var h = function () { return 1 } / 1; } /blk/.test('blk') && print(isNaN(h))" == ["true"]

-- Places where the first choice was right before the repair, kept as controls: a template
-- substitution, a class body, a division on the next line, operators, an array, `/=`, a `/` in
-- a string and in a class of a regular expression, comments, an arrow function body.
#guard out "var r2 = `a${ /in/.test('in') }b`; print(r2)" == ["atrueb"]
#guard out "class K { m() { return /c/.test('c') } } print(new K().m())" == ["true"]
#guard out "var s2 = 10; var t2 = s2\n/2/1; print(t2)" == ["5"]
#guard out "var h2 = typeof /r/; print(h2, void /r/ === undefined)" == ["object true"]
#guard out "var z2 = [/a/, /b/g].length / 2; print(z2)" == ["1"]
#guard out "var n2 = 3; n2 /= 2 / 1; print(n2)" == ["1.5"]
#guard out "var a5 = 12, g = 2; var x5 = () => a5 /g/ 3; print(x5())" == ["2"]
#guard out "var r6 = 0; for (var c6 of '/a/') r6++; print(r6, '/'.length / 1, `/${ 4 / 2 }/`)" == ["3 1 /2/"]
#guard out "print([/[/]/.test('/'), /\\//.test('/'), /a\\/b/.source.length, /=/.test('=')].join())" == ["true,true,4,true"]
#guard out "var y8 = 0; y8 = y8 /* c */ / 1 // 2\n+ 1; print(y8)" == ["1"]

-- A regular expression literal with no end is a SyntaxError; `eval` uses the same lexer.
#guard out "try { eval('var u9 = 1 + / 2') } catch (e) { print(e instanceof SyntaxError) }" == ["true"]
#guard out "try { eval('var w9 = 1 /\\n 2/') } catch (e) { print(e instanceof SyntaxError) }" == ["true"]
#guard out "var t9 = eval('var q9 = 8\\n/2/1; q9'); print(t9)" == ["4"]

/-! ## The name of a function

A function declaration's name is a binding of the scope that has the declaration (§10.2.11,
§16.1.7): code in the body that assigns to the name changes that binding. A function
expression's name is a binding of a scope of its own (§15.2.5), immutable and not strict: an
assignment from code that is not strict does nothing, and from strict code it throws a TypeError
(§9.1.1.1.5). Before the repair of 2026-11-10 a declaration also got the scope of an expression,
and every assignment to either name threw "Assignment to constant variable": 13 of these 21
scripts failed. Helpers that Babel writes replace themselves this way
(`function _extends() { _extends = Object.assign ...`), and the `marked` library did not load. -/

-- Function declarations.
#guard out "function f() { f = 1 } f(); print(typeof f)" == ["number"]
#guard out "function g() { 'use strict'; g = function () { return 2 }; return g() } print(g(), g())" == ["2 2"]
#guard out "(function () { 'use strict'; function h() { h = Object.assign || function () { return 3 }; return typeof h } print(h(), typeof h) })()" == ["function function"]
#guard out "function k() { return k } var k2 = k; k = 5; print(typeof k2(), k)" == ["number 5"]
#guard out "{ function b1() { b1 = 7 } b1(); print(b1) }" == ["7"]
#guard out "function outer() { function inner() { inner = 8 } inner(); return inner } print(outer())" == ["8"]
#guard out "function fact(n) { return n < 2 ? 1 : n * fact(n - 1) } var f0 = fact; fact = function () { return 0 }; print(f0(5))" == ["0"]
#guard out "function _ext() { _ext = Object.assign ? Object.assign.bind() : function (t) { return t }; return _ext.apply(this, arguments) } print(_ext({a: 1}, {b: 2}).b, _ext({}, {c: 3}).c)" == ["2 3"]
#guard out "function cnt() { var n = 0; function step() { n++; if (n < 3) step(); } step(); return n } print(cnt())" == ["3"]
#guard out "function* gen() { gen = 1; yield 1 } var it = gen(); it.next(); print(gen)" == ["1"]

-- Function expressions. A parameter or a `var` with the same name is a different binding.
#guard out "var b = function g() { 'use strict'; try { g = 1 } catch (e) { return e instanceof TypeError } return 'no' }; print(b())" == ["true"]
#guard out "const d = function d2() { return 1 }; try { d = 2 } catch (e) { print(e instanceof TypeError) }" == ["true"]
#guard out "var e2 = function w() { var w = 5; w = 6; return w }; print(e2())" == ["6"]
#guard out "var f3 = function q(q) { q = 7; return q }; print(f3(1))" == ["7"]
#guard out "class C { m() { try { C = 1 } catch (e) { return e instanceof TypeError } } } print(new C().m())" == ["true"]
#guard out "var o = { m: function n() { return typeof n } }; print(o.m())" == ["function"]
#guard out "var fe = function fact2(n) { return n < 2 ? 1 : n * fact2(n - 1) }; var fact2 = 0; print(fe(5))" == ["120"]

-- Function expressions, an assignment to the name from code that is not strict. The expected
-- lines are those of V8 and of §9.1.1.1.5; QuickJS-NG 0.18.0 throws a TypeError here.
#guard out "var a = function f() { f = 1; return typeof f }; print(a())" == ["function"]
#guard out "var c = function h() { h++; h += 1; var k = 0; for (var i = 0; i < 3; i++) { h = i; k += typeof h == 'function' ? 1 : 0 } return k }; print(c())" == ["3"]
#guard out "var g3 = function r() { return (() => { r = 3; return typeof r })() }; print(g3())" == ["function"]
#guard out "var h3 = function s() { eval('s = 4'); return typeof s }; print(h3())" == ["function"]

/-! ## encodeURI and decodeURI

§19.2.6.1 and §19.2.6.3. Before 2026-11-10 the global object had `encodeURIComponent` and
`decodeURIComponent` only; the `marked` library catches the ReferenceError of `encodeURI` and
then writes a link as plain text. `encodeURI` keeps the reserved characters and `#`;
`decodeURI` keeps the escape of a reserved character or of `#` as it is written. -/

#guard out "print(typeof encodeURI, typeof decodeURI, encodeURI.length, decodeURI.name)" == ["function function 1 decodeURI"]
#guard out "print(encodeURI('https://example.org/p/0?a=b c&d=é#x%'))" == ["https://example.org/p/0?a=b%20c&d=%C3%A9#x%25"]
#guard out "print(encodeURI(\";/?:@&=+$,#-_.!~*'()AZaz09 \\\"<>[]\\\\^`{|}\"))" == [";/?:@&=+$,#-_.!~*'()AZaz09%20%22%3C%3E%5B%5D%5C%5E%60%7B%7C%7D"]
#guard out "print(encodeURI('\\u{1F600}é中'), encodeURI(''), encodeURI(undefined))" == ["%F0%9F%98%80%C3%A9%E4%B8%AD  undefined"]
#guard out "try { encodeURI('\\uD800') } catch (e) { print(e instanceof URIError, e.name) }" == ["true URIError"]
#guard out "print(decodeURI('https://example.org/a%20b%2Fc?x=%C3%A9&y=%F0%9F%98%80'))" == ["https://example.org/a b%2Fc?x=é&y=😀"]
#guard out "print(decodeURI('%3B%2F%3F%3A%40%26%3D%2B%24%2C%23'), decodeURI('%3b%2f%41%7A%7e'))" == ["%3B%2F%3F%3A%40%26%3D%2B%24%2C%23 %3b%2fAz~"]
#guard out "print(decodeURI('%E4%B8%AD%2fa%25%20'), decodeURIComponent('%3B%2F%23%25'))" == ["中%2fa%  ;/#%"]
#guard out "try { decodeURI('%') } catch (e) { print(e instanceof URIError) }" == ["true"]
#guard out "try { decodeURI('%E4%B8') } catch (e) { print(e instanceof URIError) }" == ["true"]
#guard out "try { decodeURI('%zz') } catch (e) { print(e instanceof URIError) }" == ["true"]
#guard out "print(decodeURI(encodeURI('a b/c?d=e&f=ü#g')) === 'a b/c?d=e&f=ü#g', encodeURI(decodeURI('%2F%20')))" == ["true %252F%20"]

/-! ## A function with many names

A function whose environment has more than `FunInfo.indexedFrom` names gets an index from name
to slot, shared by its environments (`FunInfo.index`). Before 2026-11-10 a name that such an
environment does not have (a global, `typeof` of an absent name) cost one string comparison for
each of its names, on every read: a program from `js_of_ocaml` has one function with thousands
of names around all of its code. The parser's list of `var` names had the same cost for each
declaration and each block (`P.addVar`, `parseBlock`). These scripts check the answers; the times
are in `docs/designissues/2026-11-09-foafnaut-perf-exploration.md`, section 6.6. -/

/-- `var v0 = 0; ... ` for `n` names. -/
def manyVars (n : Nat) : String :=
  String.join ((List.range n).map fun i => s!"var v{i} = {i};")

-- a global, a name of the large function, an absent name, from an inner function
#guard out ("(function () {" ++ manyVars 40 ++
    "function f() { return Math.abs(-3) + v7 + (typeof nothere === 'undefined' ? 1 : 0) }" ++
    "print(f(), v39, typeof v40) })()") == ["11 39 undefined"]
-- a name of the large function hides a global; an assignment from an inner function reaches it
#guard out ("(function () {" ++ manyVars 30 ++
    "var Math = { abs: function () { return 'mine' } }; function g() { v3 = 'w'; return Math.abs(1) }" ++
    "print(g(), v3, v29) })()") == ["mine w 29"]
-- the same name twice, a block with its own declarations, a function declared after its use
#guard out ("function big() {" ++ manyVars 30 ++ manyVars 3 ++
    "{ let v1 = 'inner'; var late = v1 + after() } function after() { return v2 } return late + v1 }" ++
    "print(big())") == ["inner21"]
-- at the top level of a script
#guard out (manyVars 30 ++ "function h() { return v28 + (typeof zz) } print(h())") == ["28undefined"]

end L4Factoidal.JS.Tests
