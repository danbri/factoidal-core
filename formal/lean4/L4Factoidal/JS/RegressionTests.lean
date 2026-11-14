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

/-! ## String append in compiled code

`s += t` in a compiled function or loop: the register lets go of the string before the append,
so the append is in place when nothing else holds the string (`vmLoop`, `.add`). Before
2026-11-10 the register machine copied the string at each append (400,000 appends: 1.86 s; the
evaluator: 0.13 s). These scripts check that a second holder of the string keeps its value. -/

#guard out "function f(n) { var s = ''; for (var i = 0; i < n; i++) { s += 'ab'; } return s.length } print(f(1000))" == ["2000"]
#guard out "function g(n) { var s = 'x', t = s; for (var i = 0; i < n; i++) { s += i; } return t + '|' + s } print(g(5))" == ["x|x01234"]
#guard out "function h() { var s = 'a'; s += s; s += s; return s } print(h())" == ["aaaa"]
#guard out "function k(n) { var a = []; var s = ''; for (var i = 0; i < n; i++) { s += 'q'; a.push(s) } return a.join() } print(k(3))" == ["q,qq,qqq"]
#guard out "var s = ''; for (var i = 0; i < 4; i++) { s += i + ',' } print(s)" == ["0,1,2,3,"]
#guard out "function m() { var s = '\\uD83D'; s += '\\uDE00'; return s.length + ':' + s.codePointAt(0) } print(m())" == ["2:128512"]
#guard out "function p(n) { var s = '', u; for (var i = 0; i < n; i++) { u = s; s += 1.5; s += true; s += null; } return u + '>' + s } print(p(2))" == ["1.5truenull>1.5truenull1.5truenull"]
#guard out "function q(o) { var s = 'k'; for (var i = 0; i < 3; i++) { o.v = s; s += i } return o.v + ' ' + s } print(q({}))" == ["k01 k012"]

/-! ## Numeric separators and `Error.prototype.stack`

Found 2026-11-13 by the WPT `wasm/core` pages: every one of them failed on BubblePopJS. The
generated tests write numbers as `2_147_483_647` (ES2021 numeric separators, §12.9.3), which the
lexer refused, and the harness reads `new Error().stack.toString()`, which threw because errors
had no `stack`. `stack` is the accessor of the Error Stack Accessor proposal on
`Error.prototype`; its string lists call frames, and this engine records none, so it is empty
(QuickJS-NG and V8 print a frame list there; the scripts below print only what all agree on).
The last two scripts follow the proposal and its test262 tests (`built-ins/Error/prototype/stack`),
where V8 and QuickJS-NG differ: an own `stack` made by the setter is enumerable, and the setter
refuses a value that is not a string and refuses `Error.prototype` itself. -/

#guard out "print(1_000_000, 0x7f_ff, 0b1_0, 0o7_7, 1.5_5, 1e1_0, 10_0n)" == ["1000000 32767 2 63 1.55 10000000000 100"]
#guard out "print(-2_147_483_648 | 0, 0x1_0.toString(16))" == ["-2147483648 10"]
#guard out "var r = []; for (var t of ['1__0', '1_', '0_1', '1_.5', '1._5', '1_e5', '0x_1', '1_n']) { try { eval(t); r.push('ok') } catch (e) { r.push(e.name) } } print(r.join())" == ["SyntaxError,SyntaxError,SyntaxError,SyntaxError,SyntaxError,SyntaxError,SyntaxError,SyntaxError"]
#guard out "print(Number('1_0'), parseInt('1_0'))" == ["NaN 1"]
#guard out "print(typeof new Error('m').stack, typeof new TypeError().stack.toString(), Object.prototype.hasOwnProperty.call(new Error(), 'stack'))" == ["string string false"]
#guard out "var d = Object.getOwnPropertyDescriptor(Error.prototype, 'stack'); print(d.get.name, d.set.name, d.set.length, d.enumerable, d.configurable, d.get.call({}))" == ["get stack set stack 1 false true undefined"]
#guard out "var e = new Error('x'); e.stack = 's'; var d = Object.getOwnPropertyDescriptor(e, 'stack'); print(e.stack, d.writable, d.enumerable)" == ["s true true"]
#guard out "try { Error.prototype.stack = '' } catch (e) { print(e.name) } try { new Error().stack = 1 } catch (e) { print(e.name) }" == ["TypeError", "TypeError"]

/-! ## `charAt` and `charCodeAt` on a string that is not ASCII

They index the units that `cachedChars` keeps for the last string (2026-11-13), so a loop over
such a string is linear. These check the answers on supplementary characters, lone surrogates,
two strings in turn (the cache changes hands) and indices out of range. -/

#guard out "var s = 'a\\u00e9\\ud83d\\ude00\\ud800z', r = []; for (var i = -1; i <= s.length; i++) r.push(s.charCodeAt(i)); print(r.join())" == ["NaN,97,233,55357,56832,55296,122,NaN"]
#guard out "var s = '\\u00e9\\ud83d\\ude00', t = 'x\\u0101', r = ''; for (var i = 0; i < 3; i++) r += s.charAt(i).length + ':' + s.charCodeAt(i) + '/' + t.charCodeAt(i % 2) + ' '; print(r, s.charAt(1) + s.charAt(2) === '\\ud83d\\ude00', s.charAt(9) === '')" == ["1:233/120 1:55357/257 1:56832/120  true true"]
#guard out "var b = '\x00\x61\x73\x6d\x80\xff'.repeat(40), n = 0; for (var i = 0; i < b.length; i++) n += b.charCodeAt(i); print(b.length, n)" == ["240 28160"]
/-! ## JSON.parse and lone surrogate escapes

§25.5.1: JSON.parse reads code units, so `"\uD800"` parses to a string of one lone surrogate.
Before 2026-11-13 BubblePopJS used RFC 8259's strict parser alone and threw "Unexpected token in
JSON at position 0" for every text with one such escape (WPT `url/resources/urltestdata-javascript-only.json`,
about 9,000 subtests of `url/`). -/

#guard out "var v = JSON.parse('[\"\\\\uD800\", \"a\\\\uDFFFb\"]'); print(v[0].length, v[0].charCodeAt(0), v[1].length, v[1].charCodeAt(1))" == ["1 55296 3 57343"]
#guard out "var v = JSON.parse('\"\\\\uD83D\\\\uDE00\"'); print(v.length, v.codePointAt(0))" == ["2 128512"]
#guard out "var v = JSON.parse('{\"\\\\uD800k\": \"\\\\uDBFC\\\\uDC00\"}'); var k = Object.keys(v)[0]; print(k.length, k.charCodeAt(0), v[k].length, v[k].charCodeAt(1))" == ["2 55296 2 56320"]
#guard out "try { JSON.parse('[1,'); } catch (e) { print(e.name) }" == ["SyntaxError"]
#guard out "try { JSON.parse('\"\\\\uZZZZ\"'); } catch (e) { print(e.name) }" == ["SyntaxError"]

/-! ## Position arguments of `startsWith`, `endsWith`, `includes` and `lastIndexOf`

§22.1.3.24, §22.1.3.7, §22.1.3.8, §22.1.3.11. Before 2026-11-14 the four methods ignored their
second argument. WPT's `resources/webidl2.js` finds each punctuation token with
`str.startsWith(punctuation, lastCharIndex)`, so no IDL file parsed ("Unrecognised tokens") and
every `idlharness` test of WPT (39,327 Chrome subtests) failed at setup. -/

#guard out "print('a[b'.startsWith('[', 1), 'abc'.startsWith('b'), 'abc'.startsWith('c', 9), 'abc'.startsWith('', 9))" == ["true false false true"]
#guard out "print('abc'.endsWith('b', 2), 'abc'.endsWith('c', 2), 'abc'.endsWith('abc'), 'abc'.endsWith('', 0), 'abc'.endsWith('abcd'))" == ["true false true true false"]
#guard out "print('abc'.includes('a', 1), 'abc'.includes('c', 2), 'abc'.includes('a'), 'abc'.includes('', 9))" == ["false true true true"]
#guard out "print('canal'.lastIndexOf('a', 2), 'canal'.lastIndexOf('a'), 'canal'.lastIndexOf('a', 0), 'canal'.lastIndexOf('', 9), 'canal'.lastIndexOf('c', -5), 'canal'.lastIndexOf('x'))" == ["1 3 -1 5 0 -1"]
#guard out "var s = 'x\\u00e9\\ud83d\\ude00z'; print(s.startsWith('\\ude00z', 3), s.startsWith('z', 4), s.endsWith('\\ud83d', 3), s.lastIndexOf('\\ude00', 9))" == ["true true true 3"]

/-! ## A sticky match that fails, and a short string between two matches

A sticky regular expression is tried at `lastIndex` only, so a failed match takes one step, not
the steps of the rest of the subject; and a match on a short string (under `cachedCharsMin`
bytes) leaves the decoded long subject in place. The tokeniser of `webidl2.js` does both for
every token: `html.idl` (109 KB) took over 5 M steps and tens of seconds, and takes about 1 M
steps now. The first script fails 20,000 sticky matches on a 64 KB subject inside a budget of
200,000 steps (each failure took 1,000 steps before). -/

#guard outWith 200000 "var s = 'a'.repeat(64000) + 'b', re = /b/y, n = 0; for (var i = 0; i < 20000; i++) { re.lastIndex = i; if (!re.test(s)) n++; } re.lastIndex = 64000; print(n, re.test(s), re.lastIndex)" == ["20000 true 64001"]
#guard out "var s = 'a'.repeat(300) + 'b', re = /b/y, r = []; for (var i = 299; i < 302; i++) { re.lastIndex = i; r.push(/[ab]/.test(s.charAt(i)), re.test(s), re.lastIndex); } print(r.join())" == ["true,false,0,true,true,301,false,false,0"]

/-! ## `new` on a Proxy

§10.5.13: a Proxy whose target is a constructor is a constructor; `new` calls its `construct`
trap, or constructs the target when the handler has none. Before 2026-11-14 `new` on any Proxy
threw "is not a constructor", so the IsConstructor check of WPT's `idlharness.js`
(`new (new Proxy(o, {construct: () => ({})}))`) failed for every interface. -/

#guard out "function F() { this.b = 2; } var P = new Proxy(F, { construct: function (t, args, nt) { return { a: args.length, same: t === F }; } }); var p = new P(7, 8); print(p.a, p.same); var Q = new Proxy(F, {}); var q = new Q(); print(q.b, q instanceof F)" == ["2 true", "2 true"]
#guard out "try { new (new Proxy({}, {})); } catch (e) { print(e.name) } try { new (new Proxy(function () {}, { construct: function () { return 1; } })); } catch (e) { print(e.name) }" == ["TypeError", "TypeError"]

/-! ## A host's named properties of the global object

`namedGlobal`: a name with no binding, and a property that the global object and its prototype
chain do not have, are asked of the function in the global's internal slot (`namedGetterKey`,
a private-name key that no reflection lists). A page's function answers with the named
properties of the Window object (HTML §7.3.3). Here a script plays the host. With no such
function nothing changes: the last script. -/

/-- `out` on a realm whose global `host` has the engine's `setNamedGetter`, as a page host's
natives object has (the slot's key is a private-name key: no String key of a script is it). -/
private def outHost (src : String) : List String :=
  let (nobj, h) := hostObject freshHeap #[]
  let h := addNatives h nobj #[("setNamedGetter", .x .namedGetterSet, 1)]
  let ((_, f), h) := evalValue h "(function (n) { globalThis.host = n })"
  let (_, h) := callFunction h f .undef #[nobj]
  match runScript h src with
  | (.ok, h) => h.out.toList
  | (.threw _ m, h) => h.out.toList ++ ["Uncaught " ++ m]
  | (.syntaxError m, _) => [m]
  | (.halted w, _) => ["halted " ++ w]

#guard outHost "host.setNamedGetter(function (name) { return name === 'foo' ? 42 : undefined; }); print(typeof foo, foo, globalThis.foo, typeof bar, globalThis.bar); try { bar } catch (e) { print(e.name) } print(Object.getOwnPropertyNames(globalThis).some(function (k) { return k.indexOf('WindowNamed') >= 0; }))" == ["number 42 42 undefined undefined", "ReferenceError", "false"]
-- a declared name shadows a named property
#guard outHost "host.setNamedGetter(function (name) { return 42; }); var foo; print(typeof foo, foo); foo = 5; print(foo, globalThis.foo)" == ["undefined undefined", "5 5"]
#guard out "print(typeof nothing, globalThis.nothing); try { nothing } catch (e) { print(e.name) }" == ["undefined undefined", "ReferenceError"]
-- a script cannot set the slot: its String key is not the slot's key (`strKey_not_priv`)
#guard out "Object.defineProperty(globalThis, '\\u{10FFFE}WindowNamedProperties', { value: function (name) { return 42; } }); print(typeof foo, globalThis.foo)" == ["undefined undefined"]
/-! ## `for await` (§14.7.5)

The parser reads `for await (x of e) body` as statements the evaluator already runs
(`forAwaitStmt`): GetIterator with the async hint, `next` called and awaited each turn, and
AsyncIteratorClose on an abrupt end of the body. Before 2026-11-14 it was a SyntaxError, and
the 1,140 Test262 pages of `language/statements/for-await-of` that are not negative tests never
finished (they were counted as timeouts). -/

-- an async generator, a sync iterable of promises (async-from-sync, §27.1.6), an array
#guard out "async function* g() { yield 1; yield 2 } async function f() { var s = 0; for await (const x of g()) s += x; for await (var y of [Promise.resolve(3), 4]) s += y; return s } f().then(print)" == ["10"]
-- `break` closes the iterator: `return` is called once, and awaited
#guard out "var log = []; var it = { [Symbol.asyncIterator]() { return this }, next() { return Promise.resolve({ value: 1, done: false }) }, return() { log.push('ret'); return Promise.resolve({}) } }; async function f() { for await (const x of it) { log.push(x); break } log.push('after') } f().then(() => print(log.join()))" == ["1,ret,after"]
-- a throw in the body closes the iterator, drops what `return` throws, and keeps the error
#guard out "var it = { [Symbol.asyncIterator]() { return this }, next() { return { value: 1, done: false } }, return() { throw new Error('dropped') } }; async function f() { for await (const x of it) throw new TypeError('kept') } f().catch(e => print(e.name, e.message))" == ["TypeError kept"]
-- the iterator is not closed when it ends, or when `next` rejects
#guard out "var n = 0; var it = { [Symbol.asyncIterator]() { return this }, next() { return Promise.reject(7) }, return() { n++; return {} } }; async function f() { for await (const x of it) ; } f().catch(e => print(e, n))" == ["7 0"]
-- a result that is not an Object is a TypeError; `continue` and a label; destructuring; assignment targets
#guard out "var it = { [Symbol.asyncIterator]() { return this }, next() { return 1 } }; async function f() { for await (const x of it) ; } f().catch(e => print(e.name))" == ["TypeError"]
#guard out "async function f() { var r = []; outer: for await (const [a, b] of [[1, 2], [3, 4], [5, 6]]) { for (const k of [0, 1]) { if (a == 3) continue outer; if (a == 5) break outer; r.push(a + b + k) } } var o = {}; for await (o.p of [8]) r.push(o.p); return r.join() } f().then(print)" == ["3,4,8"]
-- two labels on one loop (`continue` to either continues it), on `for await` and on `for`
#guard out "var log = []; async function f() { A: B: for await (const x of [1, 2, 3]) { for (const y of [7]) { log.push(x); if (x == 1) continue A; if (x == 2) continue B; break A } log.push('no') } } f().then(() => print(log.join()))" == ["1,2,3"]
#guard out "var log = []; A: B: for (const x of [1, 2, 3]) { for (const y of [7]) { log.push(x); if (x == 1) continue A; if (x == 2) continue B; break A } log.push('no') } print(log.join()); try { eval('A: B: { continue A; }') } catch (e) { print(e.name) }" == ["1,2,3", "SyntaxError"]
-- in an async generator; the loop variable is new for each turn
#guard out "async function* g() { var fs = []; for await (let x of [1, 2]) { fs.push(() => x); yield x * 10 } yield fs.map(h => h()).join() } async function f() { var r = []; for await (const v of g()) r.push(v); return r.join('|') } f().then(print)" == ["10|20|1,2"]
-- not a statement outside an async function; `of` is needed; the helpers are not names of the language
#guard out "var r = []; for (var t of ['function f() { for await (x of y) ; }', 'async function f() { for await (x in y) ; }', 'async function f() { for await (;;) ; }']) { try { eval(t); r.push('ok') } catch (e) { r.push(e.name) } } print(r.join())" == ["SyntaxError,SyntaxError,SyntaxError"]
#guard out "print(Object.getOwnPropertyNames(globalThis).filter(k => /forAwait|AsyncFromSync/.test(k)).length, Reflect.ownKeys(globalThis).filter(k => typeof k == 'string' && k.charCodeAt(0) > 0xD7FF).length)" == ["0 0"]

/-! ## Property keys of strings that start with a reserved character

A key is a Lean `String`; U+10FFFF starts a Symbol's key and U+10FFFE a private name's.
Before 2026-11-14 a String value was its own key, so `o["\u{10FFFE}x"]` read the private
member `#x`, and `o["\u{10FFFF}0"]` the property of `Symbol.iterator`. ToPropertyKey of a
String now puts U+10FFFD before a string that starts with one of the three (`strKey`);
listings of keys take it off (`keyStr`). Theorems: `strKey_injective` and the others in
`JS/Theorems.lean`. WPT `wasm/core/names.wast` (480 subtests) has an export name that starts
with U+10FFFE. -/

#guard out "class A { #x = 1; static has(o) { return #x in o } } var a = new A(); print(A.has(a), A.has({}), a['\\u{10FFFE}x'], '\\u{10FFFE}x' in a, Object.keys(a).length)" == ["true false undefined false 0"]
#guard out "var o = {}; var k = '\\u{10FFFE}x', s = '\\u{10FFFF}0', m = '\\u{10FFFD}q'; o[k] = 1; o[s] = 2; o[m] = 3; print(Object.keys(o).map(x => x.length + ':' + x.codePointAt(0).toString(16)).join(), o[k], o[s], o[m], k in o, o.hasOwnProperty(s), JSON.stringify(o) === JSON.stringify({[k]: 1, [s]: 2, [m]: 3}), Object.getOwnPropertySymbols(o).length, Reflect.ownKeys(o).length)" == ["3:10fffe,3:10ffff,3:10fffd 1 2 3 true true true 0 3"]
#guard out "var o = {'\\u{10FFFE}a': 1, '\\u{10FFFF}1': 2}; var r = []; for (var k in o) r.push(k.codePointAt(0).toString(16) + k.slice(2)); print(r.join(), Object.entries(o).map(e => e[0].length + '=' + e[1]).join(), Object.getOwnPropertyNames(o).length); var p = JSON.parse(JSON.stringify(o)); print(Object.keys(p).length, p['\\u{10FFFE}a'], p['\\u{10FFFF}1'], Object.getOwnPropertySymbols(p).length)" == ["10fffea,10ffff1 3=1,3=2 2", "2 1 2 0"]
#guard out "var o = {}; o[Symbol.iterator] = 5; print(o['\\u{10FFFF}0'], Object.keys(o).length, globalThis['\\u{10FFFE}forAwait0'], '\\u{10FFFE}forAwait0' in globalThis)" == ["undefined 0 undefined false"]
#guard out "var f = {['\\u{10FFFE}n']() {}}; var g = Object.values(f)[0]; print(g.name.length, g.name.codePointAt(0).toString(16)); var {['\\u{10FFFE}n']: h} = f; print(typeof h); var d = Object.getOwnPropertyDescriptors({'\\u{10FFFD}z': 1}); print(Object.keys(d)[0].length, d['\\u{10FFFD}z'].value)" == ["3 10fffe", "function", "3 1"]
#guard out "var m = new Map([['\\u{10FFFE}k', 1]]); var o = Object.fromEntries(m); print(o['\\u{10FFFE}k'], Object.keys(o)[0] === '\\u{10FFFE}k', Object.keys(Object.assign({}, o))[0] === '\\u{10FFFE}k', Object.keys({...o})[0] === '\\u{10FFFE}k')" == ["1 true true true"]
-- a name of source text does not start with a reserved character
#guard out "try { eval('var \\u{10FFFE}forAwait0 = 1') } catch (e) { print(e.name) } try { eval('var o = {}; o.\\u{10FFFE}x') } catch (e) { print(e.name) }" == ["SyntaxError", "SyntaxError"]

/-! ## A promise resolved with a thenable through its resolve function

§27.2.2.2 NewPromiseResolveThenableJob makes a new pair of resolving functions with its own
[[AlreadyResolved]] record. Before 2026-11-14 the pair read the promise's own flag, which the
first call of `resolve` had already set, so `new Promise(r => r(otherPromise))` stayed pending
for ever (Test262's `assert.throwsAsync` is written that way). -/

#guard out "var res; var p = new Promise(r => res = r); res(Promise.resolve(3)); res(9); p.then(v => print('a', v)); print('s')" == ["s", "a 3"]
#guard out "var p = new Promise(r => { r({ then(f, g) { f(4); f(5); g(6) } }) }); p.then(v => print('d', v), e => print('e', e))" == ["d 4"]
#guard out "var p = new Promise(r => r(Promise.reject(new Error('no')))); p.then(v => print('f', v), e => print('r', e.message))" == ["r no"]
#guard out "var p = new Promise(function (resolve) { resolve(Promise.resolve(1).then(v => new Promise(r2 => r2(Promise.resolve(v + 1))))) }); p.then(v => print('chain', v))" == ["chain 2"]

/-! ## Async generators: `yield` awaits, `return` awaits, `yield*` delegates to an async iterator

§27.6.3.8 AsyncGeneratorYield awaits the operand of `yield`; §14.10.1 `return e` awaits `e`;
§15.5.5 `yield*` uses GetIterator with the async hint and awaits each result of the inner
iterator's `next`, `throw` and `return`; a `return(v)` request awaits `v`. Before 2026-11-14 a
yielded promise was given to the consumer as it was, `return await x` was a ReferenceError,
and `yield*` used the sync iterator. A `yield` whose operand holds an `await` or a `yield` is
lifted (`liftStmt`). -/

#guard out "async function* g() { yield Promise.resolve(1); try { yield Promise.reject(new Error('r')) } catch (e) { yield 'caught ' + e.message } return Promise.resolve(9) } async function f() { var it = g(), r = []; for (var i = 0; i < 4; i++) { var x = await it.next(); r.push(x.value + ':' + x.done) } return r.join() } f().then(print)" == ["1:false,caught r:false,9:true,undefined:true"]
#guard out "async function* inner() { try { var x = yield 1; yield x * 2 } finally { print('inner done') } } async function* outer() { var r = yield* inner(); yield 'after ' + r } async function f() { var it = outer(); var a = await it.next(); var b = await it.next(21); var c = await it.return(7); return [a.value, b.value, c.value, c.done].join() } f().then(print)" == ["inner done", "1,42,7,true"]
#guard out "async function* g() { yield* [Promise.resolve(1), 2] } async function f() { var r = []; for await (const v of g()) r.push(v); return r.join() } f().then(print)" == ["1,2"]
#guard out "var it = { [Symbol.asyncIterator]() { return this }, next(v) { return { value: v, done: false } }, throw(e) { return Promise.resolve({ value: 'threw ' + e, done: true }) } }; async function* g() { var r = yield* it; yield r } async function f() { var o = g(); await o.next(); var a = await o.next(5); var b = await o.throw('x'); return a.value + ',' + b.value } f().then(print)" == ["5,threw x"]
#guard out "async function* g() { var a = yield await Promise.resolve(1); var b = await (yield a + 1); return await b } async function f() { var it = g(); var x = await it.next(); var y = await it.next(10); var z = await it.next(Promise.resolve(30)); return [x.value, y.value, z.value, z.done].join() } f().then(print)" == ["1,11,30,true"]
#guard out "async function* g() { yield 1 } async function f() { var it = g(); var a = await it.return(Promise.resolve(5)); var b = await it.return(Promise.reject(6)).catch(e => 'rej ' + e); return a.value + ',' + a.done + ',' + b } f().then(print)" == ["5,true,rej 6"]

/-! ## A dense array is not grown past `maxDenseArray`

Arrays hold a value for each element. `a.length = 4294967295` asked for 32 GiB and the engine's
process was killed (Test262 `harness/propertyhelper-verifywritable-array-length`). It is a
RangeError now, as is `new Array(n)` past the limit; growth within the limit takes steps. -/

#guard out "var a = [1, 2, 3]; try { a.length = 4294967295 } catch (e) { print(e.name) } print(a.length); try { new Array(4294967295) } catch (e) { print(e.name) } a.length = 5; print(a.length, a[4]); a.length = 1; print(a.join())" == ["RangeError", "3", "RangeError", "5 undefined", "1"]

/-! ## Scripts that a swallowed SyntaxError had hidden

Until 2026-11-14 a page script that did not parse was not reported at the window, so a Test262
page whose script the parser refused was counted as passing when it expected no error. With the
report in place (`Session.eval`), 349 such pages failed; these are their causes that are now
language features: a function declared in a block (Annex B.3.3, B.3.4), `super.x = v`
(§13.3.7), a call as an assignment target in code that is not strict (a ReferenceError when it
runs, §13.15.1 with the web's exception), a Hashbang comment (§12.5), and `import()` in a
script (§13.3.10: a promise, rejected while no host loads modules for scripts). -/

-- Annex B.3.3.1: the `var` binding gets the function when the declaration is evaluated
#guard out "print(typeof f); { print(typeof f); function f() { return 1 } } print(typeof f, f()); if (true) function g() { return 2 } print(g()); (function () { var r = [typeof h]; { function h() {} } r.push(typeof h); let k = 1; { function k() {} } r.push(typeof k); print(r.join()) })()" == ["undefined", "function", "function 1", "2", "undefined,function,number"]
#guard out "'use strict'; { function f() {} } print(typeof f)" == ["undefined"]
#guard out "switch (1) { case 1: function s() { return 's' } } print(s()); function outer() { if (0) { function inner() {} } return typeof inner } print(outer()); for (let q of [1]) { function q() {} } print(typeof q)" == ["s", "undefined", "undefined"]
-- a super reference as a target: the receiver of the [[Set]] is `this`
#guard out "class A { get x() { return 1 } set x(v) { this.log = 'set ' + v } } class B extends A { f() { super.x = 5; super.y = 7; super['z'] = 8; var a = [super.x, this.y, this.z, this.log, this.hasOwnProperty('y')]; [super.w] = [9]; a.push(this.w); return a.join() } } print(new B().f())" == ["1,7,8,set 5,true,9"]
#guard out "var o = { __proto__: { v: 1 }, f() { super.v++; return [super.v, this.v, Object.keys(this).join('+')].join() } }; print(o.f())" == ["1,2,f+v"]
-- a call as a target: evaluated once, then a ReferenceError; an early error in strict code and in a pattern
#guard out "var n = 0; function f() { n++ } try { f() = 1 } catch (e) { print(e.name, n) } try { f()++ } catch (e) { print(e.name, n) } try { f() += 1 } catch (e) { print(e.name, n) } try { for (f() in {a: 1}) ; } catch (e) { print(e.name, n) } try { eval('\"use strict\"; f() = 1') } catch (e) { print(e.name) } try { eval('[f()] = []') } catch (e) { print(e.name) }" == ["ReferenceError 1", "ReferenceError 2", "ReferenceError 3", "ReferenceError 4", "SyntaxError", "SyntaxError"]
-- a Hashbang comment at the start; `import()` answers a promise and is not a name of the global object
#guard out "#!/usr/bin/env node\nprint(1)" == ["1"]
#guard out "var p = import('./x.js'); print(p instanceof Promise); p.catch(e => print(e.name)); import({ toString() { throw new RangeError('s') } }).catch(e => print(e.name)); print(typeof globalThis['%import'], Object.getOwnPropertyNames(globalThis).filter(k => /import/.test(k)).length)" == ["true", "undefined 0", "TypeError", "RangeError"]

/-! ## Early errors of classes, async functions and generators (§15.7.1, §15.8.1, §15.5.1)

Negative Test262 pages that the parser accepted until 2026-11-14 (the largest group left once
parse errors were reported). -/

private def syn (src : String) : String :=
  match parseScript src with | .ok _ => "ok" | .error _ => "SyntaxError"

-- `await` and `yield` as names where they are operators; `let` and `yield` in strict code
#guard ["async function f() { var await }", "async function f() { await: ; }", "async function f() { void \\u0061wait }",
  "function* g() { void yield }", "function* g() { yield: ; }", "'use strict'; var yield", "'use strict'; yield: ;",
  "'use strict'; let = 1"].map syn == List.replicate 8 "SyntaxError"
#guard ["var await = 1; await: ;", "var yield = 1; void yield", "function f() { var await, yield; return await + yield }",
  "var let = 1; let"].map syn == List.replicate 4 "ok"
-- `arguments` and `super()` in a field initialiser or a static block; an arrow function keeps the rule
#guard ["class C { x = arguments }", "class C { static { arguments } }", "class C { x = () => arguments }",
  "class C extends Object { x = super() }", "class C extends Object { static { super() } }"].map syn ==
  List.replicate 5 "SyntaxError"
#guard ["class C { x = function () { return arguments } }", "class C { m() { return arguments } }",
  "class C extends Object { constructor() { super() } }", "class C { x = 1; static { var a = 1 } }"].map syn ==
  List.replicate 4 "ok"
-- private names: declared once, used only inside a class that declares them, not deleted
#guard ["class C { #x; #x }", "class C { #x() {} get #x() { return 1 } }", "class C { m() { this.#y } }",
  "var o = {}; o.#x", "class C { #x; m() { delete this.#x } }", "class C { #x; m() { delete (this.#x) } }",
  "class C { #x; m() { delete this?.#x } }"].map syn == List.replicate 7 "SyntaxError"
#guard ["class C { get #x() { return 1 } set #x(v) {} }", "class C { #x; m() { class D { n(o) { return o.#x } } } }",
  "class C { #x = 1; static has(o) { return #x in o } }"].map syn == List.replicate 3 "ok"
#guard out "class C { #x = 7; m() { return eval('this.#x') } } print(new C().m()); try { eval('var o = {}; o.#q') } catch (e) { print(e.name) }" == ["7", "TypeError"]
-- a "use strict" directive needs simple parameters
#guard ["function f(a = 1) { 'use strict' }", "function f([a]) { 'use strict' }", "function f(...a) { 'use strict' }",
  "(a = 1) => { 'use strict' }"].map syn == List.replicate 4 "SyntaxError"
#guard syn "function f(a, b) { 'use strict' }" == "ok"

/-! ## Built-ins that were missing: `Symbol.for`, `String.raw`, WeakRef, FinalizationRegistry, `getOrInsert`

`Symbol.for` is how libraries share a symbol across bundles (React's element type is
`Symbol.for('react.element')`); it was "for is not a function". The heap has no collector, so a
WeakRef's target is never collected and a FinalizationRegistry never calls back. -/

#guard out "var a = Symbol.for('app.x'), b = Symbol.for('app.x'), c = Symbol('app.x'); print(a === b, a === c, Symbol.keyFor(a), Symbol.keyFor(c), a.description, typeof a, a.toString()); try { Symbol.keyFor('x') } catch (e) { print(e.name) } var o = { [a]: 1 }; print(o[Symbol.for('app.x')], Symbol.for.length, Symbol.keyFor.name)" == ["true false app.x undefined app.x symbol Symbol(app.x)", "TypeError", "1 1 keyFor"]
#guard out "print(String.raw`a\\n${1 + 1}b\\t${'c'}`, String.raw({ raw: ['x', 'y', 'z'] }, 0, 1, 2), String.raw({ raw: 'abc' }, '-', '+'), String.raw.length)" == ["a\\n2b\\tc x0y1z a-b+c 1"]
#guard out "var t = {}; var w = new WeakRef(t); print(w.deref() === t, Object.prototype.toString.call(w), typeof WeakRef.prototype.deref); try { new WeakRef(1) } catch (e) { print(e.name) } try { WeakRef(t) } catch (e) { print(e.name) } var fr = new FinalizationRegistry(() => {}); var tok = {}; print(fr.register(t, 'held', tok), fr.unregister(tok), fr.unregister(tok), Object.prototype.toString.call(fr)); try { fr.register(t, t) } catch (e) { print(e.name) } try { new FinalizationRegistry(1) } catch (e) { print(e.name) }" == ["true [object WeakRef] function", "TypeError", "TypeError", "undefined true false [object FinalizationRegistry]", "TypeError", "TypeError"]
#guard out "var m = new Map([[1, 'a']]); print(m.getOrInsert(1, 'x'), m.getOrInsert(2, 'b'), m.getOrInsertComputed(3, k => 'k' + k), m.getOrInsertComputed(3, k => 'no'), m.size, [...m.keys()].join()); var wm = new WeakMap(), k = {}; print(wm.getOrInsert(k, 5), wm.getOrInsertComputed(k, () => 6)); try { wm.getOrInsert(1, 2) } catch (e) { print(e.name) } try { Map.prototype.getOrInsert.call(new Set, 1, 2) } catch (e) { print(e.name) }" == ["a b k3 k3 3 1,2,3", "5 5", "TypeError", "TypeError"]

/-! ## No string past `maxStringBytes`

A script could make the engine allocate without bound: `s += s` in a loop doubles a string at
one step a turn, and `replace` with `$1` multiplies a match (Test262
`staging/sm/String/replace-math` asks for 2^36 units; the WPT runner's process ended in the
middle of that page on 2026-11-14). Concatenation, templates, `join`, `concat` and `replace` now
ask `checkStrLen` first and throw a RangeError, as `repeat` and `padStart` did; `repeat` builds
by doubling, not from a list of its parts. -/

#guard out "var s = 'x'; try { while (true) s += s } catch (e) { print(e.name, s.length) } try { var t = 'ab'; for (var i = 0; i < 40; i++) t = t + t } catch (e) { print(e.name, t.length) }" == ["RangeError 268435456", "RangeError 268435456"]
#guard out "function puff(x, n) { while (x.length < n) x += x; return x.substring(0, n); } var x = puff('1', 1 << 16); var rep = puff('$1', 1 << 14); try { var y = x.replace(/(.+)/g, rep); print(y.length) } catch (e) { print(e.name, e.message) }" == ["RangeError Invalid string length"]
#guard out "var big = 'y'.repeat(1 << 22); var r = []; for (var f of [() => new Array(128).fill(big).join(''), () => big.concat(...new Array(100).fill(big)), () => { var a = `${big}${big}`; for (var i = 0; i < 7; i++) a = `${a}${a}`; return a }, () => big.replace(big, '$&'.repeat(100))]) { try { f(); r.push('made') } catch (e) { r.push(e.name) } } print(r.join())" == ["RangeError,RangeError,RangeError,RangeError"]
#guard out "print('abc'.replace('b', '[$&$&]'), 'a-b'.replace(/(\\w)-(\\w)/, '$2$1$&'), 'abc'.repeat(3), 'x'.padStart(7, 'ab'), 'x'.padEnd(6, '-'), ''.repeat(5).length, [1, 2].join('-'), 'a'.concat('b', 1))" == ["a[bb]c baa-b abcabcabc abababx x----- 0 1-2 ab1"]
#guard repeatStr "ab" 0 == "" && repeatStr "ab" 1 == "ab" && repeatStr "ab" 5 == "ababababab" && repeatStr "" 9 == ""

/-! ## `Reflect.set` with a receiver; receivers of `getOrInsert`; `arguments` in a class body

`Reflect.set(target, key, value, receiver)` (§10.1.9.2 OrdinarySetWithOwnDescriptor): a setter
found on the target is called with the receiver as `this`, and a data property is made on the
receiver (through a Proxy receiver's `defineProperty` trap, or its target). It used the target
for both, so a Proxy `set` trap that forwards with `Reflect.set` lost the proxy.
`WeakMap.prototype.getOrInsert` took a Map and `Map.prototype.getOrInsert` a WeakMap.
`arguments` in the parameters of a method or function inside a static block is that function's
own and no early error (§15.7.1 forbids it in the initialiser or block itself and its arrows). -/

#guard out "var t = { set x(v) { this.got = v } }, r = {}; print(Reflect.set(t, 'x', 1, r), r.got, t.got, Reflect.set(t, 'y', 2, r), r.y, t.y, Reflect.set(t, 'z', 3), t.z); var p = new Proxy(t, { set(tg, k, v, rc) { return Reflect.set(tg, k, v, rc) } }); p.x = 9; print(p.got, t.got); var fr = Object.freeze({ a: 1 }); print(Reflect.set({}, 'a', 2, fr), Reflect.set(Object.freeze({ q: 1 }), 'q', 2, {}), Reflect.set({ get g() { return 1 } }, 'g', 2, {}))" == ["true 1 undefined true 2 undefined true 3", "9 9", "false false false"]
#guard out "var log=[]; var p = new Proxy({}, { defineProperty(t,k,d){ log.push(k, d.value, Object.keys(d).join()); return Reflect.defineProperty(t,k,d) } }); print(Reflect.set({}, 'a', 5, p), p.a, log.join('|'))" == ["true 5 a|5|value,writable,enumerable,configurable"]
#guard out "function tt(f){ try { f(); return 'no' } catch (e) { return e.constructor.name } } print(tt(()=>WeakMap.prototype.getOrInsert.call(new Map, {}, 1)), tt(()=>Map.prototype.getOrInsertComputed.call(new WeakMap, {}, ()=>1)), new Map().getOrInsert(1,2), new WeakMap().getOrInsertComputed({}, ()=>7))" == ["TypeError TypeError 2 7"]
#guard out "var m; class C { static { new class { method({a = m = arguments}) { } }().method({}); (function(){ m = arguments.length })(1,2) } } print(m)" == ["2"]
#guard (out "class C { static { arguments } }").head!.startsWith "SyntaxError"
#guard (out "class C { x = () => arguments }").head!.startsWith "SyntaxError"

/-! ## A full heap stops the script (`HeapOf.full`, `maxObjs`)

The heap has no collector, so a script that makes objects for ever grew until the operating
system ended the process (the WPT runner's processes ended with SIGKILL on pages that poll
through promises and timers). `tick` looks at the heap's size every 1024 steps, a call and a
`charge` every time: past `maxObjs` objects or environment records the run halts (not an
exception: `catch` does not see it), as at the end of the step budget. -/

/-- A script on a heap of at most `n` objects: how it ended, whether the heap stayed near the
limit, and how many lines it printed. -/
def onSmallHeap (n : Nat) (src : String) : String × Bool × Nat :=
  match runScript { freshHeap with maxObjs := n } src with
  | (.halted w, h) => (w, h.objs.size ≤ n + 3000, h.out.size)
  | (.ok, h) => ("ok", true, h.out.size)
  | (.threw _ m, h) => ("threw " ++ m, true, h.out.size)
  | (.syntaxError m, h) => (m, true, h.out.size)

#guard onSmallHeap 5000 "var a = []; for (;;) a.push({})" == (heapFullMsg, true, 0)
#guard onSmallHeap 5000 "function poll(i) { return new Promise(function (r) { r() }).then(function () { return poll(i + 1) }) } poll(0)" == (heapFullMsg, true, 0)
#guard onSmallHeap 5000 "var f = function () { return function () {} }; var k = []; for (;;) k.push(f())" == (heapFullMsg, true, 0)
#guard onSmallHeap 5000 "try { var a = []; for (;;) a.push({}) } catch (e) { print('caught') } print('after')" == (heapFullMsg, true, 0)
-- a script that stays within the heap is not touched
#guard onSmallHeap 5000 "var n = 0; for (var i = 0; i < 100000; i++) n += i; print(n)" == ("ok", true, 1)

/-! ## `?.` before a digit; a regular expression inside a template's substitution

§12.8: `?.` is the optional chaining punctuator only when no decimal digit follows, so the
minified conditional `a?.5:1` is `a ? .5 : 1` (6 of 111 scripts of eight live sites did not
parse for it). The scan for the `}` of a template substitution took the `'` of a regular
expression literal for the start of a string: Test262's `harness/temporalHelpers.js` did not
parse ("unterminated string literal"), and with it 2,810 tests. -/

#guard out "var a = 8, o = { a: \"x'y\" }; print(a?.5:1, a ?.length, o?.a, a?.[0])" == ["0.5 undefined x'y undefined"]
#guard out "var o = { a: \"x'y\" }; print(`${o.a.replace(/'/g, \"\\\\'\")}|${ 6 / 2 }|${ [1, 2].map(x => x / 2).join('/') }|${ '}' }|${ /[/}]/.test('}') }|${ o.a.length / 3 / 1 }`)" == ["x\\'y|3|0.5/1|}|true|1"]
#guard out "var a = 8, g = 2; print(`${a / g}${a /g/ 1}`)" == ["44"]

/-! ## Redefining a property that is not configurable (§10.1.6.3)

A redefinition that changes nothing is accepted; one that would change a frozen value, the
enumerability, the kind or the functions of an accessor is a TypeError (`Desc.allowedOn`);
a new property on an object that is not extensible is a TypeError. Test262
`built-ins/Object/defineProperty`, `defineProperties`, `create`, `freeze`, `seal` and
`built-ins/Reflect`: 2,018 of 2,383 before, 2,243 after, none lost (local run). -/

#guard out "class C {} var r = []; function t(f) { try { f(); r.push('ok') } catch (e) { r.push(e.name) } } t(() => Object.defineProperty(C, 'prototype', { writable: false })); var o = {}; Object.defineProperty(o, 'x', { value: 1, writable: false, configurable: false }); t(() => Object.defineProperty(o, 'x', { value: 1 })); t(() => Object.defineProperty(o, 'x', { value: 2 })); t(() => Object.defineProperty(o, 'x', { writable: true })); t(() => Object.defineProperty(o, 'x', { enumerable: true })); t(() => Object.defineProperty(o, 'x', { get() {} })); t(() => Object.defineProperty(o, 'x', {})); t(() => Object.defineProperty(o, 'x', { configurable: true })); print(r.join())" == ["ok,ok,TypeError,TypeError,TypeError,TypeError,ok,TypeError"]
#guard out "var g = function () { return 1 }, o = {}, r = []; function t(f) { try { f(); r.push('ok') } catch (e) { r.push(e.name) } } Object.defineProperty(o, 'a', { get: g }); t(() => Object.defineProperty(o, 'a', { get: g })); t(() => Object.defineProperty(o, 'a', { get() {} })); t(() => Object.defineProperty(o, 'a', { value: 1 })); t(() => Object.defineProperty(o, 'a', { set: undefined })); var p = Object.preventExtensions({ k: 1 }); t(() => Object.defineProperty(p, 'n', { value: 1 })); t(() => Object.defineProperty(p, 'k', { value: 2 })); t(() => Object.defineProperty({}, 'z', { get: 1 })); t(() => Object.defineProperty({}, 'z', { get() {}, value: 1 })); var q = {}; Object.defineProperty(q, 'acc', { get: g, configurable: true }); Object.defineProperty(q, 'acc', { enumerable: true }); print(r.join(), p.k, typeof Object.getOwnPropertyDescriptor(q, 'acc').get, Object.keys(q).join())" == ["ok,TypeError,TypeError,ok,TypeError,ok,TypeError,TypeError 2 function acc"]

/-! ## %GeneratorFunction%, %AsyncGeneratorFunction%, %AsyncFunction% (§27.3, §27.4, §27.7) -/

#guard out "var GF = Object.getPrototypeOf(function* () {}), AGF = Object.getPrototypeOf(async function* () {}), AF = Object.getPrototypeOf(async function () {}); print(GF.prototype === Object.getPrototypeOf((function* () {}).prototype), AGF.prototype === Object.getPrototypeOf((async function* () {}).prototype), AF.prototype, Object.prototype.toString.call(async () => 1), Object.getPrototypeOf(GF) === Function.prototype, GF.constructor.name, Object.getPrototypeOf(GF.constructor) === Function, GF.prototype.constructor === GF, Object.getPrototypeOf(function () {}) === Function.prototype)" == ["true true undefined [object AsyncFunction] true GeneratorFunction true true true"]
#guard out "var GF = Object.getPrototypeOf(function* () {}).constructor; var g = new GF('a', 'yield a; yield a * 2'); print([...g(3)].join(), Object.getPrototypeOf(g) === GF.prototype, typeof g.prototype, g.name); var AF = Object.getPrototypeOf(async function () {}).constructor; AF('return 7')().then(v => print('af', v))" == ["3,6 true object anonymous", "af 7"]
#guard out "var AIP = Object.getPrototypeOf(Object.getPrototypeOf(async function* () {}).prototype); print(typeof AIP[Symbol.asyncIterator])" == ["function"]

/-! ## [[SetPrototypeOf]] and Object.prototype.__proto__ (§10.1.2, §10.4.7, B.2.2.1) -/

#guard out "var r = []; function t(f) { try { r.push(String(f())) } catch (e) { r.push(e.name) } } var a = {}, b = Object.create(a); t(() => Object.setPrototypeOf(a, b) === a); t(() => Reflect.setPrototypeOf(a, b)); t(() => Reflect.setPrototypeOf(Object.freeze({}), {})); t(() => Reflect.setPrototypeOf(Object.prototype, {})); t(() => Reflect.setPrototypeOf(Object.prototype, null)); t(() => Object.setPrototypeOf(1, null)); t(() => Object.setPrototypeOf(undefined, null)); t(() => Object.setPrototypeOf({}, 1)); var f = Object.preventExtensions({}); t(() => Object.setPrototypeOf(f, Object.prototype) === f); print(r.join())" == ["TypeError,false,false,false,true,1,TypeError,TypeError,true"]
#guard out "var d = Object.getOwnPropertyDescriptor(Object.prototype, '__proto__'); var o = {}, p = { x: 1 }; o.__proto__ = p; var q = Object.create(null); q.__proto__ = p; print(typeof d.get, typeof d.set, d.enumerable, d.configurable, o.x, Object.getPrototypeOf(o) === p, o.__proto__ === p, Object.keys(o).length, Object.keys(q).join(), (1).__proto__ === Number.prototype, d.set.name)" == ["function function false true 1 true true 0 __proto__ true set __proto__"]

/-! ## Redeclarations in a block and in a switch (§14.2.1, §14.12.1, B.3.2.4) -/

private def parses (src : String) : Bool := syn src == "ok"

#guard !parses "{ async function f() {} var f; }" && !parses "{ var f; function* f() {} }" && !parses "{ function f() {} async function f() {} }"
#guard !parses "switch (0) { case 1: function f() {} default: var f; }" && !parses "{ { var f; } function f() {} }"
#guard !parses "'use strict'; { function f() {} function f() {} }"
#guard parses "{ function f() {} function f() {} }" && parses "function g() { function f() {} var f; }" && parses "var f; function f() {}"
#guard parses "{ function f() {} } var f;" && parses "{ { function f() {} } let f; }" && parses "{ function f() { var f; } }"

/-! ## Class elements, private names, `super`, `new.target`, ImportCall and statement positions (early errors) -/

#guard !parses "class C { get constructor() {} }" && !parses "class C { *constructor() {} }" && !parses "class C { async constructor() {} }"
#guard !parses "class C { static prototype() {} }" && !parses "class C { static get prototype() {} }" && !parses "class C { constructor = 1 }" && !parses "class C { 'constructor' }"
#guard !parses "class C { static prototype = 1 }" && !parses "class C { static constructor = 1 }" && !parses "class C { #constructor() {} }"
#guard parses "class C { static constructor() {} constructor() {} static async *constructor() {} ['constructor'] = 1; static ['prototype'] = 2; prototype() {} }"
#guard !parses "class C { # x }" && !parses "class C { #x; m() { this.# x } }" && !parses "class C { #x; m() { # x in this } }" && parses "class C { #x; m() { return this.#x + (#x in this) } }"
#guard !parses "class C { m() { super() } }" && !parses "class C { constructor() { super() } }" && !parses "function f() { super.x }" && !parses "class C extends B { m() { super() } }"
#guard parses "class C extends B { constructor() { super(); (() => super())(); } m() { return super.m() } static s() { super.x } x = super.y; static { super.z } }"
#guard parses "var o = { m() { return super.x }, get g() { return super.y }, set s(v) { super.z = v }, *gen() { super.w } }"
#guard parses "class C extends B { constructor(a = super()) { } m(a = super.x) {} }"
#guard !parses "function f() { return () => super.x }" && !parses "var o = { m() { function g() { super.x } } }"
#guard !parses "new import('x')" && !parses "new import.defer('x')" && !parses "import('x') = 1" && !parses "import('x')++" && parses "import('x').then(f)"
#guard !parses "super()" && !parses "super.x" && !parses "new.target" && !parses "() => new.target" && parses "function f() { return () => new.target }"
#guard parses "class C { x = new.target; static { new.target } }" && !parses "function f(a = super()) {}"
#guard !parses "while (0) function f() {}" && !parses "if (1) async function f() {}" && parses "if (1) function f() {}" && !parses "for (;;) async function* g() {}"
#guard parses "function f(a = new.target) {}" && parses "var o = { m(a = super.x) {} }" && !parses "function f(a = super.x) {}"
#guard !parses "class C { g\\u0065t x() {} }" && !parses "class C { st\\u0061tic m() {} }" && !parses "class C { \\u0061sync m() {} }" && parses "class C { 'get'; x() {} }"
#guard !parses "class yield {}" && !parses "var C = class static {}" && !parses "class let {}" && parses "class C {} var yield;"
#guard !parses "({ get x(a) {} })" && !parses "({ set x() {} })" && !parses "({ set x(...a) {} })" && !parses "class C { get x(a = 1) {} }" && parses "({ get x() {}, set x([a]) {} })"
#guard !parses "'use strict'; ({ public })" && !parses "function* g() { ({ yield }) }" && !parses "async function f() { ({ await }) }" && parses "var public = 1; ({ public })"

/-! ## ValidateTypedArray and the %TypedArray%.prototype methods of their own (§23.2.3) -/

#guard out "var r = []; function t(f) { try { r.push(String(f())) } catch (e) { r.push(e.name) } } var u = new Uint8Array([1, 2, 3]); var TP = Object.getPrototypeOf(Uint8Array.prototype); t(() => TP.forEach === Array.prototype.forEach); t(() => TP[Symbol.iterator] === TP.values); t(() => u.join('-')); t(() => [...u.keys()].join()); t(() => TP.forEach.call([1], x => x)); u.buffer.transfer(); t(() => u.join()); t(() => u.at(0)); t(() => u.fill(1)); t(() => u.set([])); t(() => u.subarray(0).length); t(() => TP.values.length); print(r.join())" == ["false,true,1-2-3,0,1,2,TypeError,TypeError,TypeError,TypeError,TypeError,TypeError,0"]

/-! ## Proxy traps: defineProperty, getPrototypeOf, setPrototypeOf, isExtensible, preventExtensions (§10.5) -/

#guard out "var log = [], r = []; function t(f) { try { r.push(String(f())) } catch (e) { r.push(e.name) } } var tgt = {}; var p = new Proxy(tgt, { defineProperty(t, k, d) { log.push(k + ':' + d.value + ':' + ('writable' in d)); return Reflect.defineProperty(t, k, d) } }); t(() => Object.defineProperty(p, 'a', { value: 1 }) === p); t(() => Reflect.defineProperty(p, 'b', { value: 2, writable: true })); t(() => tgt.a + tgt.b); var q = new Proxy({}, { defineProperty() { return false } }); t(() => Reflect.defineProperty(q, 'x', { value: 1 })); t(() => Object.defineProperty(q, 'x', { value: 1 })); var ne = Object.preventExtensions({}); t(() => Reflect.defineProperty(new Proxy(ne, { defineProperty() { return true } }), 'y', { value: 1 })); t(() => Reflect.defineProperty({}, 'z', { get: 1 })); print(log.join(), r.join())" == ["a:1:false,b:2:true true,true,3,false,TypeError,TypeError,TypeError"]
#guard out "var r = []; function t(f) { try { r.push(String(f())) } catch (e) { r.push(e.name) } } var pr = {}; var p = new Proxy({}, { getPrototypeOf() { return pr }, isExtensible() { return true }, preventExtensions(t) { Object.preventExtensions(t); return true }, setPrototypeOf(t, v) { return false } }); t(() => Object.getPrototypeOf(p) === pr); t(() => Object.isExtensible(p)); t(() => Reflect.setPrototypeOf(p, null)); t(() => Object.setPrototypeOf(p, null)); t(() => Reflect.preventExtensions(p)); t(() => Object.isExtensible(p)); t(() => Reflect.isExtensible(new Proxy({}, {}))); t(() => Object.getPrototypeOf(new Proxy({}, { getPrototypeOf() { return 1 } }))); print(r.join())" == ["true,true,false,TypeError,true,TypeError,true,TypeError"]
#guard out "var a = [1, 2]; Object.defineProperty(a, '0', { writable: false }); Object.freeze(a); Object.defineProperty(a, 'length', { value: 2 }); print(a.length, Object.getOwnPropertyDescriptor(a, 'length').writable)" == ["2 false"]

/-! ## `await` in a `switch` (the generator machine), Promise.withResolvers (§27.2.4.8) -/

#guard out "async function f(x) { var r = []; switch (x) { case 1: r.push(await 'a'); case 2: r.push('b'); break; default: r.push(await 'd'); case 3: r.push('c') } return r.join() } async function g(c) { var a; switch ('k') { case 'k': a = c ? await 1 : 2; break } return a } Promise.all([f(1), f(2), f(3), f(9), g(true), g(false)]).then(v => print(v.join('|')))" == ["a,b|b|c|d,c|1|2"]
#guard out "var w = Promise.withResolvers(); w.promise.then(v => print('got', v)); print(Object.keys(w).join(), typeof w.resolve); w.resolve(5); try { Promise.withResolvers.call(1) } catch (e) { print(e.name) }" == ["promise,resolve,reject function", "TypeError", "got 5"]

/-! ## Array iteration over array-likes and holes (§23.1.3: HasProperty, LengthOfArrayLike) -/

#guard out "var seen = []; Array.prototype.forEach.call({ 0: 'a', 2: 'c', length: 4 }, (v, i) => seen.push(i + v)); var m = [1, , 3].map(x => x * 2); var f = [1, , 3].findIndex(x => x === undefined); var o = { 1: 11, 2: 9, length: { valueOf() { return {} }, toString() { return '2' } } }; var fl = Array.prototype.filter.call(o, () => true); var r = Array.prototype.reduce.call({ 1: 'x', 3: 'y', length: 4 }, (a, b) => a + b); var e; try { [].reduce((a, b) => a) } catch (x) { e = x.name } var g = []; var a = [1, 2, 3]; a.forEach((v, i) => { if (i === 0) a.pop(); g.push(v) }); print(seen.join(), m.length, 1 in m, f, fl.join(), r, e, g.join())" == ["0a,2c 3 true 1 11 xy TypeError 1,2"]

/-! ## Iterator.concat (§27.1.3.2.2) -/

#guard out "var it = Iterator.concat([1, 2], new Set([3]), 'ab'.split('')); print([...it].join(), typeof it.next, Object.getPrototypeOf(it) === Object.getPrototypeOf(Iterator.from([]).map(x => x))); try { Iterator.concat(1) } catch (e) { print(e.name) } var c = 0; var r = { [Symbol.iterator]() { c++; return [9][Symbol.iterator]() } }; var j = Iterator.concat(r, r); print(c, j.next().value, c, [...j].join(), c)" == ["1,2,3,a,b function true", "TypeError", "0 9 1 9 2"]

/-! ## DisposableStack, SuppressedError, Symbol.dispose, Iterator.prototype[@@dispose] -/

#guard out "var log = []; var s = new DisposableStack(); s.use({ [Symbol.dispose]() { log.push('a') } }); s.defer(() => log.push('b')); s.adopt(7, v => log.push('c' + v)); print(s.disposed, typeof Symbol.dispose); s.dispose(); print(log.join(), s.disposed, String(s.dispose())); try { s.use(null) } catch (e) { print(e.name) } var t = new DisposableStack(); t.defer(() => { throw 1 }); t.defer(() => { throw 2 }); try { t.dispose() } catch (e) { print(e.name, e.error, e.suppressed) } var m = new DisposableStack(); m.defer(() => log.push('m')); var m2 = m.move(); print(m.disposed, m2.disposed); m2[Symbol.dispose](); print(log.join(), Object.prototype.toString.call(m2))" == ["false symbol", "c7,b,a true undefined", "ReferenceError", "SuppressedError 1 2", "true false", "c7,b,a,m [object DisposableStack]"]
#guard out "var f = []; var g = (function* () { try { yield 1 } finally { f.push('closed') } })(); g.next(); g[Symbol.dispose](); var e = new SuppressedError(1, 2, 'm'); print(f.join(), e.error, e.suppressed, e.message, e instanceof Error, SuppressedError.prototype.name)" == ["closed 1 2 m true SuppressedError"]

/-! ## Error.isError, Promise.try, RegExp.escape -/

#guard out "print(RegExp.escape('foo.bar'), RegExp.escape('1 '), RegExp.escape('_\\n'), RegExp.escape('\\u2028,'), Error.isError(new TypeError()), Error.isError({}), Error.isError(Object.create(Error.prototype))); Promise.try((a, b) => a + b, 2, 3).then(v => print('try', v)); Promise.try(() => { throw 7 }).catch(e => print('caught', e))" == ["\\x66oo\\.bar \\x31\\x20 _\\n \\u2028\\x2c true false false", "try 5", "caught 7"]
#guard out "var a = [1, 2, 1, NaN]; print(a.lastIndexOf(1), a.lastIndexOf(1, 1), a.lastIndexOf(1, -3), a.lastIndexOf(1, -9), a.indexOf(1, 1), a.indexOf(NaN), a.includes(NaN), a.includes(2, -1), Array.prototype.indexOf.call({ 0: 'x', 2: 'x', length: 3 }, 'x', 1), Array.prototype.includes.call({ length: 2 }, undefined), Array.prototype.indexOf.call({ length: 2 }, undefined))" == ["2 0 0 -1 2 -1 true false 2 true -1"]

/-! ## Parameters with defaults are in their temporal dead zone until bound (§10.2.11) -/

#guard out "var r = []; function t(f) { try { r.push(String(f())) } catch (e) { r.push(e.name) } } var b = 'outer'; t(() => (function (a = b, b) { return a })()); t(() => (function (x = x) { return x })()); t(() => (function (a, c = a) { return c })(3)); t(() => (function (a = 1, { d } = { d: a }) { return d })()); t(() => ({ m(y = y) {} }).m()); print(r.join())" == ["ReferenceError,ReferenceError,3,1,ReferenceError"]
#guard out "var r = []; function t(f) { try { r.push(String(f())) } catch (e) { r.push(e.name) } } t(() => (function (p = eval('var arguments')) {})()); t(() => (function (p = eval('var a = 1'), q = a) { return q })()); t(() => ((p = eval('var arguments = 2')) => 'arrow')()); t(() => (function () { eval('var arguments = 3'); return arguments })()); print(r.join())" == ["SyntaxError,1,arrow,3"]
/-! ## Iterator.zip and Iterator.zipKeyed -/

#guard out "var z = Iterator.zip([[1, 2, 3], 'ab'.split('')]); print(JSON.stringify([...z])); print(JSON.stringify([...Iterator.zip([[1], [2, 3]], { mode: 'longest', padding: ['p', 'q'] })])); try { [...Iterator.zip([[1], [2, 3]], { mode: 'strict' })] } catch (e) { print(e.name) } var k = Iterator.zipKeyed({ a: [1, 2], b: [3] }); print(JSON.stringify([...k])); try { Iterator.zip([1]) } catch (e) { print(e.name) } try { Iterator.zip([], { mode: 'x' }) } catch (e) { print(e.name) }" == ["[[1,\"a\"],[2,\"b\"]]", "[[1,2],[\"p\",3]]", "TypeError", "[{\"a\":1,\"b\":3}]", "TypeError", "TypeError"]

end L4Factoidal.JS.Tests
