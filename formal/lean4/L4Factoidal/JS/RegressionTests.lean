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

end L4Factoidal.JS.Tests
