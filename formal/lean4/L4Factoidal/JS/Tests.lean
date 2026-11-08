import L4Factoidal.JS.Interp

/-! Build-time tests of the JavaScript engine: each `#guard` runs a script and
checks what it printed. -/

namespace L4Factoidal.JS.Tests
open L4Factoidal.JS

def out (src : String) : List String :=
  match run src with
  | (.ok, o) => o.toList
  | (.threw _ m, o) => o.toList ++ ["Uncaught " ++ m]
  | (.syntaxError m, _) => [m]
  | (.halted w, _) => ["halted " ++ w]

#guard out "print(1 + 2)" == ["3"]
#guard out "print(0.1 + 0.2, 1/3, 1e21, 1e-7, -0, 2**53 + 2)" ==
  ["0.30000000000000004 0.3333333333333333 1e+21 1e-7 0 9007199254740994"]
#guard out "print('a' + 1, 1 + '2', '3' * '4', null + 1, undefined + 1, true + true)" ==
  ["a1 12 12 1 NaN 2"]
#guard out "var x = 0; function f() { x = x + 1; } f(); f(); print(x)" == ["2"]
#guard out "function mk() { var n = 0; return function () { n++; return n; }; } var c = mk(); c(); print(c())" == ["2"]
#guard out "var o = { n: 3, f: function () { return this.n; } }; print(o.f())" == ["3"]
#guard out "print('a'); throw 1; print('b')" == ["a", "Uncaught 1"]
#guard out "try { null.x } catch (e) { print(e instanceof TypeError, e.name) }" == ["true TypeError"]
#guard out "let s = 0; for (let i = 0; i < 10; i++) { if (i == 5) continue; s += i } print(s)" == ["40"]
#guard out "var fs = []; for (let i = 0; i < 3; i++) fs.push(() => i); print(fs.map(f => f()).join())" == ["0,1,2"]
#guard out "outer: for (var i = 0; i < 3; i++) { for (var j = 0; j < 3; j++) { if (j == 1) continue outer; if (i == 2) break outer; print(i, j) } }" == ["0 0", "1 0"]
#guard out "switch (2) { case 1: print(1); case 2: print(2); case 3: print(3); break; default: print('d') }" == ["2", "3"]
#guard out "function f() { try { return 1 } finally { print('fin') } } print(f())" == ["fin", "1"]
#guard out "{ print(typeof x); let x = 1; }" == ["Uncaught ReferenceError: Cannot access 'x' before initialization"]
#guard out "const c = 1; try { c = 2 } catch (e) { print(e.name) }" == ["TypeError"]
#guard out "function P(x) { this.x = x } P.prototype.get = function () { return this.x }; print(new P(7).get(), new P(1) instanceof P)" == ["7 true"]
#guard out "var a = [3, 1, 2]; a.sort(); print(a, a.length, [1,2,3].indexOf(2))" == ["1,2,3 3 1"]
#guard out "print(JSON.stringify({a: [1, 'x', null, true], b: {c: 1.5}}))" == ["{\"a\":[1,\"x\",null,true],\"b\":{\"c\":1.5}}"]
#guard out "var o = {a: 1, b: 2}; var ks = []; for (var k in o) ks.push(k); print(ks.join('|'))" == ["a|b"]
#guard out "print(String(-1/0), Number('0x10'), parseInt('42px'), (255).toString(16), 7 % -3, -7 % 3)" ==
  ["-Infinity 16 42 ff 1 -1"]
#guard out "print(1 << 31, -1 >>> 0, ~5, 5 & 3, 5 | 3, 5 ^ 3)" == ["-2147483648 4294967295 -6 1 7 6"]
#guard out "var o = { get v() { return 4 }, set v(x) { print('set', x) } }; o.v = 9; print(o.v)" == ["set 9", "4"]
#guard out "print(typeof undeclared, typeof null, typeof function(){}, typeof {})" == ["undefined object function object"]
#guard out "1 +" == ["SyntaxError: unexpected end of input at end of input (offset 3)"]

end L4Factoidal.JS.Tests
