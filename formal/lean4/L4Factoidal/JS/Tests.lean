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
#guard out "var [a, , b = 5, ...r] = [1, 2, undefined, 4, 5]; var {x, y: {z} = {z: 9}, ...o} = {x: 1, p: 2, q: 3}; print(a, b, r.join(), x, z, Object.keys(o).join())" ==
  ["1 5 4,5 1 9 p,q"]
#guard out "function f(a, b = a + 1, ...c) { return [a, b, c.length]; } print(f(1).join(), f(1, 2, 3, 4).join(), f.length)" == ["1,2,0 1,2,2 1"]
#guard out "var s = 0; for (const v of [1, 2, 3]) s += v; for (const ch of 'ab') s += ch; print(s)" == ["6ab"]
#guard out "print(Math.max(...[1, 5, 3]), [...'hi', ...[1]].join('-'), `a${1 + 1}b${'c'}`)" == ["5 h-i-1 a2bc"]
#guard out "class A { constructor(x) { this.x = x } get dbl() { return this.x * 2 } static mk() { return new A(3) } } class B extends A { constructor() { super(4); this.y = 1 } sum() { return this.x + this.y + super.constructor.name.length } } print(A.mk().dbl, new B().sum(), new B() instanceof A)" == ["6 6 true"]
#guard out "class C { n = 2; m() { return this.n } } print(new C().m(), typeof C, (() => { try { C() } catch (e) { return e.name } })())" == ["2 function TypeError"]
#guard out "var s = Symbol('k'); var o = {[s]: 1, a: 2}; print(typeof s, String(s), o[s], Object.keys(o).length, s.description)" == ["symbol Symbol(k) 1 1 k"]
#guard out "var it = { [Symbol.iterator]() { var i = 0; return { next: () => ({ value: i, done: i++ >= 2 }), return() { print('closed'); return {} } }; } }; for (var v of it) { print(v); break; }" == ["0", "closed"]
#guard out "print(eval('var q = 1; q + 1'), typeof q, new Function('a', 'b', 'return a * b')(3, 4))" == ["2 number 12"]
#guard out "[a, b] = [1, 2]; ({c: d} = {c: 3}); print(a, b, d)" == ["1 2 3"]
#guard out "function* g() { var x = yield 1; print('got', x); try { yield 2 } finally { print('fin') } } var it = g(); print(it.next().value); print(it.next('a').value); print(JSON.stringify(it.return(7)))" ==
  ["1", "got a", "2", "fin", "{\"value\":7,\"done\":true}"]
#guard out "function* r(n) { for (let i = 0; i < n; i++) yield i; } print([...r(4)].join(), Array.from(r(2)).length)" == ["0,1,2,3 2"]
#guard out "function* a() { yield 1; yield* [2, 3]; return 4 } var s = []; for (var v of a()) s.push(v); print(s.join())" == ["1,2,3"]
#guard out "label: for (var i = 0; i < 3; i++) { if (i == 1) continue label; } try { eval('break;') } catch (e) { print(e.name) }" == ["SyntaxError"]
#guard out "print(2n ** 64n, -7n / 2n, -7n % 2n, typeof 1n, 1n == 1, 2n > 1, 5n & -2n, BigInt('0x10'), (255n).toString(16))" ==
  ["18446744073709551616 -3 -1 bigint true true 4 16 ff"]
#guard out "try { 1n + 1 } catch (e) { print(e.name) }" == ["TypeError"]
#guard out "var o = { a: 1, f: function () { return this === o } }; with (o) { a = 2; print(a, f()) } print(o.a)" == ["2 true", "2"]
#guard out "var log = []; Promise.resolve(1).then(v => log.push('a' + v)); log.push('sync'); async function f(x) { var y = await x; log.push('b' + y); return y + 1 } f(Promise.resolve(2)).then(v => { log.push('c' + v); print(log.join()) })" ==
  ["sync,a1,b2,c3"]
#guard out "async function g() { try { await Promise.reject(new TypeError('no')) } catch (e) { return e.message } } g().then(print); new Promise((res, rej) => rej(5)).catch(e => print('caught', e)).finally(() => print('fin'))" ==
  ["caught 5", "no", "fin"]
#guard out "Promise.all([1, Promise.resolve(2), 3]).then(v => print(v.join()))" == ["1,2,3"]
#guard out "1 +" == ["SyntaxError: unexpected end of input at end of input (offset 3)"]

end L4Factoidal.JS.Tests
