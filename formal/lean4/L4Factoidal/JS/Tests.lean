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

-- The fuel is a scalar on wasm32 (below 2^31) and covers the largest step budget.
theorem fuel_scalar_on_wasm32 : defaultFuel < 2 ^ 31 := by decide
theorem fuel_covers_steps : (1000000000 : Nat) < defaultFuel := by decide

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
#guard out "class A { #n = 1; static #k = 5; static { this.s = A.#k } inc() { return ++this.#n } has(o) { return #n in o } } var a = new A(); a.inc(); print(a.inc(), A.s, a.has(a), Object.keys(a).length)" ==
  ["3 5 true 0"]
#guard out "async function* g() { var x = await Promise.resolve(1); yield x; yield x + 1 } var it = g(); it.next().then(r => { print(r.value, r.done); return it.next() }).then(r => print(r.value)).then(() => it.next()).then(r => print(r.done))" ==
  ["1 false", "2", "true"]
#guard out "var m = new Map([[1, 'a'], [NaN, 'b']]); m.set(-0, 'z'); var s = new Set([1, 2, 2, 3]); s.delete(2); print(m.get(NaN), m.get(0), m.size, [...s].join(), [...m.keys()].length, Reflect.ownKeys({a: 1, [Symbol.iterator]: 2}).length)" ==
  ["b z 3 1,3 3 2"]
#guard out "print([1, [2, [3, [4]]]].flat(2).length, 'abc'.padStart(5, '-'), 'a-b-c'.replaceAll('-', '+'), [5, 6].at(-1), Math.hypot(3, 4), Math.clz32(1))" ==
  ["4 --abc a+b+c 6 5 31"]
#guard out "1 +" == ["SyntaxError: unexpected end of input at end of input (offset 3)"]

/-- A script with a budget of `steps`: built-ins take steps for the size they walk
(`charge`, `sizeCost`), so a loop of `charCodeAt` over a long string stops at the budget
instead of running for minutes (WPT wasm/jsapi/js-string/constants.any.js did). -/
def outWith (steps : Nat) (src : String) : List String :=
  match runScript { freshHeap with steps } src with
  | (.ok, h) => h.out.toList
  | (.threw _ m, h) => h.out.toList ++ ["Uncaught " ++ m]
  | (.syntaxError m, _) => [m]
  | (.halted w, _) => ["halted " ++ w]

-- a String method that walks its receiver takes steps for it: here a non-ASCII string,
-- indexed by walking it, so the loop stops at the budget
#guard outWith 200000 "var s = '\u00e9'.repeat(100000), t = 0; for (var i = 0; i < s.length; i++) t += s.charCodeAt(i); print(t)" ==
  ["halted step budget exhausted"]
#guard outWith 2000000 "var s = 'ab'.repeat(1000), t = 0; for (var i = 0; i < s.length; i++) t += s.charCodeAt(i); print(t)" == ["195000"]
#guard outWith 2000000 "try { 'x'.repeat(2 ** 30) } catch (e) { print(e.name) }" == ["RangeError"]
#guard outWith 1000000 "var a = new Array(4000000000)" == ["halted step budget exhausted"]
/-! The String methods that index an ASCII string do not walk it (`indexesReceiver`): a
loop of 100 000 `charCodeAt`, `at` and one-unit `slice` calls on a 100 000-character string
ends well within a page's budget (5 M steps). -/
#guard outWith 5000000 "var s = '0'.repeat(100000), t = 0; for (var i = 0; i < s.length; i++) t += s.charCodeAt(i); print(t)" ==
  ["4800000"]
#guard outWith 5000000 "var s = 'ab'.repeat(50000), t = 0; for (var i = 0; i < s.length; i++) t += s.at(i) === s.slice(i, i + 1) ? 1 : 0; print(t)" ==
  ["100000"]

/-! Strings are UTF-16 code units (§6.1.4; `JS/Str.lean`). -/
#guard out "var s = 'a\\u{1F600}b'; print(s.length, s.charCodeAt(1), s.charCodeAt(2), s.codePointAt(1), [...s].length)" ==
  ["4 55357 56832 128512 3"]
#guard out "print('\\uD800'.length, '\\uD800'.charCodeAt(0), String.fromCharCode(0xD83D, 0xDE00) === '\\u{1F600}')" ==
  ["1 55296 true"]
#guard out "var s = '\\u{1F600}'; print(s.slice(0, 1) + s.slice(1) === s, JSON.stringify('\\uD800'), '\\uD800'.isWellFormed())" ==
  ["true \"\\ud800\" false"]

/-! Typed arrays, ArrayBuffer, SharedArrayBuffer, Atomics. -/
#guard out "var TA = Object.getPrototypeOf(Int8Array); print(TA.name, Int16Array.of(1, 2).join(), new Uint8Array([1, 2, 3, 4, 5]).copyWithin(0, 3).join())" ==
  ["TypedArray 1,2 4,5,3,4,5"]
#guard out "var b = new ArrayBuffer(4, { maxByteLength: 8 }); b.resize(8); var c = b.transfer(); print(b.byteLength, b.detached, c.byteLength)" ==
  ["0 true 8"]
#guard out "var a = new Int32Array(new SharedArrayBuffer(8)); Atomics.store(a, 0, 5); print(Atomics.add(a, 0, 2), Atomics.load(a, 0), new BigInt64Array([-1n])[0])" ==
  ["5 7 -1"]

#guard out "var d = new Date(Date.UTC(2026, 10, 9, 3, 4, 5)); print(d.toISOString(), d.getMonth(), d.getDay(), Date.parse(d.toString()) === d.getTime())" ==
  ["2026-11-09T03:04:05.000Z 10 1 true"]

end L4Factoidal.JS.Tests
