import L4Factoidal.JS.Interp
import L4Factoidal.JS.Clone

/-! Build-time tests of the structured clone (`JS.Clone`): a value made by a script in one
realm, serialized there, deserialized in a second realm (as a dedicated worker receives a
message), and checked by a script in that realm. -/

namespace L4Factoidal.JS.CloneTests
open L4Factoidal.JS

def globalOf (h : Heap) (name : String) : Value :=
  match (h.obj h.realm.globalObj).getOwn name with
  | some (.data v ..) => v
  | _ => .undef

/-- Run `src` in a fresh realm, clone its global `x` into another fresh realm as `y`, and
run `check` there: the lines it printed, or the serialization's error. -/
def roundTrip (src check : String) : List String :=
  let (_, h1) := runScript freshHeap src
  match Clone.serialize h1 (globalOf h1 "x") #[] with
  | .error e => ["DataCloneError " ++ e]
  | .ok (bytes, _) =>
    match Clone.deserialize freshHeap bytes with
    | none => ["bad bytes"]
    | some (v, h2) =>
      let h2 := { h2 with objs := h2.objs.modify h2.realm.globalObj (·.putOwn "y" (.data v true true true)) }
      match runScript h2 check with
      | (.ok, h) => h.out.toList
      | (.threw _ m, h) => h.out.toList ++ ["Uncaught " ++ m]
      | (_, h) => h.out.toList ++ ["stopped"]

#guard roundTrip "var x = [1, 'two', null, undefined, true, -0, NaN, 2n ** 70n]"
  "print(y.length, y[0], y[1], y[2], y[3], y[4], Object.is(y[5], -0), Number.isNaN(y[6]), y[7], Array.isArray(y))" ==
  ["8 1 two null undefined true true true 1180591620717411303424 true"]
#guard roundTrip "var x = {a: 1, b: {c: 'é😀'}, d: [1, 2]}; x.self = x; x.d.push(x.b)"
  "print(y.a, y.b.c, y.self === y, y.d[2] === y.b, Object.keys(y).join(), Object.getPrototypeOf(y) === Object.prototype)" ==
  ["1 é😀 true true a,b,d,self true"]
#guard roundTrip "var x = new Map([[1, 'one'], ['k', {v: 2}]]); x.set(x, x)"
  "print(y instanceof Map, y.size, y.get(1), y.get('k').v, y.get(y) === y)" == ["true 3 one 2 true"]
#guard roundTrip "var x = new Set([3, 1, 2])" "print(y instanceof Set, [...y].join())" == ["true 3,1,2"]
#guard roundTrip "var x = [new Date(86400000), /a+b/gi, new Number(3), new String('s'), new Boolean(false), Object(5n)]"
  "print(y[0] instanceof Date, y[0].getTime(), y[1] instanceof RegExp, y[1].source, y[1].flags, y[1].lastIndex, typeof y[2], y[2] + 1, y[3] + '!', y[4].valueOf(), typeof y[5])" ==
  ["true 86400000 true a+b gi 0 object 4 s! false object"]
#guard roundTrip "var b = new ArrayBuffer(8); var x = {b: b, u: new Uint16Array(b, 2, 2), v: new DataView(b, 4)}; x.u[0] = 513; x.v.setUint8(0, 9)"
  "print(y.b.byteLength, y.u instanceof Uint16Array, y.u.buffer === y.b, y.u.byteOffset, y.u.length, y.u[0], new Uint8Array(y.b)[4], y.v.getUint8(0), y.v.buffer === y.b)" ==
  ["8 true true 2 2 513 9 9 true"]
#guard roundTrip "var x = [new TypeError('bad'), new RangeError(), new Error('m')]"
  "print(y[0] instanceof TypeError, y[0].message, y[1] instanceof RangeError, y[1].message === '', y[2].name, y[2].message)" ==
  ["true bad true true Error m"]
#guard ((roundTrip "var x = {f: function () {}}" "").headD "").startsWith "DataCloneError function"
#guard roundTrip "var x = [Symbol()]" "" == ["DataCloneError Symbol could not be cloned"]
#guard roundTrip "var x = new WeakMap()" "" == ["DataCloneError #<Object> could not be cloned"]
#guard roundTrip "var x = new Proxy({}, {})" "" == ["DataCloneError #<Object> could not be cloned (a Proxy)"]
-- a getter is read as `undefined` (the known limit); a non-enumerable property is not cloned
#guard roundTrip "var x = Object.defineProperty({get g() { return 1 }}, 'h', {value: 2, enumerable: false})"
  "print('g' in y, y.g, 'h' in y)" == ["true undefined false"]
-- deep nesting costs no Lean stack
#guard roundTrip "var x = []; var c = x; for (var i = 0; i < 20000; i++) { var d = []; c.push(d); c = d }"
  "var n = 0; var c = y; while (c.length) { c = c[0]; n++ } print(n)" == ["20000"]

-- transfer: the bytes move, and the sender detaches its buffer
#guard
  let (_, h1) := runScript freshHeap "var x = new ArrayBuffer(4)"
  match globalOf h1 "x" with
  | .obj b =>
    match Clone.serialize h1 (.obj b) #[b] with
    | .ok (_, det) => det == #[b]
    | .error _ => false
  | _ => false
#guard
  let (_, h1) := runScript freshHeap "var x = new ArrayBuffer(4)"
  match globalOf h1 "x" with
  | .obj b => (Clone.serialize h1 (.obj b) #[b, b]).toOption.isNone
  | _ => false

-- bytes that are not a serialization are refused, not misread
#guard (Clone.deserialize freshHeap (ByteArray.mk #[99])).isNone
#guard (Clone.deserialize freshHeap (ByteArray.mk #[24, 5])).isNone
#guard (Clone.deserialize freshHeap ByteArray.empty).isNone

end L4Factoidal.JS.CloneTests
