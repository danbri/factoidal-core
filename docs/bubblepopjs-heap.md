# BubblePopJS heap: measurements, design and migration plan

Status: design draft with a measured baseline, 2026-11-16. Tracking issue:
[BubblePopJS JIT: proven equivalent to the interpreter](https://github.com/danbri/factoidal-core/issues/471).
Later work that this design leaves hook points for:
[guarded execution hints](https://github.com/danbri/factoidal-core/issues/532).

This record has three parts: what the engine allocates today and where (measured), the design of
the heap that replaces the hot parts of it (value slots, objects, memory, frames) with the
theorems each part owes, and a plan of small steps, the largest measured source first.

The inductive `Value`, `Obj`, `Env` and `HeapOf` of
[`JS/Value.lean`](../formal/lean4/L4Factoidal/JS/Value.lean) and the evaluator of
[`JS/Interp.lean`](../formal/lean4/L4Factoidal/JS/Interp.lean) with the register machine off
stay the specification. Nothing here changes what a script computes.

## 1. Measurements

### 1.1 What was measured, and how

| Input | What it is |
|---|---|
| Library corpus | lodash 4.17.21, acorn 8.11.3, immutable 4.3.5, marked 4.3.0, pako 2.1.0 with the drivers of [`bubblepop_perf/realworld.py`](../labs/demos/foafnaut/bubblepop_perf/realworld.py), at size 4N, less the load (size 0) |
| Operations | the 60 loop bodies of [`bubblepop_perf/opcost.py`](../labs/demos/foafnaut/bubblepop_perf/opcost.py), slope between N and 5N iterations, less the empty loop |
| Test262 | 5,067 files of nine directories at Test262 `2e58f87` (object and call expressions, `for-of`, class elements, `Array.prototype.map`, `String.prototype.replace`, `JSON.stringify`, `Object.defineProperty`); `Array.prototype.splice` is left out because one of its files loops ten million times and hides the rest |
| Real pages | offline snapshots of the [real-page survey](../skills/realpages-survey/SKILL.md) (development test inputs only): Wikipedia "This Is Spinal Tap" (desktop skin), MDN `display`, BBC News article, jvns.ca, Hacker News; release engine `1b2fc90d`, macOS arm64 |

Two instruments, both in
[`bubblepop_perf/alloc/`](../labs/demos/foafnaut/bubblepop_perf/alloc/) (the outputs behind the
tables are in its `baseline-20261116/`):

- **Counts.** `build-count.sh` compiles the C that Lean generated for `leanjs` a second time with
  `leanprof.h` force-included. The header wraps the runtime's allocation, reference-count and array
  and string entry points and counts each call site: constructor allocations by tag, field count and
  scalar size, closures, boxed floats, arrays made, grown and copied (with the bytes), strings, and
  `lean_inc`/`lean_dec` on heap objects. It needs no Lean build. `leancount.py` reads the counts by
  shape and by function; `opcount.py` gives them for one JavaScript operation. A constructor is known
  by its shape, not its name: `Value.num` is the only hot constructor with tag 3 and eight scalar
  bytes, but `(0, 2, 0)` is every pair and every `EStateM.Result.ok`, so shapes are grouped in
  families below. Allocations inside the Lean runtime and the precompiled `Init` and `Std` libraries
  are seen only through the wrapped calls.
- **Time.** `sampleprof.py` reads a macOS `sample` profile (1 ms), puts each self sample in a class
  by its leaf symbol, and charges it to the nearest enclosing engine function. The allocator's
  inlined fast path counts as engine time, so the shares below are lower bounds.

The counts were taken on the generated C of the evaluator at `c5121e3aa` plus one line (the tree
of the open fuel-monotonicity work); the `JS/` sources of `main` at `54fa9b357` are the same as
`c5121e3aa`. The time profiles of the libraries used the `leanjs` built from that tree on
2026-11-16; the machine carried other work (load 3 to 9), which does not move counts and moves
profile shares little.

### 1.2 Time: memory management is 29 to 57% of script time

Share of self samples (main thread; `tls` is `_tlv_get_addr`, reached only from the allocator):

| Workload | engine code | alloc | free | tls | rc slow paths | sum of the four |
|---|---|---|---|---|---|---|
| lodash | 65.1 | 8.0 | 8.1 | 7.8 | 5.4 | 29.3 |
| acorn | 58.9 | 9.5 | 10.0 | 8.9 | 4.3 | 32.7 |
| immutable | 63.8 | 8.0 | 9.1 | 7.3 | 5.2 | 29.6 |
| marked | 36.7 | 11.0 | 25.2 | 17.3 | 3.7 | 57.2 |
| pako | 46.6 | 12.2 | 15.5 | 9.5 | 3.3 | 40.5 |
| Test262 (nine directories) | 42.3 | 6.3 | 11.7 | 8.2 | 7.4 | 33.6 |
| Wikipedia article, script turns | 41.5 | 10.7 | 11.4 | 17.9 | 5.5 | 45.5 |
| MDN `display`, script turns | 45.5 | 8.4 | 10.1 | 11.4 | 9.5 | 39.4 |
| jvns.ca, script turns | 27.6 | 7.7 | 8.7 | 12.8 | 7.8 | 37.0 |
| Hacker News, script turns (191 samples) | 30.9 | 11.0 | 16.2 | 23.0 | 6.3 | 56.5 |
| BBC News, script turns | 30.9 | 5.0 | 6.6 | 8.0 | 10.4 | 30.0, plus 27.7 copying |

"Script turns" are the samples below a frame of the JavaScript engine or of its page host, so they
include layout and DOM work that a script asked for.

Findings:

1. **The figure of about half holds for pages** (30 to 57% on the five pages, and BBC adds 28% of
   copying), and is 29 to 41% on the library corpus apart from `marked` (57%, a regular expression
   workload).
2. **A thread-local lookup is 7 to 23% of script time.** On macOS every small allocation calls
   `_tlv_get_addr` twice: once from `lean_inc_heartbeat`, which `lean_alloc_small_object` calls, and
   once from `mi_malloc_small` (both callers are named in the profiles). The engine library pays more
   than the command line binary. This cost is in the runtime build, not in the engine's Lean code,
   and each allocation removed takes its lookups with it. The profiled release is older than the
   change on `main` that drops the heartbeat call from the native engine (section 4).
3. **The BBC page spends 27.7% of script time copying the object array.** `newArray` pushes onto
   `HeapOf.objs` while a second reference to the heap is alive (the copy kept for a synchronous
   `XMLHttpRequest`), so each push copies the array. This is the defect that
   [PR 510](https://github.com/danbri/factoidal-core/pull/510) addresses; it is listed here because
   every design below depends on the same rule: the heap's arrays must have one owner.
4. **On pages, the engine's own memory management is spread over three places**: the built-in call
   path, the register machine, and the bridge to the DOM. Wikipedia, memory-management samples by
   enclosing function (of 11,360 script-turn samples): `callNative` 5.2%, `vmLoop` 3.3%, the page
   host's `callImport` 2.8%, `Page.i32v` 2.4%, `Dom.ret` 2.2%, `serveNative` 2.0%, `getV` 1.6%,
   `Obj.putOwn` 1.1%, `callHost`'s argument map 1.1%, `callClosure` 1.0%. Regular expressions and
   the parser are under 1% there. On MDN and jvns.ca most of it belongs to style and layout that
   scripts trigger, which is outside this record.

### 1.3 Counts: what is allocated

Run less load, per workload:

| Workload | allocations | bytes | reference-count operations | per allocation | bytes copied |
|---|---|---|---|---|---|
| lodash | 12.4 M | 349 MB | 70.7 M | 5.7 | 8.2 MB |
| acorn | 26.8 M | 737 MB | 153.8 M | 5.7 | 27.1 MB |
| immutable | 23.5 M | 644 MB | 136.4 M | 5.8 | 26.0 MB |
| marked | 14.5 M | 479 MB | 51.0 M | 3.5 | 2.5 MB |
| pako | 59.1 M | 1,458 MB | 245.8 M | 4.2 | 8.7 MB |
| Test262 (nine directories) | 60.9 M | 1,854 MB | 157.8 M | 2.6 | 257.3 MB |

By family, percentage of allocations (percentage of bytes):

| Family | lodash | acorn | immutable | marked | pako | Test262 |
|---|---|---|---|---|---|---|
| Result of a monadic call, or a tuple: `(0,2,0)`, `(0,3,0)`, `(1,2,0)` | 38.1 (32.9) | 44.9 (41.1) | 41.4 (37.4) | 48.3 (35.4) | 49.9 (52.8) | 57.2 (46.1) |
| `Option.some` and other one-field cells | 7.3 (4.1) | 26.3 (15.3) | 10.2 (5.9) | 26.1 (12.6) | 13.6 (8.9) | 14.2 (7.5) |
| `Value` box: `num`, `bool`, `obj`, `str`, boxed `Float` | 33.9 (19.3) | 7.5 (4.4) | 23.7 (13.8) | 1.2 (0.6) | 25.7 (16.7) | 3.3 (1.7) |
| Closure | 1.1 (1.5) | 7.8 (17.1) | 5.7 (8.2) | 22.6 (48.9) | 3.6 (5.8) | 1.6 (2.1) |
| Copy of the `HeapOf` record (88 bytes) | 7.3 (22.8) | 2.6 (8.5) | 3.5 (11.3) | 0.1 (0.4) | 2.6 (9.2) | 0.3 (0.8) |
| `VFrame` or `Env` record (56 bytes) | 5.7 (11.4) | 1.7 (3.6) | 2.7 (5.6) | 0.2 (0.4) | 1.0 (2.4) | 1.2 (2.3) |
| Object records: `Obj`, `PropV`, `Binding`, `Ctx` | 2.4 (3.4) | 3.5 (3.8) | 6.8 (10.0) | 0.3 (0.3) | 0.8 (0.7) | 1.6 (2.0) |
| Arrays made, grown, copied | 2.8 (3.9) | 3.8 (4.7) | 4.4 (6.5) | 0.7 (0.7) | 1.7 (2.6) | 4.6 (14.7) |
| Other constructors | 1.3 | 1.6 | 1.5 | 0.5 | 1.1 | 13.5 |

By function, percentage of allocations (mean of the five libraries in the last column):

| Function | lodash | acorn | immutable | marked | pako | mean |
|---|---|---|---|---|---|---|
| `vmLoop` (the register machine) | 54.7 | 11.8 | 26.7 | 0.6 | 7.8 | 20.3 |
| `Re.readAt`, `Re.matchNode` and the matcher's range loop | 0.0 | 19.0 | 0.1 | 87.9 | 0.0 | 21.4 |
| `toNum` | 3.0 | 2.2 | 11.4 | 0.7 | 15.7 | 6.6 |
| `Std.HashMap` lookup (`AssocList.get?`) | 0.3 | 11.4 | 2.7 | 0.3 | 5.9 | 4.1 |
| `evalExpr` | 0.8 | 7.2 | 2.0 | 0.7 | 7.4 | 3.6 |
| `arrayIndex?` | 0.2 | 1.2 | 1.5 | 0.1 | 13.9 | 3.4 |
| `setElem` | 1.5 | 0.0 | 9.7 | 0.0 | 2.6 | 2.8 |
| `setOwnData` | 0.3 | 3.8 | 3.2 | 0.1 | 4.9 | 2.4 |
| `binop` | 6.8 | 0.5 | 2.2 | 0.1 | 2.3 | 2.4 |

On Test262 the parser leads: `P.peek` alone is 21.4% of allocations (one result cell per token
looked at), the lexer's token record 6.7%.

Findings:

5. **The largest family is not `Value`.** 45 to 75% of allocations are the plumbing of the monad:
   the `EStateM.Result` cell of every call that is not inlined, tuples, `Option` results of lookups,
   and closures for continuations. `Value` boxes are a quarter to a third on numeric and object
   workloads and a few per cent elsewhere. A flat value representation alone cannot remove the
   larger share; the machine that uses it must also stop returning boxed results (section 2.5).
6. **The `HeapOf` record is copied on calls**: 2.6 to 7.3% of allocations but 8.5 to 22.8% of the
   bytes on four of the five libraries, and each copy also touches the count of the eight arrays it
   points to.
7. **The register machine allocates most on call-heavy code** (55% of lodash's allocations) and the
   regular expression matcher on text-heavy code (88% of marked's).

### 1.4 Cost of one operation

Allocations, bytes and reference-count operations for one iteration, less the empty loop (which
allocates nothing and does 14 reference-count operations for its three instructions):

| Operation | allocations | bytes | rc operations | What is allocated |
|---|---|---|---|---|
| `s = s + k`, `s++`, `s = o.x`, `s = a[3]`, `if (i < 0)`, `i ? 1 : 2` | 0 | 0 | 0 to 8 | nothing |
| `s = i < k`, `s = !i`, `s = i === k` | 1 | 16 | 0 | a `Value.bool` |
| `s = i == k` | 4 | 72 | 6 | two boxed numbers, a boolean, a result cell |
| `s = i & 255`, `s = i \| 1`, `s = i % 7`, `s = i << 1` | 7 to 8 | 128 to 152 | 8 to 10 | two boxed operands, two `toNum` result cells with two boxed floats, the boxed result |
| `s = a[i & 7]` | 8 | 152 | 18 | as `&` |
| `o.x = i` | 5 | 128 | 21 | boxed number, `PropV.data`, a closure, two result cells |
| `a[3] = i` | 7 | 184 | 18 | two boxed numbers, a new `Obj` record, `Kind.array`, a closure, two result cells |
| `s = g1(i)` (compiled callee) | 8 | 264 | 57 | `HeapOf` copy, `VFrame`, list cell, `Option`, two tuples, boxed return value, `Value.obj` for `this` |
| `s = o.m(i)` | 7 | 248 | 49 | as a call, without the `this` box |
| `s = Math.floor(i)` | 16 | 384 | 68 | result cells of the built-in call path, a boxed argument and result |
| `s = t.charCodeAt(3)` | 22 | 544 | 82 | as a built-in call, plus index parsing |
| `s = {}` | 4 | 114 | 5 | `Obj`, two `Value.obj`, a result cell |
| `s = { x: i, y: k }` | 16 | 442 | 24 | per property: `PropV.data`, boxed number, a new `Obj` record, a copy of the key array, a result cell |
| `s = [i, k, 1]` | 9 | 226 | 5 | three boxed numbers, `Obj`, `Kind.array`, the array, two `Value.obj`, a result cell |
| `s = function () { return i; }` | 38 | 1,148 | 85 | the function object and its `prototype` object, property by property |
| `try { s = i; } catch (e) { }` (evaluator) | 18 | 464 | 116 | the tree evaluator's result cells and environment records |

### 1.5 Operand distribution

Class of every number written into a boxed value (a `Value.num` or a boxed `Float`) and into a
float register, per workload:

| Workload | where | count | +0 | 1 to 255 | other 29-bit integer | other 32-bit integer | larger integer | fraction, −0, NaN, ∞ |
|---|---|---|---|---|---|---|---|---|
| lodash | boxed | 1.8 M | 7.9 | 32.6 | 53.4 | 3.5 | 2.4 | 0.2 |
| lodash | register | 3.2 M | 18.4 | 37.1 | 42.6 | 1.1 | 0.7 | 0.0 |
| acorn | boxed | 1.1 M | 16.6 | 31.4 | 52.1 | 0.0 | 0.0 | 0.0 |
| acorn | register | 1.4 M | 9.8 | 47.2 | 43.0 | 0.0 | 0.0 | 0.0 |
| immutable | boxed | 4.6 M | 12.2 | 43.8 | 39.2 | 4.2 | 0.7 | 0.0 |
| immutable | register | 7.7 M | 10.7 | 66.0 | 21.7 | 1.4 | 0.2 | 0.0 |
| marked | boxed | 0.15 M | 35.4 | 27.5 | 14.5 | 19.5 | 3.2 | 0.0 |
| marked | register | 0.07 M | 13.3 | 20.1 | 34.8 | 28.5 | 3.2 | 0.0 |
| pako | boxed | 14.7 M | 12.3 | 34.9 | 49.4 | 2.1 | 1.3 | 0.0 |
| pako | register | 14.9 M | 6.9 | 16.6 | 74.5 | 1.3 | 0.7 | 0.0 |

In this corpus 93 to 100% of numbers are integers that fit 29 bits, except on `marked` (77 to
68%); fractions are under 0.2%. The corpus has no graphics or animation code, where fractions
dominate; the Hub's canvas and layout demos must be measured before any step that makes a
fraction more costly than an integer.

## 2. Design

### 2.1 Rules that the measurements and Lean impose

- **Flat scalar storage is `ByteArray` and `FloatArray` only.** An `Array UInt64` holds one heap cell per
  element; an `Array UInt32` does too on wasm32. A `UInt64`, `UInt32`, `UInt8` or `Float` is a plain
  machine value in a local, a parameter, a result and a structure field, on both targets.
- **A tagged word cannot pass through `Float`.** `Float.ofBits` and `Float.toBits` go through the
  model of [`Init/Data/Float`](https://github.com/leanprover/lean4/tree/v4.33.1/src/Init/Data/Float),
  which has one NaN, and both are calls into the runtime (`lean_float_of_bits`, `lean_float_to_bits`),
  not inline casts.
- **One owner.** An array is updated in place only when its count is one. Every array of the heap is
  taken out of its record before it is written and put back after, as `pushEnv` and `vmTake` do now,
  and no second reference to the heap may live across a write (findings 3 and 6).
- **A function on the hot path returns a scalar or the machine record itself.** A function that
  returns `M α`, a pair or an `Option` and is not inlined allocates its result (finding 5).
- **A nat that indexes an array stays below 2^31**, so that it is a tagged scalar on wasm32 too. The
  existing bound on heap size (`maxObjs`, 2^23) gives this for every handle.

### 2.2 Value representation

Three candidates for a slot (a register, an environment slot, a property value, an array element):

| | A. NaN-boxed 64-bit word | B. tag byte, number and reference in parallel arrays | C. 32-bit tagged word (as Hermes HV32) |
|---|---|---|---|
| Storage in Lean | `ByteArray`, 8 bytes a slot | `ByteArray` tags (1), `FloatArray` numbers (8), `ByteArray` references (4): 13 bytes a slot | `ByteArray`, 4 bytes a slot |
| Read a number | eight byte loads, shifts, then `Float.ofBits` (a runtime call) | one byte load, one `double` load | four byte loads; an integer needs a conversion, anything else a second read in a number table |
| Write a number | `Float.toBits` (a call), eight byte stores | one byte store, one `double` store | range test, four byte stores, or an allocation in the number table |
| Numbers that allocate | none | none | every number outside 29 or 31 bits: 0.2 to 7% here, 23 to 32% on `marked`, most numbers of graphics code |
| NaN | the encoder must write one canonical pattern and every producer of words must be proved to | none: a number is a Lean `Float` in a `FloatArray`, as in the registers today | as B, in the number table |
| Needs a collector before it can land | no | no | yes, for the number table |
| Fits linear memory for later compilation to Wasm | yes, one word | yes, three regions | yes |
| Memory | 8 | 13 | 4, plus number cells |

The microbenchmark [`alloc/RepBench.lean`](../labs/demos/foafnaut/bubblepop_perf/alloc/RepBench.lean)
(standalone, `Init` only, native arm64, 100 million iterations, two runs) times the two commonest
register instructions on each candidate and on the present registers (an `Array` of a boxed
inductive with a `fl` marker, plus a `FloatArray`):

| | add two number registers | move a reference |
|---|---|---|
| Present registers | 9.1 to 9.8 ns | 5.3 to 5.7 ns |
| B, the three arrays in one record | 15.8 to 16.3 ns | 8.7 to 8.8 ns |
| C, integers only | 12.1 to 12.3 ns | not measured |
| A, word in a `ByteArray` | 33.0 to 33.5 ns | 11.0 to 11.2 ns |

- **A is 3.5 times slower than the present registers on an add and 2 times on a move.** Each word
  access is eight checked byte accesses, and each number is a runtime call in each direction.
- **The present registers are the fastest.** A move of a boxed reference costs two count updates on
  an object that one thread owns, which is cheaper than four checked byte loads and stores. B pays for
  a third array and for the record that holds the arrays (the generated code tests `isShared` on the
  record at each update; threading the arrays as separate arguments, as `vmLoop` does, removes that).
- So flat storage is not a gain for registers. Its gain is where a value is *stored*: a number
  written to a property, an element or an environment slot costs an allocation today (section 1.4:
  16 bytes, and on macOS two thread-local lookups), and none in B.

**Decision.**

- **Registers stay as they are** (`Array Value` with the `fl` marker, and a `FloatArray`). The boxes
  made at their edges (a boolean result, a returned number, the callee's `this`) are removed by
  local changes (steps 1 and 2 of the plan), not by a new representation.
- **Stored slots use B**: property values, array elements and environment slots, in the object
  model of section 2.3. B needs no runtime call for a number, has no NaN obligation in Lean, and
  needs no collector before it can land.
- **A is specified as the image for Wasm linear memory**, where one word a slot matters and a word
  access is one load in compiled Wasm. `encodeW` below is that layout, proved against the same
  `Value`, so the later step does not need a new specification.
- **C is not taken**: it allocates for the numbers that graphics code uses, needs the collector
  first, and the measured integer share comes from a corpus without such code.

Lean representation:

```lean
/-- The tag of a slot. `Value.fl` has no tag: it is only the registers' marker. -/
def Tag.undef : UInt8 := 0   -- null 1, false 2, true 3, num 4, str 5, obj 6, sym 7, big 8, hole 9

/-- Slots in flat storage. Slot `i` is `tag[i]`, `num[i]` and the four bytes `ref[4*i ..]`. -/
structure Slots where
  tag : ByteArray
  num : FloatArray
  ref : ByteArray

/-- What a reference means: strings and big integers by handle. Objects and symbols are numbers already. -/
structure Tables where
  strs : Array String
  bigs : Array Int

def decodeSlot (T : Tables) (t : UInt8) (x : Float) (r : UInt32) : Option Value
def encodeSlot (T : Tables) : Value → (UInt8 × Float × UInt32) × Tables   -- a string or big integer takes a handle
def Slots.read (T : Tables) (s : Slots) (i : Nat) : Option Value
def Slots.write (s : Slots) (i : Nat) (t : UInt8) (x : Float) (r : UInt32) : Slots
```

Theorems owed (B):

```lean
theorem decode_encode (hv : v ≠ .fl) :
    decodeSlot (encodeSlot T v).2 (encodeSlot T v).1.1 (encodeSlot T v).1.2.1 (encodeSlot T v).1.2.2 = some v
theorem decode_grow (hT : T ≤ T') (h : decodeSlot T t x r = some v) : decodeSlot T' t x r = some v
theorem Slots.read_write (hi : i < s.size) :
    (s.write i t x r).read T j = if j = i then decodeSlot T t x r else s.read T j
theorem Slots.write_wf (h : s.WF) : (s.write i t x r).WF        -- the three arrays keep their sizes
```

No statement about NaN is needed for B: `Value.num` holds a Lean `Float`, the slot holds the same
`Float`, and typed-array and `DataView` reads already make their `Float` with `Float.ofBits`.

Theorems owed (A, the linear-memory image), with the correct canonical-NaN image:

```lean
def canonNaN : UInt64 := 0x7FF8000000000000
/-- Doubles are every word below 0xFFF9000000000000 whose NaN, if it is one, is `canonNaN`; the seven
tags 0xFFF9 to 0xFFFF in the top 16 bits carry constants (payload 0) and 32-bit handles. -/
def encodeW (T : Tables) : Value → UInt64 × Tables
def decodeW (T : Tables) (w : UInt64) : Option Value
def IsCanonicalW (T : Tables) (w : UInt64) : Bool           -- bit tests and handle bounds only

theorem decodeW_encodeW (hv : v ≠ .fl) : decodeW (encodeW T v).2 (encodeW T v).1 = some v
theorem isCanonicalW_iff : IsCanonicalW T w = true ↔ ∃ v, decodeW T w = some v
theorem encodeW_decodeW (h : decodeW T w = some v) (hi : v.isImmediate) : (encodeW T v).1 = w   -- not str, not big
theorem encodeW_num_nan (h : x.isNaN) : (encodeW T (.num x)).1 = canonNaN
theorem encodeW_negZero : (encodeW T (.num (-0.0))).1 = 0x8000000000000000
```

`decodeW_encodeW` rests on `Float.ofBits (Float.toBits x) = x`, which holds in the one-NaN model
because `toBits` gives the canonical pattern. The reverse direction (`encodeW_decodeW`) holds only on
canonical words, and for strings and big integers only up to the handle, since encoding takes a new
handle. So `IsCanonicalW` is a concrete predicate and every producer of words
(arithmetic, typed-array reads, host values) must be proved to establish it. The bit lemmas use
core `UInt64` and `BitVec` lemmas and `decide` on closed terms; `bv_decide` and `native_decide` are
not used.

### 2.3 Objects: atoms, shapes over flat slots, dictionaries as specification and fallback

Today an ordinary object is an `Obj` record with a `PropMap` (key array, value array of boxed
`PropV`, an optional hash index) and a second key array for order. A property write rebuilds the
`Obj` record (section 1.4); a read scans the keys by string comparison.

- **Atoms.** A property key is a number: `atoms : Array String` with `atomOf : HashMap String Atom`,
  filled by the parser for names in program text and by `toKey` for computed keys. Symbols keep their
  numbers in a separate range. Theorem: `atoms[atomOf k] = k`, and `atomOf` is injective.
- **Shapes.** A shape is an immutable record: the atoms of an object's own properties in insertion
  order, the attributes of each (data or accessor, writable, enumerable, configurable), the
  prototype, and whether the object is extensible. Shapes are interned in a table
  (`shapes : Array Shape`); a transition table maps (shape, atom, attributes) to the next shape.
  Property `i` of an object of shape `s` is slot `base + i` of the object's slot range in one `Slots`
  store for the whole heap. An accessor's getter and setter take two slots.
- **Object headers** are fixed-width records in a `ByteArray`, indexed by the object's handle (the
  number that `Value.obj` already carries): shape, slot base, slot capacity, kind tag, flags.
- **Dictionaries stay.** An object leaves shape mode and keeps today's `Obj` (in a side array) when
  it is exotic (Proxy, arguments, typed arrays, module namespaces), after `delete` of a property that
  is not the last, when it passes a bound on properties, or when integer-like keys are added to a
  non-array. The generic operations on `Obj` are the specification of both modes.
- **Array elements** are a second slot range of an array object (dense, with holes as tag `hole`),
  with the same fallback to `Kind.array` semantics for sparse or huge arrays.

The refinement, with handles kept equal on both sides (no renaming):

```lean
/-- The flat heap, read as the specification's heap. -/
def FHeap.abs (f : FHeap H) : HeapOf H

/-- Well-formedness: slot ranges are disjoint and inside the store, every shape id and handle is in
range, each shape lists distinct atoms, the transition table agrees with the shapes. -/
structure FHeap.Inv (f : FHeap H) : Prop

/-- `f` refines `h` on what is reachable from the roots. -/
def HeapRefines (roots : List Nat) (f : FHeap H) (h : HeapOf H) : Prop :=
  f.Inv ∧ (∀ id, Reachable h roots id → (f.abs).objs[id]? = h.objs[id]?) ∧
  (∀ e, ReachableEnv h roots e → (f.abs).envs[e]? = h.envs[e]?) ∧ (f.abs).toColdHeap = h.toColdHeap

theorem abs_getOwn (hI : f.Inv) : (f.getOwn o k) = (f.abs).getOwn o (atomName k)
theorem abs_defineOwn (hI : f.Inv) : (f.defineOwn o k d).abs = (f.abs).defineOwn o (atomName k) d
theorem abs_delete, abs_setProto, abs_preventExtensions                  -- the same form
theorem abs_ownKeys (hI : f.Inv) : (f.ownKeys o).map atomName = (f.abs).ownKeys o   -- integer keys ascending, then insertion order
theorem op_inv : f.Inv → (f.op args).Inv                                 -- for each operation
```

`abs_*` are commuting squares against the existing `Obj` functions, so the step from one object
operation to `getV` and `putV` reuses the evaluator's own code on `f.abs`. Enumeration order,
attributes, deletion and array length each have their own clause, as the fact-check on the tracking
issue asked.

### 2.4 Inline caches: `ValidIC`

A cache entry is data beside the bytecode, one per instruction site, read with the receiver's
header. The entry kinds, and what each needs to be valid:

```lean
inductive IC where
  | empty
  /-- An own data property of the receiver. -/
  | own (shape : ShapeId) (slot : UInt32)
  /-- A data property found on the prototype chain. -/
  | proto (shape : ShapeId) (holder : UInt32) (holderShape : ShapeId) (slot : UInt32) (epoch : UInt32)
  /-- No property on the receiver or its chain. -/
  | absent (shape : ShapeId) (epoch : UInt32)
  /-- A write to an existing writable own data property. -/
  | write (shape : ShapeId) (slot : UInt32)
  /-- A write that adds a property: the transition, with no setter and no read-only property on the chain. -/
  | add (shape next : ShapeId) (slot : UInt32) (epoch : UInt32)

def ValidIC (f : FHeap H) (key : Atom) : IC → Prop
  | .empty => True
  | .own s i => (shape f s).ordinary ∧ (shape f s).key i = some key ∧ (shape f s).isData i
  | .proto s holder hs i e =>
      (shape f s).ordinary ∧ key ∉ (shape f s).keys ∧
      (e = f.protoEpoch → ChainTo f (shape f s).proto key holder ∧ (header f holder).shape = hs) ∧
      (shape f hs).key i = some key ∧ (shape f hs).isData i
  | .absent s e => (shape f s).ordinary ∧ key ∉ (shape f s).keys ∧
      (e = f.protoEpoch → ChainLacks f (shape f s).proto key)
  | .write s i => (shape f s).ordinary ∧ (shape f s).key i = some key ∧ (shape f s).isWritableData i
  | .add s n i e => (shape f s).ordinary ∧ (shape f s).extensible ∧ key ∉ (shape f s).keys ∧
      transition f s key dataDefault = some n ∧ (shape f n).key i = some key ∧
      (e = f.protoEpoch → ChainLacksSetterAndReadOnly f (shape f s).proto key)
```

- **Own and write** entries are facts about immutable shapes only, so they stay valid for ever; the
  run-time guard is "the receiver is in shape mode and its shape is `s`". The prototype chain does not
  matter for an own data property.
- **Proto, absent and add** entries depend on the chain. The guard is the receiver's shape (which
  fixes its prototype), the realm's `protoEpoch`, and for `proto` the holder's shape. `protoEpoch`
  rises when an object that is some object's prototype changes shape or leaves shape mode, when any
  object's prototype is set, and when an object first becomes a prototype. `ChainTo`, `ChainLacks`
  and `ChainLacksSetterAndReadOnly` walk ordinary shape-mode objects only: a Proxy or a dictionary
  object on the chain makes the entry not fillable. The epoch is coarse (one change on any
  prototype empties every chain entry); a validity cell per holder is the later refinement, with the
  same theorem.
- **A miss runs the generic operation from the unchanged state and may then refill the entry.** No
  state has to be rebuilt, so there is no deoptimisation relation.

```lean
structure ICInv (f : FHeap H) (c : Caches) : Prop where
  valid : ∀ site key ic, c.at site = some (key, ic) → ValidIC f key ic

theorem cachedGet_eq (hI : f.Inv) (hC : ICInv f c) :
    (cachedGet f c site recv key).1 = genericGet f recv key          -- the result and the heap; the cache is .2
theorem cachedSet_eq (hI : f.Inv) (hC : ICInv f c) :
    (cachedSet f c site recv key v).1 = genericSet f recv key v
theorem icInv_step (hC : ICInv f c) : ICInv f' c'                    -- for every heap operation and every refill
```

`icInv_step` is easy for a write to a slot value and for an epoch rise (the premise of each chain
clause becomes false). The work is in showing that every operation that changes a chain fact
raises the epoch.

A cache is not assumed to be a gain. quickjs-ng removed its caches after measuring a loss; step 9
of the plan lands only with a before-and-after timing on the library corpus and on real pages.

### 2.5 Frames in flat storage; the register file keeps one owner

The register file stays `Array Value` and `FloatArray` (section 2.2). What changes around it:

```lean
structure Frames where
  bytes : ByteArray     -- one fixed-width record a call: code id, return pc, base, environment, result register
  depth : UInt32
```

- A call writes 20 bytes at the top of `Frames.bytes`; today it allocates a `VFrame` (56 bytes) and
  a list cell (24 bytes). The code of a frame is an index into `codes : Array Code`, filled when a
  function is compiled, not a pointer.
- The registers, the frames and the heap's arrays each have one owner across an instruction: no
  `let h ← get` may stay alive across a write to the heap (the `HeapOf` copy of section 1.4).
- An instruction's fast path returns a scalar or the arrays themselves, with no `M` result, tuple or
  `Option`; it enters `M` only to call an operation that can throw or run user code. This is the
  shape of [`CoreModel.lean`](../labs/demos/foafnaut/bubblepop_perf/lean/CoreModel.lean), which runs
  a call in 17 ns where the machine takes 145 ns.

Theorem: the frame stack refines the present `List VFrame`:

```lean
def Frames.abs (codes : Array Code) (f : Frames) : List VFrame
theorem Frames.abs_push : (f.push c pc bp env dst).abs codes = { code := codes[c]!, pc, bp, env, dst, depth := f.depth + 1 } :: f.abs codes
theorem Frames.abs_pop (h : 0 < f.depth) : ∃ fr, f.abs codes = fr :: (f.pop).abs codes
theorem vmStep_refines : -- one instruction of the machine with flat frames, read back, is one instruction of `vmLoop`
    absState (flatStep n code pc fr regs fregs h) = vmLoopStep n code pc (absState (fr, regs, fregs, h))
```

and by induction on fuel the loop with flat frames equals `vmLoop`; with the compiler theorem and
fuel monotonicity of the evaluator (in progress under the tracking issue, not repeated here) that
gives equality with the evaluator when the machine is off.

### 2.6 Memory: a mark and sweep that does not move, over handle arrays

Objects are indices already, and a Lean value cannot hold a cycle of pointers, so the runtime's
reference counts cannot reclaim objects whatever is done: the choice is a collector over handles or
no reclamation (today: no collector, and a script is stopped at 2^23 objects).

| | Mark and sweep, not moving | Keep counting, find cycles separately | Moving or generational |
|---|---|---|---|
| Frees cycles | yes | only with a second tracing pass, which is the collector | yes |
| Cost on the hot path | none between collections | a count per handle copy, in Lean code, and a count array | write barrier |
| Proof | handles are stable, so the refinement keeps identity on handles | counts must be proved equal to the number of references: every slot write is a proof obligation | every theorem gains "up to renaming of handles" |
| Pause | proportional to live objects, at a task boundary | none | shorter |

**Decision: mark and sweep, not moving**, run between tasks of the event loop when allocation since
the last run passes a threshold. Free handles go on a free list per table (objects, environments,
strings, big integers); slot ranges go on size-class free lists. The roots are the global
environment, the job queue, the host's handles (DOM wrappers, timers, pending callbacks), realms and
the machine's registers and frames (empty between tasks).

The specification gets the same operation, so that handles stay equal on both sides:

```lean
/-- The specification's collector: every object not reachable from the roots becomes the default
object and its id goes on `objFree`; `alloc` takes from `objFree` first (as `pushEnv` does for
environments today). -/
def HeapOf.sweep (roots : List Nat) (h : HeapOf H) : HeapOf H

theorem sweep_reachable (hr : Reachable h roots id) : (h.sweep roots).objs[id]? = h.objs[id]?
theorem sweep_unobservable :                       -- proved once, about the specification
    ResultRel ρ (run prog h) (run prog (h.sweep roots))     -- ρ: a partial bijection on object ids
theorem fsweep_refines (hR : HeapRefines roots f h) : HeapRefines roots (f.sweep roots) (h.sweep roots)
theorem mark_bound : marking visits each live object once: work ≤ c * (live objects + live slots)
```

Renaming appears in one theorem, `sweep_unobservable`, about the specification alone. The flat heap
is then proved against the specification with the collector in it, with identity on handles.
`mark_bound` is the safety property that a collection cannot hang; the collector's own work lists
are flat arrays with a proved size bound.

The Lean runtime keeps counting what it owns: the tables themselves and the strings inside
`Tables.strs` (a freed string slot is overwritten with `""`).

### 2.7 Hook for guarded hints

[Issue 532](https://github.com/danbri/factoidal-core/issues/532) wants learned profiles, kept on
the user's machine and partitioned by site. This design leaves two hook points and ships no data:

- `Caches` is created by `Caches.init (hints : Hints) (code : Code)`. A hint may pre-fill an entry or
  choose which kind to try first. Every entry, however it was made, is read through the guard of
  `cachedGet` and `cachedSet`, and `ICInv` is established for a pre-filled entry by checking
  `ValidIC`'s shape clauses at fill time and stamping chain entries with an epoch that is not the
  current one.
- The hint store is keyed by the top-level site, and a run reads only its own key.

```lean
theorem hints_irrelevant : (run hints prog f).eraseCaches = (run Hints.none prog f).eraseCaches
theorem hints_partitioned (h : ∀ k, k = site → store.get k = store'.get k) :
    runSite site store prog f = runSite site store' prog f
```

The first says a hint can cost time and never change a result; the second says what one site
recorded cannot reach a run of another site.

## 3. Expected gains, with the arithmetic

Let `m` be the share of script time in allocation, free and thread-local lookup (20 to 54% in
section 1.2, without the reference-count column) and `a` the share of allocations a step removes. If
the cost of an allocation does not depend on its kind, the step saves about `m × a` of script time.
These are estimates from measured shares; each step replaces its row by a measurement.

| Step | `a`, measured | Estimated saving of script time |
|---|---|---|
| Call path of the register machine: no `HeapOf` copy, no `Option` and tuples, no boxed return, constant `this` (5 or 6 of 8 allocations a call) | lodash 27%, immutable 11%, acorn 7% | lodash 6 to 7%, immutable and acorn 2 to 3% |
| Booleans as constants | lodash 10%, acorn 3%, immutable 2.5% | lodash 2.5%, others under 1% |
| `toNum` and bit operators without a result cell and boxed float | pako 16%, immutable 11% | pako 6%, immutable 3% |
| Property and element writes without a new `Obj` record and closure | immutable 13%, pako 7.5% | immutable 3%, pako 3% |
| Regular expression matcher without `Option`, tuple and closure per character | marked 88%, acorn 19% | marked up to 47%, acorn 5% |
| Flat frames | lodash 11%, immutable 4% | lodash 2.5% |
| Flat slots for stored values: environments, properties and elements (the `Value` boxes that the first two rows do not remove; part overlaps the third row) | lodash 13%, pako 23%, immutable 17% | lodash 3%, pako up to 8%, immutable 4% |
| Thread-local lookups (runtime build) | not an allocation count | up to the 7 to 23% of section 1.2; measured for the heartbeat half alone: 2 to 3% (below) |

Sum for lodash, counting each allocation once: about 16% of script time, 1.2 times; the runtime
change then removes what is left of the 7.8% thread-local share. The bound for removing every
allocation is `1 / (1 - m)`, 1.25 to 2.2 times. The larger factor that `CoreModel.lean` shows (8 times on a call) comes from the
machine's instruction path as well, not from allocation alone; shapes and caches add the gain on
property access (lookup is 5 to 15% of corpus samples in the stage C spike on
[PR 486](https://github.com/danbri/factoidal-core/pull/486)).

## 4. Migration plan

Small steps, each a PR with its theorem, its count from `opcount.py` and `leancount.py` before and
after, timings on the library corpus and the page snapshots, and identical Test262 verdicts with
the machine on and off. A step changes no code path it does not name. Each works on wasm32 and
native: every structure below uses `ByteArray`, `FloatArray` and scalar fields only.

| # | Step | Target to show | Theorem |
|---|---|---|---|
| 0 | This record, the instruments, and `RepBench.lean` | baseline | none |
| 1 | Register machine call path. **1a, done (section 4.2):** the step decrement of a call in a function of its own, so that the `HeapOf` record is updated in place. **1b, open:** the callee test as a function that returns scalars; `ret` moves a number without boxing; a constant `Value.obj` for the global `this` | 1a: a compiled call from 8 allocations and 264 bytes to 7 and 176. 1b: to 2 and 80; lodash allocations −27% in all | 1a: `HeapOf.decStep_eq`. 1b: the `call` and `ret` arms satisfy the same step equations as before (stated as lemmas on `vmLoop`) |
| 2 | `Value.ofBool`: the two boolean values as constants | comparisons allocate nothing | `Value.ofBool b = .bool b` |
| 3 | `toNum`, `toInt32` and the bit operators with a pure first case for numbers | `s = i & 255` from 8 allocations to 1 | the fast function equals the monadic one |
| 4 | Writes: `setOwnData`, `setElem`, `defineOwn` update the object in place with no closure and no rebuilt record | `o.x = i` from 5 allocations to 1, `a[3] = i` from 7 to 1 | equal to `updateObj` with the present function |
| 5 | Built-in call path: `sizeCost`, `charge`, `subjectCached`, `Ctx` | `Math.floor(i)` from 16 allocations to under 6 | equal results and equal step count |
| 6 | Regular expression matcher: the character read inlined into its callers; no continuation for a sequence whose first term (a character or an assertion) fails. **Done with this record** (section 4.1) | marked allocations −64%, bytes −73%, time −37% | `matchNode_seq` in [`RegexTheorems.lean`](../formal/lean4/L4Factoidal/JS/RegexTheorems.lean): the shorter path gives the answer of the sequencing rule |
| 7 | Parser: `peek` and `advance` without a result cell | Test262 allocations −20% | equal token stream and tree |
| 8 | Flat frames (`Frames`, `codes`) | no `VFrame` and list cell | `Frames.abs_push`, `Frames.abs_pop`, `vmStep_refines` |
| 9 | Flat slots (B) for environment slots and array elements that hold numbers | a number stored in a closure variable or an array allocates nothing | `decode_encode`, `Slots.read_write` |
| 10 | Atoms | none alone | injective table |
| 11 | Shapes and flat object slots, dictionaries as fallback | property read with no string comparison; object literal from 16 allocations to under 4 | `HeapRefines`, `abs_*` |
| 12 | Inline caches, own and write first, then proto, absent and add | timed on corpus and pages; kept only if faster | `cachedGet_eq`, `cachedSet_eq`, `icInv_step` |
| 13 | Collector; strings and big integers by handle | memory bounded on long-lived pages | `sweep_unobservable`, `fsweep_refines`, `mark_bound` |
| 14 | Hints hook | none | `hints_irrelevant`, `hints_partitioned` |

Steps 1 to 5 edit functions of the evaluator's mutual block or the built-in dispatchers, which the
fuel-monotonicity proof covers arm by arm; they are sequenced with that work so that neither
invalidates the other. Steps 6 and 7 are in files of their own, which is why step 6 went first: the
matcher is the largest source by mean on the library corpus (21.4% of allocations, against 20.3% for
the register machine), though not on the pages measured.

### 4.1 Step 6, measured

Two changes in [`JS/Regex.lean`](../formal/lean4/L4Factoidal/JS/Regex.lean):

- `readAt` and `step1` are `@[inline]`. Every caller matches on their answer at once, so the
  compiler removes the `Option` and the pair: a character read allocates nothing. No definition
  changed, so the existing theorems (`readAt_fwd`, `readAt_back`, `step1_fwd`, `step1_back`) still
  state what the matcher reads.
- In a forward sequence whose first term is a single character or an assertion (`^`, `$`, `\b`),
  `matchNode` tests the term before it makes the continuation for the rest. A pattern that starts
  with `^` and is tried at every later start position made one closure (71 bytes) per position
  before. `matchNode_seq` proves the shorter path equal to the general rule for every first term and
  every fuel (axioms: `propext`, `Quot.sound`).

| | allocations before | after | bytes before | after | CPU ms before | after |
|---|---|---|---|---|---|---|
| marked | 14.54 M | 5.20 M (−64.2%) | 479 MB | 127 MB (−73.4%) | 283 | 179 (−37%) |
| acorn | 26.81 M | 23.09 M (−13.9%) | 737 MB | 591 MB (−19.8%) | 823 | 791 (−3.9%) |
| lodash | 12.38 M | 12.38 M | 349 MB | 349 MB | 410 | 413 |
| immutable | 23.46 M | 23.46 M | 644 MB | 644 MB | 749 | 746 |
| pako | 59.15 M | 59.15 M | 1,458 MB | 1,458 MB | 1,692 | 1,644 |

CPU time is user plus system, least of nine interleaved runs, on two `leanjs` binaries made from
the same generated C apart from `Regex.c` (`build-count.sh` with `LEANPROF_PLAIN=1`); the last three
rows changed no code that they run, so their differences (+0.9% to −2.8%) are the noise of the
method on a shared machine. The five libraries print the same result line before and after.
Test262, 3,082 files (`built-ins/RegExp` without the generated `property-escapes` files, the six
`String.prototype` methods that take a pattern, `language/literals/regexp`, and two directories that
use no pattern): the same verdict for every file (3,011 pass, 71 fail on both), 25.8 s to 23.7 s of
CPU.

What is left in the matcher on marked: one `St` record (24 bytes) per start position (3.0 M), which
needs either a first-character test before the record is made or a search that skips start positions
an anchored pattern cannot match. A recursion in place of the `for` loop of `exec` was tried and
proved equal to the loop; it removed no allocation and was not kept.

Separate, in the runtime build and not in this plan's proofs: the two thread-local lookups per
allocation on macOS (finding 2). The Linux engine already links the runtime with initial-exec
thread-local storage. One of the two is gone from the native engine on `main` since `fd53dac77`
(`lean_no_heartbeat.h`: the compiled code counts no heartbeat), after the release that was profiled
here. Measured for `leanjs` the same way: the generated C compiled with `lean_inc_heartbeat` replaced
by an empty function runs the five libraries in 0.969 to 0.983 of the time (CPU, least of five
interleaved runs). The allocator's own lookup (`mi_malloc_small`) remains on macOS; removing it
needs a runtime built for it and is not measured.

Also separate: the DOM bridge (`callImport`, `Page.i32v`, `Dom.ret`, `serveNative`) is the second
owner of memory-management time on the Wikipedia page. Its values cross as byte buffers and boxed
integers; it needs its own measurement with the same instruments.

### 4.2 Step 1a, measured

The counting build records the line of each allocation in the generated C. For a compiled call it
shows where the 88-byte `HeapOf` record of section 1.4 is made: at `tickCall`'s
`{ h with steps := h.steps - 1 }`, inlined into `vmLoop`. There the compiler has passed the record's
fields to a join point before the update, so it does not see a record it may reuse and builds a new
one (five count increments, then the allocation) on every call. `tick`, at loop heads, has a shape
that it does reuse.

The change: the update is `HeapOf.decStep`, a function of its own that is not inlined. Inside it the
record is the function's argument at its last use, so it is updated in place when nothing else holds
it. `tickCall` keeps its `do` block and calls it. `HeapOf.decStep_eq` (by `rfl`, a `simp` lemma)
states that it is the record update, so the meaning of `tickCall` is unchanged. `tickCall` is
defined before the evaluator's mutual block; no function of the block changes.

| | allocations before | after | bytes before | after | count operations before | after | CPU ms before | after |
|---|---|---|---|---|---|---|---|---|
| one compiled call (loop of `s = g1(i)`) | 8 | 7 | 264 | 176 | 71 | 53 | 761 (3 M calls) | 650 (−14.5%) |
| lodash, whole run | 13.30 M | 12.64 M (−5.0%) | 377.6 MB | 319.4 MB (−15.4%) | 73.5 M | 60.8 M (−17.2%) | 431 | 416 (−3.3%) |
| immutable, whole run | 24.04 M | 23.55 M (−2.1%) | 663.7 MB | 619.9 MB (−6.6%) | 138.0 M | 127.9 M (−7.3%) | 775 | 745 (−3.8%) |
| acorn, pako, marked | not counted | | | | | | 788, 1,709, 183 | 782, 1,688, 182 |

CPU time is the least of nine interleaved runs on a machine with other work; a second run of seven
gave −5% on the call loop and larger gains on lodash and immutable, so the time figures are
±5%; the counts are exact. The five libraries print the same lines.

What is left of the `HeapOf` copies: `callClosure` and `vmEnter` (the call depth updates of a call
that enters from the evaluator), 0.24 M copies on lodash. They are in the mutual block and wait with
step 1b.

## 5. What is not known yet

- The counts name constructor shapes, not types. An exact table by type needs the compiler's IR
  trace (`trace.compiler.ir.result`) of the evaluator, which is a full build of that file.
- No number here is from wasm32. The counts are the same there (they are taken in the C source),
  but sizes and the cost of a thread-local lookup differ.
- The operand distribution has no graphics workload.
- The page profiles cover five pages and the first 22 to 75 seconds of each run on a loaded machine.
- B for stored slots is chosen from the cost of the allocation it avoids; it is not yet timed against
  today's `Array Value` slots with boxed numbers. Step 9 starts with that measurement, on
  `RepBench.lean` extended with a stored-number case.
