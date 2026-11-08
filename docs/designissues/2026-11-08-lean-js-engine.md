# A JavaScript engine written in Lean

Date: 2026-11-08. Author: leanjs, a subagent of session depmap-0e.
Related: https://github.com/danbri/factoidal/issues/1244 (WasmVM, the Lean WebAssembly
engine), https://github.com/danbri/factoidal/issues/1252 (VerifiedJS cannot run the
script fixtures), https://github.com/danbri/factoidal/issues/1203 (JSCert study).
Records it joins: `2026-11-07-wasmvm-engine.md`, `2026-11-07-wasmvm-spec-layer.md`,
`2026-11-08-page-scripts.md`, `2026-11-08-event-loop.md`.

## 1. Result

`formal/lean4/L4Factoidal/JS/` is the start of a JavaScript engine in Lean, in its own
library `JS` (lakefile), with no Mathlib. It parses and runs a core of ECMAScript:
values, objects and prototypes, property access with accessors, functions, closures
that share their environment, `this`, `new`, `let`/`const`/`var` with hoisting and the
temporal dead zone, `if`/`while`/`do`/`for`/`for`-`in`/`switch`/labels,
`return`/`throw`/`try`/`catch`/`finally`, arrow functions, and the built-ins that the
Test262 harness and simple pages use. Stage 2 added destructuring (binding and
assignment patterns), default and rest parameters, spread, template literals (and
tagged templates), Symbol with the well-known symbols, the iteration protocol with
`for`-`of` and Array and String iterators, classes (`extends`, `super`, accessors,
static members, public fields), `new.target`, direct and indirect `eval`, the `Function`
constructor and identifier escapes. Stage 3 added generators (section 6a) and early
errors: `break`/`continue` targets, labels, lexical declarations in single-statement
positions, redeclarations in a block or script, duplicate parameters where they are
not allowed, strict-mode reserved words. Stage 4 added BigInt (literals, arithmetic,
comparison with Numbers, `BigInt()`), the `with` statement (an object environment
record, with `@@unscopables`), and more early errors (escaped keywords, `switch`
redeclarations, `eval`/`arguments` in strict assignment patterns). Stage 5 added
Promise (`then`, `catch`, `finally`, `resolve`, `reject`, `all`), the job queue,
`async` functions, arrows and methods with `await`, and `yield`/`await` inside
expressions (section 6a). Stage 6 added async generators, private class members
(`#x` fields, methods, accessors, `#x in o`) and class static blocks. Stage 7 added
built-ins: Map, Set, WeakMap, WeakSet, Reflect, `Object.defineProperties`/`seal`/
`isSealed`/`getOwnPropertyDescriptors`/`fromEntries`, `Array.prototype.flat`/`flatMap`/
`at`/`findLast`/`findLastIndex`, `String.prototype.padStart`/`padEnd`/`at`/
`codePointAt`/`trimStart`/`trimEnd`/`replace`/`replaceAll` (string patterns),
`String.fromCodePoint`, `Number.isFinite`/`isNaN`/`isSafeInteger`, and more of Math. `lake exe leanjs` runs a script, Test262 files
or the benchmarks.

Measured results are in section 9 (Test262 counts) and section 10 (speed).

It is not wired into the browser (section 11 says what that takes).

## 2. Why a JavaScript engine in Lean

Today a page script runs in QuickJS-NG compiled to WebAssembly, run by WasmVM
(`2026-11-07-wasmvm-engine.md`, "QuickJS in WasmVM"). That is two interpreters: WasmVM
interprets the Wasm of QuickJS, and QuickJS interprets the script. WasmVM runs about
360 M Wasm instructions per second natively and about 11 M per second on the Hub; the
QuickJS path is about 80 to 170 times slower than native QuickJS. An engine written in
Lean removes the outer interpreter: Lean compiles it to C (native) and to Wasm through
Emscripten (Hub), as for the rest of the engine.

It also puts the semantics where the rest of the browser is: the DOM arena, the event
loop and the typed DOM commands are Lean. A JavaScript value can then be a Lean value,
and a theorem can state what a script can do to the DOM.

## 3. Earlier work: VerifiedJS

https://github.com/danbri/factoidal/issues/1252 records the measurement of VerifiedJS at
its pin. It is blocked for three reasons: the repository has no licence, so nothing of
it may be committed here; its full build fails in `ClosureConvertCorrect`, so the
end-to-end theorem is not checked; and its compiled Wasm and its Core semantics cannot
run the script fixtures (closure writes are lost, strings compare by identity, arrays
are stubs, a compiled module can import nothing that returns a value). Its option 3,
"a page-script engine in Lean here, with semantics checked against Test262", is this
work.

## 4. Spec sources

### 4a. ESMeta (mechanised ECMA-262)

https://github.com/es-meta/esmeta, BSD-3-Clause, main at `22a5ba04` (2026-11-07). ESMeta
(the successor of JISET) reads `spec.html` of tc39/ecma262 and compiles each algorithm
of the specification into IR functions (`src/main/scala/esmeta/ir`: `Inst` =
`let`, `assign`, `if`, `loop`, `call`, `sdo-call`, `return`, `assert`, `expand`,
`delete`, `push`, `remove-elem`; `Expr` with records, lists, `?`/`!` completion
shortcuts). It has an interpreter of that IR and runs Test262 on it. Its own summary
(`src/main/resources/result/spec-summary`), for ecma262 `0248456c` (ES2026):

- 2,909 algorithms, 2,549 compiled completely (87.6 %);
- 22,863 algorithm steps, 22,156 compiled (96.9 %);
- 400 grammar productions (205 syntactic, 179 lexical, 16 numeric string);
- 32 algorithms written by hand in IR (`manuals/funcs/override`), for example
  `Math.random` and `BigInt::toString`.

The extracted IR is not stored in the repository: it is produced by running ESMeta
(Scala 3, sbt, a JVM). `esmeta extract -extract:log` writes it.

### 4b. The ecmarkup source of ECMA-262

https://github.com/tc39/ecma262, `spec.html` (ecmarkup). Licence: the text under Ecma's
"alternative copyright notice" (copy and derivative works allowed with the notice),
code under Ecma's MIT-style software policy. Algorithm steps are structured HTML
(`<emu-alg>` lists); grammar is `<emu-grammar>`. ESMeta parses exactly this; parsing it
ourselves repeats ESMeta's 87.6 %.

### 4c. Test262

https://github.com/tc39/test262, BSD-3-Clause. The conformance suite: about 48,600
files under `test/built-ins`, `test/language` and `test/annexB` at the pinned commit.
This is what the owner's bar is stated in (80 % of Test262 for an engine without a JIT,
Apple's EU rule).

### 4d. Decision

The route copies the WasmVM one in shape, but not in order:

1. **Now: a hand-written definitional interpreter, structured by the spec.** Each Lean
   function is named after the ECMA-262 operation it implements (`GetV`, `OrdinarySet`,
   `ToPrimitive`, `IsLooselyEqual`, `ForBodyEvaluation`, ...) and cites its section.
   Test262 measures it. This gives a running engine tonight and a measured base.
2. **Next: a generated reference semantics.** Port ESMeta's IR to Lean the way
   `tools/wasmvm/port-spec.py` ports SpecTec's output: a dumped IR (pinned ESMeta
   commit + pinned ecma262 commit, vendored with the exact command) and a Python
   rewrite into Lean definitions over an IR interpreter in Lean. The 12.4 % of
   algorithms that ESMeta does not compile completely are the gap, listed by ESMeta's
   own `complete-funcs`.
3. **Then: refinement.** Theorems that the hand-written evaluator (the fast form) agrees
   with the IR semantics, operation by operation, as `step_refines` does for WasmVM.

Why not generate first: the WasmVM spec layer was usable because SpecTec gives
inductive relations for a small language. ECMA-262's algorithms are 22,863 steps over
an IR whose runtime (records, lists, completion records, syntax-directed operations)
is itself a language; an IR interpreter in Lean is a project of its own, and its
speed is the speed of interpreting the spec (ESMeta's interpreter takes seconds for a
Test262 file). A page needs a fast engine first. The spec-shaped hand-written code
makes step 3 tractable, because each function has one spec operation to agree with.

Why not ecmarkup directly: it repeats ESMeta's extraction work.

Vendored now: only the Test262 subset that the runner uses
(`third_party/testing/test262/`, PROVENANCE pinned at
`5ef1e5723be95296f36afb0386676fed0205869c`). ESMeta and ecma262 are not vendored yet,
because nothing here reads them; step 2 vendors the dumped IR.

## 5. Value, object, realm and agent model

`JS/Value.lean`:

- `Value` = `undef | null | bool | num (Float) | str (String) | obj (Nat)` (§6.1).
  Symbol and BigInt are not there yet.
- An object is an index into the heap's object arena. `Obj` has own properties
  (`Std.HashMap String PropV` plus insertion order), `[[Prototype]]`,
  `[[Extensible]]`, and a `Kind`: ordinary, Array (elements in an `Array Value`;
  `length` is their count), function closure (`FunDef`, environment number, captured
  `this` for arrows), built-in function, bound function, primitive wrapper, Error,
  arguments. `PropV` is a data property (value, writable, enumerable, configurable) or
  an accessor (get, set, enumerable, configurable) (§6.1.7.1).
- Own keys come in the order of OrdinaryOwnPropertyKeys (§10.1.11): integer keys
  ascending, then strings in insertion order.
- Environments: `Env` is a declarative Environment Record (§9.1.1.1) in a second
  arena; a binding has mutability and an initialised flag (the temporal dead zone).
  Closures hold an environment number, so all closures of one scope share writes.
  The global environment (§9.1.1.4) is environment 0 (its `let`/`const`) plus the
  global object (its `var` and function declarations and the built-ins).
- Realm (§9.3): `Realm` holds the intrinsic prototypes and the global object.
  `freshHeap` builds it once; because the heap is a Lean value, every Test262 test
  starts from the same heap after the harness at no copy cost, and a page could fork
  a realm the same way.
- Agent (§9.7): one agent, one realm, one thread, as in a page. The step budget
  (`Heap.steps`) and the call depth limit (`Heap.maxDepth`, a `RangeError` like V8's)
  are the agent's limits; `Abrupt.halt` is a host interrupt, which `try` cannot catch.

Evaluation is in `M = EStateM Abrupt Heap`. A thrown JavaScript value is
`Abrupt.throw v`; `return`, `break` and `continue` are `Compl` values. Every function
of the evaluator takes a fuel argument and passes a smaller one to each recursive
call, so the whole mutual block is total by structural recursion (no `partial def`).
The fuel is `2^40` per script; the step budget, not the fuel, stops long scripts.

## 6. Job queue and the event loop

Stage 5 built the engine side. `Heap.jobs` is the job queue of §9.5
(HostEnqueuePromiseJob): a function and its arguments. Promise reactions, thenable
resolution and `await` resumptions are jobs. `runScript` runs the jobs after the
script until none is left, as a microtask checkpoint does (`runJobs`, oldest first).
In a page the same queue is what the event loop drains. The design for that:

- ECMA-262 jobs (§9.5 HostEnqueuePromiseJob) are host-defined. In HTML a Promise job
  is a microtask. The Lean event loop (`L4Factoidal.EventLoop`) already has the
  microtask queue (`queueMicrotask`, `checkpoint`), and `Hosts/Page.lean` runs
  `qjs_run_job` for QuickJS's own job queue after Lean's microtasks
  (`2026-11-08-event-loop.md`, section 4, records that this splits the order).
- With the Lean engine, a Promise reaction job is a Lean value (`Job = callback ×
  argument`) and goes on the event loop's microtask queue as a `Handle`, so
  `queueMicrotask` and `then` callbacks interleave in the order HTML requires. The
  `effects` function of `EventLoop.checkpoint` becomes "run this job in the engine and
  return the calls it made". The theorems `checkpoint_fifo` and `checkpoint_empties`
  then hold for Promise jobs too.
- Timers and listeners keep the `Hosts.Dom.Request` form (`listen`, `timer`,
  `clearTimer`), with a callback that is a function object number in the Lean heap in
  place of a QuickJS callback number.
- The `scriptSession` op (`labs/demos/foafnaut/WebScripts.lean`) keeps its actions
  (`load`, `start`, `click`, `advance`, `settle`, `turn`, `close`); its `Session`
  holds the JavaScript heap in place of the WasmVM store.

### 6a. Generators

A generator (§27.5) must stop at a `yield` and go on later. The evaluator is a
recursive Lean function, so it cannot stop in the middle of a call. The engine runs a
generator body on a second, small machine (`genRun` in `JS/Interp.lean`): a stack of
frames (`GFrame` in `JS/Value.lean`) for the statement lists, loops (`while`, `do`,
`for`, `for`-`of`), `try` statements, a pending completion while a `finally` runs, a
`yield*` delegate, and where the value sent by `next(v)` goes. Only a statement that
holds a `yield` is taken apart into frames; every statement without one runs in the
ordinary evaluator. `return()` and `throw()` unwind the frames, run `finally` blocks
and close `for`-`of` iterators. The generator object holds its frames in the heap
(`Kind.gen`), so a suspended generator is a value like any other object.

Supported `yield` positions: an expression statement (`yield e;`, `yield* e;`), the
right side of an assignment to a name or property, a declaration initialiser, and
`return yield e`. A `yield` inside another expression that is evaluated
unconditionally is moved before its statement (`f(yield x)` becomes `let %y0 = yield
x; f(%y0)`; `liftStmt`). The callee and the operands to the left are then evaluated
after the suspension: a difference from §13.3.6 when they have side effects. A
`yield` under `&&`, `||`, `??` or `?:` is refused with a `SyntaxError` at run time.

`async` functions use the same machine. In an async function the parser reads
`await e` as a `yield`; the function's object is a coroutine (`Kind.coro`) with the
promise it returns. At each suspension `asyncStep` resolves the awaited value to a
promise and queues the resumption as its reaction (§27.7.5.3 Await); the end of the
frames resolves the promise and a throw rejects it.

Async generators (stage 6) use the same frames. In an async generator the parser
marks `await e` (`yield` of a `%await` call), so the machine tells an await
(`GOut.awaited`) from a yield. The object (`Kind.agen`) keeps a queue of requests
(`next`, `return`, `throw`, each with its promise) and serves them one at a time
(`agenDrain`, `agenRun`; §27.6.3). Not done: the await of a yielded value before the
request resolves, and `for await`.

Private names (stage 6) are properties under a key that starts with U+10FFFE
(`privKey`), hidden from every key listing; reading or writing a private name that
the object does not have throws a `TypeError`. Two classes that declare the same
private name share the key, so the brand check of §7.3.31 is not exact.

## 7. Strings and numbers

- Strings: ECMAScript strings are sequences of UTF-16 code units (§6.1.4). The slice
  uses Lean `String` (Unicode scalar values): `length` counts UTF-16 units
  (`utf16Length`), but indexing and `charCodeAt` are per scalar value, and a lone
  surrogate from `\uD800` becomes U+FFFD. The target representation is a pair of
  forms, as engines use: Latin-1 bytes (`ByteArray`) when every unit is below 256,
  else `Array UInt16`, with ropes for repeated concatenation. That change is local to
  `Value.str` and the string built-ins.
- Numbers: Lean `Float` is IEEE 754 binary64; `+ - * /` are the hardware operations,
  correctly rounded. Lean 4.33 gives `Float` a logical model (`Float.Model`, a subtype
  of `UInt64`, in `Init/Data/Float/Model`), so arithmetic is not opaque to proofs.
  `Float.ofBits` is modelled by `Float.Model.ofBits`, which maps every NaN to one
  canonical NaN, and the compiled `lean_float_of_bits` agrees. ECMAScript permits
  this: NaN values are indistinguishable to ECMAScript code (§6.1.6.1), and
  SetValueInBuffer lets an implementation choose any NaN encoding.
- What C does not give with JavaScript's meaning is written in `JS/Number.lean` with
  exact integer arithmetic: `Number::toString` (shortest round-trip digits from
  `XPath4.shortestDigits`, which is exact rational arithmetic, then the §6.1.6.1.20
  layout), `StringToNumber` (the grammar here, the rounding by `XPath4.floatOfParsed`
  through `XSD.IEEE754`), `%` (exact `fmod` on dyadic rationals), `ToInt32` and
  `ToUint32` (exact on the integer part), `**` (C `pow` with JavaScript's NaN cases).
  Numeric literals are rounded correctly the same way.

## 8. Parser and memory

- Parser: there was no JavaScript parser in Lean in the repository (the HTML tree
  builder only finds `<script>` text). `JS/Lexer.lean` and `JS/Parser.lean` are new:
  a lexer whose scanners are tail calls (loops in C), and a recursive-descent parser
  with precedence climbing for the binary operators, automatic semicolon insertion and
  the restricted productions. Each parser function takes fuel (64 per token), so it is
  total. Early errors checked so far: `return` outside a function, invalid assignment
  targets, `const` without an initialiser, strict-mode `eval`/`arguments` bindings,
  `delete` of a name in strict code, duplicate `default`. The ES2024 grammar parts not
  parsed are refused with a `SyntaxError` that names them (classes, destructuring,
  default and rest parameters, spread, templates, regular expression literals,
  generators, `async`, optional chaining, `for`-`of`, modules).
- Memory: the heap is two arenas (objects, environments) with no collector. A page
  turn allocates; the plan is a mark-compact collection between tasks of the event
  loop (no JavaScript frame is live then, so the roots are the realm, environment 0,
  the listeners, timers and pending jobs that Lean holds). Compaction renumbers
  objects; the DOM side refers to function objects only through Lean-held listener
  records, which the collector rewrites. A theorem to aim at: collection does not
  change the result of any later turn (the renaming is a bijection on reachable
  objects and every heap operation commutes with it).

## 9. Test262

Subset: 70 directories of `test/language/expressions` and `test/language/statements`
(6,301 files, `third_party/testing/test262/DIRECTORIES`), the directories of the
features of sections 1 and 8. Every file in them runs, including the ones that use
features not implemented yet, so the count is against the whole of each directory.
Command (from `formal/lean4`):

    lake exe leanjs test262 ../../third_party/testing/test262 \
      $(cat ../../third_party/testing/test262/DIRECTORIES)

Rules: one run per file, sloppy mode unless `onlyStrict`; `assert.js` and `sta.js`
first, then the `includes:`; 20 M steps per file; `module`, `async` and
`resolution`-phase tests are skipped. A negative `parse` test passes only on a
`SyntaxError` before anything runs; a negative `runtime` test only on the named
error.

Results, stage 1 (commit of this record; 2026-11-08, the owner's Mac):

- 2,811 pass, 3,262 fail, 228 skip (module 224, others 4): 46.3 % of the 6,073 run.
  The whole run takes 4.8 s.
- Failures by cause (first message of each failing test): destructuring 1,143;
  generator and async methods 261; generators 172; escapes in identifiers 222;
  `eval` 178; BigInt literals 148; classes 117; spread 111; default parameters 75;
  `Symbol` 48; the `Function` constructor 41; early errors not detected (a
  negative test that ran) 159; invalid assignment targets that should parse
  (destructuring assignment) 143.

Stage 2 (destructuring, parameters, spread, templates, Symbol and iterators, classes,
eval, the `Function` constructor, identifier escapes): **4,558 pass, 1,515 fail, 228
skip (75.0 % of 6,073 run)**. Of the passes, 638 are negative tests (an expected
early or runtime error); the positive tests pass 3,920 of 5,068 (77.3 %). Stage 1 by
the same split: 840 negative and 1,971 positive passes. The negative count went down
because the parser now accepts syntax that it refused before, so a test that expects
an early error the parser does not check yet now fails.

Remaining failures by cause (stage 2): early errors not detected 362; generator
functions 296 and generator or async methods 261; BigInt 148; other unsupported syntax
94 (async, optional chaining, regular expression literals); private class members 79;
class static blocks 17; call depth (`RangeError` at depth 400) 30.

Stage 3 (generators, early errors): **5,098 pass, 975 fail, 228 skip (83.9 % of 6,073
run)**; 722 of the passes are negative tests, 4,376 of 5,068 positive tests pass
(86.3 %). 38 tests that passed at stage 2 fail now: 32 are negative tests that passed
only because the parser refused generators, 5 are `let` followed by a line break as
an identifier in a single-statement position (`if (x) let // newline {}`), 1 is an
escaped `let`.

Remaining failures by cause (stage 3): early errors not detected 278; BigInt 148;
other unsupported syntax 94 (optional chaining, regular expression literals, `async`
arrows); private class members 79; `async` methods 58; `yield` inside an expression
30; call depth 30; class static blocks 17.

Stage 4 (BigInt, `with`, more early errors, ToNumeric order): **5,403 pass, 670 fail,
228 skip (89.0 % of 6,073 run)**; 830 negative and 4,573 positive passes (positive
tests 90.2 %). No test that passed at stage 3 fails.

Remaining failures by cause (stage 4): early errors not detected 170; private class
members 79; `async` methods 58; `yield` inside an expression 35; call depth 31; class
static blocks 17; the rest are single semantic differences (about 280, each cause
under 35 tests).

Stage 5 (Promise, jobs, async functions, lifted `yield`): the runner now also runs the
225 tests with `flags: [async]` (with `harness/doneprintHandle.js`; a pass is the
`Test262:AsyncTestComplete` line), so 6,297 run and 4 are skipped (3 modules, 1 missing
include). **5,404 pass, 893 fail (85.8 % of 6,297 run)**: 804 negative passes, 4,600
of 5,292 positive tests (86.9 %). 21 of the 225 async tests pass; 200 of them are
async generators. 26 negative tests that passed at stage 4 only because `async` was
refused fail now; no positive test was lost.

Remaining failures by cause (stage 5): async generator methods 255; early errors not
detected 196; private class members 80; `yield` in a conditional position 32; call
depth 31; class static blocks 17.

Stage 6 (async generators, private members, static blocks): **5,616 pass, 681 fail, 4
skip (89.2 % of 6,297 run)**: 731 negative passes, 4,885 of 5,292 positive tests
(92.3 %). 171 of the 225 async tests pass. 73 negative tests that passed only because
the parser refused private names or async generators fail now; no positive test was
lost.

Remaining failures by cause (stage 6): early errors not detected 269; `yield` in a
conditional position 32; call depth 31; the rest are single semantic differences
(each cause under 35 tests).

Stage 7 (built-ins): 5,618 pass, 679 fail, 4 skip (89.2 % of 6,297 run); no stage-6
pass lost.

### 9a. The QuickJS sample: built-ins included

The subset above is `test/language` only. To compare with QuickJS on the same files,
the 436 tests of the QuickJS-in-WasmVM measurement (`test262-sample.py 500 1244`:
random over `built-ins`, `language` and `annexB`, same Test262 commit) run with
`tools/leanjs/test262-sample.sh`:

| Engine | Pass of 436 |
|---|---|
| QuickJS-NG in WasmVM (2 G instructions per test) | 431 (98.8 %) |
| QuickJS-NG native | 434 (99.5 %) |
| Lean JS, stage 6 | 226 (51.8 %) |
| Lean JS, stage 7 | 247 (56.7 %) |

The failures are mostly built-ins that are not there yet: TypedArray, ArrayBuffer and
DataView (about 30), RegExp (about 30, with regular expression literals), Date, Proxy,
Iterator helpers, and 21 negative tests whose early error the parser misses. Apple's
EU bar (80 % of Test262 without a JIT) is not met by the Lean engine yet; on this
sample QuickJS in WasmVM meets it.

## 10. Speed

The same two scripts as the QuickJS measurement in `2026-11-07-wasmvm-engine.md`
(`WasmVM/Bench/QuickJS.lean`), on the owner's Mac, 2026-11-08, one after the other:

| Script | Lean JS (`leanjs`) | QuickJS-NG in WasmVM (`wasmvm-bench qjs`) | QuickJS-NG native |
|---|---|---|---|
| `fib(24)` | 125 to 143 ms | 1,069 ms (154 M Wasm instructions) | 6 ms |
| loop of 200,000 + `JSON.stringify` of 2,000 objects | 277 to 341 ms | 2,123 ms (330 M Wasm instructions) | 18 ms |

So the Lean engine is 6 to 8 times faster than QuickJS in WasmVM, and 18 to 20
times slower than native QuickJS. A loop of 10^6 iterations runs in constant stack
(the loop is a self tail call in the emitted C).

Where the time goes, from the design (not yet sampled): each variable access is a
hash lookup by `String` along the environment chain; each call allocates a
`HashMap` environment; numbers are boxed in `Value.num`; property keys are strings.
The planned fast form (section 12) resolves names to slots at parse time, keeps
small objects as shapes with slot arrays, and caches property lookups.

## 11. Not wired into the browser: what it takes

1. A host object layer in Lean for the page: `document`, `window`, `Node`, `Element`,
   `Event` and the rest of `tools/wasmvm/quickjs/prelude.js` (1,493 lines of
   JavaScript). The prelude can run as JavaScript in the Lean engine as it does in
   QuickJS, once the engine has classes, getters on prototypes (present),
   `Symbol.iterator` and the other features it uses. Its 13 `foafnaut_dom` natives
   become `Native` cases that call `WasmVM.Hosts.Dom`'s operations on the arena
   directly (`Dom.setTextContent`, `Dom.setAttribute`, `Dom.createElement`, ...), and
   record the same typed `Command`s, so `WebRenderScript.applyCommands` and the
   render replay do not change.
2. A `Session` variant in `Hosts/Page.lean` that holds the JavaScript `Heap` and the
   `DOM.Arena` in place of the WasmVM store: `start` runs the scripts with
   `runScript`, `click` asks `EventLoop.Dispatch.plan` and calls listeners with
   `callV`, `advance` and `settle` run timer and frame callbacks.
3. Promise jobs on the event loop's microtask queue (section 6).
4. A selector in `scriptSession` (`engine: "lean"`), with QuickJS as the default
   until the WPT testharness results are at least as good.
5. The Wasm build: the engine is plain Lean, so it compiles into the Foafnaut core
   Wasm as the rest of the engine does; it adds no import.

## 12. Next steps

1. Language: the remaining early errors (269 tests, now the largest group); `for
   await`; exact private-name brands; regular expression literals (the repository's
   `L4Factoidal.Regex` engines are candidates); `yield` in conditional positions
   (lift into `if` statements); a call depth limit set from the native stack rather
   than 400.
2. Built-ins, by the failures of section 9a: TypedArray, ArrayBuffer and DataView;
   RegExp (the repository's `L4Factoidal.Regex` engines are candidates); Date (on the
   virtual clock); Proxy; Iterator helpers; then a vendored built-ins subset of
   Test262, as for `language`.
3. UTF-16 strings (section 7).
4. The fast form: slot-resolved names, shapes, inline caches; each with a theorem
   that it computes what the definitional evaluator computes, as for WasmVM.
5. The generated reference semantics from ESMeta's IR, and refinement theorems
   (section 4d).
6. The collector (section 8).
