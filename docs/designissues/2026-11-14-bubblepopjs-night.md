# BubblePopJS, 2026-11-14: what Test262 was losing, and the repairs

Date: 2026-11-14. Branch: `wip/js-core`. Related: `2026-11-13-bubblepopjs-webassembly.md`
(the previous record), `2026-11-13-module-scripts.md` (module scripts, merged with this work),
`2026-11-13-wpt-plan.md` (the plan this follows).

## 1. Findings

The full run of 2026-11-13 (main `6dde36491`) passed 30,345 of the 53,833 Test262 pages that WPT
serves (`third_party/test262`), with 1,799 timeouts. Grouping the failure messages of every
page gave these causes.

1. **The timeouts were not speed.** 1,140 of them are `language/statements/for-await-of`:
   `for await` was a SyntaxError, the script did not run, and an async test that never calls
   `$DONE` is a timeout. 390 more are dynamic `import()`, 62 are `await using`. None of the
   pages looked at stopped at the step budget.
2. **A classic script that did not parse was not reported at the window.** The session kept the
   SyntaxError in its own log only. Test262's negative tests (`negative: phase: parse`) wait for
   the `error` event, so 2,803 pages that the parser rightly refused were counted as failing
   ("Expected SyntaxError but test completed without error"). The same silence made 349 pages
   pass that should not have: their scripts used syntax the parser lacks, did not run, and a
   page that reports nothing passes when it expects no error.
3. **`new Promise(resolve => resolve(otherPromise))` never settled.** The resolving functions that
   NewPromiseResolveThenableJob makes read the promise's own already-resolved flag, which the
   first call of `resolve` had set. `await`, `then` chains and async functions take another path
   and worked, so the defect showed only in code that resolves a promise with a promise by hand:
   Test262's `assert.throwsAsync`, and a common pattern on real sites.
4. **A property key could collide with a private name or a Symbol.** A key is a Lean `String`;
   U+10FFFE starts a private name's key and U+10FFFF a Symbol's, and a String value was its own
   key. `o["\u{10FFFE}x"]` read `#x`. WPT `wasm/core/names.wast` has an export name that starts
   with U+10FFFE (480 subtests).
5. **Arrays are dense, and nothing bounded their growth.** `a.length = 4294967295` asked for
   32 GiB; the engine's process was killed (the CRASH rows of the full run, and a local run that
   pushed the development machine into swap).
6. Missing language: `for await`, async `yield*`, `yield` and `return` awaiting in async
   generators, Annex B function declarations in blocks, `super.x = v`, Hashbang comments,
   a call as an assignment target in sloppy code, `import()` in a script.

## 2. Repairs

All in Lean unless said; each has `#guard`s in `JS/RegressionTests.lean`.

| Repair | Where |
|---|---|
| A script that does not parse reports its SyntaxError (HTML "create a classic script", error to rethrow) | `WasmVM/Hosts/LeanJS.lean`, `Session.eval` |
| `for await`: the parser writes it as statements the generator machine runs; `%AsyncFromSyncIteratorPrototype%` | `JS/Parser.lean` `forAwaitStmt`; `JS/Interp.lean` `NativeX.forAwait`, `asyncFromSync` |
| Property keys: `strKey` puts U+10FFFD before a string that starts with U+10FFFD, U+10FFFE or U+10FFFF; listings give `keyStr`; an identifier does not start with one of the three; `#x in o` is not a string operand | `JS/Syntax.lean`, `JS/Lexer.lean`, `toKey`, `keyValue`, `Object.keys` and the other listings |
| Thenable jobs get their own resolving functions (`promiseThenableFn`) | `JS/Interp.lean` |
| Async generators: `yield` awaits its operand, `return e` awaits, `return(v)` awaits `v`, `yield*` delegates to an async iterator (a record in the `delegate` frame); a `yield` whose operand holds an `await` or `yield` is lifted | `agenDrain`, `agenRun`, `agenAwait`, `genRun`, `genUnwind`, `liftStmt` |
| Annex B.3.3, B.3.4: a block's function declaration in sloppy code is also a `var`, set when the declaration is evaluated, unless a lexical name of an enclosing block has the name | parser (`lexStack`, `annexBLabel`), evaluator's `labeled` case |
| `super.x = v` and the other super targets; a call as a target (a ReferenceError when it runs); Hashbang; `import()` and `import.source()`/`import.defer()` answer a rejected promise | parser, `evalRef`, `getRef`, `putTarget`, `NativeX.dynImport` |
| Dense arrays: `new Array(n)` and `length = n` past `maxDenseArray` (2^25) are a RangeError, and growth takes steps; the job queue drops the jobs it has run | `JS/Interp.lean` |
| `<body onerror>`: five parameters; a handler source that does not compile sets the handler to null (JavaScript glue) | `tools/wasmvm/quickjs/prelude.js`, `contentHandler` |

`for await` is not a new syntax-tree node: `forAwaitStmt` builds a block of `const`, `try`,
`while` and `await` (the comment at the definition shows the text), with helper functions that
are hidden properties of the global object (private-name keys). So the resolver, the snapshot
and the generator machine did not change for it, and a page with no `for await` pays nothing.

### Early errors (second batch)

With parse errors reported, the largest group left was negative tests that the parser accepted
(1,721 pages). These are now SyntaxErrors, each a check at the place the parser reads the
construct (`JS/Parser.lean`):

- `await` as a binding name, label or identifier in an async function; `yield` as a label or an
  identifier in a generator or strict code; `let` as an identifier in strict code;
- `arguments` and `super()` in a class field initialiser or a static block (arrow functions keep
  the rule; other functions reset it);
- `delete o.#x` in every form the cover grammar gives;
- a `"use strict"` directive in a function whose parameters are not simple;
- a private name used where no enclosing class declares it, and a private name declared twice
  (a getter and a setter may share one). The code of a direct `eval` may use the private names
  of the classes around the call (`parseScript`'s `evalCode`).

Not done: a regular expression literal is still compiled when it is evaluated, not when it is
parsed (361 pages). Checking it at parse time would turn one pattern this engine cannot yet
compile, in a branch that never runs, into a script that does not load: wrong for real sites
until `JS.Re` reads every valid pattern.

## 2b. URLPattern (URL Pattern Standard)

`formal/lean4/L4Factoidal/WHATWG/URLPattern.lean` is the Standard as pure functions of strings:
the pattern tokenizer and parser, the regular expression and pattern string of a part list, the
constructor string parser, canonicalization through the URL parser's state overrides
(`WHATWG.URL.basicParse`), `create` (the constructor) and `exec`. Regular expressions are
compiled and run by `JS.Re`. The page object is glue: `NativeX.urlPattern` converts the WebIDL
arguments and builds the result object, and the class in `prelude.js` holds the record
(component pattern strings, and hidden: the compiled expressions and group names, so `exec`
does not compile again). Names above ASCII use General_Category (L, Nl; Mn, Mc, Nd, Pc) from
`Regex.UnicodeProps` with the Other_ID_Start and Other_ID_Continue characters.

Measured locally: the WPT driver `urlpattern/resources/urlpatterntests.js`, run on the engine
with the class as written in the prelude, passes 367 of the 369 entries of
`urlpatterntestdata.json` (331 directly; 36 more need `new URL` for an expectation, which the
local harness lacks and the pure comparison confirms). The two that fail use the `v` flag's set
operations (`[[a-z]--a]`, `[\d&&[0-1]]`).

Theorems (`WHATWG/URLPatternTests.lean`): `tokenizeGo_lenient` (the lenient tokenizer is total),
`create_init_with_base` and `exec_init_with_base` (an object input with a base URL is always
refused), `Component.exec_size` (one group entry per name). Open: `compareComponent` and
`generate` (tentative), the `v` flag; that a compiled pattern's regular expression accepts
exactly what its part list describes is not proved.

## 3. Proved, tested, open

Proved (`JS/Theorems.lean`, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only):

- `strKey_not_priv`, `strKey_not_sym`: no String value's key is a private name's or a Symbol's.
- `keyStr_strKey`, `strKey_injective`, `strKey_ne_privKey`: the encoding is undone by `keyStr`
  and is injective.
- `isPrivKey_privKey`, `forAwaitFn_private`: the `for await` helpers are private-name keys.
- `forAwaitStmt_hasYield`: the statements of a `for await` always go to the generator machine.
- `tick_spent`, `tick_step`, `charge_spent`, `charge_step`: what one step and one charge do to the
  budget; `maxDenseArray_bounds`.

Tested only (`#guard`s and Test262): that `toKey`, the parser and `JSON.parse` call `strKey` at
every place a string becomes a key; the behaviour of `for await`, async generators, promises,
Annex B hoisting; that every loop of the evaluator takes a step.

Open:

- Dynamic `import()` does not load (it rejects); import maps; top-level `await`.
- `using`, `await using`, DisposableStack; decorators; Temporal; Intl.
- Arrays stay dense: a length above 2^25 is a RangeError where ECMA-262 allows a sparse array.
- A super reference as a target sets on `this` with `this`'s own lookup: a setter of the parent
  that the object overrides is not the one called.
- Annex B.3.3: a `let` of an enclosing block that comes *after* the nested block is not seen
  (one pass); parameters named like the function are treated as a clash (no hoisting).
- The heap has no collector, so memory is bounded only by steps times what a step can allocate.

## 4. Measured

See the hand-back in the night report; the numbers are added to this record when the cloud
rounds finish.

## 5. Streams, compression, early errors, prototypes (third agent)

What was added, on top of the second agent's branch (Reflect.set receiver, heap guard, the
lexer fixes, `WHATWG/Streams.lean`):

- **Property descriptors**: `Object.defineProperty` reads the descriptor once in
  ToPropertyDescriptor's order and asks `Desc.allowedOn` (ValidateAndApplyPropertyDescriptor,
  §10.1.6.3) whether a property that is not configurable may take it.
- **Intrinsics**: %GeneratorFunction%, %AsyncGeneratorFunction%, %AsyncFunction% and their
  prototypes (`Realm.closureProto`); `Object.getPrototypeOf(function* () {}).prototype` was
  undefined, and with it the usual way to reach %AsyncIteratorPrototype%.
- **[[SetPrototypeOf]]**: cycles, objects that are not extensible and the immutable
  Object.prototype refuse a new prototype (`protoChangeAllowed`); Object.prototype.__proto__ is
  the Annex B accessor (idlharness reads its setter).
- **Typed arrays**: ValidateTypedArray in every %TypedArray%.prototype method (`typedOob`), and
  the generic ones are functions of their own instead of Array.prototype's.
- **Streams Standard** in the prelude (lazy globals: a page that names no stream class makes
  none), over `n.streams` (the queue-with-sizes and the BYOB fill plan in Lean).
- **Encoding streams and the Compression Standard**: TextEncoderStream, TextDecoderStream,
  CompressionStream, DecompressionStream; formats, compression and what received bytes are in
  `WHATWG/Compression.lean` (web_api ops 50 to 52).
- **Early errors** in the parser: function declarations redeclared in a block or a switch;
  class element names; `super` and `new.target` placement; private names with a space after
  `#`; `new import(...)`; accessor parameter counts; shorthand properties that are reserved
  words; function declarations as loop bodies. Test262 negative syntax tests outside RegExp that
  the parser accepted: 655 before, 255 after; the 23,928 positive Test262 files of language/,
  annexB/language and the Function, Object, Reflect and Proxy built-ins parse as before (none
  newly refused).

Proved (`JS/Theorems.lean`, `WHATWG/Compression.lean`, `WHATWG/Streams.lean`):
`allowedOn_configurable`, `allowedOn_empty`, `allowedOn_stays_unconfigurable`,
`allowedOn_frozen`, `allowedOn_accessor`; `orFn_ne_zero`, `closureProto_ne_zero`,
`closureProto_plain`, `closureProto_gen`, `closureProto_asyncGen`, `closureProto_async`;
`protoChange_same`, `protoChange_fixed`, `protoChange_no_cycle`; `blockFunsOk_strict`,
`blockFunsOk_distinct`, `blockFunsOk_special`; `classElementOk_special_ctor`,
`classElementOk_static_prototype`, `classElementOk_field_ctor`, `classElementOk_computed`,
`superCallIn_derived`, `superPropIn_normal`, `accessorParamsOk_getter`,
`accessorParamsOk_setter`; `typedOob_false`, `typedOob_detached`; `ofName_name`,
`ofName_brotli`, `zlibHeaderOk_fcheck`, `decompress_raw_done`, `decompress_raw_extra`,
`op_refuses`; the queue and fill-plan theorems of `Streams.lean`.

Tested only: the stream classes' promise plumbing (WPT streams tests on BubblePopJS alone:
1,114 of 1,145 reported subtests), the JS glue of the encoding and compression streams (under
node, with zlib standing in for the Lean operations), the round trips and WPT corrupt-input
cases of `Compression.lean` (`#guard`), the parser rules (`#guard` and Test262 files).

Open:

- memory64 and table64 in the WasmVM (about 2,300 subtests of wasm/core): the decoder refuses
  the 64-bit address type; the executor, the validator and the refinement proofs all assume
  32-bit addresses.
- A Proxy's setPrototypeOf trap is not called; the immutable prototype of the Window's
  prototype chain (Web IDL) is not set (the worker scope changes the global's prototype).
- Request and Response with a stream body are refused; DecompressionStream decodes the buffered
  input again for each chunk (up to 1 MiB, then once at close); CompressionStream writes stored
  blocks, so its output is larger than its input.
- Regular expression early errors (361 Test262 tests) wait for a validator that tells an
  invalid pattern from one `JS.Re` cannot compile yet.

Measured (branch checks against the full run of d799500c7):

| Check | Directory | Before | After |
|---|---|---:|---:|
| 43574504956 (730b228cf, merged 80b518bb7) | third_party/test262 (all) | 36,341 | 36,610 |
| 43575824292 (edee47c79, merged e37ca8b6b) | streams | 52 | 2,788 |
| | compression | 8 | 484 |
| | encoding/streams | 0 | 216 |
| | fetch/api (119 names) | 501 | 600 |

Performance: a page that names no stream class makes none (lazy globals); the prelude's parse
is done once when the realm snapshot is made. The Array iteration methods read one element at a
time (one object lookup per element more than the copy they took before); not timed, as no
engine could be built locally tonight.
