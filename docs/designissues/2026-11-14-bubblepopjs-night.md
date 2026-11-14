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
