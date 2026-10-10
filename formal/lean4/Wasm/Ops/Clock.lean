/-
Wasm.Ops.Clock — the one place the wasm entry layer reads the wall clock.

SPARQL 1.1 §17.4.5.1 (`NOW`): "Returns an XSD dateTime value for the
current query execution. All calls to this function in any one query
execution must return the same value."
(https://github.com/danbri/factoidal/issues/743)

The evaluator is pure: `NOW()` is `EvalEnv.now`, an `xsd:dateTime`
lexical form the caller passes (`L4Factoidal/SPARQL/Expr.lean`). An op
that runs in `IO` calls `nowDateTime` ONCE at the start of a query or
update execution and passes the result as `now` to every evaluator call
of that execution. Every `NOW()` in the execution then has the same
value. The pure ops (`queryDataset`, `updateDataset`, ...) keep `now` as
a parameter whose default is `none`, so they remain functions of their
inputs; with `none`, `NOW()` is an error, as the evaluator defines.

The clock is the Lean toolchain's own: `Std.Time.Timestamp.now`
(`lean_get_current_time` in the Lean runtime, `src/runtime/io.cpp`,
`std::chrono::system_clock`). Emscripten's libc serves `system_clock`
from the host's `Date.now()`, so the wasm module reads the host clock
through the same primitive. The formatting is the pure function
`L4Factoidal.SPARQL.dateTimeOfUnixMillis`, which carries the `#guard`s.

`Wasm/build-wasm.sh` generates and links the C of the 26 `Std.Time`
modules this import needs (and no other `Std.Time` module).
-/
import Std.Time.DateTime.Timestamp
import L4Factoidal.SPARQL.Now

namespace L4Wasm.Ops

/-- Milliseconds since 1970-01-01T00:00:00Z on the system clock. -/
def unixMillisNow : IO Int := do
  let ts ← Std.Time.Timestamp.now
  pure ts.toMillisecondsSinceUnixEpoch.val

/-- The `xsd:dateTime` lexical form of the system clock now, in UTC
(XML Schema 1.1 Part 2 §3.3.7), to pass as `EvalEnv.now`. Read it once per
query or update execution. -/
def nowDateTime : IO String := do
  pure (L4Factoidal.SPARQL.dateTimeOfUnixMillis (← unixMillisNow))

end L4Wasm.Ops
