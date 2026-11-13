import L4Factoidal.JS.Modules

/-!
# Tests of modules (`JS/Modules.lean`)

Each `#guard` runs module scripts on a fresh realm and checks what they printed. A graph is
given as modules by name; a specifier is the name of a module (the page's loader resolves
URLs, `WasmVM/Hosts/LeanJSModules.lean`). The expected lines are what V8 (Node 22) prints for
the same modules.
-/

namespace L4Factoidal.JS.ModuleTests
open L4Factoidal.JS

/-- The graph of named modules: each specifier names a module of the list. -/
def graphOf (mods : List (String × String)) : Except String ModGraph := do
  let parsed ← mods.mapM fun (u, src) => do pure (u, ← parseModule src)
  let names := parsed.map (·.1)
  let nodes ← parsed.mapM fun (u, syn) => do
    let deps ← syn.requests.mapM fun spec =>
      match names.idxOf? spec with
      | some i => pure (spec, i)
      | none => throw s!"no module {spec}"
    pure { ModNode.ofSyntax u syn with deps }
  return nodes.toArray

/-- Run the module scripts `roots` (indices of `mods`), in order, on one realm: the printed
lines, and `threw: m` for a run that threw. -/
def runMods (mods : List (String × String)) (roots : List Nat) : List String :=
  match graphOf mods with
  | .error e => [e]
  | .ok g => Id.run do
    let mut h := freshHeap
    let mut lives : ModLives := #[]
    let mut extra : Array String := #[]
    for r in roots do
      let ((o, lv), h') := runModuleGraph h g r lives
      h := h'
      lives := lv
      match o with
      | .threw _ m => h := { h with out := h.out.push ("threw: " ++ m) }
      | .halted w => h := { h with out := h.out.push ("halted: " ++ w) }
      | _ => pure ()
    let _ := extra
    return h.out.toList

-- imports of a function and a constant
#guard runMods [("a", "import {x, f} from 'b'; print(x + f())"), ("b", "export const x = 1; export function f() { return 2 }")] [0] == ["3"]
-- a live binding
#guard runMods [("a", "import {c, inc} from 'b'; print(c); inc(); print(c)"), ("b", "export let c = 0; export function inc() { c++ }")] [0] == ["0", "1"]
-- default exports: a function's name is "default"
#guard runMods [("a", "import f from 'b'; print(f(), f.name)"), ("b", "export default function () { return 7 }")] [0] == ["7 default"]
#guard runMods [("a", "import v, {w} from 'b'; print(v, w)"), ("b", "export default 3 * 4; export const w = 'w'")] [0] == ["12 w"]
#guard runMods [("a", "import C from 'b'; print(new C().k, C.name)"), ("b", "export default class { constructor() { this.k = 1 } }")] [0] == ["1 default"]
-- a namespace object
#guard runMods [("a", "import * as ns from 'b'; print(Object.keys(ns).join(), ns[Symbol.toStringTag], Object.getPrototypeOf(ns), Object.isExtensible(ns))"),
  ("b", "export let zed = 0; export function alpha() {}")] [0] == ["alpha,zed Module null false"]
-- renames, and export of an import
#guard runMods [("a", "import {y as z, q} from 'b'; print(z, q)"), ("b", "const x = 5; export {x as y}; export {r as q} from 'c'"), ("c", "export const r = 'r'")] [0] == ["5 r"]
#guard runMods [("a", "import {q} from 'b'; print(q)"), ("b", "import {r} from 'c'; export {r as q}"), ("c", "export const r = 'r2'")] [0] == ["r2"]
-- export *
#guard runMods [("a", "import {x, y} from 'b'; print(x, y)"), ("b", "export * from 'c'; export const y = 2"), ("c", "export const x = 1; export default 9")] [0] == ["1 2"]
#guard runMods [("a", "import * as n from 'b'; print('default' in n, n.x)"), ("b", "export * from 'c'"), ("c", "export const x = 1; export default 9")] [0] == ["false 1"]
#guard runMods [("a", "import {n} from 'b'; print(n.x)"), ("b", "export * as n from 'c'"), ("c", "export const x = 4")] [0] == ["4"]
-- a cycle: hoisted functions are there before either module runs
#guard runMods [("a", "import {g} from 'b'; export function f() { return 'f' } print(g())"),
  ("b", "import {f} from 'a'; export function g() { return f() + 'g' } print('b first')")] [0] == ["b first", "fg"]
-- a cycle: a `let` read before it is initialised is the exporter's ReferenceError
#guard runMods [("a", "import 'b'; export let v = 1"), ("b", "import {v} from 'a'; print(v)")] [0] ==
  ["threw: ReferenceError: Cannot access 'v' before initialization"]
-- module code: strict, its own scope, `this` undefined
#guard runMods [("a", "var q = 1; print(this === undefined, typeof globalThis.q); try { undeclared = 1 } catch (e) { print(e.name) }")] [0] ==
  ["true undefined", "ReferenceError"]
-- an import is read-only
#guard runMods [("a", "import {x} from 'b'; try { x = 2 } catch (e) { print(e.name) } print(x)"), ("b", "export var x = 1")] [0] == ["TypeError", "1"]
-- a module is evaluated once
#guard runMods [("a", "import 'c'; print('a')"), ("b", "import 'c'; print('b')"), ("c", "print('c')")] [0, 1] == ["c", "a", "b"]
-- a missing export is a SyntaxError before anything runs
#guard runMods [("a", "print('a'); import {nope} from 'b'"), ("b", "print('b')")] [0] ==
  ["threw: SyntaxError: The requested module 'b' does not provide an export named 'nope'"]
-- an ambiguous star export
#guard runMods [("a", "import {x} from 'b'"), ("b", "export * from 'c'; export * from 'd'"), ("c", "export const x = 1"), ("d", "export const x = 2")] [0] ==
  ["threw: SyntaxError: The requested module 'b' contains conflicting star exports for name 'x'"]
-- an error in evaluation is kept: a later importer gets it again, the module does not run again
#guard runMods [("a", "import 'c'"), ("b", "import 'c'; print('b')"), ("c", "print('c'); throw new Error('boom')")] [0, 1] ==
  ["c", "threw: Error: boom", "threw: Error: boom"]
-- import.meta
#guard runMods [("https://example.test/m.js", "print(import.meta.url, Object.getPrototypeOf(import.meta))")] [0] == ["https://example.test/m.js null"]
-- module code may use globals and loops (the register machine sees imports through the imports object)
#guard runMods [("a", "import {k} from 'b'; let s = 0; for (let i = 0; i < 10; i++) s += k; print(s, Math.max(1, 2))"), ("b", "export const k = 3")] [0] == ["30 2"]
#guard runMods [("a", "import {k} from 'b'; function f() { let s = 0; for (let i = 0; i < 10; i++) s += k; return s } print(f())"), ("b", "export const k = 3")] [0] == ["30"]

-- syntax: early errors
#guard (parseModule "export const a = 1; export {a}").toOption.isNone
#guard (parseModule "import {a} from 'x'; let a = 1").toOption.isNone
#guard (parseModule "export {nothere}").toOption.isNone
#guard (parseModule "return 1").toOption.isNone
#guard (parseModule "with (o) {}").toOption.isNone
#guard (parseModule "import x from 'y' with { type: 'json' }").toOption.isNone
#guard (parseModule "import {a as b, 'c d' as e, default as f} from 'm'; export {b, e as 'e f'}").toOption.map (·.imports.size) == some 3
#guard (parseModule "import 'a'; import {b} from 'b'; export * from 'a'").toOption.map (·.requests) == some #["a", "b"]
-- classic scripts: `import.meta` is a SyntaxError, `import()` parses
#guard (parseScript "import.meta").toOption.isNone
#guard (parseScript "import('x').then(m => m)").toOption.isSome
#guard (parseScript "import {a} from 'b'").toOption.isNone

end L4Factoidal.JS.ModuleTests
