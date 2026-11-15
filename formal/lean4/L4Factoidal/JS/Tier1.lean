import L4Factoidal.JS.Syntax

/-!
# L4Factoidal.JS.Tier1 — the first tier of the BubblePopJS JIT

A rewrite of the resolved tree, once per function, into specialised nodes that the evaluator
runs with fewer of its own calls (each call of a monadic function of the evaluator returns a
fresh result object, and allocation is more than half of the time of a plain loop):

- `update pre inc (local x h i)` becomes `incLocal pre inc x h i`: a number in a writable slot
  is read and written in place, with no call of `lookupLocal` and `assignLocal`;
- `assign none (local x h i) v` (`v` not a function expression, whose name the assignment
  gives it) becomes `setLocal x h i v`: no `evalRef`, no pair of options, no `putTarget`;
- `block ss`, when `ss` declares nothing lexical, becomes `blockN ss`: no `evalBlock`, no
  `enterBlock` and no scan of the statements at each entry.

**What is proved.** `JS/Tier1Proofs.lean`: for every fuel, context and heap, the evaluator on
each specialised node gives the same result and the same heap as the evaluator on the node it
replaces, the fuel exhaustion and the steps included (`incLocal_eq`, `setLocal_eq`,
`blockN_eq`). Nodes this pass does not specialise are left as they are (the identity).

The pass does not enter function bodies (each function is rewritten once, by the resolver,
when its own body is resolved), generator and async bodies (their machine matches on the
syntax), patterns, or loops compiled for the register machine. It walks with fuel (the
nesting depth); out of fuel it leaves the subtree as it is.

`enabled` turns the pass off: the differential test runs Test262 with it on and off.
-/

namespace L4Factoidal.JS.Tier1
open L4Factoidal.JS

/-- Tier 1 is on. -/
def enabled : Bool := true

/-- The statements declare something lexical: `enterBlock` would make an environment. -/
def lexical (ss : List Stmt) : Bool := ss.any Stmt.isLexical

mutual
def tE : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e =>
    match e with
    | .update pre inc (.local x h i) => .incLocal pre inc x h i
    | .assign none (.local x h i) v =>
      match v with
      | .func _ => e
      | _ => .setLocal x h i (tE n v)
    | .unary op a => .unary op (tE n a)
    | .binary op a b => .binary op (tE n a) (tE n b)
    | .logical op a b => .logical op (tE n a) (tE n b)
    | .assign op t v =>
      match v with
      | .func _ | .classE _ => .assign op (tE n t) v
      | _ => .assign op (tE n t) (tE n v)
    | .cond a b c => .cond (tE n a) (tE n b) (tE n c)
    | .call f args => .call (tE n f) (tEs n args)
    | .new f args => .new (tE n f) (tEs n args)
    | .member o k => .member (tE n o) k
    | .index o k => .index (tE n o) (tE n k)
    | .seq a b => .seq (tE n a) (tE n b)
    | .array es => .array (tEs n es)
    | _ => e

def tEs : Nat → List Expr → List Expr
  | 0, es => es
  | n + 1, es => es.map (tE n)

def tOptE : Nat → Option Expr → Option Expr
  | 0, e => e
  | _ + 1, none => none
  | n + 1, some e => some (tE n e)

def tS : Nat → Stmt → Stmt
  | 0, s => s
  | n + 1, s =>
    match s with
    | .expr e => .expr (tE n e)
    | .ret (some e) => .ret (some (tE n e))
    | .throwS e => .throwS (tE n e)
    | .ifS c t f => .ifS (tE n c) (tS n t) (tOptS n f)
    | .whileS c b => .whileS (tE n c) (tS n b)
    | .doWhile b c => .doWhile (tS n b) (tE n c)
    | .forS init t u b =>
      let init' := match init with
        | some (.expr e) => some (.expr (tE n e))
        | i => i
      .forS init' (tOptE n t) (tOptE n u) (tS n b)
    | .block ss => if lexical ss then .block (tSs n ss) else .blockN (tSs n ss)
    | .blockF ss => .blockF (tSs n ss)
    | .labeled l b => .labeled l (tS n b)
    | _ => s

def tOptS : Nat → Option Stmt → Option Stmt
  | 0, s => s
  | _ + 1, none => none
  | n + 1, some s => some (tS n s)

def tSs : Nat → List Stmt → List Stmt
  | 0, ss => ss
  | n + 1, ss => ss.map (tS n)
end

/-- The nesting depth the pass follows. -/
def fuel : Nat := 1000

/-- The statements of a function body or of a script, rewritten when tier 1 is on. -/
def stmts (ss : List Stmt) : List Stmt :=
  if enabled then tSs fuel ss else ss

end L4Factoidal.JS.Tier1
