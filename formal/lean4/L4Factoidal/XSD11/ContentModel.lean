/-
L4Factoidal.XSD11.ContentModel — validation of a sequence of element
names against a particle: XML Schema 1.1 Part 1 §3.9.4.1 (Element
Sequence Locally Valid (Particle)), §3.8.4.1 (Element Sequence Valid,
for `sequence`, `choice` and `all`) and §3.10.4.1 (wildcards), with the
open content of §3.4.4.2 clause 1.3.

The particle is compiled to a regular expression (`RE`) with counted
repetition, and the input is consumed one element at a time by
derivatives: the state is the list of residual expressions still
possible. `all` is the shuffle of its members (§3.8.4.1 clause 2.3 in
1.1: the members may interleave, each with its own occurrence range).

Each step also reports WHICH term the element matched (an element
declaration or a wildcard), which is what the PSVI needs. When an
element declaration and a wildcard both match, the declaration wins
(§3.8.4.2, the 1.1 relaxation of Unique Particle Attribution).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Components

namespace L4Factoidal.XSD11

/-- A residual content model. -/
inductive RE where
  | eps
  | fail
  | elem (d : Nat) (pos : Nat)
  | wild (w : Wildcard) (pos : Nat)
  | seq (l : List RE)
  | alt (l : List RE)
  | all (l : List RE)
  | rep (e : RE) (min : Nat) (max : Option Nat)
deriving Repr, Inhabited, BEq

/-- What one element matched. -/
inductive Matched where
  | decl (d : Nat)
  | wild (w : Wildcard)
deriving Repr, Inhabited, BEq

def mkSeq (l : List RE) : RE :=
  if l.any (· == .fail) then .fail
  else match l.filter (· != .eps) with
    | [] => .eps
    | [x] => x
    | xs => .seq xs

def mkAlt (l : List RE) : RE :=
  match (l.filter (· != .fail)).eraseDups with
  | [] => .fail
  | [x] => x
  | xs => .alt xs

/-- Counted repetition, with `(x{a,b}){n,k} = x{n·a, b·k}` when `a ≤ 1`:
with `a = 0` every count up to `b·k` is reachable, and with `a = 1` every
count `c` in `[n, b·k]` is reached by `max n ⌈c/b⌉ ≤ k` iterations. This
keeps nested counters (`(c{0,100}){1,40}`) to one counter. -/
def mkRep (e : RE) (mn : Nat) (mx : Option Nat) : RE :=
  match e, mx with
  | .rep x a b, _ =>
    if a ≤ 1 && mx != some 0 && mx != some 1 then
      .rep x (mn * a) (match b, mx with
        | some b, some k => some (b * k)
        | _, _ => none)
    else mkRep1 e mn mx
  | _, _ => mkRep1 e mn mx
where
  mkRep1 (e : RE) (mn : Nat) (mx : Option Nat) : RE :=
    match mx with
    | some 0 => .eps
    | some 1 => if mn == 0 then mkAlt [e, .eps] else e
    | _ => if e == .eps then .eps else if e == .fail then (if mn == 0 then .eps else .fail) else .rep e mn mx

/-- Compile a particle. Each element and wildcard term gets the position
`pos` of its particle (in document order), so two matches can be told
apart when they come from different particles (Unique Particle
Attribution, `XSD11/Constraints.lean`). -/
def RE.ofParticleM : Nat → Particle → StateM Nat RE
  | 0, _ => pure .fail
  | f + 1, p =>
    match p with
    | .elem mn mx d => do
      let i ← get; set (i + 1)
      pure (mkRep (.elem d i) mn mx)
    | .wild mn mx w => do
      let i ← get; set (i + 1)
      pure (mkRep (.wild w i) mn mx)
    | .group mn mx c ps => do
      let es ← ps.mapM (RE.ofParticleM f)
      let g := match c with
        | .seq => mkSeq es
        | .choice => mkAlt es
        | .all => if es.isEmpty then .eps else .all es
      pure (mkRep g mn mx)

def RE.ofParticle (f : Nat) (p : Particle) : RE := ((RE.ofParticleM f p).run 0).1

def RE.nullable : Nat → RE → Bool
  | 0, _ => false
  | f + 1, e =>
    match e with
    | .eps => true
    | .fail => false
    | .elem _ _ | .wild _ _ => false
    | .seq l => l.all (RE.nullable f)
    | .alt l => l.any (RE.nullable f)
    | .all l => l.all (RE.nullable f)
    | .rep e mn _ => mn == 0 || RE.nullable f e

/-- The context an element name is matched in: whether a declaration
`d` accepts the name (with substitution groups), and whether a wildcard
does (with `##defined` / `##definedSibling`). -/
structure MatchCtx where
  /-- `declFor d n`: the declaration that the element named `n` is
  validated against when it matches the particle of declaration `d`
  (`d` itself, or a member of its substitution group), if any. -/
  declFor : Nat → XName → Option Nat
  wildOk : Wildcard → XName → Bool

/-- The derivatives of `e` by the element named `n`, each with the term
it matched and that term's particle position. -/
def RE.derivP (m : MatchCtx) (n : XName) : Nat → RE → List (RE × Matched × Nat)
  | 0, _ => []
  | f + 1, e =>
    match e with
    | .eps | .fail => []
    | .elem d p => match m.declFor d n with
      | some d' => [(.eps, .decl d', p)]
      | none => []
    | .wild w p => if m.wildOk w n then [(.eps, .wild w, p)] else []
    | .alt l => l.flatMap (RE.derivP m n f)
    | .seq [] => []
    | .seq (x :: xs) =>
      let first := (RE.derivP m n f x).map (fun (r, t) => (mkSeq (r :: xs), t))
      if RE.nullable f x then first ++ RE.derivP m n f (mkSeq xs) else first
    | .all l =>
      (l.zipIdx.flatMap (fun (x, i) =>
        (RE.derivP m n f x).map (fun (r, t) => (RE.all (l.set i r), t))))
    | .rep x mn mx =>
      (RE.derivP m n f x).map (fun (r, t) =>
        (mkSeq [r, mkRep x (mn - 1) (mx.map (· - 1))], t))

def RE.deriv (m : MatchCtx) (n : XName) (f : Nat) (e : RE) : List (RE × Matched) :=
  (RE.derivP m n f e).map (fun (r, t, _) => (r, t))

/-- `a` accepts every sequence `b` accepts, by shape: equal, or the same
repetition with a wider count range, or sequences that agree position by
position. Sound (each case is a language inclusion), not complete. -/
def RE.subsumes : Nat → RE → RE → Bool
  | 0, a, b => a == b
  | f + 1, a, b =>
    a == b ||
    match a, b with
    | .rep x m1 n1, .rep y m2 n2 =>
      m1 ≤ m2 && (match n1, n2 with
        | none, _ => true
        | some _, none => false
        | some k1, some k2 => k2 ≤ k1) && RE.subsumes f x y && RE.subsumes f y x
    | .seq xs, .seq ys => xs.length == ys.length && (xs.zip ys).all (fun (x, y) => RE.subsumes f x y)
    | _, _ => false

/-- Drop the residuals another residual subsumes (keeps the first of two
equal ones). -/
def pruneRes (rs : List RE) : List RE :=
  let rs := rs.eraseDups
  rs.filter (fun r => !rs.any (fun r' => r' != r && RE.subsumes 32 r' r))

/-- The state of matching: the residuals still possible, and whether
open content in `suffix` mode has started. -/
structure CMState where
  res : List RE
  suffixStarted : Bool := false
deriving Inhabited

def CMState.init (p : Particle) : CMState := { res := [RE.ofParticle 200 p] }

def CMState.nullable (s : CMState) : Bool :=
  s.suffixStarted || s.res.any (RE.nullable 200)

/-- Consume one element. `none` when the element is not allowed here.
Open content (§3.4.4.2 clause 1.3): in `interleave` mode the open
wildcard may match anywhere; in `suffix` mode only after the content
model may end. The particle's own terms are tried first. -/
def CMState.step (m : MatchCtx) (oc : Option (OpenMode × Wildcard)) (s : CMState) (n : XName)
    : Option (CMState × Matched) :=
  let ds := if s.suffixStarted then [] else s.res.flatMap (RE.deriv m n 200)
  let isDecl (d : RE × Matched) : Bool := match d.2 with | .decl _ => true | _ => false
  -- §3.8.4.2 (1.1): an element declaration takes precedence over a
  -- wildcard, so the wildcard paths are dropped when one matches.
  let ds := if ds.any isDecl then ds.filter isDecl else ds
  match ds.head? with
  | some (_, t) => some ({ s with res := pruneRes (ds.map (·.1)) }, t)
  | none =>
    match oc with
    | some (.interleave, w) => if m.wildOk w n then some (s, .wild w) else none
    | some (.suffix, w) =>
      if m.wildOk w n && s.nullable then some ({ s with suffixStarted := true }, .wild w) else none
    | none => none

end L4Factoidal.XSD11
