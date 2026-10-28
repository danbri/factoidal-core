/-
L4Factoidal.XQuery4.FlworTheorems — the tuple-stream FLWOR expression
and the nested XPath 4.0 reading.

The XQuery runtime evaluates a FLWOR expression that has a clause with no
XPath 4.0 counterpart (`count`, `order by`, `group by`, windows, `while`,
`allowing empty`) as a tuple stream (XQuery 4.0 §4.13): `runClauses`
applies each clause to the whole stream, then the return expression is
evaluated for each tuple (`evalExt cb env "flwor"`). A FLWOR of `for`,
`let` and `where` clauses only is the nested XPath 4.0 expression
(`Theorems.mkFlwor_simple`).

Proved here (no `sorry`, no new axiom):

* `step_for`, `step_let`, `step_where`: one clause over a tuple stream is
  the concatenation, tuple by tuple, of the tuples that clause makes from
  each tuple (`forT`, `letT`, `whereT`);
* `run_basic`: the tuple stream of `for` (no `allowing empty`), `let` and
  `where` clauses (`streamT`);
* `flatMapE_bind_ok`: breadth first and depth first give the same value
  when either gives one (only the error may differ, XQuery 4.0 §2.3.4);
* `flwor_stream_nested`: for those clauses, the tuple-stream evaluation
  gives the value `r` exactly when the nested evaluation (`nestT`: each
  clause tuple by tuple, then the rest, as the XPath 4.0 `for`/`let`/`if`
  expressions do) gives `r`.

Open (https://github.com/danbri/factoidal/issues/1146): `nestT` uses one
evaluator for every subexpression, while `XPath4.eval` spends one unit of
fuel at each nesting level; equality with `XPath4.eval` of
`flworToXPath` needs a fuel-monotonicity lemma for `XPath4.eval`.
-/
import L4Factoidal.XQuery4.Grammar

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4

/-- Concatenation of `f` over a list, left to right, stopping at the first error. -/
def flatMapE {α β} (f : α → M (List β)) : List α → M (List β)
  | [] => pure []
  | a :: as => do let x ← f a; let y ← flatMapE f as; pure (x ++ y)

theorem forIn_acc {α β} (ts : List α) (acc : Array β) (g : α → M (List β))
    (body : α → Array β → M (ForInStep (Array β)))
    (hb : ∀ t s, body t s = (fun r => ForInStep.yield (s ++ r.toArray)) <$> g t) :
    forIn ts acc body = (fun l => acc ++ l.toArray) <$> flatMapE g ts := by
  induction ts generalizing acc with
  | nil => simp [flatMapE]
  | cons t ts ih =>
    simp only [List.forIn_cons, hb, flatMapE]
    cases h : g t with
    | error x => simp [Functor.map, Except.map, bind, Except.bind]
    | ok r =>
      simp only [Functor.map, Except.map, bind, Except.bind]
      rw [ih]
      cases h2 : flatMapE g ts with
      | error x => simp [Functor.map, Except.map]
      | ok l => simp [Functor.map, Except.map, pure, Except.pure]


/-- The tuples a `let` clause makes from one tuple. -/
def letT (cb : XCb) (e : Expr) (vt : IType) (v : QN) (t : Env) : M (List Env) := do
  let s ← cb.eval t e
  let x ← t.coerce vt s ("$" ++ v.show)
  pure [bindV t v x]

theorem step_let (cb : XCb) (e : Expr) (vt : IType) (v : QN) (ts : List Env) (b : List QN) :
    stepClause cb (.ext "c:let" [e] [vt] [v] []) ts b =
      (fun l => (l, b ++ [v])) <$> flatMapE (letT cb e vt v) ts := by
  unfold stepClause
  simp
  rw [forIn_acc ts #[] (letT cb e vt v)]
  · cases flatMapE (letT cb e vt v) ts <;> simp [Functor.map, Except.map]
  · intro t s
    simp only [letT]
    cases h1 : cb.eval t e with
    | error x => rfl
    | ok sq =>
      cases h2 : t.coerce vt sq ("$" ++ v.show) <;>
        simp [h2, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

/-- The tuples a `where` clause keeps of one tuple. -/
def whereT (cb : XCb) (e : Expr) (t : Env) : M (List Env) := do
  let c ← ebv (← cb.eval t e)
  pure (if c then [t] else [])

theorem step_where (cb : XCb) (e : Expr) (ts : List Env) (b : List QN) :
    stepClause cb (.ext "c:where" [e] [] [] []) ts b =
      (fun l => (l, b)) <$> flatMapE (whereT cb e) ts := by
  unfold stepClause
  simp
  rw [forIn_acc ts #[] (whereT cb e)]
  · cases flatMapE (whereT cb e) ts <;> simp [Functor.map, Except.map]
  · intro t s
    simp only [whereT]
    cases h1 : cb.eval t e with
    | error x => rfl
    | ok sq =>
      cases h2 : ebv sq with
      | error x => simp [h2, bind, Except.bind, Functor.map, Except.map]
      | ok c => cases c <;> simp [h2, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

/-- The tuples of the items of `s`, positions from `k`. -/
def itemsE (f : Item → M Seq) (mk : Seq → Int → Env) : List Item → Int → M (List Env)
  | [], _ => pure []
  | a :: as, k => do let c ← f a; let r ← itemsE f mk as (k + 1); pure (mk c k :: r)

theorem foldl_items (f : Item → M Seq) (mk : Seq → Int → Env)
    (F : Array Env × Int → Item → M (Array Env × Int))
    (hF : ∀ b a, F b a = (fun c => (b.fst.push (mk c b.snd), b.snd + 1)) <$> f a)
    (s : List Item) (acc : Array Env) (k : Int) :
    List.foldlM F (acc, k) s = (fun l => (acc ++ l.toArray, k + s.length)) <$> itemsE f mk s k := by
  induction s generalizing acc k with
  | nil => simp [itemsE]
  | cons a as ih =>
    rw [List.foldlM_cons, hF]
    simp only [itemsE]
    cases h : f a with
    | error x => simp [Functor.map, Except.map, bind, Except.bind]
    | ok c =>
      show List.foldlM F (acc.push (mk c k), k + 1) as = _
      rw [ih]
      cases h2 : itemsE f mk as (k + 1) with
      | error x => simp [Functor.map, Except.map, bind, Except.bind]
      | ok l => simp [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]; omega

/-- The tuples a `for` clause (no `allowing empty`) makes from one tuple. -/
def forT (cb : XCb) (src : Expr) (vt : IType) (v pv : QN) (t : Env) : M (List Env) := do
  let s ← cb.eval t src
  itemsE (fun a => t.coerce vt [a] ("$" ++ v.show)) (fun c k => bindOpt (bindV t v c) pv (sInt k)) s 1

theorem step_for (cb : XCb) (src : Expr) (vt : IType) (v pv : QN) (ts : List Env) (b : List QN) :
    stepClause cb (.ext "c:for" [src] [vt] [v, pv] ["item", "0"]) ts b =
      (fun l => (l, b ++ v :: (if isNoName pv = true then [] else [pv]))) <$> flatMapE (forT cb src vt v pv) ts := by
  unfold stepClause
  simp
  rw [forIn_acc ts #[] (forT cb src vt v pv)]
  · cases flatMapE (forT cb src vt v pv) ts <;> simp [Functor.map, Except.map]
  · intro t s
    simp only [forT]
    cases h1 : cb.eval t src with
    | error x => rfl
    | ok sq =>
      simp only [bind, Except.bind]
      rw [foldl_items (fun a => t.coerce vt [a] ("$" ++ v.show)) (fun c k => bindOpt (bindV t v c) pv (sInt k)) _
        (fun b a => rfl)]
      cases itemsE (fun a => t.coerce vt [a] ("$" ++ v.show)) (fun c k => bindOpt (bindV t v c) pv (sInt k)) sq 1 <;>
        simp [Functor.map, Except.map]

theorem flatMapE_append {α β} (g : α → M (List β)) (a b : List α) :
    flatMapE g (a ++ b) = (do let x ← flatMapE g a; let y ← flatMapE g b; pure (x ++ y)) := by
  induction a with
  | nil =>
    simp only [List.nil_append, flatMapE]
    cases flatMapE g b <;> rfl
  | cons x xs ih =>
    simp only [List.cons_append, flatMapE, ih]
    cases g x with
    | error e => rfl
    | ok u =>
      cases flatMapE g xs with
      | error e => rfl
      | ok w =>
        cases flatMapE g b with
        | error e => rfl
        | ok z => simp [bind, Except.bind, pure, Except.pure, List.append_assoc]

theorem ok_bind_append {β} (m : M (List β)) (y r : List β) :
    (do let z ← m; pure (y ++ z)) = Except.ok r ↔ ∃ z, m = .ok z ∧ r = y ++ z := by
  cases m with
  | error e => simp [bind, Except.bind]
  | ok z => simp [bind, Except.bind, pure, Except.pure, eq_comm]

theorem bind_congr_ok {α β} (m : M α) (F G : α → M β) (h : ∀ x r, F x = .ok r ↔ G x = .ok r) (r : β) :
    (m >>= F) = .ok r ↔ (m >>= G) = .ok r := by
  cases m with
  | error e => simp [bind, Except.bind]
  | ok x => exact h x r

/-- Breadth first (all of `f`, then all of `g`) and depth first (`f`
    then `g`, item by item) give the same value whenever either gives a
    value; only the error raised may differ (XQuery 4.0 §2.3.4). -/
theorem flatMapE_bind_ok {α β γ} (f : α → M (List β)) (g : β → M (List γ)) (xs : List α) (r : List γ) :
    (flatMapE f xs >>= flatMapE g) = .ok r ↔ flatMapE (fun x => f x >>= flatMapE g) xs = .ok r := by
  induction xs generalizing r with
  | nil => simp [flatMapE, bind, Except.bind, pure, Except.pure]
  | cons x xs ih =>
    simp only [flatMapE]
    cases hf : f x with
    | error e => simp [bind, Except.bind]
    | ok a =>
      rw [show (Except.ok a : M (List β)) = pure a from rfl]
      cases hg : flatMapE g a with
      | error e =>
        have he : ∀ ys, flatMapE g (a ++ ys) = .error e := by
          intro ys; rw [flatMapE_append, hg]; rfl
        simp only [pure_bind, bind_assoc]
        constructor
        · intro h
          cases hr : flatMapE f xs with
          | error e2 => rw [hr] at h; cases h
          | ok as => rw [hr] at h; simp only [bind, Except.bind] at h; rw [he] at h; cases h
        · intro h; rw [hg] at h; cases h
      | ok y =>
        have hg' : flatMapE g a = pure y := hg
        have hap : ∀ ys, flatMapE g (a ++ ys) = (flatMapE g ys >>= fun z => pure (y ++ z)) := by
          intro ys; rw [flatMapE_append, hg']; simp only [pure_bind]
        simp only [pure_bind, bind_assoc, hap, hg']
        rw [← bind_assoc]
        rw [ok_bind_append, ok_bind_append]
        constructor
        · rintro ⟨z, hz, rfl⟩; exact ⟨z, (ih z).1 hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩; exact ⟨z, (ih z).2 hz, rfl⟩

/-- The FLWOR clauses that the XPath 4.0 `for`/`let`/`if` expressions
    also have: `for` without `allowing empty`, `let`, `where`. -/
def Clause.basic : Clause → Bool
  | .forI k _ _ _ allowing _ => k == "item" && !allowing
  | .letC .. | .whereC .. => true
  | _ => false

/-- The tuples one basic clause makes from one tuple. -/
def stepT (cb : XCb) : Clause → Env → M (List Env)
  | .forI _ v vt pos _ src => forT cb src vt v pos
  | .letC v vt e => letT cb e vt v
  | .whereC e => whereT cb e
  | _ => fun t => pure [t]

theorem step_basic (cb : XCb) (c : Clause) (hc : Clause.basic c = true) (ts : List Env) (b : List QN) :
    ∃ b', stepClause cb c.toExt ts b = (fun l => (l, b')) <$> flatMapE (stepT cb c) ts := by
  cases c with
  | forI k v vt pos allowing src =>
    simp only [Clause.basic, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨_, step_for cb src vt v pos ts b⟩
  | letC v vt e => exact ⟨_, step_let cb e vt v ts b⟩
  | whereC e => exact ⟨_, step_where cb e ts b⟩
  | _ => simp [Clause.basic] at hc

/-- The tuple stream of basic clauses. -/
def streamT (cb : XCb) : List Clause → List Env → M (List Env)
  | [], ts => pure ts
  | c :: cs, ts => do let ts' ← flatMapE (stepT cb c) ts; streamT cb cs ts'

theorem run_basic (cb : XCb) (cs : List Clause) (hc : cs.all Clause.basic = true) (ts : List Env) (b : List QN) :
    (·.1) <$> runClauses cb (cs.map Clause.toExt) ts b = streamT cb cs ts := by
  induction cs generalizing ts b with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hc
    obtain ⟨b', hb⟩ := step_basic cb c hc.1 ts b
    simp only [runClauses, List.map_cons, List.foldlM_cons, streamT]
    rw [hb]
    cases flatMapE (stepT cb c) ts with
    | error e => rfl
    | ok l =>
      have := ih hc.2 l b'
      simp only [runClauses] at this
      simpa [Functor.map, Except.map, bind, Except.bind] using this

/-- The nested reading of basic clauses: each clause, tuple by tuple,
    then the rest of the clauses and the return expression (the XPath
    4.0 `for`/`let`/`if` reading, §4.13). -/
def nestT (cb : XCb) : List Clause → Env → Expr → M Seq
  | [], t, ret => cb.eval t ret
  | c :: cs, t, ret => do let ts ← stepT cb c t; flatMapE (fun t' => nestT cb cs t' ret) ts

theorem foldl_flat (ev : Env → M Seq) (ts : List Env) (acc : Array Item) :
    List.foldlM (fun b a => (fun c => b ++ List.toArray c) <$> ev a) acc ts =
      (fun l => acc ++ l.toArray) <$> flatMapE ev ts := by
  induction ts generalizing acc with
  | nil => simp [flatMapE]
  | cons t ts ih =>
    simp only [List.foldlM_cons, flatMapE]
    cases h : ev t with
    | error e => rfl
    | ok c =>
      show List.foldlM _ (acc ++ c.toArray) ts = _
      rw [ih]
      cases flatMapE ev ts <;> simp [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]

theorem forIn_push (d : List Item) (s : Array Item) :
    (forIn d s (fun i s => pure (ForInStep.yield (s.push i))) : M (Array Item)) = pure (s ++ d.toArray) := by
  induction d generalizing s with
  | nil => simp
  | cons i is ih =>
    simp only [List.forIn_cons, pure_bind]
    rw [ih]
    simp

theorem stream_nest_ok (cb : XCb) (cs : List Clause) (ret : Expr) (ts : List Env) (r : Seq) :
    (streamT cb cs ts >>= flatMapE (fun t => cb.eval t ret)) = .ok r ↔
      flatMapE (fun t => nestT cb cs t ret) ts = .ok r := by
  induction cs generalizing ts r with
  | nil => simp only [streamT, pure_bind, nestT]
  | cons c cs ih =>
    simp only [streamT, bind_assoc, nestT]
    rw [bind_congr_ok _ _ (fun ts' => flatMapE (fun t => nestT cb cs t ret) ts') (fun x r => ih x r)]
    exact flatMapE_bind_ok _ _ ts r

/-- **The tuple-stream FLWOR agrees with the nested form.** For `for`,
    `let` and `where` clauses, the tuple-stream evaluation
    (`ext "flwor"`, XQuery 4.0 §4.13: each clause over the whole tuple
    stream) gives the value `r` exactly when the nested evaluation (each
    clause, tuple by tuple, as the XPath 4.0 `for`/`let`/`if`
    expressions) gives `r`. Only the error may differ when both fail
    (§2.3.4). -/
theorem flwor_stream_nested (cb : XCb) (env : Env) (cs : List Clause) (hc : cs.all Clause.basic = true)
    (ret : Expr) (r : Seq) :
    evalExt cb env "flwor" (cs.map Clause.toExt ++ [ret]) [] [] [] = .ok r ↔ nestT cb cs env ret = .ok r := by
  have hrun := run_basic cb cs hc [env] []
  unfold evalExt
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.reverse_reverse]
  have hl : ∀ ts : List Env,
      (do
        let s ← forIn ts #[] fun t s => do
              let d ← cb.eval t ret
              let s ← forIn d s fun i s => pure (ForInStep.yield (s.push i))
              pure (ForInStep.yield s)
        pure s.toList) = flatMapE (fun t => cb.eval t ret) ts := by
    intro ts
    rw [forIn_acc ts #[] (fun t => cb.eval t ret)]
    · cases flatMapE (fun t => cb.eval t ret) ts <;> simp [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
    · intro t s
      simp only [forIn_push]
      cases cb.eval t ret <;> simp [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  have hL : (do
        let x ← runClauses cb (List.map Clause.toExt cs) [env] []
        let s ← forIn x.fst #[] fun t s => do
              let d ← cb.eval t ret
              let s ← forIn d s fun i s => pure (ForInStep.yield (s.push i))
              pure (ForInStep.yield s)
        pure s.toList) = (streamT cb cs [env] >>= flatMapE (fun t => cb.eval t ret)) := by
    rw [← hrun]
    cases runClauses cb (List.map Clause.toExt cs) [env] [] with
    | error e => rfl
    | ok x => exact hl x.fst
  rw [hL, stream_nest_ok]
  simp only [flatMapE]
  cases nestT cb cs env ret <;> simp [bind, Except.bind, pure, Except.pure]
end L4Factoidal.XQuery4
