/-
L4Factoidal.WHATWG.URL.Cost — the basic URL parser (URL Standard section 4.4,
snapshot whatwg/url `845bafca`, as transcribed in `Parser.lean`) ends within
3n + 16 rounds of its state machine on an input of n code points.

What is proved:

- `step_good`: a round that does not end the parse keeps the invariant `Inv`
  (pointer within the input; while the authority state can still rewind, the
  buffer is no longer than the input read) and lowers the measure `mu`.
- `run_fuel_irrelevant`: the loop's result is the same for every fuel that
  covers the measure.
- `basicParse_rounds_le`: `basicParse` equals the loop with any fuel of at
  least 3n + 16, for every input, base, url, state override and encoding.

What is not proved: time per round (the authority state reads its buffer at
`@`, host parsing reads the host; IDNA has its own loops), memory, and that
the transcription in `Parser.lean` is the standard's text (read state by
state; tested by tests/whatwg-url/run.sh on the WPT data).

https://github.com/danbri/factoidal-core/issues/514. No `sorry`.
-/
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.WHATWG.URL.Cost

open L4Factoidal.WHATWG.Encoding
open L4Factoidal.WHATWG.URL

/-! ## The loop is linear: the fuel is never used up -/

/-- 2 before the scheme is settled (a later "start over" is still possible),
1 while the authority state may still rewind over its buffer, 0 after. -/
def phase : State → Nat
  | .schemeStart | .scheme => 2
  | .noScheme | .specialRelativeOrAuthority | .pathOrAuthority | .relative | .relativeSlash
  | .specialAuthoritySlashes | .specialAuthorityIgnoreSlashes | .authority => 1
  | _ => 0

/-- A rank of the states that every change of state lowers: the state graph
of the standard has no cycle except a state repeating itself. -/
def rank : State → Nat
  | .fragment => 0 | .query => 1 | .opaquePath => 2 | .path => 2 | .pathStart => 3
  | .port => 4 | .fileHost => 4 | .host => 5 | .hostname => 5 | .fileSlash => 5 | .authority => 6
  | .specialAuthorityIgnoreSlashes => 7 | .pathOrAuthority => 7 | .specialAuthoritySlashes => 8
  | .relativeSlash => 8 | .relative => 9 | .file => 9 | .specialRelativeOrAuthority => 10
  | .noScheme => 11 | .scheme => 12 | .schemeStart => 13

/-- The measure: rounds still possible from `m` on an input of `n` code
points. -/
def mu (n : Nat) (m : Machine) : Nat :=
  phase m.state * (n + 1) + ((n : Int) + 1 - m.p).toNat + rank m.state

/-- What holds of the variables at the start of every round: pointer is
within the input (the EOF position included), and while a rewind is still
possible the buffer is no longer than the part of the input read. -/
structure Inv (n : Nat) (m : Machine) : Prop where
  p_nonneg : 0 ≤ m.p
  p_le : m.p ≤ n
  buf : 1 ≤ phase m.state → (m.buffer.length : Int) ≤ m.p

/-- The pointer increment of the loop. -/
def advance (m : Machine) : Machine := { m with p := m.p + 1 }

/-- A state's result is good when, if the loop goes on after it, the
invariant holds again and the measure is lower. -/
def Good (n : Nat) (m : Machine) (s : Step) : Prop :=
  ∀ m', s = .next m' → m'.p < n → Inv n (advance m') ∧ mu n (advance m') < mu n m

/-- Split the result of a state function into its branches and close each by
arithmetic on pointer, phase and rank. -/
macro "url_state" hs:ident h:ident : tactic => `(tactic|
  (intro m' h1 h2
   have hp0 := Inv.p_nonneg $h
   have hpn := Inv.p_le $h
   have hb := Inv.buf $h
   rw [$hs:ident] at hb
   simp only [phase] at hb
   try dsimp only at h1
   repeat' split at h1
   all_goals
     (cases h1 <;>
      (refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
        simp [mu, phase, rank, advance, $hs:ident] at h2 hb ⊢ <;> omega))))

theorem stSchemeStart_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .schemeStart) : Good n m (stSchemeStart cfg m c) := by
  unfold stSchemeStart; url_state hs h

theorem stScheme_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .scheme) : Good n m (stScheme cfg m c) := by
  unfold stScheme stSchemeColon; url_state hs h

theorem stNoScheme_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .noScheme) : Good n m (stNoScheme cfg m c) := by
  unfold stNoScheme; url_state hs h

theorem stSpecialRelativeOrAuthority_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char)
    (h : Inv n m) (hs : m.state = .specialRelativeOrAuthority) :
    Good n m (stSpecialRelativeOrAuthority cfg m c) := by
  unfold stSpecialRelativeOrAuthority; url_state hs h

theorem stPathOrAuthority_good {n} (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .pathOrAuthority) : Good n m (stPathOrAuthority m c) := by
  unfold stPathOrAuthority; url_state hs h

theorem stRelative_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .relative) : Good n m (stRelative cfg m c) := by
  unfold stRelative; url_state hs h

theorem stRelativeSlash_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .relativeSlash) : Good n m (stRelativeSlash cfg m c) := by
  unfold stRelativeSlash; url_state hs h

theorem stSpecialAuthoritySlashes_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char)
    (h : Inv n m) (hs : m.state = .specialAuthoritySlashes) :
    Good n m (stSpecialAuthoritySlashes cfg m c) := by
  unfold stSpecialAuthoritySlashes; url_state hs h

theorem stSpecialAuthorityIgnoreSlashes_good {n} (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .specialAuthorityIgnoreSlashes) :
    Good n m (stSpecialAuthorityIgnoreSlashes m c) := by
  unfold stSpecialAuthorityIgnoreSlashes; url_state hs h

theorem stAuthority_good {n} (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .authority) : Good n m (stAuthority m c) := by
  unfold stAuthority; url_state hs h

theorem stHost_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .host) : Good n m (stHost cfg m c) := by
  unfold stHost; url_state hs h

theorem stHostname_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .hostname) : Good n m (stHost cfg m c) := by
  unfold stHost; url_state hs h

theorem stPort_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .port) : Good n m (stPort cfg m c) := by
  unfold stPort; url_state hs h

theorem stFile_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .file) : Good n m (stFile cfg m c) := by
  unfold stFile; url_state hs h

theorem stFileSlash_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .fileSlash) : Good n m (stFileSlash cfg m c) := by
  unfold stFileSlash; url_state hs h

theorem stFileHost_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .fileHost) : Good n m (stFileHost cfg m c) := by
  unfold stFileHost; url_state hs h

theorem stPathStart_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .pathStart) : Good n m (stPathStart cfg m c) := by
  unfold stPathStart; url_state hs h

theorem stPath_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .path) : Good n m (stPath cfg m c) := by
  unfold stPath; url_state hs h

theorem stOpaquePath_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .opaquePath) : Good n m (stOpaquePath cfg m c) := by
  unfold stOpaquePath; url_state hs h

theorem stQuery_good {n} (cfg : ParseCfg) (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .query) : Good n m (stQuery cfg m c) := by
  unfold stQuery; url_state hs h

theorem stFragment_good {n} (m : Machine) (c : Option Char) (h : Inv n m)
    (hs : m.state = .fragment) : Good n m (stFragment m c) := by
  unfold stFragment; url_state hs h

/-- Every round that does not end the parse keeps the invariant and lowers
the measure. -/
theorem step_good {n} (cfg : ParseCfg) (m : Machine) (h : Inv n m) : Good n m (step cfg m) := by
  cases hs : m.state <;> simp only [step, hs]
  · exact stSchemeStart_good cfg m _ h hs
  · exact stScheme_good cfg m _ h hs
  · exact stNoScheme_good cfg m _ h hs
  · exact stSpecialRelativeOrAuthority_good cfg m _ h hs
  · exact stPathOrAuthority_good m _ h hs
  · exact stRelative_good cfg m _ h hs
  · exact stRelativeSlash_good cfg m _ h hs
  · exact stSpecialAuthoritySlashes_good cfg m _ h hs
  · exact stSpecialAuthorityIgnoreSlashes_good m _ h hs
  · exact stAuthority_good m _ h hs
  · exact stHost_good cfg m _ h hs
  · exact stHostname_good cfg m _ h hs
  · exact stPort_good cfg m _ h hs
  · exact stFile_good cfg m _ h hs
  · exact stFileSlash_good cfg m _ h hs
  · exact stFileHost_good cfg m _ h hs
  · exact stPathStart_good cfg m _ h hs
  · exact stPath_good cfg m _ h hs
  · exact stOpaquePath_good cfg m _ h hs
  · exact stQuery_good cfg m _ h hs
  · exact stFragment_good m _ h hs

theorem mu_pos {n} (m : Machine) (h : Inv n m) : 1 ≤ mu n m := by
  have := h.p_le
  unfold mu; omega

/-- One more unit of fuel changes nothing once the fuel covers the measure. -/
theorem run_succ (cfg : ParseCfg) (fuel : Nat) : ∀ (m : Machine), Inv cfg.cs.size m →
    mu cfg.cs.size m ≤ fuel → run cfg (fuel + 1) m = run cfg fuel m := by
  induction fuel with
  | zero => intro m h hm; have := mu_pos m h; omega
  | succ fuel ih =>
    intro m h hm
    rw [run, run]
    cases hstep : step cfg m with
    | done r => rfl
    | next m' =>
      dsimp only
      by_cases hp : m'.p ≥ cfg.cs.size
      · simp [hp]
      · simp only [hp, if_false]
        have hg := step_good cfg m h m' hstep (by omega)
        exact ih (advance m') hg.1 (by have := hg.2; omega)

theorem run_add (cfg : ParseCfg) (m : Machine) (h : Inv cfg.cs.size m) (k : Nat) :
    run cfg (mu cfg.cs.size m + k) m = run cfg (mu cfg.cs.size m) m := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← ih, ← Nat.add_assoc]; exact run_succ cfg _ m h (by omega)

/-- **The result of the loop does not depend on the fuel**, for any two
amounts of fuel that cover the measure of the starting variables.

Kind: resource bound (cost theorem).
Says: from variables that satisfy `Inv`, `run` gives the same result for every fuel of at
least `mu`; so the failure that `run` gives when its fuel ends is never the result.
Does not say: that one round takes constant time (the authority state reads its whole
buffer at `@`, and host parsing reads the host), or anything about memory. -/
theorem run_fuel_irrelevant (cfg : ParseCfg) (m : Machine) (h : Inv cfg.cs.size m) (f1 f2 : Nat)
    (h1 : mu cfg.cs.size m ≤ f1) (h2 : mu cfg.cs.size m ≤ f2) : run cfg f1 m = run cfg f2 m := by
  obtain ⟨k1, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨k2, rfl⟩ := Nat.exists_eq_add_of_le h2
  rw [run_add cfg m h, run_add cfg m h]

theorem init_inv (n : Nat) (urlIn : Option Url) (override : Option State) (enc : Encoding) :
    Inv n (initMachine urlIn override enc) :=
  ⟨by simp [initMachine], by simp [initMachine], by simp [initMachine]⟩

theorem init_mu (n : Nat) (urlIn : Option Url) (override : Option State) (enc : Encoding) :
    mu n (initMachine urlIn override enc) ≤ 3 * n + 16 := by
  cases h : override.getD .schemeStart <;> simp [mu, phase, rank, initMachine, h] <;> omega

/-- **The basic URL parser runs at most 3n + 16 rounds of its state machine**
on an input of n code points (after the removal of leading and trailing C0
control or space and of ASCII tab or newline), whatever the base, url, state
override and encoding.

Kind: resource bound (cost theorem).
Says: `basicParse` equals the loop `run` given any fuel of at least 3n + 16; `run` uses one
unit of fuel a round, so the loop ends within 3n + 16 rounds with the parser's own result
(a URL or the standard's failure), and the fuel `8 × (n + 2)` that `basicParse` gives is
never used up.
Does not say: that one round takes constant time, that host parsing (IDNA) is linear, or
anything about memory. -/
theorem basicParse_rounds_le (input0 : String) (base urlIn : Option Url) (override : Option State)
    (encoding : Encoding) (fuel : Nat)
    (hf : 3 * (parseCfg input0 base urlIn override).cs.size + 16 ≤ fuel) :
    basicParse input0 base urlIn override encoding
      = run (parseCfg input0 base urlIn override) fuel (initMachine urlIn override encoding) := by
  unfold basicParse
  have hi := init_inv (parseCfg input0 base urlIn override).cs.size urlIn override encoding
  have hm := init_mu (parseCfg input0 base urlIn override).cs.size urlIn override encoding
  exact run_fuel_irrelevant _ _ hi _ _ (by omega) (by omega)

end L4Factoidal.WHATWG.URL.Cost
