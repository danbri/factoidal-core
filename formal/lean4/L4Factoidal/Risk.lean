/-
L4Factoidal.Risk: risks the tree accepts only by name (skills/lean-risk-flags §2).

A function that rests on a property neither proved here nor supplied by a verified source
takes a `Risk.Accepted r`. The only way to make one is `Risk.dangerouslyAccept r`, so
`git grep dangerouslyAccept` lists every place a risk is taken, and code that does not
pass a token does not compile. The token is erased at run time.

Each constructor says what is not shown. Every acceptance is listed in the register of
skills/lean-risk-flags §5 and comes from a `--dangerously-…` flag of a host's command line,
never from page content.
-/

namespace L4Factoidal

/-- The risks the tree knows of. -/
inductive Risk where
  /-- A WebDriver endpoint (`WebDriver.Gate.start`): remote control of the browser on a
  loopback port behind a 128-bit secret. Not shown: that the compiled secret comparison
  takes the same time for every input (`Gate.sameText` reads every character but branches
  on each), nor that the host binds only the address it asked about. Bounded by the lock
  after `Gate.maxFailures` refusals. -/
  | webdriverEndpoint
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`. The constructor is private: the only way to
make one is `Risk.dangerouslyAccept`. -/
structure Risk.Accepted (r : Risk) : Type where
  private mk ::

/-- Accept risk `r`. Each call names who decided and why, and is in the register. -/
def Risk.dangerouslyAccept (r : Risk) : Risk.Accepted r := ⟨⟩

end L4Factoidal
