/-!
# Risk token for the key modules (skills/lean-risk-flags)

The key modules are our own code handling secrets, in pure Lean: nothing shows that
their timing, branching or memory use is independent of the secrets, and nothing
clears a secret from memory (see `EthereumWallet/Keys.lean`). So every entry point
that takes a secret (entropy, a mnemonic, a passphrase or password, a seed, a private
key, a derived key) takes a value of `Risk.Accepted .variableTimeSecrets`, and the only
way to make one is `Risk.dangerouslyAccept`, by name. Code that does not pass the token
does not compile; `git grep dangerouslyAccept` lists every acceptance. The token is
erased at run time.

At a command line the acceptance is the flag `--dangerously-enable-variable-time-secrets`,
off by default, and it is the only path that calls `Risk.dangerouslyAccept` there.

Functions of public data only (public child derivation, address of a public point,
ERC-55 text, path parsing, reading keystore JSON, MAC and parameter checks that refuse)
take no token.
-/

namespace EthereumWallet.Keys

/-- The risks the key modules know of. Each constructor says what is not shown. -/
inductive Risk where
  /-- Our own secret handling in pure Lean: timing, branching and allocation may depend
  on secrets (`Nat` is arbitrary-precision; scrypt indexes memory by secret values), the
  compiled code was not examined, and secrets are never zeroised. Acceptable only where
  an attacker cannot time the process or read its memory. -/
  | variableTimeSecrets
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`. The constructor is private: the only way to
make one is `Risk.dangerouslyAccept`, so every acceptance is a call to that name. -/
structure Risk.Accepted (r : Risk) : Type where
  private mk ::

def Risk.dangerouslyAccept (r : Risk) : Risk.Accepted r := ⟨⟩

/-- The token the secret-taking entry points ask for. -/
abbrev SecretRisk : Type := Risk.Accepted .variableTimeSecrets

/-- The command-line flag that stands for the acceptance. -/
def secretRiskFlag : String := "--dangerously-enable-variable-time-secrets"

end EthereumWallet.Keys
