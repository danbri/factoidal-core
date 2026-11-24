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
  /-- Verification of an RSA signature under a 1024-bit modulus
  (`Crypto.Rsa.rsaPublicOp1024`, XML Signature 1.1 through
  `XML.DSig11.nativeBackendRsa1024`). The arithmetic is HACL*'s, as for 2048 bits and more.
  Not shown: that the key resists factoring. NIST SP 800-131A Rev. 2 (2019) allows a
  1024-bit RSA key only to verify legacy signatures; XML Signature 1.1 §6.4.2 permits it.
  A signature that validates under such a key is evidence only against a party who cannot
  factor a 1024-bit modulus. Owner, 2026-11-17, on
  https://github.com/danbri/factoidal/issues/1227: "off by default and make user pass in a
  \"dangerously_and_regrettsbly_.... \" symbol". -/
  | rsa1024Verify
  /-- Finite-field Diffie-Hellman key agreement over a prime of fewer than 2048 bits
  (XML Encryption 1.1 `xmlenc11#dh-es` through `XML.Enc.Opts.dh1024`). The arithmetic is
  HACL*'s, as for 2048 bits and more. Not shown: that the group resists the discrete
  logarithm. NIST SP 800-131A Rev. 2 (2019) disallows key agreement with a modulus of fewer
  than 2048 bits; the W3C interop case AGRMNT.7 uses 1024 bits. The coordinator applied the
  owner's 1024-bit RSA decision (https://github.com/danbri/factoidal/issues/1227) to this
  case; it is not an owner decision of its own. -/
  | dh1024Agreement
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`. The constructor is private: the only way to
make one is `Risk.dangerouslyAccept`. -/
structure Risk.Accepted (r : Risk) : Type where
  private mk ::

/-- Accept risk `r`. Each call names who decided and why, and is in the register. -/
def Risk.dangerouslyAccept (r : Risk) : Risk.Accepted r := ⟨⟩

end L4Factoidal
