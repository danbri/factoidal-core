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
  /-- A page's real-time `AudioContext` starts, and its `resume()` goes on, with no user
  activation (Web Audio API 1.1, "allowed to start"; `WebAudio.Api.allowedToStart`). Not
  shown: that the person wants the sound. A page can make sound as it loads, before it has
  been used. Accepted only by the engine's start request with `dangerouslyPermitAudio: true`
  (`labs/demos/foafnaut/WebScripts.lean`, `audioLimits`), which the browser sends only for the
  command-line option `--dangerously-permit-audio` or the Settings switch. Owner, 2026-11-26:
  "3. yes (but with a Settings or CLI setting --dangerously-permit-audio). In future we may
  have other mechanisms for page trust." -/
  | audioWithoutActivation
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`. The constructor is private: the only way to
make one is `Risk.dangerouslyAccept`. -/
structure Risk.Accepted (r : Risk) : Type where
  private mk ::

/-- Accept risk `r`. Each call names who decided and why, and is in the register. -/
def Risk.dangerouslyAccept (r : Risk) : Risk.Accepted r := ⟨⟩

end L4Factoidal
