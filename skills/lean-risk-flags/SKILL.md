---
name: lean-risk-flags
description: How code that rests on something unproved, unverified or unsafe is flagged so the risk is visible where it is used, in the build and to the person running it — the risk token, `--dangerously-…` flags, no silent fallbacks, and the register of open risks. Use before adding or reviewing crypto, code that handles secrets or private data, a fast path or fallback, or anything whose safety is assumed rather than shown; and before describing such code as safe.
---

# Flagging risky properties in Lean code

Owner, 2026-11-13: code we wrote ourselves for a job that needs assurance we do not have (the example
was a home-grown AES) is off by default. Keeping it in the codebase is fine, with warnings. Using it is an
explicit choice that shows where it is made: a client accepts the risk by name, in code and on the
command line. Companion rules: [`local-lean-rules`](../local-lean-rules/SKILL.md) (the banned escape
hatches), [`crypto-policy`](../crypto-policy/SKILL.md) (HACL\*, never hand-rolled).

## 1. What needs a flag

A risk is a property the code depends on that is neither proved here nor supplied by a verified source we
trust (HACL\*, for example). In particular:

- **Crypto or secret handling we wrote**: an implementation of a primitive, or any code whose timing,
  allocation or branching depends on a secret, unless its constant-time property is shown. Pure Lean on
  `Nat` and `ByteArray` leaks through allocation and the interpreter's timing (`Crypto/ChaChaPoly.lean`).
- **Data of unknown sensitivity.** Code cannot know that its input is "public". An RDF or SPARQL engine
  has no record of the rights or sensitivity of a graph, so any argument that starts "this data is
  public" is not one the code can rely on. The only inputs that count as non-secret are those that are
  non-secret **by the protocol's definition**, in every deployment (the WebSocket accept key, a public
  key, a signature to verify).
- **A silent fallback** from a verified path to an unverified one: for example, HACL\* refusing and pure
  Lean answering instead.
- **An unproved fast path** standing in for a proved specification, beyond what `local-lean-rules` §4
  already allows (a differential test, said so).

Refusing is not a risk. `NotSupportedError` for AES on hosts without a verified AES is the safe default.

## 2. The mechanism: a risk token

The risky function takes a value that only a loudly named function can make:

```lean
/-- The risks the tree knows of. Each constructor's doc comment says what is not shown. -/
inductive Risk where
  | unverifiedAes      -- an AES that is not HACL*'s
  | pureHashOnPrivate  -- a pure Lean hash run on data of unknown sensitivity
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`. The constructor is private: the only way to make
one is `Risk.dangerouslyAccept`, so every acceptance is a call to that name. -/
structure Risk.Accepted (r : Risk) : Type where
  private mk ::

def Risk.dangerouslyAccept (r : Risk) : Risk.Accepted r := ⟨⟩

def aesEncryptUnverified (_ : Risk.Accepted .unverifiedAes) (key iv data : ByteArray) : ByteArray := …
```

- Code that does not pass a token **does not compile**. The token is erased at run time, so it costs
  nothing.
- `git grep dangerouslyAccept` lists every acceptance. Each one needs a comment naming who decided and
  why, and it is listed in section 5. A new acceptance needs the owner, as raising a hygiene baseline does.
- Planned (not yet built): a Lean-level check like `labs/demos/foafnaut/LabHygiene.lean` that walks
  the constants each shipped entry point (Hub, CLI, npm) depends on and fails the build when one reaches
  `Risk.dangerouslyAccept` with a risk that is not allowed for that target. It is the same machinery as
  the hygiene ratchet, and it can check what grep cannot (an acceptance reached through three modules).

**Why not an axiom.** `axiom AcceptsUnverifiedAes : Prop` would make `#print axioms` list the risk on
every theorem that depends on it, which is attractive. But `local-lean-rules` §1 bans user axioms, and a
theorem may report only `propext`, `Classical.choice` and `Quot.sound`. Using axioms for this needs the
owner's exception first. Until then, use the token.

## 3. At run time: `--dangerously-…`

Where a person, not code, must choose the risk (a CLI run, a Hub setting, an npm option):

- The flag is off by default, named `--dangerously-enable-<risk>` (for example
  `--dangerously-enable-unverified-aes`), and it is the only code path that calls
  `Risk.dangerouslyAccept` for that risk.
- When it is on, it is reported: a warning on start, and a line in `about:foafnaut`, `--version` and the
  build or run record. A run whose results depend on it says so in its output (a WPT score made with an
  unverified AES is not the same score).
- Not reachable from page content. A web page cannot turn a risk on.

## 4. No silent fallbacks

A verified path that cannot answer **refuses**. It does not hand the request to an unverified path. A
fallback is allowed only behind a token, and then it is a flagged risk like any other. Proving the two
paths equal (as `hmacFast_eq_pure` does in `Crypto/WebHacl.lean`) shows they give the same answer. It
does not show the fallback has the verified path's timing.

## 5. Register of open risks

Keep this current. Remove an entry in the commit that removes the risk.

| Where | What is not shown | Since | Way out |
|---|---|---|---|
| SPARQL `MD5`, `SHA1`, `SHA256/384/512` (`SPARQL/Expr.lean` over `Crypto/MD5.lean`, `SHA1.lean`, `SHA2.lean`) | pure Lean on graph data of unknown sensitivity; constant time not shown | 2026-08-22 (flagged 2026-11-13) | run on HACL\* (SHA-1, SHA-2 vendored; MD5 upstream), pure Lean as the specification |
| XPath `fn:hash` BLAKE3 (`Crypto/Blake3.lean`) | as above; HACL\* has no BLAKE3 | 2026-10-28 | constant-time argument for the compiled code, or a verified BLAKE3 |
| RDFC-1.0 and VC document hashing (`Wasm/Ops/Vc.lean`, `Crypto.hashHex`) | pure SHA-256 on documents that may be private | 2026-08-22 | `sha256Hacl` at run time |
| `hashFast` and `hmacFast` (`Crypto/WebHacl.lean`) | fall back to pure Lean when HACL\* refuses (only above HACL\*'s size bound, never for a page's arguments) | 2026-11-09 | refuse instead |

Not risks: AES (off, refused with `NotSupportedError` on arm64 and Wasm; the host's WebCrypto in npm),
P-384, P-521 and RSA key generation (off).

## 6. In reports

Name the risk and where it is accepted. Do not call code with an open risk "verified" or "safe". Say what
is shown (proved, tested, HACL\*'s) and what is not, as `local-lean-rules` §3 requires.
