# 2026-11-03 — LWS ops: which reach resources without authorization? (audit for issue 1238)

Owner, 2026-11-03: use LWS as the storage for XMPP, Solid and other components, in-process without the full HTTP exchange, but with no way for apps to bypass authentication and ACLs. Issue: https://github.com/danbri/factoidal/issues/1238.

Read in `formal/lean4/Wasm/Ops/Lws.lean` and `npm/factoidal/lws/server.mjs`. This is a reading of the code, not a proof.

| Op | What it does | Reaches resources for a requester without authorization? |
|---|---|---|
| `lwsStep` | one LWS request | no: this is the authorized path (`LWS/Authorization.lean`) |
| `lwsRead` | puts the body files that the last `lwsStep` named into memory, checking each one's seal, length, FNV-1a and SHA-256; answers a COUNT | no: no content goes out, and the bytes must be the ones the step asked for |
| `lwsLoad`, `lwsPersist` | move the sealed files between engine and disk (journal, snapshot, bodies; `Seal.hacl` with the storage key) | no: host plumbing; plans and sealed bytes, not resources for a requester |
| `lwsFetched`, `lwsDelivered` | answers to the engine's own fetch and delivery requests | no |
| `lwsDirLock`, `lwsAtRestNotice` | pure decisions about the lock file and the at-rest notice | no |
| **`lwsSnapshot`** | **the whole storage: every resource, the ACLs, and in `sideMembers` the signing key** | **yes, by design**: a host persistence operation with no authorization decision. **Sealed under the storage key when there is one; CLEAR TEXT when there is none.** |

### What holds today

- The JS host hands components a capability, not the engine: `openLwsStorage` returns `{step, settled, close}`, closed over the engine and the handle. A component given that object can make authorized requests and nothing else.
- LWS already has an at-rest layer (`Files.persist`, `Files.readControl`, `Seal.sealSnapshot`, with HACL*). Issue 1237 should use it, not a second scheme.

### What does not hold, and to do

1. **The engine is the boundary.** Code that holds the engine object can call `lwsSnapshot` with a guessable handle (`lws1`) and take everything, the signing key included. Inside one process that is unavoidable (in-process code is trusted). So the boundary for APPS must be a process, frame or origin: never give an app the engine, or a generic op-calling channel to it. Rule to check in each host: foafos, the hub pages, any RPC.
2. **Clear text when no key is given.** `lwsSnapshot` and the files mode write clear text without a storage key (there is an `atRestNotice`). Proposal: refuse to persist without a key unless an explicit `--insecure-plaintext-at-rest` is given, as `insecureNoAuth` is for authorization.
3. **An in-process principal for components.** For `xmpp-serve` to store its state through `lwsStep` under its own identity, it needs a credential that the storage's authorization accepts, without an external issuer: for example a local issuer key known only to the process, minting short-lived tokens for `/system/xmpp/`. Not built.
4. **Entry-point gate.** Mark `lwsSnapshot`, `lwsLoad` and `lwsPersist` as HOST-ONLY in `foundation/entrypoints.toml` (with a reason), so that any new op that returns resource content without authorization is noticed.
5. **Theorems** (unchanged from the issue): mediation for `lwsStep`; containment for a component principal; no ambient default when `auth` is absent; plus, for `lwsSnapshot`, `snapshotAnswer` with a key never returns the clear document (provable over `Seal.sealSnapshot`).

## Correction, and the component principal (later, 2026-11-03)

The table above missed work already in `main`. `L4Factoidal/LWS/AccessTheorems.lean` proves
`lws_data_only_through_authorized_step`; `Wasm.Ops.lwsOpRole` classifies every LWS op, and
`Wasm.Ops.lws_only_lwsStep_serves` proves that `lwsStep` is the only op that answers with resource
content. Follow-up 4 (classify the ops) was therefore already done, by a theorem.

Follow-up 3 is now built: **a component principal.**

- `AuthzConfig.principal` (`L4Factoidal/LWS/Authorization.lean`): for a storage that a component
  opens in-process and no listener serves. No token is read; every request is the principal's,
  and Web Access Control still decides it (the existing `gate`).
- Theorems: `authenticate_no_issuers` (with no trusted issuer, no request is authenticated as
  anyone) and `decide_principal_agents` (in principal mode the only agents a request proceeds as
  are the principal and the public); `default_no_principal`.
- Configuration `"principal"`, exclusive with `"auth"` and `"insecureNoAuth"`; host option
  `openLwsStorage({ principal })`; `createLwsServer` refuses a principal storage, because served
  over HTTP every client would act as the component.
- Tests: `npm/factoidal/test/lws-principal.test.mjs` (6): granted principal reads and writes; a
  principal the ACL does not name gets 403; a bearer token changes nothing; the listener refuses;
  exclusivity; a sealed files storage survives a reopen and a wrong key refuses to open.
- Found: a provisioned `rootAcl` with a relative subject (`<#c>`) grants nothing:
  https://github.com/danbri/factoidal/issues/1241.
