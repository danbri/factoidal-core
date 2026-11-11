# LWS root ACL safety: no open window, no lockout, operator reset (2026-11-11)

Status: implemented on main (495ef4a3c, 2ae53ba2e), not yet in an npm release (0.35.1 is latest).
Operating notes: `skills/lws-solid/SKILL.md`, "Root ACL: installed at open, no lockout, operator reset".
User-side record (foafos-stack, recovery agent, migration of a real storage):
https://github.com/danbri/glitchcan-minigam/blob/master/docs/foafos-lws-acl-safety-20261111.md

## Problems

1. **Open window.** A storage made with `--insecure-no-auth` has no `/.acl`. `--root-acl` was written
   only into a NEW storage, so with `--authz` every agent, the owner too, got 403. The only way out
   was to serve it for a moment with no authorization and PUT `/.acl`; during that moment any local
   process could read and write the storage.
2. **Lockout.** A write to `/.acl` that removed the last agent with `acl:Control` on the root locked
   the storage forever: nothing could write the ACL again.

## Decisions

- **Install at open, not an offline init command.** The open already reads the storage through the
  storage library under the directory lock, and already takes `--root-acl`/`--owner`. An offline
  command would be a second load-persist path and a second place for the rule.
  Rule: authorization on, a root ACL given, no `/.acl` → write it before any request. Never replace an
  existing `/.acl`; change nothing else; nothing with `insecureNoAuth`.
- **Guard every request, decided in Lean.** After the storage operation, `Handler.decided` refuses a
  request whose result changes the root ACL texts and leaves no Control agent on the root. "Control
  agent" is WAC `allowed` itself over a finite candidate list from the same graph (public, any
  authenticated agent, each `acl:agent`, each `vcard:hasMember`), proved equal to the existential
  (`hasRootControl_iff`). There is no second ACL parser and no second meaning of Control.
- **409 Conflict, not 403.** The requester was allowed (it had Control); the state it asks for is
  refused (RFC 9110 §15.5.10). This server's 403 carries `error="insufficient_scope"`, which tells a
  client to get another token.
- **Operator reset as a last resort.** `factoidal lws-acl-reset DIR FILE --operator`, offline, under
  the directory lock, through the journaled store; refuses an ACL with no Control agent. It needs
  access to the machine, so it does not weaken remote access.
- **Recovery agent is a convention, not server code.** A second did:key with `acl:Control` of the
  root only (no Read, Write or `acl:default`) can rewrite the ACL but cannot read data. foafos-stack
  writes one; any deployment can.

## Theorems

`L4Factoidal/LWS/RootAclInstall.lean`: `install_only_when_absent`, `install_keeps_existing`,
`install_off_unchanged`, `install_no_acl_given_unchanged`, `install_has_root_acl`,
`install_writes_given`, `install_other_paths`, `allowed_without_acl` (with no ACL resource, WAC allows
no agent anything).

`L4Factoidal/LWS/NoLockout.lean`, `NoLockoutTheorems.lean`: `step_keeps_root_control` (authorization
on, a served request, Control before → Control after), `decided_served_guarded` (a refusal is 409 with
the state unchanged, no notifications), `lockout_iff`, `accepted_keeps_control`,
`guard_refused_unchanged`, `guard_keeps_control`, `allowed_of_texts`, `hasRootControl_iff`,
`decideAccess_candidates`; `reset_has_control`, `reset_writes`, `reset_other_paths`, `reset_refuses`.
Lock refusal: the existing `DirLock.decide` theorems.

## Not proved or not tested

- The socket is bound before the open (the port sets the base IRI). Requests wait for the open and
  fail closed meanwhile; no test measures it.
- That the host takes the directory lock before the operator open (host code).
- No test: PATCH of `/.acl` (only JSON Patch is accepted, 415), moves and access grants that change
  `/.acl`, `lws-acl-reset` on snapshot or encrypted storages, the browser in-page path, the Deno host,
  `solid-serve`.

## Behaviour changes

- An existing storage with no `/.acl`, started with authorization and `--root-acl`/`--owner`, now gets
  that ACL (before: 403 for all). A deleted root `/.acl` comes back at the next such start.
- A request that would remove the last root Control agent now gets 409 (before: it succeeded).
- `--insecure-no-auth` storages are unchanged.

## Related open item

HTTP over XMPP (`webdav-serve --xmpp --xmpp-allow`): the bare-JID allow list has `#guard`s and tests
but no theorem that a sender not on the list is refused with no change
([2026-10-28-http-over-xmpp.md](2026-10-28-http-over-xmpp.md)).
