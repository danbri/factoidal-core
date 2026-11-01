# Foafpod private history and commit grouping

Owner request, 2026-11-01: retain private history for a laptop LWS pod,
optionally in Git, a directory, or a second LWS storage; configure quiet
periods, maximum delay and session grouping in pod RDF configuration.

Status: scheduling policy implemented and Lean checked; durable history service
and RDF configuration loading are not implemented or activated.

## Separate durable capture from presentation

A durable change journal must retain each accepted storage revision, including
deletions, before that revision is acknowledged as durable. Hook this into the
storage commit protocol; a best-effort notification is only a wake-up hint.
Define recovery for a crash between journal and storage writes. Fetching the
current resource after a webhook cannot recover overwritten intermediate states.

Git commits can group journal revisions after a quiet period (initial example
2 seconds) or maximum wait (30 seconds), whichever comes first. Both durations
are measured by a monotonic clock. UTC timestamps are for humans, not deadlines.
A continuous stream cannot postpone a group indefinitely. These are grouping
deadlines, not guarantees about disk or network completion.

Session identifiers may advise grouping, but never grant access or bypass the
maximum wait, byte limits, destination policy or durable capture. Grouping
must include principal/application scope; clients cannot merge another user's
work by guessing an identifier. Offline destinations leave a durable backlog.
Only a confirmed destination write advances its delivery checkpoint.

## RDF configuration

Use a private operator-owned Turtle config, potentially foafpod.ttl. Parse it
with the existing Lean RDF parser into typed configuration. Do not expose a
new remote configuration-write privilege through public pod resources. The
vocabulary is not finalized. Proposed fields:

- captureMode: every durable revision
- groupingMode: quiet-period, explicit-session, or hybrid
- quietPeriod: xsd:duration, example PT2S
- maxGroupDelay: xsd:duration, example PT30S
- maxGroupBytes and maxPendingBytes
- destination: local Git repository, snapshot directory, or second LWS root
- credentialRef: reference to operator-private credentials, never their values
- publication: private; no automatic public-replica inclusion

Validate durations as nonnegative fixed time intervals (no calendar months),
with quietPeriod > 0 and quietPeriod <= maxGroupDelay. An application-selected
profile adds meaningful upper/lower bounds and byte limits. Invalid or missing
required configuration fails explicitly; it must not silently disable history.
Record the effective policy/version with each group. A configuration update
must say whether to flush the old group or preserve its already-set deadline.

Private history lives outside the public Fly replica root. Even public current
resources can have private/deleted historic versions. Destination credentials,
local filesystem paths and journal internals are not public profile data.
A second LWS destination requires private ACLs and a dedicated writer identity;
do not configure two history services to recursively archive each other.

## Proof targets and limits

Prove well-formed configuration, order-preserving grouping, each revision in
exactly one completed group, checkpoint advancement only after acknowledgement,
and no output to a destination outside the configured allowlist. Parameterize
scheduler liveness by explicit clock, scheduling and IO assumptions. Lean
cannot establish physical fsync or destination honesty from a pure model alone.

A Git commit stream gives revision grouping, not one commit per change. Preserve
the underlying journal if every intermediate revision must remain recoverable.
Restoration must use LWS's checked storage interfaces; never modify its live
backing directory behind the server.

## Checked scheduling component

`L4Factoidal.LWS.HistoryPolicy` implements validated application bounds, quiet
and maximum-delay decisions, scoped revision grouping, and a retained monotonic
clock cursor. It is imported by the library umbrella so normal library builds
check it. Eighteen kernel examples cover invalid bounds/durations, quiet and
maximum expiry, backwards timestamps, scope changes and debounce extension.
Eight axiom audits use only propext/Quot.sound. The key theorem
`extension_cannot_postpone_maximum` proves that accepted revisions cannot reset
the first-revision deadline; `poll_at_maximum` proves a poll reaching that
deadline requests a flush. Source mutations dropping the maximum cap, replacing
the maximum check with quiet expiry and bypassing the cursor were rejected.

This is executable pure scheduling, not background journal capture. Callers
must retain the returned cursor and use one monotonic clock epoch. A flush
decision does not consume the incoming revision; durable delivery must retain
it for retry. Restart/recovery, byte budgets, TTL and private destination checks
remain separate work. No server runtime is switched to this module yet.
