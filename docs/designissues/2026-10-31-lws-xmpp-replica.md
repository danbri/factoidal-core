# LWS replication through XMPP accounts

Status: proposed design, 2026-10-31. Replication is not implemented.
Related: [existing HTTP-over-XMPP transport](2026-10-28-http-over-xmpp.md).

## Deployment and accounts

Use two dedicated client accounts, for example `pod-writer@example.net/mac`
and `pod-replica@example.net/server`. Both make outbound TLS connections to
an ordinary XMPP server. They can share a provider; federation is optional.
The server can be owned by the user or hosted elsewhere. No LAN membership,
VPN, router forwarding or inbound laptop port is required.

The always-on machine runs a replica agent and an LWS read service. Ordinary
apps use HTTPS and LWS authorization; they need no XMPP accounts. Initially
the read service can remain localhost-only and be reached through SSH. Public
HTTPS is a separate deployment decision. The machine needs outbound XMPP
access in addition to the SSH access the user already has.

Never share account passwords. Provision a pod identity, writer public key,
replica identity and permitted peer JIDs out of band. JIDs route traffic;
the pinned writer key authorizes replication. XMPP TLS is hop-by-hop: a
third-party provider can see unencrypted payloads. Encrypt private batches
end-to-end with an existing supported construction; fail closed if unavailable
on a target. Do not invent crypto or silently fall back to plaintext.

## Protocol: single writer, durable replica

This is a Factoidal application protocol carried by XMPP, not a claim that
LWS or an existing XEP specifies replication.

1. The laptop commits changes and a durable outbox record together. A batch
   names protocol version, pod identity, writer epoch, revision, previous
   commit hash, operations, authorization-policy revision and payload hash.
   Authenticate the whole envelope, including destination/scope. Include
   deletions explicitly. Keep publication authority separate from app rights.
2. On connection the replica reports its last durably applied revision/hash.
   The writer sends missing batches in bounded chunks. No reliance on an
   XMPP provider's offline-message retention for correctness.
3. Lean validates peer authority, schema, limits, chain and expected revision.
   Exact duplicates return the prior acknowledgement; conflicting duplicates,
   gaps and unknown epochs are refused or trigger catch-up. Chunks are staged
   until the complete authenticated batch is present.
4. Apply resources and their access policy atomically through an LWS-owned
   replication operation. Hosts never write storage files as a shortcut.
   Acknowledge only after durable commit; transport delivery is insufficient.
5. On history expiry use an authenticated snapshot manifest, staged and
   verified before an atomic swap. An old signed snapshot must not roll back
   an existing replica. Initial enrollment requires a trusted checkpoint.
6. App requests cannot mutate replicated application resources. Replication
   is a separate capability, not a general write credential exposed to apps.
   Reads retain LWS authorization. Do not infer read permission from a roster.

Preserve logical resource identity independently of the replica transport URL.
Do not silently rewrite RDF IRIs, policy targets or signed documents. Record
replica endpoint and canonical pod identity separately in discovery metadata.
Do not replicate writer private keys or unrelated host secrets.

## Offline behavior and revocation

The server serves its last committed snapshot when the laptop sleeps, with a
revision, last-contact time and explicit freshness policy. Immediate remote
revocation during a partition is impossible while continuing unrestricted
offline reads. Select a bounded authorization lease, or explicitly accept
stale policy for a named resource class. Lease expiry denies affected reads;
it requires a trusted clock assumption. Resource and policy changes must
be applied in the same atomic batch. This tradeoff is application policy,
not something XMPP or a proof can remove.

One writer only in the first version. Replica promotion requires an explicit
new epoch and fencing of the former writer; automatic writable failover is
out of scope. Local success means locally committed; a separate status means
replicated. Optional synchronous mode waits for the durable replica ack.

## XMPP standards and limits

- [RFC 6120](https://www.rfc-editor.org/rfc/rfc6120): client authentication,
  routing and TLS. Discover server limits; test against a separate implementation.
- [XEP-0198](https://xmpp.org/extensions/xep-0198.html): acknowledgements and
  stream resumption improve transport reliability, not LWS durability.
- [XEP-0060](https://xmpp.org/extensions/xep-0060.html): optional revision
  notifications/fanout. Persistent-item support and retention are optional;
  PubSub is not the authoritative commit log. Not required for the two-peer MVP.
- [XEP-0332](https://xmpp.org/extensions/xep-0332.html): existing experimental
  HTTP-over-XMPP path can exercise request/response behavior. It is Deferred
  and explicitly not recommended for production; do not make it the mandatory
  foundation of the new replication protocol.

Bound stanza/chunk size, total pending bytes, batch length and retry rate.
Large-object transport may later use authenticated HTTPS fetches with fixed
origins and hashes; arbitrary URLs from stanzas must not trigger host fetches.

## Lean operations, assurance and tests

Proposed pure operations: makeBatch, validateBatch, receiveChunk, planApply,
commitAcknowledged, resumeFrom and admitReplicaRead. Host effects are socket,
clock, crypto and atomic persistence requests/results. Reuse the same state
machine over SSH-forwarded HTTP as well as XMPP.

Proof targets (not established yet): accepted histories are prefixes of the
authorized writer history; duplicate application is idempotent; read requests
preserve replicated resources; denied reads return no protected resource body;
visible batches never mix resource/policy revisions; conditional convergence
under eventual delivery and durable storage. Explicit assumptions include
crypto correctness, trusted enrollment, host persistence and clock behavior.

Tests must cover disconnect at each commit/ack boundary, duplicate/reordered
chunks, gaps, malicious sender, tampered payload, stale signed snapshot,
policy revocation and lease expiry, delete propagation, bounded buffering,
and laptop sleep followed by catch-up. First deliver a single-writer replica
with a disk journal and fault injection, then add XMPP transport and interop.
