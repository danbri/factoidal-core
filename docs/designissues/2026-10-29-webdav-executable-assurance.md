# WebDAV executable versions and the LWS boundary

The published 0.26.0 npm package identifies core commit
`7a58d9502ab5487b7694459d775b6f7d2997d3b4`. Its WASM SHA-256 is
`7873155103b0243c0ad9723392015fe262d3ffa4ce4b8d59208a5027b550ea65`.
The previously published standalone executable identifies itself as 0.20.0.
The two distribution channels did not advance together: failed WebDAV
checks prevented later executable publication.

## What NO LOGIN means on the older executable

Without `--users`, the listener does not authenticate its WebDAV clients.
Each mount's `did:key` is the gateway's upstream LWS identity. It is not the
identity of the Finder or Explorer user. A reachable writable mount lets a
client act with that mount agent's rights, subject to the upstream LWS ACL.
Binding to 127.0.0.1 limits the listener to local connections; it does not
identify which local user made a request.

## What 0.26.0 establishes

The emergency rules of https://github.com/danbri/factoidal/issues/1147 are
present in the release source:

- All eight write methods are refused. Only reads are routed to storage.
- Each request is either an authenticated WebDAV user or an explicitly
  configured guest. With neither, it receives 401.
- A mount lists its allowed users. Other users cannot list or read it.
- Local mounts are refused. Accepted mounts use the LWS client interface,
  so the LWS server applies its own authorization.

`formal/lean4/L4Factoidal/WebDAV/Theorems.lean` contains
`webdav_within_lws`, `handle_no_write`, `hidden_mount_no_op` and
`load_no_unauthorized_storage`. The first relates every operation in the
WebDAV program trace to an allowed remote mount and a read operation of the
LWS client. `Login.lean` proves the relevant named-user admission properties.
These are source-level statements with their explicit model and accepted
configuration hypotheses; they are not a proof of the host runtime or the
whole deployed installation.

The source explicitly leaves a further identity requirement open: every
WebDAV user listed for a mount still acts as that mount's configured LWS
agent. The user's LWS identity is not derived from the WebDAV login.
Read-only mode does not make a permissive guest mount confidential.

## Executable verification

Compile the exact published package with `tools/build-exe.sh` and
`FACTOIDAL_PKG` pointing at the installed package. `version --json` must
report 0.26.0, the recorded source and matching WASM digest. This is a local
build until the executable release pipeline passes and publishes it.

The desktop gate must use the same selected executable for LWS and WebDAV.
Its fixture writes go through authenticated LWS HTTP; its WebDAV checks
assert refusal of writes, user visibility, and unchanged stored data.
Large files remain in the gate. Measurements and the remaining failure:
[`20261029-webdav-executable-gate.md`](../20261029-webdav-executable-gate.md).
