---
title: Pods, bots and access control
description: One LWS pod owned by a did:key agent, two bot agents with read-write and read-only access through a Web Access Control ACL, and what each of them sees through a read-only webdav-serve mount of its own (0.21.0). Which identity is checked where, and what Guest gets.
layout: hub.njk
tests: tests/hub/hub_pods-and-bots_test.mjs
---

# Pods, bots and access control

<p class="warning"><strong>⚠️ EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the whole core
library and every command line tool, and in particular all protocol,
authentication and security code.</p>

[Hub](../) · [Servers](../servers/) · [WebDAV](../webdav/) · [WebDAV, LWS and custodians](../webdav-lws-design/) · the setup, who is a user, the files, the rights over LWS, one mount per bot, Guest, limits

This page builds one Linked Web Storage (LWS) storage — call it a *pod*, as
Solid does; the LWS specification says *storage* — owned by an agent
`danbri1`, with two bot agents: `danbri1_bot1` may read and write,
`danbri1_bot2` may only read. Every agent is a `did:key`. The pod checks every
request against a Web Access Control ACL. A `webdav-serve` front end then
gives each agent one WebDAV mount of its own, for Finder, `mount_webdav` and
`curl`, behind a login of the same name.

In `@factoidal/core` 0.21.0 `webdav-serve` is **read only**
([issue 1147](https://github.com/danbri/factoidal/issues/1147)): every
WebDAV write is refused, whatever the agent may do over LWS. So `danbri1_bot1`
writes over LWS, with its key, and reads over WebDAV like the others.

A server cannot run in a browser page, so this page has no live cells. The
commands were run on 2026-10-28 with `@factoidal/core` 0.21.0 from npm on
macOS; `tests/hub/hub_pods-and-bots_test.mjs` runs the setup, the rights
checks and the WebDAV checks again (not the macOS mount). Private keys and
passwords are never shown: a key file is a login.

<figure>
<img src="../assets/pods/architecture.svg" alt="Diagram: Finder and curl on the Mac talk WebDAV, read only, to webdav-serve on port 8093, which checks a login from users.txt (or treats a request with no credentials as the guest user) and has one folder per agent, each listing one user and holding that agent's key; webdav-serve talks LWS, reads only, with a Bearer token to the pod on port 8083. A bot process talks LWS to the pod directly with its own key and may write. The pod's authorization server issues the tokens and its root ACL gives danbri1 Read, Write and Control, bot1 Read and Write, bot2 Read." width="860">
<figcaption>The setup in 0.21.0. <code>webdav-serve</code> decides who may use which folder and refuses every write; the pod decides what each agent may read and write.</figcaption>
</figure>

## Who is a user?

There are three kinds of identity here:

1. **The Mac account** (`danbri`). macOS checks it. Every file in a WebDAV
   mount shows as owned by it. The pod never sees it.
2. **The WebDAV user.** `webdav-serve` checks it. Every request acts as one
   named user: a login from the `--users` file (HTTP Basic), or, for a request
   with no credentials, the user that `--guest NAME` names (with no `--guest`,
   such a request gets 401). Each mount file lists its users (`users:`); any
   other user gets 404 for that mount, and the root folder does not list it.
   The pod never sees the WebDAV user.
3. **The LWS agent**, a `did:key`. The pod's ACL names it, and the pod checks
   it on every request through an access token that the agent got by signing
   a JWT with its private key.

A WebDAV user is not an LWS agent. In 0.21.0, every user listed for a mount
acts as that mount's one agent (the key that the mount file names); there is
no per-user agent yet (the next stage of issue 1147). This page therefore
gives each agent its own mount, and lists exactly one WebDAV login for it, of
the same name: the login `danbri1_bot2` is the only user who reaches the
folder that holds `danbri1_bot2`'s key.

<figure>
<img src="../assets/pods/identities.svg" alt="Diagram of three columns: the Mac account, checked only by macOS; the WebDAV user, a login from users.txt or the --guest user, checked by webdav-serve, which reaches only the mounts whose users: list it and acts there as the mount's agent, read only; the LWS agent did:key, named in the pod's ACL and checked by the pod on every request." width="860">
<figcaption>Three layers of identity. Only the third reaches the pod; the second decides which agent's folder a request may use.</figcaption>
</figure>

## The files

Everything lives in one folder, here `~/tmp/pods` (in the home folder, not
`/tmp`):

```
~/tmp/pods
├── dav/                      webdav-serve's configuration: one mount file per agent
│   ├── danbri1.md
│   ├── danbri1_bot1.md
│   └── danbri1_bot2.md
├── keys/                     the agents' private keys (P-256 JWK, mode 0600) — logins: never share
│   ├── danbri1.jwk
│   ├── danbri1_bot1.jwk
│   └── danbri1_bot2.jwk
├── users.txt                 the WebDAV logins (PBKDF2 hashes, mode 0600)
├── root.acl                  the pod's root ACL (Turtle, Web Access Control)
├── danbri1-pod/              the pod's storage (--storage files)
│   ├── lws-files.json
│   ├── lws-journal
│   ├── lws.lock              while lws-serve runs
│   └── bodies/
├── danbri1-as/               the authorization server's signing keys
│   └── authz-keys.json
├── lws-serve.log
└── webdav-serve.log
```

The pod's files are the server's: add, change and delete content only through
the server over LWS, never in `danbri1-pod/`.

## 1. Three agents, three mounts

A mount file of kind `lws` with `auth: did-key` names a key file; when the file
does not exist, `webdav-serve` makes a new P-256 key (mode 0600) and prints the
agent's `did:key`. One mount file per agent; `users:` names the one WebDAV
login that may use it:

```
$ cat dav/danbri1_bot1.md
# danbri1_bot1 on the danbri1 pod
- kind: lws
- url: http://127.0.0.1:8083/
- auth: did-key
- key-file: ../keys/danbri1_bot1.jwk
- users: danbri1_bot1
```

`users:` is required. There is no `writable:` line: in 0.21.0 it is read and
ignored, and every mount is read only.

The WebDAV logins, one per agent, with the same names
(`webdav-user` asks for the password, with no echo):

```
$ factoidal webdav-user users.txt danbri1
webdav-user: added danbri1 in users.txt
$ factoidal webdav-user users.txt danbri1_bot1
webdav-user: added danbri1_bot1 in users.txt
$ factoidal webdav-user users.txt danbri1_bot2
webdav-user: added danbri1_bot2 in users.txt
```

A `did:key` is public: it is the agent's name, made from its public key. The
`.jwk` file is the private key.

## 2. The ACL

Web Access Control in Turtle: each `acl:Authorization` names an agent, the
resource (`acl:accessTo`), what it inherits to (`acl:default`) and the modes.
`acl:Control` is the right to change the ACL itself.

```turtle
@prefix acl: <http://www.w3.org/ns/auth/acl#> .

# danbri1 owns the pod: Read, Write and Control, here and below.
<http://127.0.0.1:8083/.acl#owner> a acl:Authorization ;
  acl:agent <did:key:zDnaeTjuckgTLgCKg4P9AyDkBPgA2dbNtBiW95miKjbTsnP6a> ;
  acl:accessTo <http://127.0.0.1:8083/> ; acl:default <http://127.0.0.1:8083/> ;
  acl:mode acl:Read, acl:Write, acl:Control .

# danbri1_bot1: Read and Write, no Control (cannot change the ACL).
<http://127.0.0.1:8083/.acl#bot1> a acl:Authorization ;
  acl:agent <did:key:zDnaepCzYnLjWcpFs7MKtRNuK3fj8sR6y42e6Wfst2pfPWML9> ;
  acl:accessTo <http://127.0.0.1:8083/> ; acl:default <http://127.0.0.1:8083/> ;
  acl:mode acl:Read, acl:Write .

# danbri1_bot2: Read only.
<http://127.0.0.1:8083/.acl#bot2> a acl:Authorization ;
  acl:agent <did:key:zDnaeTsj5cTzQ1VbhnFN2wQXj6N5gkYAeP92neWn5xamjAJbb> ;
  acl:accessTo <http://127.0.0.1:8083/> ; acl:default <http://127.0.0.1:8083/> ;
  acl:mode acl:Read .
```

(`lws-serve --owner DID` is the short form for a pod with one owner and no
other agents.)

## 3. The pod

`--authz DIR` also serves the pod's own authorization server on the same port;
`--root-acl` gives a new storage this ACL; `--storage files` keeps one file per
resource body and a journal, so a write costs the same however big the pod is.

```
$ factoidal lws-serve danbri1-pod --port 8083 --authz danbri1-as --storage files --root-acl root.acl
lws-serve: encryption at rest is OFF: the storage in …/danbri1-pod is written to disk in clear text. To seal it, make a key with `factoidal lws-keygen`, …
lws-serve: listening on http://127.0.0.1:8083 for danbri1-pod
lws-serve: authorization server http://127.0.0.1:8083 (keys in danbri1-as)
http://127.0.0.1:8083
$ curl -s -o /dev/null -w '%{http_code}\n' http://127.0.0.1:8083/
401
```

## 4. The rights, over LWS

A bot that holds its key talks LWS to the pod directly. In JavaScript, with
the npm package (`did` is the agent's `did:key`, `jwk` its private key):

```js
import { createLwsClient } from '@factoidal/core/lws/client';
const bot1 = await createLwsClient({ selfIssued: { subject: did, keyId: `${did}#${did.slice(8)}`, jwk } });
await bot1.update('http://127.0.0.1:8083/bot1.txt',
  { body: 'written by bot1', mediaType: 'text/plain', precondition: 'none' });
```

Each line is one LWS request to the pod, as one agent (a refusal is thrown;
its status is shown):

```
danbri1 PUT hello.txt           201
danbri1 GET hello.txt           200
bot1 GET hello.txt              200
bot1 PUT bot1.txt               201
bot2 GET hello.txt              200
bot2 GET bot1.txt               200
bot2 PUT bot2.txt               403
bot2 DELETE hello.txt           403
bot1 PUT /.acl                  403
anonymous GET hello.txt         401
```

| Agent, over LWS | Read | Write, create, delete | Change the ACL |
| --- | --- | --- | --- |
| danbri1 | ✅ | ✅ | ✅ |
| danbri1_bot1 | ✅ | ✅ | ⛔ 403 |
| danbri1_bot2 | ✅ | ⛔ 403 | ⛔ 403 |
| no token | ⛔ 401 | ⛔ 401 | ⛔ 401 |

These are the pod's rights, and LWS is the only way to use the write rights
in 0.21.0. The Lean theorem `lws_data_only_through_authorized_step`
(`formal/lean4/L4Factoidal/LWS/AccessTheorems.lean`) states that only the LWS
request handler reads or changes the storage's data, and only after the
authorization decision; a refused request changes nothing.

## 5. The WebDAV front end

```
$ factoidal webdav-serve dav --port 8093 --users users.txt --guest guest
factoidal webdav-serve: WARNING: read only (emergency mode, issue 1147): every write method (PUT, DELETE, MKCOL, COPY, MOVE, PROPPATCH, LOCK, UNLOCK) answers 403; `writable:` in a mount file is ignored; https://github.com/danbri/factoidal/issues/1147
factoidal webdav-serve: WARNING: a request with no credentials acts as the guest user "guest" (--guest)
webdav-serve: listening on http://127.0.0.1:8093 for dav, login from users.txt, guest guest
webdav-serve: http://127.0.0.1:8093/danbri1/ - danbri1 on the danbri1 pod (lws, read-only, as did:key:zDnaeTjuckgTLgCKg4P9AyDkBPgA2dbNtBiW95miKjbTsnP6a, users: danbri1)
webdav-serve: http://127.0.0.1:8093/danbri1_bot1/ - danbri1_bot1 on the danbri1 pod (lws, read-only, as did:key:zDnaepCzYnLjWcpFs7MKtRNuK3fj8sR6y42e6Wfst2pfPWML9, users: danbri1_bot1)
webdav-serve: http://127.0.0.1:8093/danbri1_bot2/ - danbri1_bot2 on the danbri1 pod (lws, read-only, as did:key:zDnaeTsj5cTzQ1VbhnFN2wQXj6N5gkYAeP92neWn5xamjAJbb, users: danbri1_bot2)
http://127.0.0.1:8093
```

Without TLS, `--users` is accepted only on a loopback address; see
[WebDAV](../webdav/) for `--cert` and `--key`.

## How a request logs in

<figure>
<img src="../assets/pods/login-sequence.svg" alt="Sequence diagram: Finder, logged in as danbri1_bot2, sends GET for hello.txt in the danbri1_bot2 folder; webdav-serve checks the login and that the mount lists that user; it sends the GET to the pod with no token and gets 401 with resource metadata; it sends a JWT signed with the bot2 key to the authorization server and gets an access token; it repeats the GET with the Bearer token; the pod's ACL gives bot2 Read, so it answers 200 and Finder shows the file. A PUT stops at webdav-serve with 403 before any request to the pod." width="860">
<figcaption>Two checks. <code>webdav-serve</code> checks the WebDAV user and the mount's <code>users:</code>; the pod checks the agent's token and its ACL. A write never gets past the first.</figcaption>
</figure>

The first request of an agent finds the authorization server through the
pod's 401 (RFC 9728) and exchanges a self-signed JWT for an access token
(RFC 8693); later requests reuse the token. The JWT is the agent's own
statement "I am `did:key:…`", signed with its private key (the LWS
authentication suite for controlled identifiers, CID 1.0). It is not a
Verifiable Credential: Factoidal verifies and makes VC Data Integrity proofs,
but no LWS login here uses one.

## 6. The rights, over WebDAV

Each user logs in with its own name and reads through its own folder
(`curl -u NAME:PASSWORD`; the passwords are not shown):

```
$ curl -s -u danbri1_bot1:… http://127.0.0.1:8093/danbri1_bot1/hello.txt
hello from danbri1
$ curl -s -u danbri1_bot1:… -X PROPFIND -H 'Depth: 1' http://127.0.0.1:8093/ | grep -o '<D:href>[^<]*'
<D:href>/
<D:href>/danbri1_bot1/
$ curl -s -u danbri1_bot1:… -X PUT --data-binary x http://127.0.0.1:8093/danbri1_bot1/new.txt -w '%{http_code}\n'
this server is read only (emergency mode, https://github.com/danbri/factoidal/issues/1147)
403
$ curl -s -u danbri1_bot2:… http://127.0.0.1:8093/danbri1_bot1/hello.txt -w ' %{http_code}\n'
no mount of this name
 404
$ curl -s -u danbri1_bot1:wrong http://127.0.0.1:8093/danbri1_bot1/hello.txt -o /dev/null -w '%{http_code}\n'
401
$ curl -si -u danbri1_bot1:… -X OPTIONS http://127.0.0.1:8093/danbri1_bot1/ | grep -i -E '^(dav|allow):'
dav: 1
allow: OPTIONS, GET, HEAD, PROPFIND
```

| WebDAV user | Its folder: read | Its folder: write, create, delete | Another agent's folder | The root lists |
| --- | --- | --- | --- | --- |
| danbri1 | ✅ (also `.acl`) | ⛔ 403 read only | ⛔ 404 | `/danbri1/` |
| danbri1_bot1 | ✅ | ⛔ 403 read only | ⛔ 404 | `/danbri1_bot1/` |
| danbri1_bot2 | ✅ | ⛔ 403 read only | ⛔ 404 | `/danbri1_bot2/` |
| a wrong password | ⛔ 401 | ⛔ 401 | ⛔ 401 | (401) |
| Guest (`guest`, listed nowhere) | (none) | (none) | ⛔ 404 | nothing |

**bot1's write right does not reach WebDAV in 0.21.0.** The pod would accept
bot1's PUT (section 4), but `webdav-serve` refuses every write method (PUT,
DELETE, MKCOL, COPY, MOVE, PROPPATCH, LOCK, UNLOCK) with 403 on every mount,
before it sends anything to the pod; the owner's mount is read only too. A
bot that has to write uses LWS with its key. The WebDAV theorems in
`formal/lean4/L4Factoidal/WebDAV/Theorems.lean` state this:
`handle_no_write` (every storage operation a request causes is a read),
`hidden_mount_trace` (a request whose user is not in the target mount's
`users:` causes no storage operation), `load_no_unauthorized_storage`
(every accepted mount is `kind: lws`) and `webdav_within_lws` (every
storage operation goes to an `lws` mount that lists the request's user, and
leaves the server only as an LWS read with that mount's key). So through
WebDAV a user can do nothing that the agent of a mount listed for it could
not do over LWS, and only reads. [WebDAV, LWS and
custodians](../webdav-lws-design/) says what these theorems do and do not
cover.

WebDAV still does not show the pod's rights: `OPTIONS` answers the same read
methods for every folder, and a PROPFIND for `DAV:current-user-privilege-set`
(RFC 3744) answers 404 Not Found for that property. A folder whose agent the
pod refuses to read gets the pod's 403.

## 7. Mounting

`OPTIONS` answers `DAV: 1` with only the read methods, so macOS mounts the
volume read only. In Finder (Go → Connect to Server), choose *Registered
User* and give the WebDAV login of the folder. `mount_webdav -S` (no
prompts) mounts as Guest, so for the transcript below `danbri1_bot2.md` also
listed the guest user (`- users: danbri1_bot2, guest`; see
[What does Guest get?](#what-does-guest-get) below):

```
$ /sbin/mount_webdav -S http://127.0.0.1:8093/danbri1_bot2/ ~/mnt/danbri1_bot2
$ mount | grep 8093
http://127.0.0.1:8093/danbri1_bot2/ on …/danbri1_bot2 (webdav, nodev, noexec, nosuid, read-only, mounted by danbri)
$ ls -la ~/mnt/danbri1_bot2
drwx------  1 danbri  staff  2048 28 Oct 20:35 .
-rwx------  1 danbri  staff    15 28 Oct 20:35 bot1.txt
-rwx------  1 danbri  staff    18 28 Oct 20:35 hello.txt
```

The file modes still say `rwx------` for the Mac user, but the volume is
read only, and every write fails at once with an error:

| Through the bot2 mount | What the program sees | What the pod holds |
| --- | --- | --- |
| `touch new.txt` | `Read-only file system` | no new file |
| `mkdir dir` | `Read-only file system` | no new folder |
| `rm bot1.txt` | `Read-only file system` | the file is still there |
| `echo text > hello.txt` (an existing file) | `read-only file system`, exit 1 | the old content |

With 0.20.0 the last row reported success and lost the change; in 0.21.0
macOS refuses the write before anything is sent. The server answers
`DAV: 1` and only the read methods for every folder, so a mount of the
`danbri1` or `danbri1_bot1` folder is read only in the same way, although the
pod would let those agents write.

## What does Guest get?

When Finder connects it asks for *Guest* or *Registered User*. Guest sends no
credentials. In 0.21.0 Guest gets exactly what `--guest` maps it to, and
nothing else:

* **No `--guest`:** a request with no credentials gets 401, so Guest reaches
  nothing.
* **`--guest guest`, and no mount lists `guest`** (the setup of section 5):
  Guest is the WebDAV user `guest`; the root folder lists nothing, and every
  folder is 404, the answer for a mount that does not exist.
* **A mount lists `guest`** (as `danbri1_bot2.md` did for the mount above):
  Guest reads that mount as its agent, here `danbri1_bot2`, read only, and
  no other mount.

```
$ curl -s -X PROPFIND -H 'Depth: 1' http://127.0.0.1:8093/ | grep -o '<D:href>[^<]*'
<D:href>/
<D:href>/danbri1_bot2/
$ curl -s http://127.0.0.1:8093/danbri1_bot2/hello.txt
hello from danbri1
$ curl -s http://127.0.0.1:8093/danbri1_bot1/hello.txt -w ' %{http_code}\n'
no mount of this name
 404
```

The guest name may not be a user of the users file, and a request with
credentials never falls back to Guest: a wrong password is 401. Listing
`guest` for a mount gives everyone who can reach the port that agent's read
rights; never list it for the owner's mount.

The two routes around the ACL that 0.20.0 had are closed in 0.21.0:

| 0.20.0 | 0.21.0 |
| --- | --- |
| Guest, and any name and password, reached every folder and acted as its agent, with writes: through the owner's folder, Guest could replace the ACL | A request acts as one named user and reaches only the mounts whose `users:` list it, read only |
| A `kind: local` mount over the pod's storage directory opened it with no ACL | Every `kind: local` mount is refused at start; `solid-serve` refuses a directory that holds an LWS storage |

```
$ cat raw/dav/raw.md
# the pod storage, local mount
- kind: local
- path: ../../danbri1-pod
- storage: files
- users: guest
$ factoidal webdav-serve dav --port 0 --guest guest
… raw.md:2: a `kind: local` mount opens its storage with no authorization and is refused (emergency mode, https://github.com/danbri/factoidal/issues/1147); use kind: lws with an agent key (`auth: did-key`, `key-file`) and the storage's own access control
$ factoidal solid-serve pod-copy --port 0 --issuer https://issuer.example
factoidal solid-serve: config: this directory holds a Linked Web Storage storage (written by lws-serve); only lws-serve serves it, through LWS authorization
```

(`pod-copy` is a copy of `danbri1-pod` without `lws.lock`, as the storage is
when `lws-serve` is stopped.)

What remains: anyone who can read or write the pod's folder on disk can read
or change its data, its ACL and the agents' keys; no theorem covers file
system access. Encryption at rest (`factoidal lws-keygen`,
`FACTOIDAL_LWS_KEY`; see [Servers](../servers/#encryption-at-rest)) protects
the data files; keep the folder readable by its owner only.

| Who | Can pass the pod's per-agent levels? |
| --- | --- |
| A client of `lws-serve` | No: a valid token and the ACL, on every request |
| A WebDAV user | No: only reads, as the agent of a mount that lists it |
| Anyone who can read or write the pod's folder | Yes: keys, ACL and data are files |

## Limits and next steps

* **A WebDAV user is not its own LWS agent.** Every user listed for a mount
  acts as the mount's one configured agent; this page gets one agent per
  person by giving each agent a mount that lists one login. Mapping each
  WebDAV user to an agent of its own is the next stage of
  [issue 1147](https://github.com/danbri/factoidal/issues/1147).
* **No writes over WebDAV.** A bot with Write uses LWS with its key
  (`createLwsClient`, or the Lean LWS client). [WebDAV, LWS and
  custodians](../webdav-lws-design/) discusses careful read-write LWS mounts
  for a later release.
* **Rights are not visible to WebDAV clients.** Every folder offers the same
  read methods; `DAV:current-user-privilege-set` is not served.
* **One `webdav-serve` holds every agent's key.** The `users:` lists keep
  each login to its own folder, but the process and its configuration folder
  hold all three keys; run it under an account that only the owner uses.
* **Verifiable Credentials** could let `danbri1` delegate to a bot (a VC that
  says what the bot may do) instead of editing the ACL; LWS has access requests
  and grants for this, which `lws-serve` stores but this page does not use.

## Stop and clean up

```
umount ~/mnt/danbri1_bot2
pkill -f "webdav-serve dav --port 8093"
pkill -f "lws-serve danbri1-pod"
```

Removing `~/tmp/pods` removes the pod, the agents, their keys and the WebDAV
logins.
