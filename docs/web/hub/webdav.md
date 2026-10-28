---
title: WebDAV
description: Serve local and remote Linked Web Storage to file browsers over WebDAV with the factoidal CLI — mount files, did:key login to an LWS server, HTTPS through a reverse proxy, Tailscale and SSH tunnels from behind NAT, and the steps to connect from macOS, Windows, Linux and other WebDAV apps.
layout: hub.njk
tests: tests/hub/hub_webdav_test.mjs
---

# WebDAV

<p class="warning"><strong>⚠️ EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the whole core
library and every command line tool, and in particular all protocol,
authentication and security code.</p>

[Hub](../) · [Servers](../servers/) · quick start, mount files, a remote LWS storage, login, HTTPS, Tailscale, SSH, XMPP, file browsers

`factoidal webdav-serve` serves WebDAV (RFC 4918, classes 1 and 2), so that
macOS Finder, Windows File Explorer, GNOME Files, KDE Dolphin and other
WebDAV clients can show and change the contents of Linked Web Storage (LWS)
storages. A storage can be a directory on the same machine or an LWS server
anywhere on the network. Every WebDAV decision (methods, statuses,
properties, locks, the mapping to LWS) is made by the Lean 4 code in
`formal/lean4/L4Factoidal/WebDAV/`; the Node host only moves bytes. Design
record: `docs/designissues/2026-10-27-webdav.md`
(<https://github.com/danbri/factoidal/issues/1066>).

A server cannot run in a browser page, so this page has no live cells. The
commands below were run on 2026-10-27 with `@factoidal/core` from this
repository (`node npm/factoidal/bin/factoidal.mjs`, shown as `factoidal`);
`tests/hub/hub_webdav_test.mjs` runs them again on every test run.
`webdav-serve` is in `@factoidal/core` 0.18.0 and later.

## Quick start

```
npm install -g @factoidal/core      # or: npx -y @factoidal/core webdav-serve ...
mkdir -p dav/notes
printf '# My notes\n- kind: local\n- path: ./notes\n' > dav/notes.md
factoidal webdav-serve dav
```

```
factoidal webdav-serve: WARNING: EXPERIMENTAL UNREVIEWED CODE - ...
webdav-serve: listening on http://127.0.0.1:8090 for dav
webdav-serve: http://127.0.0.1:8090/notes/ - My notes (local)
http://127.0.0.1:8090
```

Open `http://127.0.0.1:8090/` in a file browser ([steps below](#connect-a-file-browser)).
The root folder holds one folder per mount. With curl:

```
$ curl -si -X OPTIONS http://127.0.0.1:8090/ | grep -i -E '^(dav|ms-author-via|allow):'
dav: 1, 2
ms-author-via: DAV
allow: OPTIONS, GET, HEAD, PUT, DELETE, MKCOL, COPY, MOVE, PROPFIND, PROPPATCH, LOCK, UNLOCK
$ curl -s -X PUT -H 'content-type: text/plain' --data-binary hello http://127.0.0.1:8090/notes/hello.txt -w '%{http_code}\n'
201
$ curl -s -X MKCOL http://127.0.0.1:8090/notes/docs/ -w '%{http_code}\n'
201
$ curl -s -X PROPFIND -H 'Depth: 1' http://127.0.0.1:8090/notes/ | grep -o '<D:href>[^<]*'
<D:href>/notes/
<D:href>/notes/docs/
<D:href>/notes/hello.txt
```

A `local` mount directory is an LWS storage in the format `lws-serve` uses.
It is not a copy of the folder tree: an empty directory becomes a storage
held in one file (`lws-state.json`); with `- storage: files` the content is
kept in `bodies/` and a journal. Do not put other files in it, and do not
serve one directory with `lws-serve` and `webdav-serve` at the same time.

Options: `--port N` (default 8090; 0 takes a free port) and `--host ADDRESS`
(default 127.0.0.1).

## Mount files

A mount is one Markdown file `CONFIGDIR/NAME.md`; `NAME` is the folder name.
The first `# ` heading is the display name. The first `- key: value` list is
the settings; other text in the file is ignored. `README.md` is not a mount.
A malformed file stops the start with its name and line number.

| Key | Values | Applies to | Default |
| --- | --- | --- | --- |
| `kind` | `local`, `lws` | all | required |
| `path` | a directory, relative to CONFIGDIR | local | required |
| `storage` | `snapshot`, `files` | local | what the directory holds |
| `base` | the storage root's IRI, ending in `/` | local | `http://localhost/` |
| `url` | the storage root URL of an LWS server | lws | required |
| `auth` | `none`, `did-key`, `bearer` | lws | `none` |
| `key-file` | a P-256 private JWK, relative to CONFIGDIR | lws, `did-key` | required with `did-key` |
| `token-file` | a file that holds an access token | lws, `bearer` | required with `bearer` |
| `writable` | `true`, `false` | all | `true` for local, `false` for lws |

## A remote LWS storage

An `lws` mount reaches an LWS server through the Lean LWS client. With
`auth: did-key` the mount signs in as a `did:key`: the client reads the
server's 401, finds the authorization server in the protected resource
metadata (RFC 9728), and exchanges a self-signed credential for an access
token (RFC 8693). Here the LWS server is `factoidal lws-serve --authz`, which
serves the storage and its authorization server on one port.

1. Write the mount file and start `webdav-serve` once. When the key file
   does not exist, it makes a new P-256 key, writes it with mode 0600, and
   prints the key's `did:key`:

   ```
   $ cat dav/alice.md
   # Alice on the LWS server
   - kind: lws
   - url: http://127.0.0.1:8080/
   - auth: did-key
   - key-file: alice.jwk
   - writable: true
   $ factoidal webdav-serve dav
   webdav-serve: listening on http://127.0.0.1:8090 for dav
   webdav-serve: http://127.0.0.1:8090/alice/ - Alice on the LWS server (lws, as did:key:zDnaeTTXneUgXnqySJ9oDvS7LLpHW3uL5Qt7EpQFHvB6H298K)
   http://127.0.0.1:8090
   ```

2. Start the LWS server with that agent as the owner of the new storage:

   ```
   $ factoidal lws-serve alice-storage --port 8080 --authz alice-as \
       --owner did:key:zDnaeTTXneUgXnqySJ9oDvS7LLpHW3uL5Qt7EpQFHvB6H298K
   lws-serve: listening on http://127.0.0.1:8080 for alice-storage
   lws-serve: authorization server http://127.0.0.1:8080 (keys in alice-as)
   http://127.0.0.1:8080
   ```

3. Anonymous requests to the LWS server get 401; requests through the WebDAV
   mount carry Alice's token:

   ```
   $ curl -s -o /dev/null -w '%{http_code}\n' http://127.0.0.1:8080/
   401
   $ curl -s -X PUT -H 'content-type: text/plain' --data-binary 'from Finder' \
       http://127.0.0.1:8090/alice/note.txt -w '%{http_code}\n'
   201
   $ curl -s http://127.0.0.1:8090/alice/note.txt
   from Finder
   ```

A second mount file can name the same storage and key without
`writable: true`; that folder is read only and answers 403 to every write.
Two mounts may name one key file that does not exist yet; they get one key.

## Advanced: login

The WebDAV listener itself has no login and no TLS: anyone who can open a
connection to its port can read and change every writable mount
(<https://github.com/danbri/factoidal/issues/1108>, an expected failure in
`tests/hub/hub_webdav_test.mjs`). For this reason it binds 127.0.0.1 by
default. Logins exist at two other points:

* **Between the WebDAV server and an LWS server** (the mount file):
  `auth: did-key` (above) or `auth: bearer` with `token-file`, a token got
  in some other way, sent as `Authorization: Bearer` to every URL under
  `url`. The LWS server decides what the agent may do: with `lws-serve
  --authz`, the `--owner` has full control of a new storage, and other
  agents get access through access grants (`factoidal lws-client
  grantAccess`). The key file is a private key: keep it out of shared
  folders and backups that others can read.
* **Between the file browser and the WebDAV server**: give this to the
  layer in front of the listener. Choose one:
  * keep the default bind and use the machine's own users (only local
    processes reach 127.0.0.1);
  * an SSH tunnel: the SSH login and key are the login ([below](#ssh-tunnels));
  * Tailscale: the tailnet identity and its access rules are the login
    ([below](#tailscale));
  * a reverse proxy with HTTP Basic authentication over HTTPS
    ([below](#advanced-https)).

## Advanced: HTTPS

`webdav-serve` speaks plain HTTP. For HTTPS, put a TLS reverse proxy in
front of it, or use Tailscale (next section), which gets the certificate
for you.

Caddy gets a certificate from Let's Encrypt for a public name and adds HTTP
Basic authentication. `caddy hash-password` prints the hash:

```
# Caddyfile
dav.example.org {
	basic_auth {
		alice $2a$14$REPLACE_WITH_OUTPUT_OF_caddy_hash-password
	}
	reverse_proxy 127.0.0.1:8090
}
```

Rules for any proxy:

* Pass the `Host` header unchanged (Caddy does this by default; nginx needs
  `proxy_set_header Host $host;`). COPY and MOVE compare the host in the
  `Destination` header with the `Host` of the request; when they differ the
  server answers 502, because RFC 4918 §9.9.4 treats the destination as
  another server. The scheme in `Destination` is not compared, so
  `https://` at the proxy and `http://` behind it is correct.
* Do not buffer request bodies to a size limit lower than your largest file.
* Keep `webdav-serve` on 127.0.0.1 so that the proxy is the only way in.

For `lws-serve` behind a proxy, give the public URL with `--base`
(for example `--base https://dav.example.org/lws/`), so that the storage
and its authorization server name themselves with the URL clients use. The
`deploy/lws-target/` README shows this behind a proxy that removes a path
prefix: <https://github.com/danbri/factoidal-core/tree/main/deploy/lws-target>.

## Reaching a server behind NAT

### Tailscale

Tailscale (WireGuard) gives each machine a private address and a name on
your tailnet; no port is opened on the router. On the machine that runs the
server (Tailscale 1.52 or later):

```
factoidal webdav-serve dav                 # stays on 127.0.0.1:8090
tailscale serve --bg 8090                  # https://MACHINE.TAILNET.ts.net/ -> 127.0.0.1:8090
tailscale serve status
```

`tailscale serve` terminates TLS with a certificate for
`MACHINE.TAILNET.ts.net` (turn on MagicDNS and HTTPS certificates in the
admin console first). Only tailnet members that your access rules admit can
connect. Connect file browsers to `https://MACHINE.TAILNET.ts.net/`. Stop
with `tailscale serve --https=443 off`.

To expose an LWS server the same way, start it with the public URL:
`factoidal lws-serve DIR --base https://MACHINE.TAILNET.ts.net/ --authz ASDIR
--owner DID`, then `tailscale serve --bg 8080`. A WebDAV mount on another
tailnet machine then uses `- url: https://MACHINE.TAILNET.ts.net/`.

Do not use `tailscale funnel` for `webdav-serve`: Funnel makes the port
public on the Internet, and the listener has no login.

### SSH tunnels

From a laptop that can SSH to the server machine (local forward):

```
ssh -N -L 8090:127.0.0.1:8090 user@server-machine
# then connect the file browser to http://127.0.0.1:8090/
```

When the server machine is behind NAT and you have a host with a public
address (for example a small VPS), the server machine opens the tunnel out
(remote forward), and the laptop forwards to the VPS:

```
# on the server machine, behind NAT
ssh -N -R 8090:127.0.0.1:8090 user@vps.example.org
# on the laptop
ssh -N -L 8090:127.0.0.1:8090 user@vps.example.org
```

With the default `GatewayPorts no` on the VPS, the forwarded port binds
127.0.0.1 there, so only SSH users of the VPS reach it. Use `autossh -M 0`
with `-o ServerAliveInterval=30` to keep the tunnel open. The traffic is
encrypted by SSH; the file browser still uses `http://127.0.0.1:8090/`, and
macOS and Windows accept that address without TLS.

### XMPP

Not possible today. `factoidal xmpp-serve` serves XMPP (RFC 6120/6121) over
TCP or direct TLS (see [Servers](../servers/#xmpp)), but no part of
Factoidal carries HTTP over XMPP (XEP-0332), and no file browser speaks it.
Tracking: <https://github.com/danbri/factoidal/issues/1107>, an expected
failure in `tests/hub/hub_webdav_test.mjs`.

## Connect a file browser

Below, `URL` is `http://127.0.0.1:8090/`, `https://MACHINE.TAILNET.ts.net/`
or `https://dav.example.org/`. Only litmus and curl ran against
`webdav-serve` in this repository; the steps below are the clients' own
documented steps, not test results
(<https://github.com/danbri/factoidal/issues/1079>).

* **macOS Finder**: Go > Connect to Server (⌘K), type `URL`, Connect. With
  no login in front, choose Guest; behind a Basic login, Registered User.
  The volume appears under Locations.
* **Windows File Explorer**: This PC > Map network drive, Folder `URL`, or
  in a terminal `net use Z: http://127.0.0.1:8090/`. The WebClient service
  must run (`sc start WebClient`). By default WebClient sends a Basic
  password only over HTTPS (registry value `BasicAuthLevel` 2), and limits a
  file to 50 MB (`FileSizeLimitInBytes`), both under
  `HKLM\SYSTEM\CurrentControlSet\Services\WebClient\Parameters`.
* **GNOME Files**: Other Locations > Connect to Server, `dav://127.0.0.1:8090/`
  or `davs://HOST/` for HTTPS.
* **KDE Dolphin**: type `webdav://127.0.0.1:8090/` or `webdavs://HOST/` in
  the location bar.
* **Linux mount**: davfs2, `sudo mount -t davfs URL /mnt/dav`.
* **iPhone and iPad**: the Files app connects to SMB servers only. Use a
  WebDAV app such as Documents by Readdle or FE File Explorer.
* **Android**: a file manager with WebDAV, such as Solid Explorer or
  X-plore.

Other WebDAV clients:

* Cyberduck (macOS, Windows; free) and Mountain Duck (mounts as a drive):
  new connection, type WebDAV (HTTP) or WebDAV (HTTPS).
* WinSCP (Windows): File protocol WebDAV.
* Transmit (macOS): protocol WebDAV.
* rclone (all systems, command line): `rclone config` (type `webdav`, vendor
  `other`), then `rclone ls`, `rclone sync` or `rclone mount NAME: DIR`.
* cadaver (command line): `cadaver http://127.0.0.1:8090/`.
* Applications that sync to a WebDAV folder: Joplin (WebDAV sync target),
  Zotero (WebDAV file sync), Obsidian (Remotely Save plugin),
  Keepass2Android.

## Limits

* No login and no TLS on the listener:
  <https://github.com/danbri/factoidal/issues/1108>.
* Dead properties and locks are kept in memory and lost on restart:
  <https://github.com/danbri/factoidal/issues/1078>.
* One request at a time. PROPFIND with `Depth: infinity` answers 403
  (`DAV:propfind-finite-depth`); clients then list one level at a time.
* COPY and MOVE between two mounts answer 502 (RFC 4918 §9.9.4); copy with
  the file browser instead (it reads and writes).
* LWS keeps no creation time, so `DAV:creationdate` is not given.

Measured on 2026-10-27 (design record): litmus 0.13, 208 pass, 0 fail (out
of 208), on a local mount and on a remote mount.
