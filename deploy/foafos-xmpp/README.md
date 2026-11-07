# foafos-xmpp: a public test XMPP server on Fly

**This is the one Foafos box on Fly.** Since 2026-11-06 it also runs the pod that was on `foafos-proto`: one store, `https://foafos-xmpp.fly.dev:8443/`, reached over HTTPS with a bearer token or as `pod@foafos-xmpp.fly.dev/lws` over XMPP. Keep it to test data until the private review findings are closed.

The pod's bearer token is the Fly secret `POD_TOKEN`, with a local copy in `~/.config/foafos-xmpp-fly/token`. It is not a Fly login, and `fly-secrets.env` does not hold it. Accounts are in `accounts` in the same folder.

A public service that nobody announces, for test data only. Owner, 2026-11-05: "public service we do not announce,
containing only test data on ephemeral machines we don't use for anything else". The Foafos side:
https://github.com/danbri/glitchcan-minigam/blob/master/docs/foafos-shared-xmpp-20261105.md

| Port | What |
|---|---|
| 5222 | XMPP, STARTTLS required |
| 5223 | XMPP, direct TLS (XEP-0368) |
| 443 | `wss://foafos-xmpp.fly.dev/xmpp-websocket`, Origin `https://danbri.github.io` or `http://localhost:8080` only |
| 80 | The ACME HTTP-01 challenge, and one line of text |

## How it works

All Fly services are raw TCP, so TLS ends on the machine, not in the Fly proxy. A raw service needs a dedicated IP. Caddy
gets and renews the Let's Encrypt certificate and serves nothing else. One `xmpp-serve` process reads the certificate and
does all XMPP TLS. There is no plaintext login path: without TLS the server offers no SASL mechanism. `entrypoint.sh`
restarts `xmpp-serve` when the certificate changes, and that ends the rooms for a moment.

The volume keeps the certificate (Let's Encrypt allows 5 certificates a week for one name) and the sealed server state.
Nothing on it needs a backup.

## Rebuild from nothing

```sh
fly apps create foafos-xmpp --org contextris
fly ips allocate-v4 -a foafos-xmpp --yes        # dedicated, $2 a month
fly ips allocate-v6 -a foafos-xmpp
fly volumes create foafos_xmpp_data -a foafos-xmpp -r lhr -s 1 --yes
node provision.mjs ~/.config/foafos-xmpp-fly    # refuses to reuse a directory
fly secrets import --stage -a foafos-xmpp < ~/.config/foafos-xmpp-fly/fly-secrets.env
fly deploy --remote-only --ha=false -a foafos-xmpp
```

`provision.mjs` prints no secret. Keep its directory out of git. Add or change an account in both files of that directory,
then `fly secrets import`. No account can register itself.

## Test

```sh
mkdir /tmp/smoke && cp smoke.mjs /tmp/smoke && cd /tmp/smoke
npm init -y && npm install @xmpp/client ws
node smoke.mjs ~/.config/foafos-xmpp-fly/accounts --idle 240
```

## Limits and known faults

- `xmpp-serve` closes a new connection above 200 open connections, a connection with no bound resource after 30 seconds,
  and a client with more than 8 MiB queued. Fly also stops at 256 connections for each port.
- Since 0.33.0 failed logins have a limit per account name and one per client address. Behind Fly's proxy every client has
  the proxy's address, so until the step below this box runs with `--no-address-limit` in `XMPP_EXTRA_ARGS`: the limit
  then counts per account name only. The passwords are 192 random bits, which is the main defence against guessing.

## Next deploy: the PROXY protocol, and the limit per client address on again

Needs a `@factoidal/core` release with `xmpp-serve --proxy-protocol` (in `CHANGELOG.md` under "Unreleased" on
2026-11-07; not in 0.33.0). `fly deploy` reads `fly.toml` from this directory, not from `main`, so `fly.toml` here is not
changed yet: with 0.33.0 the flag would stop the start. With that release, in one deploy:

1. `[build.args] FACTOIDAL_VERSION` = the release with `--proxy-protocol`.
2. `[env] XMPP_EXTRA_ARGS = "--proxy-protocol"` (in place of `--no-address-limit`).
3. On each of the three XMPP services (internal ports 5223, 5222 and 5281; not 8080 and not 8090), in its
   `[[services.ports]]`:

   ```toml
   [[services.ports]]
     port = 5223
     handlers = ["proxy_proto"]
     proxy_proto_options = { version = "v2" }
   ```

   All three or none: with `--proxy-protocol` the server closes every connection that does not start with a header, on
   every listener.
4. After the deploy: `node smoke.mjs ~/.config/foafos-xmpp-fly/accounts` (all three ports), and the log shows
   `connection from address <12 hex digits>`, never an address.

Risks to check at that deploy:

- The `tcp_checks` on 5223. Fly's documentation does not say whether a TCP check goes through the proxy or sends a header.
  A TCP check only connects, so it passes either way; the server closes it after 10 seconds without a header, and logs
  `closing a connection that sent no PROXY header in time`.
- The server must be reachable only through Fly's proxy: a client that reaches the machine directly can send a header with
  any address. `entrypoint.sh` binds `--host 0.0.0.0` (IPv4); Fly's private network (6PN) is IPv6. Do not change it to
  `::` while `--proxy-protocol` is on.
- IPv6 clients are counted by /64. A client with a larger allocation (a /56 or /48) can move between /64s; the limit per
  account name still applies.
- Rollback: `XMPP_EXTRA_ARGS = "--no-address-limit"` and remove the two lines from the three services, in one deploy.
- The server keeps passwords in clear in machine memory and in a Fly secret. Each account has its own SCRAM salt.
- Any account can join any room unless the room is on a `--muc-members` list, or it is banned there. Rooms have no history.
- Room owners: with no `--muc-owners`, the first occupant of a room is its owner, and can kick and ban there. With
  `--muc-owners FILE` only the accounts in the file are owners, and bans and grants survive a restart (the state key seals
  them). The file has one line for each room, `room: a@foafos-xmpp.fly.dev`, or `*: a@foafos-xmpp.fly.dev` for every room.
  Keep it on the volume and add the flag to `XMPP_EXTRA_ARGS`. The flag needs an engine with `muc-owners`: an older engine
  stops at the flag.
- There is no independent review of this server.
