# foafos-xmpp: a public test XMPP server on Fly

**This is the one Foafos box on Fly.** Since 2026-11-06 it also runs the pod that was on `foafos-proto`: one store, `https://foafos-xmpp.fly.dev:8443/`, reached over HTTPS with a bearer token or as `pod@foafos-xmpp.fly.dev/lws` over XMPP. Keep it to test data until the private review findings are closed.

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
- No limit per address and no login throttle (https://github.com/danbri/factoidal-core/pull/337 is a draft). The passwords
  are 192 random bits, which is the defence against guessing.
- The server keeps passwords in clear in machine memory and in a Fly secret. One SCRAM salt serves all accounts.
- Any account can join any room unless the room is on a `--muc-members` list, or it is banned there. Rooms have no history.
- Room owners: with no `--muc-owners`, the first occupant of a room is its owner, and can kick and ban there. With
  `--muc-owners FILE` only the accounts in the file are owners, and bans and grants survive a restart (the state key seals
  them). The file has one line for each room, `room: a@foafos-xmpp.fly.dev`, or `*: a@foafos-xmpp.fly.dev` for every room.
  Keep it on the volume and add the flag to `XMPP_EXTRA_ARGS`. The flag needs an engine with `muc-owners`: an older engine
  stops at the flag.
- There is no independent review of this server.
