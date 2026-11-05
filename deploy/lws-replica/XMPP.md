# Private XMPP alpha on the replica Machine

Live validation, 2026-10-31: both provisioned accounts authenticated using
Lean's SCRAM client over certificate-validated TLS through `flyctl proxy` to
danbri-foafpod. An authenticated HTTP-over-XMPP GET and matching response passed;
no LWS resources changed. Repeat from this directory while the tunnel runs:

```sh
node xmpp-smoke.mjs "$HOME/.config/factoidal-xmpp-alpha" danbri-foafpod.fly.dev
```

Opt-in, no public XMPP ports and no registration. Two test accounts share the
Fly app hostname as their JID domain. This tests the real Factoidal Lean XMPP
server through its npm socket host; it does not install ejabberd or Prosody.
No XMPP/LWS replication coupling is implemented by enabling this service.

From the deployment directory, after choosing POD_APP:

```sh
node provision-xmpp.mjs "$HOME/.config/factoidal-xmpp-alpha" "$POD_APP.fly.dev"
flyctl secrets import --stage -a "$POD_APP" < "$HOME/.config/factoidal-xmpp-alpha/fly-secrets.env"
flyctl deploy --remote-only --ha=false -a "$POD_APP"
flyctl proxy 15223:5223 -a "$POD_APP"
```

The provisioner refuses to overwrite its directory. It generates random
passwords and a separate self-signed TLS key/certificate, valid for 30 days.
Unlike the LWS writer private key, the XMPP TLS private key DOES belong on the
server: it is uploaded as a runtime Fly secret, never baked into the image.
Keep the generated directory outside git and the Docker context. No credential
is printed or passed to flyctl as a command-line argument. The import file uses single-line base64 values; base64 is encoding, not encryption.

Clients use:

* JID `laptop@APP.fly.dev` or `replica@APP.fly.dev` (substitute the app name).
* Password from the local private `accounts.json`.
* Transport host `127.0.0.1`, port `15223`, **direct TLS**, not STARTTLS.
* TLS server name `APP.fly.dev`; explicitly trust the generated `tls.crt`.
  Keep certificate and hostname checks enabled. Clients must allow transport
  host override independently of the JID/TLS name. A second laptop needs Fly
  access to create its own tunnel and its own copy of the public certificate.

Test the TLS endpoint while the proxy is running:

```sh
openssl s_client -connect 127.0.0.1:15223 -servername "$POD_APP.fly.dev" \
  -CAfile "$HOME/.config/factoidal-xmpp-alpha/tls.crt" -verify_return_error
```

Do NOT add an XMPP `[[services]]` entry to fly.toml for this test. The IPv6
listener is reachable through Fly's private network and `flyctl proxy`, not
public Fly Proxy ports. Other authorized peers in that private network may
reach it, but still need TLS and account authentication. HTTPS/LWS are unchanged.

## Limits and what is not guaranteed

Four simultaneous sockets, 64 KiB unfinished input per session, a two-minute
socket inactivity timeout and five-minute connection lifetime bound the alpha
sessions. A 250ms watchdog stops XMPP when its pending queue exceeds 128 stanzas
or 256 KiB. This sampled check is NOT a hard memory bound or a Lean theorem;
a burst may exceed the threshold before the check. This is for trusted alpha
accounts, not hostile load testing. No public registration or federation.

XMPP is a separate process/engine instance. If it exits, the supervisor reports
that and keeps LWS/Caddy running; it does not repeatedly restart a failing alpha.
Both processes still share Machine RAM, so OOM can affect the whole Machine.
Measure memory after startup; increase to 1 GB if needed rather than claiming
512 MB is sufficient. Rosters persist under `/data/xmpp`; pending routed messages
remain volatile and are lost on restart. Spool polling is disabled here.

Rotate the 30-day test certificate and account passwords deliberately, updating
the Fly secrets and client trust. Disable with `flyctl secrets set -a "$POD_APP"
XMPP_ENABLED=false` (on one command line), then verify the private port closes.

Local tests exercise real TLS with certificate validation and actual Lean
authentication/binding, including wrong-password refusal. They use the locally
installed core0.27.0. The subsequent user deployment of pinned0.28.0 and the
live tunnel smoke above also passed. The user provisioned the Fly secrets;
the smoke reads local credentials without printing them.

References: [Fly proxy](https://fly.io/docs/flyctl/proxy/),
[existing XMPP implementation](../../formal/lean4/L4Factoidal/XMPP/README.md).
