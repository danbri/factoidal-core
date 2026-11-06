# LWS HTTPS push receiver container

Live XMPP follow-up: through the user's `flyctl proxy 15223:5223` tunnel,
certificate validation, both accounts' SCRAM login/resource binding and a
GET/response HTTP-over-XMPP roundtrip PASS. Probe `deploy/lws-replica/xmpp-smoke.mjs`
uses the existing Lean client; no stored LWS data changed. This supersedes the
earlier startup-only qualification below.

Live deployment update, 20:01 UTC: danbri-foafpod on Fly Machine
1857794dc7e018 starts LWS and XMPP successfully with 1024 MB. Fly health check
passes and public HTTPS GET /lws/ returns 200 with an empty container. The
512 MB configuration was OOM-killed (confirmed Machine event 19:56:56),
followed by lock refusals during restarts. After scaling, no manual lock
deletion was needed. The template was increased to 1024 MB. Current live status
on 2026-11-01 still reports this Machine started and healthy, using image digest
`sha256:99fe6a97773f031f303bc5eac6c4ce11ea0d49fa0136d1f6c89819a5864e409c`.
XMPP login/resource binding and an HTTP-over-XMPP roundtrip were separately
verified through the private Fly proxy. These checks do not measure load
capacity or verify the live `/dav/` route.

Source: [deployment files](../deploy/lws-replica/README.md).

Follow-up: added optional [private XMPP alpha](../deploy/lws-replica/XMPP.md),
separate worker, runtime-only generated credentials, direct TLS through a Fly
private-network tunnel, connection limits and a sampled queue watchdog. No
public XMPP service port is configured. Tested authentication, resource binding and
message routing against real Lean over certificate-validated TLS; bad passwords
are refused. Five deployment test groups passed locally; their exact live
deployment coverage is limited to the separately recorded XMPP roundtrip and
LWS health check.

2026-10-31: added Dockerfile, narrow build context, Caddy HTTPS/static routing,
Compose and Fly template, public-read WAC configuration with one laptop writer,
public-key-only provisioning and a laptop token tool. Runtime state is outside
the static repository-root export. The Fly alpha was deployed and its health
check passes; the public JWKS was installed as a Fly runtime secret. No private
laptop key was uploaded.

Validation: 3 groups pass (real Lean authorization on installed npm0.27.0,
configuration checks, real Caddy2.10.2 proxy checks). HTTPS and HTTP Caddy
configurations validate. Shell entrypoint parses. Docker daemon unavailable;
image rebuild and full container tests remain outstanding. Each build must resolve
npm's `latest` tag to an exact version and pass it as `FACTOIDAL_VERSION`; this
keeps deployments current while making the package version an explicit build
input and Docker cache key. Exact versions can also be selected for audit or
rollback builds.

This is manual resource publication through LWS, not automatic replication.
Source journal/resume design remains [proposed](designissues/2026-10-31-lws-xmpp-replica.md).
Google/GitHub identity linking is recorded in deployment docs but not implemented
in this container. Owner login must not automatically obtain replica write rights.
