# Shardborough: QLever and Virtuoso comparison readiness

Date: 2026-10-10. This records actual local readiness, not a parity claim.

## Host and initial state

The host is macOS 15.6.1 (24G90), ARM64, with eight physical/logical CPUs and
16 GiB RAM. Podman 5.8.2 has one existing `applehv` machine,
`podman-machine-default`: four CPUs, 8 GiB RAM, 60 GiB configured disk,
rootful, SSH port 53728. It was stopped. No native `qlever`, `qlever-index`,
`qlever-server`, `virtuoso-t`, or `virtuosod` was found in `PATH`.
`/opt/homebrew/bin/isql` is unixODBC 2.3.14, not the Virtuoso client.
Docker 29.4.1 initially had no daemon at `/var/run/docker.sock`.

Sandboxed machine/image inspection failed with permission errors. Repeating
the read-only checks with permission escalation confirmed a refused Podman
SSH connection, not an available container engine. The first explicitly
authorized `podman machine start podman-machine-default` printed success and
API forwarding after approximately 74 seconds. The next command nevertheless
found the VM stopped, no `vfkit`/`gvproxy` process, and connection refused.
Tool child-process cleanup is a hypothesis, not an established diagnosis.
No VM configuration was changed and no new machine was created.

## Official installation paths and immutable image pins

QLever officially supports native Apple-Silicon macOS installation through
`brew tap qlever-dev/qlever` and `brew install qlever`; its runtime also
explicitly supports Podman. The native package avoids the container/VM
overhead. See [QLever quickstart](https://docs.qlever.dev/quickstart/) and
[runtime settings](https://docs.qlever.dev/qleverfile/).
The observed [official Homebrew formula](https://github.com/qlever-dev/homebrew-qlever/blob/main/Formula/qlever.rb)
specifies version `0.6.0`, revision `1`, archive
`https://packages.qlever.dev/mac/qlever_0.6.0-1_macos_arm64.tar.gz`, SHA-256
`e496c08902a8e4a2262dfcea8106f00feaa6060cabdfcf55e4838639396022f3`.
No Homebrew package was installed for this investigation.

The official Docker Hub API exposed these Linux ARM64 manifests on this date:

| Engine | Observed tag/version | ARM64 manifest SHA-256 | Compressed bytes |
| --- | --- | --- | ---: |
| `docker.io/adfreiburg/qlever` | `commit-e8bc50289d` | `d3df85c24ecccc41cddf69b39e8223f601ee5b9dab3730fd39918e2cf91402dc` | 215,363,894 |
| `docker.io/openlink/virtuoso-opensource-7` | `7.2.17-r25.1-g2850f18-ubuntu` | `f61511271cd3931b356504768a6da5f4ee0644a3acb147a6680794dbcafb3cd4` | 50,824,066 |

QLever's commit resolves to `e8bc50289d7c7f2182192472a4aa7bc0b0f60f25`.
The observed multi-architecture index digests are respectively
`sha256:9a167f4bafec1d1915eea2bd17bae0336977c3f831e3e0bacd5bca18be32961d`
and `sha256:0dbe1ab4fa0cb7bbafc1f6c0c2b0a5d6f22d918dbd17672f2ddb24580aa6756a`.
These are observations, not promises about the moving `latest` tags.
Primary metadata: [QLever image tag](https://hub.docker.com/v2/repositories/adfreiburg/qlever/tags/commit-e8bc50289d),
[QLever source commit](https://github.com/ad-freiburg/qlever/commit/e8bc50289d7c7f2182192472a4aa7bc0b0f60f25),
[Virtuoso image tag](https://hub.docker.com/v2/repositories/openlink/virtuoso-opensource-7/tags/7.2.17-r25.1-g2850f18-ubuntu).
OpenLink documents its own image and Turtle loading in
[the official Docker guide](https://github.com/openlink/virtuoso-opensource/blob/develop/7/README.Docker.md)
and [`ld_dir`](https://docs.openlinksw.com/virtuoso/fn_ld_dir/).

## Comparison contract

- Pin each native binary hash, image manifest, actual `--version` output,
  query text/hash, corpus bytes/hash, graph assignment, engine settings and
  resource limits. Explicitly request `linux/arm64`; do not mix emulated
  x86-64 timings with native ARM64 timings.
- Start with the existing 1,000-subject synthetic Turtle file: 3,000 triples,
  202,000 bytes, SHA-256
  `55e24ac9a5ea02c54a64e55788658eeda0635d91509a7d2a0b8697c90e201db2`.
  Load its unique triples into the same default-graph dataset. Then use the
  same generator/settings for 30,000 and 300,000 triples, retaining hashes.
  The VM's configured resources are sufficient for a bounded small-data
  trial, not evidence that arbitrary larger corpora fit; check actual free
  space and RSS before increasing scale. Run engines sequentially.
- Validate complete SPARQL-JSON binding bags, including RDF term type,
  datatype, language, unbound variables and duplicate multiplicity. A row
  count or ten-row preview is not answer validation. The initial queries are
  predicate COUNT, group-0 object lookup and full shared-subject join.
  Cross-engine LIMIT/OFFSET tests require a deterministic total ORDER BY;
  otherwise different selected rows need not indicate an engine defect.
- Record exact RDF-term equality independently of any explicitly declared
  scalar-value comparison. QLever documents that integer results use
  `xsd:int` rather than `xsd:integer`; this is an exact-term mismatch, even
  when COUNT's integer values agree. Do not silently coerce it. See
  [QLever's documented compliance deviations](https://docs.qlever.dev/compliance/).
- Separate ingestion/indexing/publication/activation from query timing.
  Core's fresh-process CLI includes process startup and artifact admission;
  a warm competitor HTTP request does not. Label both operating modes rather
  than publishing an unqualified speed ratio. Include complete output
  transfer, record all samples and failures/timeouts, use a warm-up and at
  least three measured samples, and disclose that OS caches are not evicted.
- Coordinate an exclusive timing window with native builds/profiling. Bind
  only loopback ports, use isolated scratch databases/container names, and
  never stop or replace pre-existing user services.

## Bounded operational probe

The authorized fallback is one active command session that starts the
existing VM, inspects cached images/free space, and keeps its parent alive
for at most ten minutes while isolated probes run. Do not recreate the VM
or repair configuration speculatively. If the second attempt fails, retain
its exact logs and use these commands after resolving the host issue:

```sh
podman machine start podman-machine-default
podman ps -a
podman images
podman machine ssh podman-machine-default 'uname -m; df -h /; free -m'
podman pull --platform linux/arm64 docker.io/adfreiburg/qlever@sha256:d3df85c24ecccc41cddf69b39e8223f601ee5b9dab3730fd39918e2cf91402dc
podman pull --platform linux/arm64 docker.io/openlink/virtuoso-opensource-7@sha256:f61511271cd3931b356504768a6da5f4ee0644a3acb147a6680794dbcafb3cd4
```

The initial readiness observations above are captured in tool output; no
standalone log was written for the first start attempt. The second attempt
and any actual competitor measurements must be recorded before a comparison
claim is made. A 3,000-triple smoke result would establish a reproducible
comparison path, not industry-scale performance parity.
