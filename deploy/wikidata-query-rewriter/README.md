# Wikimedia query rewriter: differential oracle

Packages the upstream Java/Jena rewriter, pinned to Wikimedia GitLab commit
`e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74`, in a source-built Docker image.
It is a reference oracle for the Lean port, not a JS/WASM implementation.

```sh
docker build -t wikidata-query-rewriter .
docker run --rm -p 8080:8080 wikidata-query-rewriter
curl -sS localhost:8080/rewrite -H 'Content-Type: application/json' \
  -d '{"query":"SELECT * WHERE { ?s ?p ?o } LIMIT 1"}'
```

`POST /rewrite` accepts `{"query":"..."}` and returns the upstream JSONL
protocol envelope, including the result status, query, rewrites, warnings and
errors. HTTP 200 is not proof of equivalence or even of a rewrite. Some upstream
rules deliberately change results. `/healthz` checks only the HTTP process.
The adapter does not execute queries or fetch IRIs. It bounds body size to 1 MB,
JVM concurrency to two and each process to 75 seconds. It does not log requests.

To deploy, copy `fly.toml.example` to `fly.toml`, select an app name and run
`fly launch --no-deploy` then `fly deploy --remote-only` in this directory.
This makes a separate app; do not overwrite another Fly workload. Provisioning
may incur charges. The adapter has no authentication or rate limiting and its
thread-per-connection server is not hardened for hostile public traffic. Protect
access before using real/private queries or exposing it publicly.

Docker build and Fly deployment have not been tested here. The adapter was
smoke-tested locally against the upstream repository's checked-in JAR; that JAR
may differ from the pinned source. A local unchanged query and a hint-removal
query returned upstream statuses `unchanged` and `rewritten` respectively.
Upstream: https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter
