# Factoidal release image

One container image of the published npm package `@factoidal/core`. The
entry point is the `factoidal` command, so the first argument is the command:

    docker run --rm ghcr.io/danbri/factoidal:latest version
    docker run --rm -v "$PWD/store:/data" -p 8080:8080 ghcr.io/danbri/factoidal:latest lws-serve --help

The same image serves `lws-serve`, `solid-serve`, `authz-serve`,
`xmpp-serve`, `query` and every other command. Working directory and volume
are `/data`. The process runs as user `node`.

## Build

The Dockerfile downloads `@factoidal/core@FACTOIDAL_VERSION` with `npm pack`
and stops when its sha512 differs from `FACTOIDAL_INTEGRITY` (the registry's
`dist.integrity`):

    V=0.16.0
    docker build -t factoidal \
      --build-arg FACTOIDAL_VERSION=$V \
      --build-arg FACTOIDAL_INTEGRITY="$(npm view @factoidal/core@$V dist.integrity)" .

To build from an unpacked package directory (for example `npm/factoidal`
after a wasm build) with no registry access:

    docker build --build-context source=../../npm/factoidal -t factoidal .

## Publication

The workflow `image.yml` in https://github.com/danbri/factoidal-builds builds
this directory after each npm publish and pushes `ghcr.io/danbri/factoidal:VERSION`
and `:latest`, after `--version` and `lws-serve --help` exit 0 in the image.

`deploy/lws-target` is a different image: it wraps `lws-serve --authz` for the
Touchstone server contract.
