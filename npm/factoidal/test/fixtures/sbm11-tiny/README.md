# sbm11-tiny

An SBM11 collection root (`root/`, with `CURRENT` naming `gen`) packed from
`input.nq` by the native packer, and the answers of native `l4sbm11 query` to
the queries of `queries.json` (`expected/NAME.out`, without the final line
break that the command writes; `expected/paths.json`: the path that ran).

Used by `../../sbm11-host.test.mjs`
(https://github.com/danbri/factoidal/issues/1009 KR1): the wasm ops
`sbm11Open` / `sbm11Query` must give the same bytes and the same path.

Made with (from the repository root, after `lake build` in `formal/lean4`):

    B=formal/lean4/.lake/build/bin
    $B/l4sbm11-pack input.nq root/gen --workers 1
    $B/l4sbm11 activate root gen
    $B/l4sbm11 query root 'QUERY'      # per entry of queries.json

A change of the SBM11 wire format changes these files; pack them again with
the same commands.
