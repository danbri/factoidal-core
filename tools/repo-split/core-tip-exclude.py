# Path rule for the non-formal part of factoidal-core's first snapshot
# commit (Claude-inferred default, 2026-10-09). Build products and
# deployment move to danbri/factoidal-builds; tools/fetch-builds.sh
# installs the build products back at these same paths, which core's
# .gitignore lists.
import re
import os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else '.', 'core-formal-exclude.py')).read())
_formal_excluded = excluded
TIP_EXCLUDE = [
    # Native binaries per platform and the old CI shadow dirs; compiled
    # objects next to the bin/<consumer>/ sources. The consumer SOURCES
    # (bin/<consumer>/*.ml, READMEs, scripts) are source and stay
    # (iron rule 11: consumer tools live in bin/<consumer>/).
    r'^bin/(linux-x86_64|darwin-arm64|ci-[^/]+)/',
    r'^bin/.*\.(cmi|cmx|cmo|cmt|o|byte)$',
    r'^bin/[^/]+/[^/.]+$',
    # Generated dashboard and measurements; the two measured baselines
    # that bench tools read as inputs stay.
    r'^docs/test-results/(?!closure-bench-baseline\.json$|perf-quadstore-baseline\.(json|fragment\.html)$|ukparliament-bench(-modern)?\.(json|csv)$)',
    # Pages mirrors of the packages.
    r'^docs/npm/',
    # F* JS and wasm bundles (hand-written pages, clients and samples in
    # docs/fstar-extracted/ stay).
    r'^docs/fstar-extracted/(w3c-runner|factoidal|factoidal-npm-entry|factoidal-npm-entry-lite)(\.wasm)?\.js$',
    r'^docs/fstar-extracted/[^/]*\.wasm\.assets/',
    r'^docs/fstar-extracted/factoidal\.debug\.(js|map)$',
    r'^docs/fstar-extracted/[^/]*_results\.log$',
    # Lean wasm module and its Emscripten glue (the loader l4factoidal.js
    # is source; the build stamps its WASM_VERSION line).
    r'^docs/web/hub/assets/l4/l4factoidal\.(wasm|mjs)$',
    # Engine bundles inside the npm packages.
    r'^npm/factoidal/factoidal(-npm-entry(-lite)?)?(\.wasm)?\.js$',
    r'^npm/factoidal/factoidal(-npm-entry(-lite)?)?\.wasm\.assets/',
    r'^npm/factoidal/l4-assets/l4factoidal\\.(js|mjs|wasm)$',
    r'^npm/factoidal-lean/l4factoidal\.(js|mjs|wasm)$',
    # Deployment (moves to danbri/factoidal-builds) and stray logs.
    r'^(Dockerfile|\.dockerignore|fly\.toml|serve-lifesci-demo\.sh)$',
    r'^deploy/',
    r'^experiments/',
    r'^\.claude-runs-[^/]*\.log$',
    r'^(fix-quad-build|merged-build)\.log$',
    r'^(qsforph\.fxt|tinc_time\.txt)$',
]
_TRX = [re.compile(p) for p in TIP_EXCLUDE]
def tip_excluded(path):
    if path.startswith('formal/'):
        return _formal_excluded(path)
    return any(r.search(path) for r in _TRX)
