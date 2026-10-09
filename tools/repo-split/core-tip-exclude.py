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
    r'^bin/',
    r'^docs/test-results/',
    r'^docs/npm/',
    r'^docs/fstar-extracted/',
    r'^docs/web/hub/assets/l4/.*\.wasm$',
    r'^npm/factoidal/factoidal(-npm-entry(-lite)?)?(\.wasm)?\.js$',
    r'^npm/factoidal/factoidal(-npm-entry(-lite)?)?\.wasm\.assets/',
    r'^npm/factoidal/l4-assets/',
    r'^npm/factoidal-lean/l4factoidal\.(js|mjs|wasm)$',
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
