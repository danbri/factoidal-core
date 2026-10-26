# Path rule for factoidal-core's formal/ history (Claude-inferred default,
# split plan option B: keep specs, extraction scripts and extracted .ml;
# drop object files, logs, executables, build state and generated stores).
import re
EXCLUDE = [
    r'\.(o|cmx|cmi|cmo|cmt|cmti|cma|cmxa|cmxs|a|so|dylib|byte|exe|log|merkle|ibk3|ibk4|tli1|sri2|oli2|ptd1|sbm[0-9]*)$',
    r'^formal/lean4/COLL/',
    r'^formal/lean4/\.lake/',
    r'(^|/)\.lake/',
    r'^formal/fstar/(COMPILE|EXTRACT|VERIFY)_DONE$',
    r'^formal/fstar/ocaml-output/\.extract-state/',
    r'^formal/fstar/ocaml-output/(?!Makefile$|dune$)[^/.]+$',
    r'^formal/fstar/c-output/deltalog/demo/delta_log_demo$',
]
RX = [re.compile(p) for p in EXCLUDE]
def excluded(path: str) -> bool:
    return any(r.search(path) for r in RX)
