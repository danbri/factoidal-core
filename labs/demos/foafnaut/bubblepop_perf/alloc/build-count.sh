#!/bin/bash
# build-count.sh BUILD_DIR OUT_DIR [JOBS]
# Make a counting build of `leanjs` from the C that Lean already generated, with no Lean build:
# every .c file that the linked `leanjs` names (BUILD_DIR/bin/leanjs.rsp, written by `lake build leanjs`)
# is compiled again with leanprof.h force-included, and linked with leanprof.c into OUT_DIR/leanjs-count.
#   BUILD_DIR  formal/lean4/.lake/build of a checkout where `lake build leanjs` has run (its ir/ must hold the .c files)
#   OUT_DIR    objects and the binary (about 160 MB)
# Run a script with LEANPROF_OUT=FILE.tsv to get the counts; read them with leancount.py and opcount.py.
# The optimisation level (-O1, LEANPROF_OPT to change) does not change the counts: they are taken in the C source.
# About 9 minutes on an M1 at 3 jobs; the evaluator's file takes most of it.
set -euo pipefail
B=$(cd "$1" && pwd); O=$2; J=${3:-3}; HERE=$(cd "$(dirname "$0")" && pwd)
L=$(lean --print-prefix)
mkdir -p "$O/o"; O=$(cd "$O" && pwd)
names='lean_ctor_set_float|lean_alloc_ctor|lean_alloc_closure|lean_box_float|lean_box_uint64|lean_inc|lean_inc_ref|lean_inc_n|lean_inc_ref_n|lean_dec|lean_dec_ref|lean_alloc_array|lean_mk_empty_array_with_capacity|lean_mk_array|lean_array_uset|lean_array_fset|lean_array_set|lean_array_pop|lean_array_fswap|lean_array_swap|lean_array_push|lean_copy_expand_array|lean_float_array_uset|lean_float_array_fset|lean_float_array_set|lean_float_array_push|lean_string_append|lean_string_push|lean_string_utf8_extract|lean_mk_string_unchecked'
cat > "$O/one.sh" <<ONE
#!/bin/bash
# one module: the generated file re-declares the runtime functions it calls; the wrapped names are macros here,
# so those prototype lines are dropped (lean.h declares them).
src="$B/ir/\$1.c"; obj="$O/o/\$(echo "\$1" | tr / _).o"
[ "\$obj" -nt "\$src" ] && [ "\$obj" -nt "$HERE/leanprof.h" ] && exit 0
grep -v -E "^[A-Za-z_][A-Za-z0-9_ ]*[ *]+($names)\\(.*\\);\\\$" "\$src" | "$L/bin/clang" -x c -c -o "\$obj" - -include "$HERE/leanprof.h" \\
  -I "$L/include" -ffp-contract=off -fvisibility=hidden -Wno-unused-command-line-argument --sysroot "$L" -nostdinc \\
  -isystem "$L/include/clang" ${LEANPROF_OPT:--O1} -DNDEBUG -DLEAN_EXPORTING
ONE
chmod +x "$O/one.sh"
tr ' ' '\n' < "$B/bin/leanjs.rsp" | tr -d '"' | grep '\.c\.o\.export$' | sed 's#.*/build/ir/##; s#\.c\.o\.export$##' > "$O/modules.txt"
xargs -P "$J" -n 1 "$O/one.sh" < "$O/modules.txt"
cc -c -O1 -o "$O/leanprof.o" "$HERE/leanprof.c"
libs=$(tr ' ' '\n' < "$B/bin/leanjs.rsp" | tr -d '"' | grep '\.a$' | sed "s#.*/build/lib/#$B/lib/#" | tr '\n' ' ')
objs=$(sed "s#/#_#g; s#^#$O/o/#; s#\$#.o#" "$O/modules.txt" | tr '\n' ' ')
MACOSX_DEPLOYMENT_TARGET=99.0 "$L/bin/clang" -o "$O/leanjs-count" $objs "$O/leanprof.o" $libs -L "$L/lib/lean" --sysroot "$L" -L "$L/lib" \
  -L "$L/lib/libc" -fuse-ld=lld -lleancpp -lInit -lStd -lLean -lleanrt -lc++ -lLake -lgmp -luv -lssl -lcrypto -Wl,-dead_strip
echo "$O/leanjs-count"
