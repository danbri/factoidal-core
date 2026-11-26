# Authenticated proposer projection — kernel repair, 2026-11-25

Parent: #725; #1025, #1026 and #1027.

Base: 60422dd57d71e08a4d1555f39540f95bdcd49af1. Source repair: 8c90473bb2d437a30c825fd20b801c89ea9c8552. ProposerProjection.lean blob after repair: 700668e50fb126fde807b08f3750b0b9d62ac97f.

## Actual predecessor results

Run 45601564170, job 139161507579, merge checkout 8071b799565a78ac138a330b0ba52ec95a1558f8, tree 95dc74159b5e4acc63b90ad50083095390d71664. Independent fixture oracle passed: 102 expectations, two raw authenticated cases, six comparator controls. Combined compilation failed at ProposerProjection.lean:79:57, unexpected identifier; expected '}'. The failed mark_checked elaboration printed [sorryAx]; it is not a checked theorem. The other emitted reports in that failed compilation were mark_overflow [propext], authentication_error and authentication_success [propext, Quot.sound]. No native comparison ran and neither axiom-audit step ran. Do not promote these outputs into a passing checkpoint.

## Repair

Use a single-line record update in the mark_checked conclusion, removing the field-layout ambiguity. Exact source comparison confirms that reversing this whitespace change reproduces the predecessor file byte-for-byte. All executable definitions, theorem propositions (intended record update), tactics, imports, toolchain and test driver remain unchanged. No implementation dependency introduced.

Fresh hosted workflow must compile the actual combined graph, audit the exact four projection and seven authentication theorem reports, enforce source/import/native-link checks, and compare all 102 actual executable results with the existing independent oracle. The compiler/runtime and host transport remain trusted. No local Lean compiler is installed here; fresh proof and native results are not claimed by this record.

The output remains a partial commitment projection relative to supplied authenticated witnesses, NOT a protocol post-state. Exit queue, slashings vector, balances, proposer selection and rewards, canonical state authentication and complete transitions remain open. No main merge or release.
